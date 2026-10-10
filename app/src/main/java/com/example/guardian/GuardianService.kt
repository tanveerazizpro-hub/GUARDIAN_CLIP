package com.example.guardian

import android.Manifest
import android.annotation.SuppressLint
import android.app.Activity
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.bluetooth.BluetoothAdapter
import android.bluetooth.BluetoothDevice
import android.bluetooth.BluetoothManager
import android.bluetooth.BluetoothSocket
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.content.pm.PackageManager
import android.content.pm.ServiceInfo
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.media.MediaRecorder
import android.net.Uri
import android.os.Binder
import android.os.Build
import android.os.IBinder
import android.os.PowerManager
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.VibratorManager
import android.telephony.PhoneNumberUtils
import android.telephony.SmsManager
import android.telephony.SubscriptionManager
import android.util.Log
import androidx.core.app.ActivityCompat
import androidx.core.app.NotificationCompat
import androidx.core.app.ServiceCompat
import androidx.core.content.ContextCompat
import com.google.android.gms.location.FusedLocationProviderClient
import com.google.android.gms.location.LocationServices
import com.google.android.gms.location.Priority
import com.google.android.gms.tasks.CancellationTokenSource
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.cancel
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asStateFlow
import kotlinx.coroutines.isActive
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext
import java.io.File
import java.io.InputStream
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.UUID
import kotlin.math.sqrt

class GuardianService : Service(), SensorEventListener {

    sealed class GuardianState {
        /** The service is not running; no device monitoring is active. */
        object INACTIVE : GuardianState()
        /** The foreground service is running and monitoring safety signals. */
        object ARMED : GuardianState()
        data class COUNTDOWN(val remainingSeconds: Int, val reason: String) : GuardianState()
        data class EXECUTING(val currentTask: String) : GuardianState()
    }

    inner class LocalBinder : Binder() {
        fun getService(): GuardianService = this@GuardianService
    }

    private val binder = LocalBinder()
    private val serviceScope = CoroutineScope(SupervisorJob() + Dispatchers.Default)

    // Hardware Managers
    private lateinit var sensorManager: SensorManager
    private lateinit var vibrator: Vibrator
    private lateinit var fusedLocationClient: FusedLocationProviderClient
    private lateinit var powerManager: PowerManager
    private var wakeLock: PowerManager.WakeLock? = null

    // Sensors
    private var accelerometer: Sensor? = null
    private var gyroscope: Sensor? = null

    // Jobs
    private var countdownJob: Job? = null
    private var bluetoothJob: Job? = null

    // Struggle detection state
    private var lastStruggleTimestamp = 0L
    private var currentGyroMagnitude = 0.0f

    // Bluetooth
    private var bluetoothSocket: BluetoothSocket? = null
    private var inputStream: InputStream? = null

    // Audio Recorder
    private var mediaRecorder: MediaRecorder? = null
    private var audioRecordingFile: File? = null

    companion object {
        private const val TAG = "GuardianService"
        private const val PREFS_NAME = "guardian_prefs"
        private const val KEY_EMERGENCY_NUMBER = "emergency_contact_number"
        const val NOTIFICATION_ID = 9001
        const val CHANNEL_ID = "guardian_fgs_channel"
        const val COUNTDOWN_DURATION_SECONDS = 30
        const val AUDIO_RECORDING_DURATION_MS = 180_000L // 3 minutes

        // Emergency dispatch targets (can be updated dynamically from UI/preferences)
        var emergencyPhoneNumber: String = "+15551234567"
        var emergencySmsNumber: String = "+15551234567"

        // Universal Standard SPP UUID for HC-05 Bluetooth modules
        private val SPP_UUID: UUID = UUID.fromString("00001101-0000-1000-8000-00805F9B34FB")

        private val _guardianState = MutableStateFlow<GuardianState>(GuardianState.INACTIVE)
        val guardianState: StateFlow<GuardianState> = _guardianState.asStateFlow()

        // Service Command Actions
        const val ACTION_START_FGS = "ACTION_START_FGS"
        const val ACTION_STOP_FGS = "ACTION_STOP_FGS"
        const val ACTION_CANCEL_ALARM = "ACTION_CANCEL_ALARM"
        const val ACTION_MANUAL_SOS = "ACTION_MANUAL_SOS"
    }

    override fun onCreate() {
        super.onCreate()
        Log.d(TAG, "GuardianService initialized")

        initializeHardware()
        createNotificationChannel()
        startAsForegroundService()

        registerSensors()
        startBluetoothSerialListener()
        _guardianState.value = GuardianState.ARMED
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        when (intent?.action) {
            ACTION_CANCEL_ALARM -> cancelAlarm()
            ACTION_MANUAL_SOS -> triggerManualSos()
            ACTION_STOP_FGS -> stopServiceGracefully()
            else -> Log.d(TAG, "GuardianService running in foreground")
        }
        return START_STICKY
    }

    override fun onBind(intent: Intent?): IBinder = binder

    private fun initializeHardware() {
        sensorManager = getSystemService(Context.SENSOR_SERVICE) as SensorManager
        accelerometer = sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER)
        gyroscope = sensorManager.getDefaultSensor(Sensor.TYPE_GYROSCOPE)

        vibrator = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            val vibratorManager = getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as VibratorManager
            vibratorManager.defaultVibrator
        } else {
            @Suppress("DEPRECATION")
            getSystemService(Context.VIBRATOR_SERVICE) as Vibrator
        }

        fusedLocationClient = LocationServices.getFusedLocationProviderClient(this)

        powerManager = getSystemService(Context.POWER_SERVICE) as PowerManager
        wakeLock = powerManager.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "Guardian:HardwareDemoWakeLock").apply {
            setReferenceCounted(false)
            acquire(10 * 60 * 1000L) // 10 minute safe acquisition
        }
    }

    private fun createNotificationChannel() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            val channel = NotificationChannel(
                CHANNEL_ID,
                "Guardian Active Protection Service",
                NotificationManager.IMPORTANCE_HIGH
            ).apply {
                description = "Monitors safety triggers: HC-05 Bluetooth serial & struggle sensors"
                setShowBadge(true)
            }
            val manager = getSystemService(NotificationManager::class.java)
            manager.createNotificationChannel(channel)
        }
    }

    private fun startAsForegroundService() {
        val notification = buildServiceNotification("Guardian Active Protection: Armed & Monitoring")
        val foregroundServiceType = foregroundServiceTypeForGrantedPermissions()

        ServiceCompat.startForeground(this, NOTIFICATION_ID, notification, foregroundServiceType)
    }

    private fun foregroundServiceTypeForGrantedPermissions(): Int {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.Q) return 0

        var types = 0
        if (hasPermission(Manifest.permission.ACCESS_FINE_LOCATION) ||
            hasPermission(Manifest.permission.ACCESS_COARSE_LOCATION)
        ) {
            types = types or ServiceInfo.FOREGROUND_SERVICE_TYPE_LOCATION
        }
        if (hasPermission(Manifest.permission.RECORD_AUDIO)) {
            types = types or ServiceInfo.FOREGROUND_SERVICE_TYPE_MICROPHONE
        }
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.S ||
            hasPermission(Manifest.permission.BLUETOOTH_CONNECT)
        ) {
            types = types or ServiceInfo.FOREGROUND_SERVICE_TYPE_CONNECTED_DEVICE
        }
        return types
    }

    private fun hasPermission(permission: String): Boolean =
        ActivityCompat.checkSelfPermission(this, permission) == PackageManager.PERMISSION_GRANTED

    private fun buildServiceNotification(statusText: String): Notification {
        val launchIntent = packageManager.getLaunchIntentForPackage(packageName)
            ?: Intent(this, MainActivity::class.java)
        val pendingIntent = PendingIntent.getActivity(
            this,
            0,
            launchIntent,
            PendingIntent.FLAG_UPDATE_CURRENT or PendingIntent.FLAG_IMMUTABLE
        )

        return NotificationCompat.Builder(this, CHANNEL_ID)
            .setContentTitle("Guardian Safety System")
            .setContentText(statusText)
            .setSmallIcon(android.R.drawable.ic_dialog_alert)
            .setContentIntent(pendingIntent)
            .setOngoing(true)
            .setPriority(NotificationCompat.PRIORITY_HIGH)
            .build()
    }

    private fun updateNotification(statusText: String) {
        val notificationManager = getSystemService(NotificationManager::class.java)
        notificationManager.notify(NOTIFICATION_ID, buildServiceNotification(statusText))
    }

    private fun registerSensors() {
        accelerometer?.let {
            sensorManager.registerListener(this, it, SensorManager.SENSOR_DELAY_GAME)
        }
        gyroscope?.let {
            sensorManager.registerListener(this, it, SensorManager.SENSOR_DELAY_GAME)
        }
    }

    override fun onSensorChanged(event: SensorEvent?) {
        if (event == null) return

        when (event.sensor.type) {
            Sensor.TYPE_GYROSCOPE -> {
                val rx = event.values[0]
                val ry = event.values[1]
                val rz = event.values[2]
                currentGyroMagnitude = sqrt(rx * rx + ry * ry + rz * rz)
            }
            Sensor.TYPE_ACCELEROMETER -> {
                val ax = event.values[0]
                val ay = event.values[1]
                val az = event.values[2]
                val netAcc = sqrt(ax * ax + ay * ay + az * az) - SensorManager.GRAVITY_EARTH

                // Violent Struggle Detection:
                val isViolentSpike = netAcc > 26.0f && currentGyroMagnitude > 4.5f
                val now = System.currentTimeMillis()

                if (isViolentSpike && (now - lastStruggleTimestamp > 8000L)) {
                    lastStruggleTimestamp = now
                    Log.w(TAG, "Violent struggle detected: Acc=$netAcc m/s2, Gyro=$currentGyroMagnitude rad/s")
                    triggerAlarm("Violent Struggle Detected")
                }
            }
        }
    }

    override fun onAccuracyChanged(sensor: Sensor?, accuracy: Int) {}

    private fun startBluetoothSerialListener() {
        bluetoothJob = serviceScope.launch(Dispatchers.IO) {
            val bluetoothManager = getSystemService(Context.BLUETOOTH_SERVICE) as? BluetoothManager
            val adapter: BluetoothAdapter? = bluetoothManager?.adapter

            if (adapter == null || !adapter.isEnabled) {
                Log.w(TAG, "Bluetooth not available or disabled")
                return@launch
            }

            while (isActive) {
                try {
                    if (ActivityCompat.checkSelfPermission(this@GuardianService, Manifest.permission.BLUETOOTH_CONNECT) 
                        != PackageManager.PERMISSION_GRANTED && Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
                        Log.w(TAG, "BLUETOOTH_CONNECT permission missing")
                        delay(5000)
                        continue
                    }

                    val bondedDevices = adapter.bondedDevices
                    val hc05Device = bondedDevices.find { 
                        it.name?.contains("HC-05", ignoreCase = true) == true ||
                        it.name?.contains("Guardian", ignoreCase = true) == true
                    } ?: bondedDevices.firstOrNull()

                    if (hc05Device == null) {
                        Log.d(TAG, "No HC-05 device bonded. Retrying in 10s...")
                        delay(10000)
                        continue
                    }

                    Log.d(TAG, "Connecting to Bluetooth Device: ${hc05Device.name} (${hc05Device.address})")
                    bluetoothSocket = hc05Device.createRfcommSocketToServiceRecord(SPP_UUID)
                    adapter.cancelDiscovery()
                    bluetoothSocket?.connect()

                    Log.d(TAG, "HC-05 Serial Connected! Listening for 'S' or 'SOS'...")
                    inputStream = bluetoothSocket?.inputStream
                    val buffer = ByteArray(1024)

                    while (isActive) {
                        val bytesRead = inputStream?.read(buffer) ?: -1
                        if (bytesRead > 0) {
                            val receivedText = String(buffer, 0, bytesRead).trim()
                            Log.d(TAG, "Bluetooth serial received: '$receivedText'")

                            if (receivedText.contains("S") || receivedText.contains("SOS")) {
                                withContext(Dispatchers.Main) {
                                    triggerAlarm("HC-05 Bluetooth Emergency Signal ('$receivedText')")
                                }
                            }
                        } else if (bytesRead == -1) {
                            break
                        }
                    }
                } catch (e: Exception) {
                    Log.e(TAG, "Bluetooth loop connection error: ${e.message}")
                    try {
                        bluetoothSocket?.close()
                    } catch (_: Exception) {}
                    delay(5000)
                }
            }
        }
    }

    @Synchronized
    fun triggerAlarm(reason: String) {
        if (_guardianState.value is GuardianState.EXECUTING) {
            Log.d(TAG, "Already executing emergency protocol")
            return
        }

        Log.w(TAG, "Alarm triggered: $reason. Starting heartbeat vibration & countdown.")
        countdownJob?.cancel()

        playHeartbeatVibration()

        countdownJob = serviceScope.launch(Dispatchers.Main) {
            for (sec in COUNTDOWN_DURATION_SECONDS downTo 1) {
                _guardianState.value = GuardianState.COUNTDOWN(remainingSeconds = sec, reason = reason)
                updateNotification("EMERGENCY COUNTDOWN: ${sec}s remaining! (Reason: $reason)")
                delay(1000L)
            }
            executeEmergencyProtocol()
        }
    }

    fun triggerManualSos() {
        Log.w(TAG, "Manual SOS triggered directly!")
        countdownJob?.cancel()
        vibrator.cancel()
        serviceScope.launch(Dispatchers.Main) {
            executeEmergencyProtocol()
        }
    }

    fun cancelAlarm() {
        Log.d(TAG, "Alarm cancelled by user. Resetting to IDLE.")
        countdownJob?.cancel()
        countdownJob = null
        vibrator.cancel()
        resetStruggleDetection()
        _guardianState.value = GuardianState.ARMED
        updateNotification("Guardian Active Protection: Armed & Monitoring")
    }

    private fun resetStruggleDetection() {
        lastStruggleTimestamp = 0L
        currentGyroMagnitude = 0f
    }

    private fun playHeartbeatVibration() {
        val timings = longArrayOf(0, 150, 100, 150, 600)
        val amplitudes = intArrayOf(0, 255, 0, 255, 0)

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            val effect = VibrationEffect.createWaveform(timings, amplitudes, 0)
            vibrator.vibrate(effect)
        } else {
            @Suppress("DEPRECATION")
            vibrator.vibrate(timings, 0)
        }
    }

    private fun playShortVibration() {
        vibrator.cancel()
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            vibrator.vibrate(VibrationEffect.createOneShot(500, VibrationEffect.DEFAULT_AMPLITUDE))
        } else {
            @Suppress("DEPRECATION")
            vibrator.vibrate(500)
        }
    }

    private suspend fun executeEmergencyProtocol() {
        _guardianState.value = GuardianState.EXECUTING("Initiating Emergency Actions")
        playShortVibration()

        updateNotification("EXECUTING: Acquiring precise GPS coordinates...")
        _guardianState.value = GuardianState.EXECUTING("Fetching GPS Location")
        val locationString = fetchCurrentGpsLocation()

        updateNotification("EXECUTING: Dispatching emergency SMS with GPS link...")
        _guardianState.value = GuardianState.EXECUTING("Sending Emergency SMS")
        val mapsLink = if (locationString != null) {
            "https://maps.google.com/?q=$locationString"
        } else {
            "Location unavailable (GPS timeout)"
        }
        val smsMessage = "SOS! I need help. Location: $mapsLink"
        sendEmergencySms(emergencySmsRecipient(), smsMessage)

        updateNotification("EXECUTING: Placing phone call to emergency contact...")
        _guardianState.value = GuardianState.EXECUTING("Calling Emergency Contact")
        placeEmergencyCall(emergencyPhoneNumber)

        updateNotification("EXECUTING: Recording 3 minutes of ambient evidence...")
        _guardianState.value = GuardianState.EXECUTING("Recording 3-min Ambient Audio")
        startAudioRecording()

        delay(AUDIO_RECORDING_DURATION_MS)
        stopAudioRecording()

        Log.d(TAG, "Emergency execution completed. Resetting to IDLE.")
        _guardianState.value = GuardianState.ARMED
        updateNotification("Guardian Active Protection: Armed & Monitoring")
    }

    @SuppressLint("MissingPermission")
    private suspend fun fetchCurrentGpsLocation(): String? = withContext(Dispatchers.IO) {
        val hasFine = ActivityCompat.checkSelfPermission(this@GuardianService, Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED
        val hasCoarse = ActivityCompat.checkSelfPermission(this@GuardianService, Manifest.permission.ACCESS_COARSE_LOCATION) == PackageManager.PERMISSION_GRANTED

        if (!hasFine && !hasCoarse) {
            Log.e(TAG, "Location permissions not granted")
            return@withContext null
        }

        try {
            val cts = CancellationTokenSource()
            val location = fusedLocationClient.getCurrentLocation(
                Priority.PRIORITY_HIGH_ACCURACY,
                cts.token
            ).addOnFailureListener {
                Log.e(TAG, "Failed to get current location: ${it.message}")
            }

            var elapsed = 0
            while (!location.isComplete && elapsed < 70) {
                delay(100)
                elapsed++
            }

            if (location.isSuccessful && location.result != null) {
                val loc = location.result
                return@withContext "${loc.latitude},${loc.longitude}"
            }
        } catch (e: Exception) {
            Log.e(TAG, "Exception getting GPS: ${e.message}")
        }
        return@withContext null
    }

    private fun getTargetSmsManager(): SmsManager {
        return if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            val baseSmsManager = getSystemService(SmsManager::class.java)
            val defaultSubId = SubscriptionManager.getDefaultSmsSubscriptionId()

            if (defaultSubId != SubscriptionManager.INVALID_SUBSCRIPTION_ID) {
                baseSmsManager.createForSubscriptionId(defaultSubId)
            } else {
                baseSmsManager
            }
        } else {
            @Suppress("DEPRECATION")
            SmsManager.getDefault()
        }
    }

    private fun sendEmergencySms(phoneNumber: String, message: String) {
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.SEND_SMS) != PackageManager.PERMISSION_GRANTED) {
            Log.e(TAG, "Cannot dispatch SMS: SEND_SMS permission is missing")
            return
        }

        val sanitizedNumber = PhoneNumberUtils.normalizeNumber(phoneNumber)
        if (sanitizedNumber.isNullOrBlank()) {
            Log.e(TAG, "Cannot dispatch SMS: Destination number is blank")
            return
        }

        try {
            val smsManager = getTargetSmsManager()
            val parts = smsManager.divideMessage(message)

            if (parts.isEmpty()) return

            val smsStatusReceiver = object : BroadcastReceiver() {
                private var partsRemaining = parts.size
                override fun onReceive(context: Context?, intent: Intent?) {
                    val partIndex = intent?.getIntExtra("part_index", -1) ?: -1
                    when (resultCode) {
                        Activity.RESULT_OK -> Log.d(TAG, "SMS part #$partIndex successfully routed to carrier cell tower.")
                        SmsManager.RESULT_ERROR_GENERIC_FAILURE -> Log.e(TAG, "SMS part #$partIndex failed: GENERIC_FAILURE (Modem/carrier reject)")
                        SmsManager.RESULT_ERROR_RADIO_OFF -> Log.e(TAG, "SMS part #$partIndex failed: RADIO_OFF")
                        SmsManager.RESULT_ERROR_NO_SERVICE -> Log.e(TAG, "SMS part #$partIndex failed: NO_SERVICE")
                        else -> Log.e(TAG, "SMS part #$partIndex failed with resultCode: $resultCode")
                    }
                    partsRemaining--
                    if (partsRemaining <= 0) {
                        try { unregisterReceiver(this) } catch (_: Exception) {}
                    }
                }
            }

            val filter = IntentFilter("com.example.guardian.SMS_SENT")
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
                registerReceiver(smsStatusReceiver, filter, Context.RECEIVER_NOT_EXPORTED)
            } else {
                registerReceiver(smsStatusReceiver, filter)
            }

            val flags = PendingIntent.FLAG_UPDATE_CURRENT or PendingIntent.FLAG_IMMUTABLE

            if (parts.size == 1) {
                val sentIntent = PendingIntent.getBroadcast(
                    this, 0,
                    Intent("com.example.guardian.SMS_SENT").apply { setPackage(packageName); putExtra("part_index", 0) },
                    flags
                )
                smsManager.sendTextMessage(sanitizedNumber, null, parts[0], sentIntent, null)
                Log.d(TAG, "Single-part SMS queued for $sanitizedNumber")
            } else {
                val sentIntents = ArrayList<PendingIntent>(parts.size)
                for (index in parts.indices) {
                    sentIntents.add(
                        PendingIntent.getBroadcast(
                            this, index,
                            Intent("com.example.guardian.SMS_SENT").apply { setPackage(packageName); putExtra("part_index", index) },
                            flags
                        )
                    )
                }
                smsManager.sendMultipartTextMessage(sanitizedNumber, null, parts, sentIntents, null)
                Log.d(TAG, "Multi-part SMS (${parts.size} segments) queued for $sanitizedNumber")
            }
        } catch (e: Exception) {
            Log.e(TAG, "Fatal failure invoking SmsManager", e)
        }
    }

    private fun emergencySmsRecipient(): String {
        val storedNumber = getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE)
            .getString(KEY_EMERGENCY_NUMBER, emergencySmsNumber)
            .orEmpty()
        return PhoneNumberUtils.normalizeNumber(storedNumber) ?: ""
    }

    private fun placeEmergencyCall(phoneNumber: String) {
        if (ActivityCompat.checkSelfPermission(this, Manifest.permission.CALL_PHONE) != PackageManager.PERMISSION_GRANTED) {
            Log.e(TAG, "CALL_PHONE permission not granted")
            return
        }

        try {
            val callIntent = Intent(Intent.ACTION_CALL).apply {
                data = Uri.parse("tel:$phoneNumber")
                addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            }
            startActivity(callIntent)
            Log.d(TAG, "Emergency call placed to $phoneNumber")
        } catch (e: Exception) {
            Log.e(TAG, "Failed to place emergency call: ${e.message}")
        }
    }

    private fun startAudioRecording() {
        if (ActivityCompat.checkSelfPermission(this, Manifest.permission.RECORD_AUDIO) != PackageManager.PERMISSION_GRANTED) {
            Log.e(TAG, "RECORD_AUDIO permission not granted")
            return
        }

        try {
            val dir = File(filesDir, "guardian_evidence").apply { mkdirs() }
            val timeStamp = SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(Date())
            audioRecordingFile = File(dir, "EVIDENCE_${timeStamp}.m4a")

            mediaRecorder = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
                MediaRecorder(this)
            } else {
                @Suppress("DEPRECATION")
                MediaRecorder()
            }.apply {
                setAudioSource(MediaRecorder.AudioSource.MIC)
                setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
                setAudioEncoder(MediaRecorder.AudioEncoder.AAC)
                setAudioEncodingBitRate(128000)
                setAudioSamplingRate(44100)
                setOutputFile(audioRecordingFile?.absolutePath)
                prepare()
                start()
            }
            Log.d(TAG, "3-min ambient audio recording started: ${audioRecordingFile?.absolutePath}")
        } catch (e: Exception) {
            Log.e(TAG, "Failed to start MediaRecorder: ${e.message}")
        }
    }

    private fun stopAudioRecording() {
        val recorder = mediaRecorder ?: return
        mediaRecorder = null
        try {
            recorder.stop()
            Log.d(TAG, "Ambient audio recording completed successfully.")
        } catch (e: RuntimeException) {
            Log.w(TAG, "Audio recording ended before it could be finalized: ${e.message}")
        } finally {
            recorder.release()
        }
    }

    private fun stopServiceGracefully() {
        cancelAlarm()
        stopAudioRecording()
        try {
            bluetoothSocket?.close()
        } catch (_: Exception) {}
        serviceScope.cancel()
        sensorManager.unregisterListener(this)
        wakeLock?.let {
            if (it.isHeld) it.release()
        }
        stopForeground(STOP_FOREGROUND_REMOVE)
        _guardianState.value = GuardianState.INACTIVE
        stopSelf()
    }

    override fun onDestroy() {
        stopServiceGracefully()
        super.onDestroy()
    }
}
