require "import"
import "android.app.*"
import "android.os.*"
import "android.widget.*"
import "android.view.*"
import "android.content.*"
import "android.provider.MediaStore"
import "android.text.*"
import "android.graphics.Color"
import "android.graphics.Typeface"
import "android.graphics.Bitmap"
import "android.graphics.Canvas"
import "android.graphics.Paint"
import "android.graphics.Rect"
import "android.graphics.drawable.ColorDrawable"
import "android.graphics.drawable.GradientDrawable"
import "android.view.Gravity"
import "android.view.Surface"
import "android.view.inputmethod.EditorInfo"
import "android.media.MediaPlayer"
import "android.media.MediaExtractor"
import "android.media.MediaMuxer"
import "android.media.MediaFormat"
import "android.media.MediaCodec"
import "android.media.MediaCodecInfo"
import "android.media.MediaRecorder"
import "android.media.MediaMetadataRetriever"
import "android.media.MediaScannerConnection"
import "android.media.PlaybackParams"
import "android.media.audiofx.LoudnessEnhancer"
import "android.speech.tts.TextToSpeech"
import "java.nio.ByteBuffer"
import "java.nio.ByteOrder"
import "java.io.File"
import "java.io.FileInputStream"
import "java.io.FileOutputStream"
import "java.text.SimpleDateFormat"
import "java.util.Date"
import "java.util.Locale"
import "java.lang.System"
import "java.lang.Thread"
import "java.lang.Runnable"
import "java.lang.String"
import "android.net.Uri"
import "android.database.Cursor"
import "android.content.Intent"

if not activity then
    if service then
        service.speak("Please open Smart Media Studio Pro from the Jieshuo Plugins menu.")
    end
    return true
end

local ctx = activity

pcall(function()
    local builder = StrictMode.VmPolicy.Builder()
    StrictMode.setVmPolicy(builder.build())
end)

local prefs = ctx.getSharedPreferences("AudioVideoEditorPrefs", Context.MODE_PRIVATE)

-- ================= HAPTIC VIBRATION (35ms - Proven Method) =================
local function vibrate(ms)
    pcall(function()
        local v = activity.getSystemService(Context.VIBRATOR_SERVICE)
        if v then v.vibrate(ms or 35) end
    end)
end

-- Vibrate immediately when the tool is executed/opened!
vibrate(35)

-- ================= PRO MEDIA STUDIO COLOR PALETTES (Tailored Per Window!) =================
-- Every window has its own distinct, purpose-built Pro Media Studio theme (zero white backgrounds!)
local STUDIO_MAIN_BG     = 0xFF12101B
local STUDIO_MAIN_CARD   = 0xFF1E1B2E
local STUDIO_MAIN_HDR1   = 0xFF3B0764
local STUDIO_MAIN_HDR2   = 0xFF1E1B4B
local STUDIO_NEON_CYAN   = 0xFF22D3EE
local STUDIO_WARM_GOLD   = 0xFFFBBF24
local STUDIO_PURE_TEXT   = 0xFFF8FAFC
local STUDIO_MUTED_TEXT  = 0xFFCBD5E1

local function rnd(c, r)
    local gd = GradientDrawable()
    gd.setColor(c)
    gd.setCornerRadius(r or 20)
    return gd
end

local function grad(s, e, r)
    local gd = GradientDrawable(GradientDrawable.Orientation.TL_BR, {s, e})
    gd.setCornerRadius(r or 22)
    return gd
end

local function brd(bg, bc, r, strokeW)
    local gd = GradientDrawable()
    gd.setColor(bg or STUDIO_MAIN_CARD)
    gd.setStroke(strokeW or 3, bc or 0xFF8B5CF6)
    gd.setCornerRadius(r or 20)
    return gd
end

local function gradBrd(c1, c2, borderCol, r, strokeW)
    local gd = GradientDrawable(GradientDrawable.Orientation.TL_BR, {c1, c2})
    gd.setCornerRadius(r or 22)
    gd.setStroke(strokeW or 3, borderCol or STUDIO_NEON_CYAN)
    return gd
end

local function styleDialogWindow(dlg)
    pcall(function()
        dlg.getWindow().setBackgroundDrawable(ColorDrawable(Color.TRANSPARENT))
    end)
end

-- ================= GLOBAL STATE =================
local media_type = 0 -- 0 = Audio, 1 = Video
local app_mode = 0   -- 0 = Editing, 1 = Add Music to Voice
local current_op = nil

local primary_file = nil   -- {uri=..., path=..., name=..., duration=...}
local secondary_file = nil -- {uri=..., path=..., name=..., duration=...}
local merge_list = {}      -- List of {uri=..., path=..., name=..., duration=...}

local voice_file = nil
local music_file = nil
local smart_filtering_enabled = true
local voice_vol_pct = 100
local music_high_pct = 75
local music_duck_pct = 28
local master_boost_pct = 100

local voice_envelope = {}
local voice_scan_ready = false
local voice_has_detected_pauses = false

local start_time_ms = 0
local end_time_ms = 0
local video_quality_idx = 0  -- 0=Original(Fastest), 1=Ultra HD 4K/8K, 2=Full HD 1080p, 3=HD 720p, 4=SD 480p, 5=Low 360p
local split_layout_mode = 0  -- 0=Top & Bottom (Upper & Lower Half Screen), 1=Left & Right (Side by Side Half Screen)

-- New Studio Feature State Variables
local conv_format_idx = 0    -- 0=M4A, 1=MP3, 2=WAV, 3=AAC, 4=MP4 Video
local conv_bitrate_idx = 0   -- 0=320kbps, 1=256kbps, 2=192kbps, 3=128kbps, 4=64kbps
local echo_preset_idx = 0    -- 0=Madinah Hall, 1=Studio Vocal, 2=Deep Mosque, 3=Double Chorus, 4=Custom
local echo_delay_ms = 220    -- 50ms to 600ms
local echo_decay_pct = 45    -- 10% to 85%
local echo_voice_boost_pct = 120 -- 50% to 200%
local noise_strength_pct = 80    -- 10% to 100%
local noise_voice_boost_pct = 130 -- 100% to 200%
local vol_booster_pct = 200      -- 20% to 300%
local rec_clean_noise = true
local rec_add_echo = false
local rec_voice_boost_pct = 130

local previewPlayer = MediaPlayer()
local bgMusicPlayer = MediaPlayer()
local outVoicePlayer = MediaPlayer()
local outMusicPlayer = MediaPlayer()
local voiceBooster = nil
local bgMusicBooster = nil
local outVoiceBooster = nil
local outMusicBooster = nil

local active_sequence_list = nil
local active_sequence_idx = 1

local uiHandler = Handler(Looper.getMainLooper())
local is_preview_prepared = false
local is_playing = false
local current_speed = 1.0
local tts = nil

local loaded_preview_id = ""
local loaded_bg_id = ""

local mediaRecorder = nil
local is_recording = false
local system_picker_callback = nil

local showMainWindow
local openOperationWindow
local showOutputReadyDialog

-- ================= TTS, WHATSAPP FEEDBACK & SYSTEM NOTIFICATION HELPERS =================
tts = TextToSpeech(ctx, TextToSpeech.OnInitListener{
    onInit = function(status)
        if status == TextToSpeech.SUCCESS then
            pcall(function() tts.setLanguage(Locale.US) end)
        end
    end
})

local function speak(msg)
    local text = tostring(msg)
    pcall(function()
        if service and service.speak then
            service.speak(text)
        elseif tts then
            tts.speak(text, TextToSpeech.QUEUE_FLUSH, nil)
        end
    end)
end

-- Pre-filled WhatsApp Feedback Message with Developer Name & Tool Name!
local function openWhatsAppFeedback()
    vibrate(35)
    local prefilledMsg = "Assalam o Alaikum Abdul Rehman! I am using your Smart Media Studio Pro (Audio Video Editor) tool and contacting you to share my feedback: "
    local encodedMsg = Uri.encode(prefilledMsg)
    local ok = pcall(function()
        local uri = Uri.parse("https://wa.me/923124255300?text=" .. tostring(encodedMsg))
        local intent = Intent(Intent.ACTION_VIEW, uri)
        intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
        activity.startActivity(intent)
    end)
    if not ok then
        pcall(function()
            local uri2 = Uri.parse("https://api.whatsapp.com/send?phone=923124255300&text=" .. tostring(encodedMsg))
            local intent2 = Intent(Intent.ACTION_VIEW, uri2)
            activity.startActivity(intent2)
        end)
    end
end

local function sendCompletionNotification(titleText, bodyText)
    vibrate(35)
    speak(titleText .. ". " .. bodyText)
    pcall(function()
        local nm = ctx.getSystemService(Context.NOTIFICATION_SERVICE)
        local channelId = "smart_media_studio_done"
        local builder = nil
        if Build.VERSION.SDK_INT >= 26 then
            local NotificationChannel = luajava.bindClass("android.app.NotificationChannel")
            local chan = NotificationChannel(channelId, "Smart Media Studio Pro", NotificationManager.IMPORTANCE_HIGH)
            nm.createNotificationChannel(chan)
            builder = Notification.Builder(ctx, channelId)
        else
            builder = Notification.Builder(ctx)
            builder.setPriority(Notification.PRIORITY_HIGH)
        end
        pcall(function()
            local reopenIntent = Intent(ctx, ctx.getClass())
            reopenIntent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            reopenIntent.addFlags(Intent.FLAG_ACTIVITY_REORDER_TO_FRONT)
            reopenIntent.addFlags(Intent.FLAG_ACTIVITY_SINGLE_TOP)
            local flags = (Build.VERSION.SDK_INT >= 31) and 67108864 or 0
            local pi = PendingIntent.getActivity(ctx, 88991, reopenIntent, flags)
            builder.setContentIntent(pi)
        end)
        builder.setContentTitle(tostring(titleText))
        builder.setContentText(tostring(bodyText))
        builder.setSmallIcon(android.R.drawable.stat_sys_download_done)
        builder.setAutoCancel(true)
        nm.notify(88991, builder.build())
    end)
    pcall(function()
        Toast.makeText(ctx, tostring(titleText) .. ": " .. tostring(bodyText), Toast.LENGTH_LONG).show()
    end)
end

local function setT(view, text)
    if not view then return end
    local str = tostring(text)
    if tostring(view):find("ProgressDialog") then
        view.setMessage(str)
    else
        view.setText(str)
    end
end

local function sanitizeName(name)
    if not name then return "media_file" end
    local n = tostring(name):gsub('[\\/:*?"<>|]', "_")
    return n ~= "" and n or "media_file"
end

local function formatDurationMs(ms)
    if not ms or ms <= 0 then return "00:00.000" end
    local totalMs = math.floor(ms)
    local totalSec = math.floor(totalMs / 1000)
    local m = math.floor(totalSec / 60)
    local s = totalSec % 60
    local msec = totalMs % 1000
    return string.format("%02d:%02d.%03d", m, s, msec)
end

local function getDownloadDir()
    local dir = "/storage/emulated/0/Download/Audio Video Editor/"
    local folder = File(dir)
    if not folder.exists() then folder.mkdirs() end
    return dir
end

local function getTempCacheDir()
    local base = ctx.getExternalCacheDir() or ctx.getCacheDir()
    local dir = tostring(base.getAbsolutePath()) .. "/ave_work/"
    local folder = File(dir)
    if not folder.exists() then folder.mkdirs() end
    return dir
end

local function getDownloadPath(filename)
    return getDownloadDir() .. sanitizeName(filename)
end

local function scanMediaFile(filePath, onScannedCallback)
    pcall(function()
        MediaScannerConnection.scanFile(
            ctx,
            String{tostring(filePath)},
            nil,
            MediaScannerConnection.OnScanCompletedListener{
                onScanCompleted = function(path, uri)
                    if onScannedCallback then
                        uiHandler.post(Runnable{
                            run = function() onScannedCallback(path, uri) end
                        })
                    end
                end
            }
        )
    end)
end

local function copyFileReliable(srcPath, dstPath)
    local srcFile = File(tostring(srcPath))
    if not srcFile.exists() or srcFile.length() == 0 then
        error("Source file is empty or missing")
    end
    local dstFile = File(tostring(dstPath))
    local parent = dstFile.getParentFile()
    if parent and not parent.exists() then parent.mkdirs() end

    local fis = FileInputStream(srcFile)
    local fos = FileOutputStream(dstFile)
    local inChan = fis.getChannel()
    local outChan = fos.getChannel()
    local buf = ByteBuffer.allocateDirect(262144)

    while true do
        buf.clear()
        local r = inChan.read(buf)
        if r <= 0 then break end
        buf.flip()
        while buf.hasRemaining() do
            outChan.write(buf)
        end
    end

    outChan.force(true)
    inChan.close()
    outChan.close()
    fos.flush()
    fos.close()
    fis.close()
end

-- ================= UI COMPONENT BUILDERS (Pro Studio Aesthetic) =================
local function styleCard(view, bgColor, strokeColor, strokeWidth, cornerRadius)
    local c = bgColor or STUDIO_MAIN_CARD
    if c == 0xFFFFFFFF or c == 0xFFF4F7FA or c == 0xFFF8FAFC or c == 0xFFEAF2F8 or c == 0xFFE3F2FD or c == 0xFFF3E5F5 or c == 0xFFE0F2F1 or c == 0xFFFFF8E1 then
        c = STUDIO_MAIN_CARD
    end
    view.setBackground(brd(c, strokeColor or 0xFF8B5CF6, cornerRadius or 22, strokeWidth or 3))
end

local function createStyledButton(text, bgColor, textColor, strokeColor, radius)
    local b = Button(ctx)
    setT(b, text)
    b.setAllCaps(false)
    b.setTextColor(textColor or 0xFFFFFFFF)
    b.setTextSize(14)
    b.setTypeface(nil, Typeface.BOLD)
    b.setPadding(22, 26, 22, 26)
    pcall(function()
        b.setFocusable(true)
    end)
    local c1 = bgColor or 0xFF6D28D9
    local c2 = strokeColor or 0xFF4C1D95
    b.setBackground(gradBrd(c1, c2, 0x55FFFFFF, radius or 22, 2))
    return b
end

local function createStyledCard(bgColor, borderColor, padding)
    local card = LinearLayout(ctx)
    card.setOrientation(1)
    local p = padding or 26
    card.setPadding(p, p, p, p)
    local c = bgColor or STUDIO_MAIN_CARD
    if c == 0xFFFFFFFF or c == 0xFFF4F7FA or c == 0xFFF8FAFC or c == 0xFFEAF2F8 or c == 0xFFE3F2FD or c == 0xFFF3E5F5 or c == 0xFFE0F2F1 or c == 0xFFFFF8E1 then
        c = STUDIO_MAIN_CARD
    end
    card.setBackground(brd(c, borderColor or 0xFF8B5CF6, 22, 3))
    local lp = LinearLayout.LayoutParams(-1, -2)
    lp.setMargins(0, 12, 0, 12)
    card.setLayoutParams(lp)
    return card
end

local function addSpacer(parent, heightPx)
    local sp = View(ctx)
    sp.setLayoutParams(LinearLayout.LayoutParams(-1, heightPx or 14))
    parent.addView(sp)
end

local function createSpinnerContainer(spinnerView, borderColor)
    local box = LinearLayout(ctx)
    box.setOrientation(1)
    box.setPadding(16, 8, 16, 8)
    box.setBackground(brd(0xFFE0E7FF, borderColor or STUDIO_NEON_CYAN, 16, 3))
    box.addView(spinnerView)
    return box
end

-- ================= MEDIA DATA SOURCE HELPERS =================
local function isLegacyBrokenFileName(name)
    if not name then return false end
    local n = tostring(name)
    if n:find("^Merged_") and n:lower():find("%.mp3$") then
        return true
    end
    return false
end

local function purgeBrokenEditorFiles()
    pcall(function()
        pcall(function() File("/storage/emulated/0/Download/Audio Video Editor/Merged_3Audios_151308.mp3").delete() end)
        pcall(function() File("/storage/emulated/0/Download/AudioVideoEditor/Merged_3Audios_151308.mp3").delete() end)
    end)
end
purgeBrokenEditorFiles()

local function createOpenExtractor(uri, filePath)
    local ex = nil
    local handleToClose = nil

    if filePath and tostring(filePath) ~= "" then
        pcall(function()
            local origF = File(tostring(filePath))
            if not origF.exists() or origF.length() < 256 then
                local baseName = tostring(origF.getName())
                local cacheCandidate = File(getTempCacheDir() .. baseName)
                if cacheCandidate.exists() and cacheCandidate.length() >= 256 then
                    filePath = cacheCandidate.getAbsolutePath()
                end
            end
        end)
    end

    if not ex and filePath and tostring(filePath) ~= "" then
        pcall(function()
            local f = File(tostring(filePath))
            if f.exists() and f.length() >= 256 then
                local fis = FileInputStream(f)
                local ok = pcall(function()
                    local e = MediaExtractor()
                    e.setDataSource(fis.getFD())
                    if e.getTrackCount() > 0 then
                        ex = e
                        handleToClose = fis
                    else
                        e.release()
                    end
                end)
                if not ok or not ex then
                    pcall(function() fis.close() end)
                end
            end
        end)
    end

    if not ex and filePath and tostring(filePath) ~= "" then
        pcall(function()
            local f = File(tostring(filePath))
            if f.exists() and f.length() >= 256 then
                local e = MediaExtractor()
                e.setDataSource(tostring(filePath))
                if e.getTrackCount() > 0 then
                    ex = e
                else
                    e.release()
                end
            end
        end)
    end

    if not ex and uri then
        pcall(function()
            local pfd = ctx.getContentResolver().openFileDescriptor(uri, "r")
            if pfd then
                local ok = pcall(function()
                    local e = MediaExtractor()
                    e.setDataSource(pfd.getFileDescriptor())
                    if e.getTrackCount() > 0 then
                        ex = e
                        handleToClose = pfd
                    else
                        e.release()
                    end
                end)
                if not ok or not ex then
                    pcall(function() pfd.close() end)
                end
            end
        end)
    end

    if not ex and uri then
        pcall(function()
            local e = MediaExtractor()
            e.setDataSource(ctx, uri, nil)
            if e.getTrackCount() > 0 then
                ex = e
            else
                e.release()
            end
        end)
    end

    return ex, handleToClose
end

local function setPlayerSourceSafe(mp, uri, filePath)
    local opened = false
    if filePath and tostring(filePath) ~= "" then
        pcall(function()
            local f = File(tostring(filePath))
            if f.exists() and f.length() >= 256 then
                local fis = FileInputStream(f)
                mp.setDataSource(fis.getFD())
                fis.close()
                opened = true
            end
        end)
        if not opened then
            pcall(function()
                mp.setDataSource(tostring(filePath))
                opened = true
            end)
        end
    end
    if not opened and uri then
        pcall(function()
            local pfd = ctx.getContentResolver().openFileDescriptor(uri, "r")
            if pfd then
                mp.setDataSource(pfd.getFileDescriptor())
                pfd.close()
                opened = true
            end
        end)
        if not opened then
            pcall(function()
                mp.setDataSource(ctx, uri)
                opened = true
            end)
        end
    end
end

local function getMediaDuration(uri, filePath)
    local dur = 0
    pcall(function()
        local mp = MediaPlayer()
        setPlayerSourceSafe(mp, uri, filePath)
        mp.prepare()
        dur = mp.getDuration()
        mp.release()
    end)
    return dur
end

-- ================= VOICE PAUSE & SPEECH DETECTOR (Runs via AndroLua task() in isolated LuaState!) =================
local function scanVoiceSilenceAndSpeechAsync(vFile, onCompleteCallback)
    voice_envelope = {}
    voice_scan_ready = false
    voice_has_detected_pauses = false
    if not vFile then return end

    local vPath = vFile.path and tostring(vFile.path) or ""
    local vUriStr = vFile.uri and tostring(vFile.uri) or ""

    task(function(act, pathStr, uriStr)
        require "import"
        import "android.media.MediaExtractor"
        import "android.media.MediaFormat"
        import "android.media.MediaCodec"
        import "java.nio.ByteOrder"
        import "java.io.File"
        import "java.io.FileInputStream"
        import "android.net.Uri"

        local activeBuckets = {}
        local pauseFound = false
        local speechFound = false

        pcall(function()
            local ex = nil
            local pfd = nil
            if pathStr ~= "" then
                pcall(function()
                    local f = File(pathStr)
                    if f.exists() and f.length() > 256 then
                        local fis = FileInputStream(f)
                        local e = MediaExtractor()
                        e.setDataSource(fis.getFD())
                        ex = e
                        pfd = fis
                    end
                end)
            end
            if not ex and uriStr ~= "" then
                pcall(function()
                    local u = Uri.parse(uriStr)
                    local d = act.getContentResolver().openFileDescriptor(u, "r")
                    if d then
                        local e = MediaExtractor()
                        e.setDataSource(d.getFileDescriptor())
                        ex = e
                        pfd = d
                    end
                end)
            end
            if not ex then return end

            local aTrack = -1
            local fmt = nil
            for i = 0, ex.getTrackCount() - 1 do
                local f = ex.getTrackFormat(i)
                local m = f.getString(MediaFormat.KEY_MIME)
                if m and m:find("audio/") then
                    aTrack = i; fmt = f; break
                end
            end

            if aTrack ~= -1 and fmt then
                ex.selectTrack(aTrack)
                local mime = fmt.getString(MediaFormat.KEY_MIME)
                local decoder = MediaCodec.createDecoderByType(mime)
                decoder.configure(fmt, nil, nil, 0)
                decoder.start()

                local inBuffers = nil
                local outBuffers = nil
                pcall(function()
                    inBuffers = decoder.getInputBuffers()
                    outBuffers = decoder.getOutputBuffers()
                end)

                local info = MediaCodec.BufferInfo()
                local exDone = false
                local decDone = false
                local eosCount = 0
                local maxBucket = 0
                local rawEnergies = {}

                while not decDone do
                    if not exDone then
                        local inIdx = decoder.dequeueInputBuffer(3000)
                        if inIdx >= 0 then
                            local inBuf = nil
                            pcall(function() inBuf = decoder.getInputBuffer(inIdx) end)
                            if not inBuf and inBuffers then inBuf = inBuffers[inIdx + 1] end
                            if inBuf then
                                inBuf.clear()
                                local sz = ex.readSampleData(inBuf, 0)
                                if sz < 0 then
                                    decoder.queueInputBuffer(inIdx, 0, 0, 0, MediaCodec.BUFFER_FLAG_END_OF_STREAM)
                                    exDone = true
                                else
                                    decoder.queueInputBuffer(inIdx, 0, sz, math.max(0, ex.getSampleTime()), 0)
                                    ex.advance()
                                end
                            end
                        end
                    end

                    local outIdx = decoder.dequeueOutputBuffer(info, 3000)
                    if outIdx == MediaCodec.INFO_OUTPUT_BUFFERS_CHANGED then
                        pcall(function() outBuffers = decoder.getOutputBuffers() end)
                    elseif outIdx >= 0 then
                        eosCount = 0
                        local outBuf = nil
                        pcall(function() outBuf = decoder.getOutputBuffer(outIdx) end)
                        if not outBuf and outBuffers then outBuf = outBuffers[outIdx + 1] end
                        if info.size > 0 and outBuf then
                            outBuf.position(info.offset)
                            outBuf.limit(info.offset + info.size)
                            outBuf.order(ByteOrder.LITTLE_ENDIAN)
                            local sumAbs = 0
                            local count = 0
                            local stepBytes = 64
                            local limitIdx = info.offset + info.size - 2
                            for bPos = info.offset, limitIdx, stepBytes do
                                local s = outBuf.getShort(bPos)
                                sumAbs = sumAbs + math.abs(s)
                                count = count + 1
                            end
                            local avgAmp = (count > 0) and (sumAbs / count) or 0
                            local bucket = math.floor(math.max(0, info.presentationTimeUs) / 50000)
                            if bucket > maxBucket then maxBucket = bucket end
                            if not rawEnergies[bucket] or avgAmp > rawEnergies[bucket] then
                                rawEnergies[bucket] = avgAmp
                            end
                        end
                        decoder.releaseOutputBuffer(outIdx, false)
                        if math.floor((info.flags or 0) / 4) % 2 == 1 then
                            decDone = true
                        end
                    else
                        if exDone then
                            eosCount = eosCount + 1
                            if eosCount > 15 then decDone = true end
                        end
                    end
                end

                pcall(function() decoder.stop(); decoder.release() end)

                local peakE = 1
                for b = 0, maxBucket do
                    local e = rawEnergies[b] or 0
                    if e > peakE then peakE = e end
                end
                local thresh = math.max(220, peakE * 0.11)
                for b = 0, maxBucket do
                    local e = rawEnergies[b] or 0
                    if e >= thresh then
                        activeBuckets[b] = "1"
                        speechFound = true
                    else
                        activeBuckets[b] = "0"
                        pauseFound = true
                    end
                end
            end

            pcall(function() ex.release() end)
            if pfd then pcall(function() pfd.close() end) end
        end)

        if not speechFound or not pauseFound then
            return ""
        end
        return table.concat(activeBuckets, "", 0)
    end, ctx, vPath, vUriStr, function(bitStr)
        voice_envelope = {}
        if bitStr and #bitStr > 0 then
            for i = 1, #bitStr do
                voice_envelope[i - 1] = (bitStr:sub(i, i) == "1")
            end
            voice_has_detected_pauses = true
        else
            voice_has_detected_pauses = false
        end
        voice_scan_ready = true
        if onCompleteCallback then pcall(onCompleteCallback) end
    end)
end

local function isSpeakerTalkingAtMs(posMs)
    if not posMs or posMs < 0 then return true end
    if voice_scan_ready and voice_has_detected_pauses then
        local b = math.floor(posMs / 50)
        for k = b - 2, b + 2 do
            if voice_envelope[k] == true then
                return true
            end
        end
        return false
    end
    local cyclePos = posMs % 4200
    return cyclePos < 2700
end

-- ================= HARDWARE LOUDNESS BOOSTER (Up to 200%) =================
local function createBoosterForPlayer(mp)
    local booster = nil
    pcall(function()
        local sid = mp.getAudioSessionId()
        if sid and sid ~= 0 then
            booster = LoudnessEnhancer(sid)
            booster.setTargetGain(0)
            booster.setEnabled(true)
        end
    end)
    return booster
end

local function releaseBoosters()
    pcall(function() if voiceBooster then voiceBooster.release(); voiceBooster = nil end end)
    pcall(function() if bgMusicBooster then bgMusicBooster.release(); bgMusicBooster = nil end end)
end

local function applyVolumeWithBoost(mp, booster, desiredPct)
    if not mp then return end
    local pct = math.max(0, desiredPct or 100)
    if pct <= 100 then
        local linear = pct / 100.0
        pcall(function() mp.setVolume(linear, linear) end)
        if booster then
            pcall(function() booster.setTargetGain(0) end)
        end
    else
        pcall(function() mp.setVolume(1.0, 1.0) end)
        if booster then
            local extraPct = math.min(200, pct - 100)
            local gainMb = math.floor(extraPct * 28)
            pcall(function()
                booster.setTargetGain(gainMb)
                booster.setEnabled(true)
            end)
        end
    end
end

-- ================= REAL-TIME SMART FILTERING & PREVIEW ENGINE =================
local previewTimerRunnable = nil
local activeLivePosTV = nil
local activePlayBtn = nil
local currentLiveBgPct = 28

local function getFileUniqueId(f)
    if not f then return "" end
    return tostring(f.path or "") .. "|" .. tostring(f.uri or "") .. "|" .. tostring(f.name or "")
end

local function applySpeed(mp, speed)
    if not mp then return end
    pcall(function()
        if Build.VERSION.SDK_INT >= 23 then
            local params = PlaybackParams()
            params.setSpeed(speed)
            mp.setPlaybackParams(params)
        end
    end)
end

local function stopPreview()
    is_preview_prepared = false
    is_playing = false
    loaded_preview_id = ""
    loaded_bg_id = ""
    active_sequence_list = nil
    active_sequence_idx = 1
    if previewTimerRunnable then uiHandler.removeCallbacks(previewTimerRunnable) end
    releaseBoosters()
    if previewPlayer then
        pcall(function()
            if previewPlayer.isPlaying() then previewPlayer.stop() end
            previewPlayer.reset()
        end)
    end
    if bgMusicPlayer then
        pcall(function()
            if bgMusicPlayer.isPlaying() then bgMusicPlayer.stop() end
            bgMusicPlayer.reset()
        end)
    end
    if activePlayBtn then setT(activePlayBtn, "Play Preview") end
end

local function updateLivePlayerVolumes(isVoiceActiveNow)
    local masterFactor = (master_boost_pct or 100) / 100.0
    local effVoicePct = (voice_vol_pct or 100) * masterFactor
    if previewPlayer and is_preview_prepared then
        applyVolumeWithBoost(previewPlayer, voiceBooster, effVoicePct)
    end

    if bgMusicPlayer and is_playing then
        local highPct = (music_high_pct or 75) * masterFactor
        local lowPct = (music_duck_pct or 28) * masterFactor
        if not smart_filtering_enabled then
            currentLiveBgPct = highPct
        else
            local targetPct = isVoiceActiveNow and lowPct or highPct
            if targetPct < currentLiveBgPct then
                currentLiveBgPct = currentLiveBgPct * 0.35 + targetPct * 0.65
            else
                currentLiveBgPct = currentLiveBgPct * 0.75 + targetPct * 0.25
            end
        end
        applyVolumeWithBoost(bgMusicPlayer, bgMusicBooster, currentLiveBgPct)
    end
end

local function startPreviewForFile(fileObj, startMs, stopMs, playBtnRef, posTVRef, optionalBgMusicObj, optionalSeqList)
    if optionalSeqList and #optionalSeqList > 0 then
        fileObj = optionalSeqList[1]
    end
    if not fileObj or (not fileObj.uri and not fileObj.path) then
        speak("Please select a file first")
        Toast.makeText(ctx, "Please select a file first.", Toast.LENGTH_SHORT).show()
        return
    end

    local reqMainId = getFileUniqueId(fileObj) .. (optionalSeqList and ("|SEQ:" .. tostring(#optionalSeqList)) or "")
    local reqBgId = getFileUniqueId(optionalBgMusicObj)

    if is_preview_prepared and previewPlayer and loaded_preview_id == reqMainId and loaded_bg_id == reqBgId then
        if is_playing and previewPlayer.isPlaying() then
            previewPlayer.pause()
            pcall(function()
                if bgMusicPlayer and bgMusicPlayer.isPlaying() then
                    bgMusicPlayer.pause()
                end
            end)
            is_playing = false
            if previewTimerRunnable then uiHandler.removeCallbacks(previewTimerRunnable) end
            if playBtnRef then setT(playBtnRef, "Play Preview") end
            return
        else
            previewPlayer.start()
            applySpeed(previewPlayer, current_speed)
            pcall(function()
                if optionalBgMusicObj and bgMusicPlayer then
                    bgMusicPlayer.start()
                end
            end)
            is_playing = true
            if previewTimerRunnable then uiHandler.postDelayed(previewTimerRunnable, 50) end
            if playBtnRef then setT(playBtnRef, "Pause Preview") end
            return
        end
    end

    stopPreview()
    loaded_preview_id = reqMainId
    loaded_bg_id = reqBgId
    activePlayBtn = playBtnRef
    activeLivePosTV = posTVRef
    active_sequence_list = optionalSeqList
    active_sequence_idx = 1

    local masterFactor = (master_boost_pct or 100) / 100.0
    currentLiveBgPct = (music_duck_pct or 28) * masterFactor

    local function playSequenceItem(idx)
        local targetItem = (active_sequence_list and active_sequence_list[idx]) or fileObj
        if not targetItem then
            stopPreview()
            return
        end

        previewPlayer = MediaPlayer()
        local ok = pcall(function()
            setPlayerSourceSafe(previewPlayer, targetItem.uri, targetItem.path)

            if idx == 1 and optionalBgMusicObj and (optionalBgMusicObj.uri or optionalBgMusicObj.path) then
                pcall(function()
                    bgMusicPlayer = MediaPlayer()
                    setPlayerSourceSafe(bgMusicPlayer, optionalBgMusicObj.uri, optionalBgMusicObj.path)
                    bgMusicPlayer.setLooping(true)
                    bgMusicPlayer.prepare()
                    bgMusicBooster = createBoosterForPlayer(bgMusicPlayer)
                    applyVolumeWithBoost(bgMusicPlayer, bgMusicBooster, currentLiveBgPct)
                end)
            end

            previewPlayer.setOnPreparedListener(MediaPlayer.OnPreparedListener{
                onPrepared = function(mp)
                    is_preview_prepared = true
                    local dur = mp.getDuration()
                    local sPos = (idx == 1) and (startMs or 0) or 0
                    if sPos < 0 or sPos >= dur then sPos = 0 end
                    mp.seekTo(sPos)
                    voiceBooster = createBoosterForPlayer(mp)
                    applyVolumeWithBoost(mp, voiceBooster, (voice_vol_pct or 100) * masterFactor)
                    mp.start()
                    applySpeed(mp, current_speed)

                    if idx == 1 and optionalBgMusicObj and bgMusicPlayer then
                        pcall(function()
                            bgMusicPlayer.seekTo(0)
                            bgMusicPlayer.start()
                        end)
                    end

                    is_playing = true
                    if activePlayBtn then setT(activePlayBtn, "Pause Preview") end

                    local limitMs = (idx == 1 and stopMs and stopMs > 0 and stopMs <= dur) and stopMs or dur

                    if previewTimerRunnable then uiHandler.removeCallbacks(previewTimerRunnable) end
                    previewTimerRunnable = Runnable{
                        run = function()
                            if is_playing and previewPlayer and previewPlayer.isPlaying() then
                                local cur = previewPlayer.getCurrentPosition()
                                if activeLivePosTV then
                                    local prefix = (active_sequence_list and #active_sequence_list > 1) and ("Clip " .. tostring(idx) .. "/" .. tostring(#active_sequence_list) .. " - ") or "Time: "
                                    setT(activeLivePosTV, prefix .. formatDurationMs(cur) .. " / " .. formatDurationMs(dur))
                                end

                                if optionalBgMusicObj and bgMusicPlayer then
                                    local speakingNow = isSpeakerTalkingAtMs(cur)
                                    updateLivePlayerVolumes(speakingNow)
                                end

                                if cur >= limitMs then
                                    stopPreview()
                                    return
                                end
                                uiHandler.postDelayed(previewTimerRunnable, 50)
                            end
                        end
                    }
                    uiHandler.postDelayed(previewTimerRunnable, 50)
                end
            })

            previewPlayer.setOnCompletionListener(MediaPlayer.OnCompletionListener{
                onCompletion = function()
                    if active_sequence_list and idx < #active_sequence_list then
                        active_sequence_idx = idx + 1
                        pcall(function() previewPlayer.release() end)
                        playSequenceItem(active_sequence_idx)
                    else
                        stopPreview()
                    end
                end
            })
            previewPlayer.prepareAsync()
        end)

        if not ok then stopPreview() end
    end

    playSequenceItem(1)
end

local function seekPreview(deltaMs, labelText)
    if not is_preview_prepared or not previewPlayer then
        speak("Please start playback first")
        return
    end
    pcall(function()
        local cur = previewPlayer.getCurrentPosition()
        local dur = previewPlayer.getDuration()
        local target = cur + deltaMs
        if target < 0 then target = 0 end
        if dur > 0 and target > dur then target = dur end
        previewPlayer.seekTo(target)
        if activeLivePosTV then
            setT(activeLivePosTV, "Time: " .. formatDurationMs(target) .. " / " .. formatDurationMs(dur))
        end
        speak((labelText or "") .. " " .. formatDurationMs(target))
    end)
end

-- ================= PLAYER CARD (Play Preview Placed Between Rewind 5s and Forward 5s) =================
local function addProfessionalPlayerCard(parentLayout, getTargetFileFunc, showCutTrimMarkers, onStartMarked, onEndMarked, getBgMusicFunc, getSeqListFunc, cardBg, cardBorder)
    local playerCard = createStyledCard(cardBg or 0xFF1A162B, cardBorder or STUDIO_NEON_CYAN, 24)

    local posTV = TextView(ctx)
    setT(posTV, "Time: 00:00.000")
    posTV.setTextColor(STUDIO_NEON_CYAN)
    posTV.setTextSize(15)
    posTV.setTypeface(nil, Typeface.BOLD)
    posTV.setPadding(12, 8, 12, 12)
    pcall(function() posTV.setFocusable(true) end)
    playerCard.addView(posTV)

    local lpLeft = LinearLayout.LayoutParams(0, -2, 1.0)
    lpLeft.setMargins(0, 0, 6, 0)
    local lpMid = LinearLayout.LayoutParams(0, -2, 1.15)
    lpMid.setMargins(6, 0, 6, 0)
    local lpRight = LinearLayout.LayoutParams(0, -2, 1.0)
    lpRight.setMargins(6, 0, 0, 0)

    -- [ Rewind 5 Seconds ] | [ Play Preview ] | [ Forward 5 Seconds ]
    local rowSkip = LinearLayout(ctx)
    rowSkip.setOrientation(0)
    rowSkip.setGravity(Gravity.CENTER_VERTICAL)

    local rew5Btn = createStyledButton("Rewind 5 Seconds", 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
    rew5Btn.setLayoutParams(lpLeft)
    rew5Btn.setOnClickListener(function()
        vibrate(35)
        seekPreview(-5000, "Rewind 5 seconds")
    end)
    rowSkip.addView(rew5Btn)

    local playPauseBtn = createStyledButton("Play Preview", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 20)
    playPauseBtn.setLayoutParams(lpMid)
    playPauseBtn.setOnClickListener(function()
        vibrate(35)
        local f = getTargetFileFunc()
        local bgF = getBgMusicFunc and getBgMusicFunc() or nil
        local seqL = getSeqListFunc and getSeqListFunc() or nil
        startPreviewForFile(f, 0, 0, playPauseBtn, posTV, bgF, seqL)
    end)
    rowSkip.addView(playPauseBtn)

    local fwd5Btn = createStyledButton("Forward 5 Seconds", 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
    fwd5Btn.setLayoutParams(lpRight)
    fwd5Btn.setOnClickListener(function()
        vibrate(35)
        seekPreview(5000, "Forward 5 seconds")
    end)
    rowSkip.addView(fwd5Btn)

    playerCard.addView(rowSkip)
    addSpacer(playerCard, 12)

    local speedRow = LinearLayout(ctx)
    speedRow.setOrientation(0)
    speedRow.setGravity(Gravity.CENTER_VERTICAL)

    local spLabel = TextView(ctx)
    setT(spLabel, "Playback Speed:  ")
    spLabel.setTextColor(STUDIO_WARM_GOLD)
    spLabel.setTypeface(nil, Typeface.BOLD)
    pcall(function() spLabel.setFocusable(true) end)
    speedRow.addView(spLabel)

    local speeds = {0.5, 0.75, 1.0, 1.25, 1.5, 2.0}
    local speedNames = String{"0.5x", "0.75x", "1.0x Normal", "1.25x", "1.5x", "2.0x"}
    local speedSpinner = Spinner(ctx)
    local spAdapter = ArrayAdapter(ctx, android.R.layout.simple_spinner_dropdown_item, speedNames)
    speedSpinner.setAdapter(spAdapter)
    speedSpinner.setSelection(2)
    speedSpinner.setOnItemSelectedListener(AdapterView.OnItemSelectedListener{
        onItemSelected = function(p, v, pos, id)
            current_speed = speeds[pos + 1] or 1.0
            if is_playing and previewPlayer then
                applySpeed(previewPlayer, current_speed)
            end
        end
    })
    local spWrap = createSpinnerContainer(speedSpinner, STUDIO_NEON_CYAN)
    spWrap.setLayoutParams(LinearLayout.LayoutParams(0, -2, 1.0))
    speedRow.addView(spWrap)
    playerCard.addView(speedRow)

    if showCutTrimMarkers then
        addSpacer(playerCard, 12)
        local markRow = LinearLayout(ctx)
        markRow.setOrientation(0)

        local setStartHereBtn = createStyledButton("Set Start Here", 0xFF0D9488, 0xFFFFFFFF, 0xFF0F766E, 18)
        setStartHereBtn.setLayoutParams(lpLeft)
        setStartHereBtn.setOnClickListener(function()
            vibrate(35)
            if is_preview_prepared and previewPlayer then
                local pos = previewPlayer.getCurrentPosition()
                if onStartMarked then onStartMarked(pos) end
            else
                speak("Play preview first to set start position")
            end
        end)
        markRow.addView(setStartHereBtn)

        local setEndHereBtn = createStyledButton("Set End Here", 0xFF0D9488, 0xFFFFFFFF, 0xFF0F766E, 18)
        setEndHereBtn.setLayoutParams(lpRight)
        setEndHereBtn.setOnClickListener(function()
            vibrate(35)
            if is_preview_prepared and previewPlayer then
                local pos = previewPlayer.getCurrentPosition()
                if onEndMarked then onEndMarked(pos) end
            else
                speak("Play preview first to set end position")
            end
        end)
        markRow.addView(setEndHereBtn)
        playerCard.addView(markRow)

        addSpacer(playerCard, 10)
        local segPlayRow = LinearLayout(ctx)
        segPlayRow.setOrientation(0)

        local playStartSegBtn = createStyledButton("Play From Start", 0xFF4F46E5, 0xFFFFFFFF, 0xFF3730A3, 18)
        playStartSegBtn.setLayoutParams(lpLeft)
        playStartSegBtn.setOnClickListener(function()
            vibrate(35)
            stopPreview()
            local f = getTargetFileFunc()
            startPreviewForFile(f, start_time_ms, start_time_ms + 10000, playStartSegBtn, posTV, nil)
        end)
        segPlayRow.addView(playStartSegBtn)

        local playEndSegBtn = createStyledButton("Play From End", 0xFF4F46E5, 0xFFFFFFFF, 0xFF3730A3, 18)
        playEndSegBtn.setLayoutParams(lpRight)
        playEndSegBtn.setOnClickListener(function()
            vibrate(35)
            stopPreview()
            local f = getTargetFileFunc()
            if f then
                local eTime = (end_time_ms and end_time_ms > 0) and end_time_ms or (f.duration or 0)
                local sTime = math.max(0, eTime - 10000)
                startPreviewForFile(f, sTime, eTime, playEndSegBtn, posTV, nil)
            end
        end)
        segPlayRow.addView(playEndSegBtn)
        playerCard.addView(segPlayRow)
    end

    parentLayout.addView(playerCard)
    return playPauseBtn, posTV
end

-- ================= DEVICE MEDIA PICKER WINDOW (Unlimited Files + Live Counter!) =================
local function getDisplayName(uri)
    local result = nil
    pcall(function()
        if tostring(uri.getScheme()) == "content" then
            local cursor = ctx.getContentResolver().query(uri, nil, nil, nil, nil)
            if cursor and cursor.moveToFirst() then
                local index = cursor.getColumnIndex("_display_name")
                if index ~= -1 then result = cursor.getString(index) end
                cursor.close()
            end
        end
    end)
    if not result then
        result = uri.getPath()
        local cut = result:match(".*/(.*)")
        if cut then result = cut end
    end
    return result or "Unknown Media"
end

function onActivityResult(requestCode, resultCode, data)
    pcall(function()
        if requestCode == 10101 and resultCode == Activity.RESULT_OK and data then
            local uri = data.getData()
            if uri and system_picker_callback then
                local name = getDisplayName(uri)
                local dur = getMediaDuration(uri, nil)
                system_picker_callback({
                    uri = uri,
                    path = nil,
                    name = name,
                    duration = dur
                })
            end
        end
    end)
end

-- Loads ALL Audios or Videos on the device (NO 400 limit!)
local function queryDeviceFiles(category)
    purgeBrokenEditorFiles()
    local list = {}
    pcall(function()
        local contentUri = (category == 0) and MediaStore.Audio.Media.EXTERNAL_CONTENT_URI or MediaStore.Video.Media.EXTERNAL_CONTENT_URI
        local projection = String{"_id", "_display_name", "_data", "duration", "_size"}
        local cursor = ctx.getContentResolver().query(contentUri, projection, nil, nil, "date_modified DESC")
        if cursor then
            local idIdx = cursor.getColumnIndex("_id")
            local nameIdx = cursor.getColumnIndex("_display_name")
            local dataIdx = cursor.getColumnIndex("_data")
            local durIdx = cursor.getColumnIndex("duration")
            local sizeIdx = cursor.getColumnIndex("_size")
            while cursor.moveToNext() do
                local id = idIdx ~= -1 and cursor.getLong(idIdx) or 0
                local name = nameIdx ~= -1 and cursor.getString(nameIdx) or nil
                local path = dataIdx ~= -1 and cursor.getString(dataIdx) or nil
                local dur = durIdx ~= -1 and cursor.getLong(durIdx) or 0
                local fsize = sizeIdx ~= -1 and cursor.getLong(sizeIdx) or 0
                local idStr = string.format("%.0f", id)
                local itemUri = Uri.withAppendedPath(contentUri, idStr)
                if not name or name == "" then
                    if path then name = path:match(".*/(.*)") else name = "Media_" .. idStr end
                end

                local isValidFile = true
                if isLegacyBrokenFileName(name) then
                    isValidFile = false
                elseif fsize > 0 and fsize < 512 then
                    isValidFile = false
                elseif dur <= 0 and fsize < 1024 then
                    isValidFile = false
                end

                if isValidFile then
                    table.insert(list, {
                        uri = itemUri,
                        path = path,
                        name = name,
                        duration = dur
                    })
                end
            end
            cursor.close()
        end
    end)
    return list
end

local function showMediaListDialog(category, dialogTitle, onSelectCallback)
    vibrate(35)
    local allItems = queryDeviceFiles(category)
    local totalDeviceCount = #allItems
    local filteredItems = {}
    for _, v in ipairs(allItems) do table.insert(filteredItems, v) end

    local typeWord = (category == 0) and "Audio" or "Video"

    local root = LinearLayout(ctx)
    root.setOrientation(1)
    root.setPadding(24, 22, 24, 22)
    root.setBackground(gradBrd(0xFF13111C, 0xFF1F1934, 0xFFA855F7, 28, 3))

    local headerCard = createStyledCard(0xFF3B0764, STUDIO_NEON_CYAN, 18)
    local headerTV = TextView(ctx)
    setT(headerTV, dialogTitle or ("Select " .. typeWord))
    headerTV.setTextColor(STUDIO_NEON_CYAN)
    headerTV.setTextSize(18)
    headerTV.setTypeface(nil, Typeface.BOLD)
    headerTV.setGravity(Gravity.CENTER)
    pcall(function() headerTV.setFocusable(true) end)
    headerCard.addView(headerTV)
    root.addView(headerCard)

    local searchCard = createStyledCard(0xFF1E1B2E, 0xFF8B5CF6, 14)
    local searchRow = LinearLayout(ctx)
    searchRow.setOrientation(0)
    searchRow.setGravity(Gravity.CENTER_VERTICAL)

    local searchET = EditText(ctx)
    searchET.setHint("Search all " .. tostring(totalDeviceCount) .. " " .. typeWord .. " files...")
    searchET.setHintTextColor(STUDIO_MUTED_TEXT)
    searchET.setTextColor(STUDIO_PURE_TEXT)
    searchET.setSingleLine(true)
    searchET.setMaxLines(1)
    searchET.setInputType(InputType.TYPE_CLASS_TEXT)
    searchET.setImeOptions(EditorInfo.IME_ACTION_SEARCH)
    searchET.setLayoutParams(LinearLayout.LayoutParams(0, -2, 1.0))
    searchRow.addView(searchET)

    local searchBtn = createStyledButton("Search", 0xFF0891B2, 0xFFFFFFFF, 0xFF155E75, 16)
    searchRow.addView(searchBtn)
    searchCard.addView(searchRow)
    root.addView(searchCard)

    local browseFolderBtn = createStyledButton("Browse Folders", 0xFF7C3AED, 0xFFFFFFFF, 0xFF5B21B6, 18)
    root.addView(browseFolderBtn)
    addSpacer(root, 6)

    local countTV = TextView(ctx)
    setT(countTV, "Total " .. typeWord .. " Files: " .. tostring(totalDeviceCount))
    countTV.setTextColor(STUDIO_WARM_GOLD)
    countTV.setTypeface(nil, Typeface.BOLD)
    countTV.setTextSize(14)
    countTV.setPadding(10, 6, 10, 6)
    pcall(function() countTV.setFocusable(true) end)
    root.addView(countTV)

    local listCard = createStyledCard(0xFFE0E7FF, 0xFF8B5CF6, 10)
    local listView = ListView(ctx)
    listView.setLayoutParams(LinearLayout.LayoutParams(-1, 680))
    listCard.addView(listView)
    root.addView(listCard)

    local closePickerBtn = createStyledButton("Cancel", 0xFF334155, 0xFFF1F5F9, 0xFF1E293B, 20)
    root.addView(closePickerBtn)

    local function updateListAdapter(queryText)
        filteredItems = {}
        local q = tostring(queryText or ""):lower():gsub("^%s*(.-)%s*$", "%1")
        for _, item in ipairs(allItems) do
            if q == "" or tostring(item.name):lower():find(q, 1, true) then
                table.insert(filteredItems, item)
            end
        end
        local labels = {}
        for i, item in ipairs(filteredItems) do
            local dStr = (item.duration and item.duration > 0) and (" (" .. formatDurationMs(item.duration) .. ")") or ""
            labels[i] = tostring(i) .. ". " .. tostring(item.name) .. dStr
        end
        if q == "" then
            setT(countTV, "Total " .. typeWord .. " Files on Device: " .. tostring(#filteredItems))
        else
            setT(countTV, "Found " .. tostring(#filteredItems) .. " of " .. tostring(totalDeviceCount) .. " " .. typeWord .. " Files:")
        end
        local adapter = ArrayAdapter(ctx, android.R.layout.simple_list_item_1, String(labels))
        listView.setAdapter(adapter)
    end

    updateListAdapter("")

    -- Live search as user types AND on Search button / Enter key!
    searchET.addTextChangedListener({
        onTextChanged = function(s, a, b, c)
            updateListAdapter(tostring(s))
        end,
        beforeTextChanged = function(s, a, b, c) end,
        afterTextChanged = function(s) end
    })

    local function triggerSearch()
        vibrate(35)
        local q = tostring(searchET.getText() or "")
        updateListAdapter(q)
        speak("Showing " .. tostring(#filteredItems) .. " " .. typeWord .. " files")
    end

    searchBtn.setOnClickListener(function()
        triggerSearch()
    end)

    searchET.setOnEditorActionListener(TextView.OnEditorActionListener{
        onEditorAction = function(v, actionId, event)
            if actionId == EditorInfo.IME_ACTION_SEARCH or actionId == EditorInfo.IME_ACTION_DONE or actionId == EditorInfo.IME_ACTION_GO or (event and event.getKeyCode() == KeyEvent.KEYCODE_ENTER) then
                triggerSearch()
                return true
            end
            return false
        end
    })

    local dlg = AlertDialog.Builder(ctx).setView(root).create()
    styleDialogWindow(dlg)
    dlg.show()

    closePickerBtn.setOnClickListener(function()
        vibrate(35)
        dlg.dismiss()
    end)

    browseFolderBtn.setOnClickListener(function()
        vibrate(35)
        dlg.dismiss()
        system_picker_callback = onSelectCallback
        local intent = Intent(Intent.ACTION_GET_CONTENT)
        intent.setType("*/*")
        local mimetypes = (category == 0) and String{"audio/*", "video/*"} or String{"video/*", "audio/*"}
        intent.putExtra(Intent.EXTRA_MIME_TYPES, mimetypes)
        intent.addCategory(Intent.CATEGORY_OPENABLE)
        pcall(function() activity.startActivityForResult(intent, 10101) end)
    end)

    listView.setOnItemClickListener(AdapterView.OnItemClickListener{
        onItemClick = function(parent, view, position, id)
            vibrate(35)
            local chosen = filteredItems[position + 1]
            if chosen then
                local testEx, testPfd = createOpenExtractor(chosen.uri, chosen.path)
                if not testEx then
                    if testPfd then pcall(function() testPfd.close() end) end
                    if chosen.path then pcall(function() File(tostring(chosen.path)).delete() end) end
                    speak("This file is empty or corrupted and was removed. Please select another file.")
                    Toast.makeText(ctx, "Removed corrupted file: " .. tostring(chosen.name), Toast.LENGTH_SHORT).show()
                    for idx, it in ipairs(allItems) do
                        if it.name == chosen.name and it.path == chosen.path then
                            table.remove(allItems, idx)
                            break
                        end
                    end
                    totalDeviceCount = #allItems
                    updateListAdapter(tostring(searchET.getText() or ""))
                    return
                end
                testEx.release()
                if testPfd then pcall(function() testPfd.close() end) end

                dlg.dismiss()
                if not chosen.duration or chosen.duration <= 0 then
                    chosen.duration = getMediaDuration(chosen.uri, chosen.path)
                end
                speak("Selected " .. tostring(chosen.name))
                if onSelectCallback then onSelectCallback(chosen) end
            end
        end
    })
end

-- ================= BUILT-IN VOICE RECORDER DIALOG (Pro Studio Crimson Theme + Live Timer + Mic Noise Suppressor) =================
local function showRecordVoiceDialog(onRecordedCallback, preferCleanMic)
    vibrate(35)
    local timestamp = SimpleDateFormat("HHmmss").format(Date())
    local outVoicePath = getTempCacheDir() .. "RecordedVoice_" .. timestamp .. ".m4a"
    is_recording = false
    local recStartSeconds = 0
    local recTimerRunnable = nil

    local layout = LinearLayout(ctx)
    layout.setOrientation(1)
    layout.setPadding(28, 28, 28, 28)
    layout.setBackground(gradBrd(0xFF1F0D1D, 0xFF2D122B, 0xFFF43F5E, 28, 3))

    local hdr = createStyledCard(0xFF881337, 0xFFFB7185, 18)
    local hdrTV = TextView(ctx)
    setT(hdrTV, "STUDIO VOICE RECORDER")
    hdrTV.setTextColor(0xFFFFFFFF)
    hdrTV.setTextSize(18)
    hdrTV.setTypeface(nil, Typeface.BOLD)
    hdrTV.setGravity(Gravity.CENTER)
    hdr.addView(hdrTV)
    layout.addView(hdr)
    addSpacer(layout, 12)

    local statusTV = TextView(ctx)
    setT(statusTV, "Tap Start Recording to record your voice (HD 44.1 kHz)")
    statusTV.setTextColor(STUDIO_PURE_TEXT)
    statusTV.setTextSize(15)
    statusTV.setTypeface(nil, Typeface.BOLD)
    statusTV.setGravity(Gravity.CENTER)
    statusTV.setPadding(12, 12, 12, 10)
    layout.addView(statusTV)

    local timerTV = TextView(ctx)
    setT(timerTV, "00:00")
    timerTV.setTextColor(STUDIO_WARM_GOLD)
    timerTV.setTextSize(22)
    timerTV.setTypeface(nil, Typeface.BOLD)
    timerTV.setGravity(Gravity.CENTER)
    timerTV.setPadding(8, 4, 8, 16)
    layout.addView(timerTV)

    local recBtn = createStyledButton("Start Recording", 0xFFE11D48, 0xFFFFFFFF, 0xFF9F1239, 22)
    layout.addView(recBtn)
    addSpacer(layout, 10)

    local cancelRecBtn = createStyledButton("Cancel", 0xFF334155, 0xFFF1F5F9, 0xFF1E293B, 20)
    layout.addView(cancelRecBtn)

    local dlg = AlertDialog.Builder(ctx).setView(layout).create()
    styleDialogWindow(dlg)
    dlg.show()

    local function stopRecTimer()
        if recTimerRunnable then
            pcall(function() uiHandler.removeCallbacks(recTimerRunnable) end)
            recTimerRunnable = nil
        end
    end

    cancelRecBtn.setOnClickListener(function()
        vibrate(35)
        stopRecTimer()
        if is_recording and mediaRecorder then
            pcall(function() mediaRecorder.stop(); mediaRecorder.release() end)
            is_recording = false
        end
        dlg.dismiss()
    end)

    recBtn.setOnClickListener(function()
        vibrate(35)
        if not is_recording then
            local ok = pcall(function()
                mediaRecorder = MediaRecorder()
                local srcSet = false
                if preferCleanMic then
                    pcall(function()
                        mediaRecorder.setAudioSource(MediaRecorder.AudioSource.VOICE_RECOGNITION)
                        srcSet = true
                    end)
                end
                if not srcSet then
                    mediaRecorder.setAudioSource(MediaRecorder.AudioSource.MIC)
                end
                mediaRecorder.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
                mediaRecorder.setAudioEncoder(MediaRecorder.AudioEncoder.AAC)
                mediaRecorder.setAudioSamplingRate(44100)
                mediaRecorder.setAudioEncodingBitRate(192000)
                mediaRecorder.setOutputFile(outVoicePath)
                mediaRecorder.prepare()
                mediaRecorder.start()
            end)
            if ok then
                is_recording = true
                recStartSeconds = 0
                setT(statusTV, "Recording now... Speak clearly into microphone.")
                setT(timerTV, "00:00")
                setT(recBtn, "Stop & Use Recording")
                recBtn.setBackground(gradBrd(0xFF059669, 0xFF065F46, 0xFF34D399, 22, 2))
                speak("Recording started")
                recTimerRunnable = Runnable{
                    run = function()
                        if is_recording then
                            recStartSeconds = recStartSeconds + 1
                            local m = math.floor(recStartSeconds / 60)
                            local s = recStartSeconds % 60
                            setT(timerTV, string.format("%02d:%02d", m, s))
                            uiHandler.postDelayed(recTimerRunnable, 1000)
                        end
                    end
                }
                uiHandler.postDelayed(recTimerRunnable, 1000)
            else
                Toast.makeText(ctx, "Microphone error", Toast.LENGTH_SHORT).show()
            end
        else
            stopRecTimer()
            pcall(function()
                mediaRecorder.stop()
                mediaRecorder.release()
                mediaRecorder = nil
            end)
            is_recording = false
            dlg.dismiss()
            local dur = getMediaDuration(nil, outVoicePath)
            if not dur or dur <= 0 then dur = math.max(1000, recStartSeconds * 1000) end
            if onRecordedCallback then
                onRecordedCallback({
                    uri = Uri.fromFile(File(outVoicePath)),
                    path = outVoicePath,
                    name = "RecordedVoice_" .. timestamp .. ".m4a",
                    duration = dur
                })
            end
        end
    end)
end

-- ================= TIME INPUT DIALOG (Pro Studio Teal Theme) =================
local function showTimeInputDialog(isStart, maxDuration, onTimeSet)
    vibrate(35)
    local title = isStart and "SET START TIME" or "SET END TIME"
    local layout = LinearLayout(ctx)
    layout.setOrientation(1)
    layout.setPadding(26, 24, 26, 24)
    layout.setBackground(gradBrd(0xFF0A191E, 0xFF132A32, 0xFF2DD4BF, 28, 3))

    local hdr = createStyledCard(0xFF0F766E, 0xFF2DD4BF, 16)
    local hdrTV = TextView(ctx)
    setT(hdrTV, title)
    hdrTV.setTextColor(0xFFFFFFFF)
    hdrTV.setTextSize(18)
    hdrTV.setTypeface(nil, Typeface.BOLD)
    hdrTV.setGravity(Gravity.CENTER)
    hdr.addView(hdrTV)
    layout.addView(hdr)
    addSpacer(layout, 8)

    local durTV = TextView(ctx)
    setT(durTV, "Total Duration: " .. formatDurationMs(maxDuration))
    durTV.setTextColor(STUDIO_WARM_GOLD)
    durTV.setTypeface(nil, Typeface.BOLD)
    durTV.setPadding(6, 4, 6, 12)
    layout.addView(durTV)

    local curMs = isStart and start_time_ms or end_time_ms
    local totalSec = math.floor((curMs or 0) / 1000)
    local curM = math.floor(totalSec / 60)
    local curS = totalSec % 60
    local curMilli = (curMs or 0) % 1000

    local minTV = TextView(ctx)
    setT(minTV, "Minutes:")
    minTV.setTextColor(STUDIO_NEON_CYAN)
    layout.addView(minTV)

    local minET = EditText(ctx)
    minET.setInputType(InputType.TYPE_CLASS_NUMBER)
    minET.setSingleLine(true)
    minET.setTextColor(STUDIO_PURE_TEXT)
    minET.setBackground(brd(0xFF091318, 0xFF14B8A6, 12))
    minET.setText(tostring(curM))
    layout.addView(minET)
    addSpacer(layout, 8)

    local secTV = TextView(ctx)
    setT(secTV, "Seconds:")
    secTV.setTextColor(STUDIO_NEON_CYAN)
    layout.addView(secTV)

    local secET = EditText(ctx)
    secET.setInputType(InputType.TYPE_CLASS_NUMBER)
    secET.setSingleLine(true)
    secET.setTextColor(STUDIO_PURE_TEXT)
    secET.setBackground(brd(0xFF091318, 0xFF14B8A6, 12))
    secET.setText(tostring(curS))
    layout.addView(secET)
    addSpacer(layout, 8)

    local msTV = TextView(ctx)
    setT(msTV, "Milliseconds:")
    msTV.setTextColor(STUDIO_NEON_CYAN)
    layout.addView(msTV)

    local msET = EditText(ctx)
    msET.setInputType(InputType.TYPE_CLASS_NUMBER)
    msET.setSingleLine(true)
    msET.setTextColor(STUDIO_PURE_TEXT)
    msET.setBackground(brd(0xFF091318, 0xFF14B8A6, 12))
    msET.setText(tostring(curMilli))
    layout.addView(msET)
    addSpacer(layout, 14)

    local btnRow = LinearLayout(ctx)
    btnRow.setOrientation(0)
    local lpL = LinearLayout.LayoutParams(0, -2, 1.0)
    lpL.setMargins(0, 0, 8, 0)
    local lpR = LinearLayout.LayoutParams(0, -2, 1.0)
    lpR.setMargins(8, 0, 0, 0)

    local okBtn = createStyledButton("OK", 0xFF0D9488, 0xFFFFFFFF, 0xFF0F766E, 20)
    okBtn.setLayoutParams(lpL)
    local canBtn = createStyledButton("Cancel", 0xFF334155, 0xFFF1F5F9, 0xFF1E293B, 20)
    canBtn.setLayoutParams(lpR)
    btnRow.addView(okBtn)
    btnRow.addView(canBtn)
    layout.addView(btnRow)

    local dlg = AlertDialog.Builder(ctx).setView(layout).create()
    styleDialogWindow(dlg)
    dlg.show()

    canBtn.setOnClickListener(function()
        vibrate(35)
        dlg.dismiss()
    end)

    okBtn.setOnClickListener(function()
        vibrate(35)
        local m = tonumber(tostring(minET.getText())) or 0
        local s = tonumber(tostring(secET.getText())) or 0
        local ms = tonumber(tostring(msET.getText())) or 0
        local calcMs = (m * 60 + s) * 1000 + ms
        if maxDuration and maxDuration > 0 and calcMs > maxDuration then
            calcMs = maxDuration
        end
        dlg.dismiss()
        if onTimeSet then onTimeSet(calcMs) end
    end)
end

-- ================= OUTPUT READY WINDOW / DIALOG (Pro Studio Emerald-Gold Theme) =================
local outDuckTimer = nil
local outLivePct = 28

local function stopOutputPreview()
    if outDuckTimer then uiHandler.removeCallbacks(outDuckTimer) end
    pcall(function() if outVoiceBooster then outVoiceBooster.release(); outVoiceBooster = nil end end)
    pcall(function() if outMusicBooster then outMusicBooster.release(); outMusicBooster = nil end end)
    pcall(function()
        if outVoicePlayer then
            if outVoicePlayer.isPlaying() then outVoicePlayer.stop() end
            outVoicePlayer.reset()
        end
    end)
    pcall(function()
        if outMusicPlayer then
            if outMusicPlayer.isPlaying() then outMusicPlayer.stop() end
            outMusicPlayer.reset()
        end
    end)
end

local function shareMediaFileSafely(filePath, fileName)
    vibrate(35)
    local f = File(tostring(filePath))
    if not f.exists() then
        Toast.makeText(ctx, "File not found to share", Toast.LENGTH_SHORT).show()
        return
    end
    local lower = tostring(fileName or filePath):lower()
    local isVid = lower:find("%.mp4$") or lower:find("%.mkv$") or lower:find("%.3gp$")
    local mimeType = isVid and "video/*" or "audio/*"

    speak("Preparing file to share...")
    scanMediaFile(filePath, function(scannedPath, contentUri)
        pcall(function()
            local shareUri = contentUri or Uri.fromFile(f)
            local shareIntent = Intent(Intent.ACTION_SEND)
            shareIntent.setType(mimeType)
            shareIntent.putExtra(Intent.EXTRA_STREAM, shareUri)
            shareIntent.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
            ctx.startActivity(Intent.createChooser(shareIntent, "Share File"))
        end)
    end)
end

showOutputReadyDialog = function(tempFilePath, defaultFileName, isSmartMixOutput, fallbackDurMs)
    stopPreview()
    stopOutputPreview()

    local curTempPath = tempFilePath
    local curName = sanitizeName(defaultFileName)
    local savedFinalPath = nil

    local realDur = getMediaDuration(nil, curTempPath)
    local outDur = (realDur and realDur > 0) and realDur or (fallbackDurMs or 0)
    local fileSizeKB = 0
    pcall(function()
        fileSizeKB = math.floor(File(tostring(curTempPath)).length() / 1024)
    end)

    local card = LinearLayout(ctx)
    card.setOrientation(1)
    card.setPadding(26, 24, 26, 24)
    card.setBackground(gradBrd(0xFF0A1F17, 0xFF132F23, 0xFF34D399, 28, 3))

    local hdr = createStyledCard(0xFF065F46, STUDIO_WARM_GOLD, 18)
    local titleTV = TextView(ctx)
    setT(titleTV, "STUDIO FILE READY")
    titleTV.setTextColor(STUDIO_WARM_GOLD)
    titleTV.setTextSize(19)
    titleTV.setTypeface(nil, Typeface.BOLD)
    titleTV.setGravity(Gravity.CENTER)
    pcall(function() titleTV.setFocusable(true) end)
    hdr.addView(titleTV)
    card.addView(hdr)

    local infoCard = createStyledCard(0xFF11261E, 0xFF10B981, 18)
    local infoTV = TextView(ctx)
    setT(infoTV, "File: " .. curName .. "\nTotal Duration: " .. formatDurationMs(outDur) .. " (" .. tostring(fileSizeKB) .. " KB)")
    infoTV.setTextColor(STUDIO_NEON_CYAN)
    infoTV.setTypeface(nil, Typeface.BOLD)
    infoTV.setTextSize(14)
    pcall(function() infoTV.setFocusable(true) end)
    infoCard.addView(infoTV)
    card.addView(infoCard)
    addSpacer(card, 10)

    local playBtn = createStyledButton("Play", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 20)
    card.addView(playBtn)
    addSpacer(card, 10)

    local downloadBtn = createStyledButton("Save / Download", 0xFF2563EB, 0xFFFFFFFF, 0xFF1E40AF, 20)
    card.addView(downloadBtn)
    addSpacer(card, 10)

    local renameBtn = createStyledButton("Rename", 0xFFD97706, 0xFFFFFFFF, 0xFFB45309, 20)
    card.addView(renameBtn)
    addSpacer(card, 10)

    local shareBtn = createStyledButton("Share", 0xFF7C3AED, 0xFFFFFFFF, 0xFF5B21B6, 20)
    card.addView(shareBtn)
    addSpacer(card, 10)

    local closeReadyBtn = createStyledButton("Close", 0xFF334155, 0xFFF1F5F9, 0xFF1E293B, 20)
    card.addView(closeReadyBtn)

    local dlg = AlertDialog.Builder(ctx).setView(card).create()
    styleDialogWindow(dlg)
    dlg.show()

    speak("File Ready. Duration " .. formatDurationMs(outDur))

    closeReadyBtn.setOnClickListener(function()
        vibrate(35)
        stopOutputPreview()
        dlg.dismiss()
    end)

    playBtn.setOnClickListener(function()
        vibrate(35)
        pcall(function()
            if outVoicePlayer and outVoicePlayer.isPlaying() then
                stopOutputPreview()
                setT(playBtn, "Play")
                return
            end
            stopOutputPreview()

            outVoicePlayer = MediaPlayer()
            local targetPath = savedFinalPath or curTempPath
            setPlayerSourceSafe(outVoicePlayer, nil, targetPath)
            outVoicePlayer.prepare()
            outVoicePlayer.start()
            setT(playBtn, "Pause")
            outVoicePlayer.setOnCompletionListener(MediaPlayer.OnCompletionListener{
                onCompletion = function() setT(playBtn, "Play") end
            })
        end)
    end)

    downloadBtn.setOnClickListener(function()
        vibrate(35)
        local ok, err = pcall(function()
            local destPath = getDownloadPath(curName)
            if savedFinalPath and savedFinalPath ~= destPath and File(savedFinalPath).exists() then
                File(savedFinalPath).renameTo(File(destPath))
            else
                copyFileReliable(curTempPath, destPath)
            end
            savedFinalPath = destPath
            local savedKB = math.floor(File(savedFinalPath).length() / 1024)
            local realSavedDur = getMediaDuration(nil, savedFinalPath)
            if realSavedDur and realSavedDur > 0 then outDur = realSavedDur end
            scanMediaFile(savedFinalPath)
            setT(infoTV, "Saved: Download/Audio Video Editor/" .. curName .. "\nDuration: " .. formatDurationMs(outDur) .. " (" .. tostring(savedKB) .. " KB)")
            setT(downloadBtn, "Saved")
            speak("Saved as " .. curName .. ", Duration " .. formatDurationMs(outDur))
            Toast.makeText(ctx, "Saved: " .. curName .. " (" .. formatDurationMs(outDur) .. ")", Toast.LENGTH_LONG).show()
        end)
        if not ok then
            Toast.makeText(ctx, "Save error: " .. tostring(err), Toast.LENGTH_LONG).show()
        end
    end)

    renameBtn.setOnClickListener(function()
        vibrate(35)
        local rLayout = LinearLayout(ctx)
        rLayout.setOrientation(1)
        rLayout.setPadding(26, 24, 26, 24)
        rLayout.setBackground(gradBrd(0xFF13111C, 0xFF1F1934, STUDIO_WARM_GOLD, 28, 3))

        local ext = curName:match("(%.[^%.]+)$") or ".m4a"
        local baseOnly = curName:gsub("%.[^%.]+$", "")

        local rTitle = TextView(ctx)
        setT(rTitle, "RENAME FILE")
        rTitle.setTextColor(STUDIO_WARM_GOLD)
        rTitle.setTextSize(17)
        rTitle.setTypeface(nil, Typeface.BOLD)
        rTitle.setGravity(Gravity.CENTER)
        rLayout.addView(rTitle)
        addSpacer(rLayout, 12)

        local et = EditText(ctx)
        et.setSingleLine(true)
        et.setTextColor(STUDIO_PURE_TEXT)
        et.setBackground(brd(0xFF0E0C16, 0xFF8B5CF6, 12))
        et.setText(baseOnly)
        rLayout.addView(et)
        addSpacer(rLayout, 14)

        local saveRenBtn = createStyledButton("Save Name", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 20)
        rLayout.addView(saveRenBtn)
        addSpacer(rLayout, 8)
        local canRenBtn = createStyledButton("Cancel", 0xFF334155, 0xFFF1F5F9, 0xFF1E293B, 20)
        rLayout.addView(canRenBtn)

        local rDlg = AlertDialog.Builder(ctx).setView(rLayout).create()
        styleDialogWindow(rDlg)
        rDlg.show()

        canRenBtn.setOnClickListener(function()
            vibrate(35)
            rDlg.dismiss()
        end)

        saveRenBtn.setOnClickListener(function()
            vibrate(35)
            local newBase = sanitizeName(tostring(et.getText()))
            curName = newBase .. ext
            if savedFinalPath and File(savedFinalPath).exists() then
                local newFinalPath = getDownloadPath(curName)
                if File(savedFinalPath).renameTo(File(newFinalPath)) then
                    savedFinalPath = newFinalPath
                    scanMediaFile(savedFinalPath)
                end
                setT(infoTV, "Saved: Download/Audio Video Editor/" .. curName .. "\nDuration: " .. formatDurationMs(outDur))
            else
                setT(infoTV, "File: " .. curName .. "\nTotal Duration: " .. formatDurationMs(outDur))
            end
            rDlg.dismiss()
            speak("Renamed to " .. curName)
        end)
    end)

    shareBtn.setOnClickListener(function()
        vibrate(35)
        local shareSource = savedFinalPath or curTempPath
        shareMediaFileSafely(shareSource, curName)
    end)
end

local function checkPendingBackgroundTask()
    pcall(function()
        local pPath = prefs.getString("bg_ready_path", nil)
        local pName = prefs.getString("bg_ready_name", nil)
        local pDur = prefs.getLong("bg_ready_dur", 0)
        if pPath and pName and File(pPath).exists() then
            prefs.edit().remove("bg_ready_path").remove("bg_ready_name").remove("bg_ready_dur").commit()
            showOutputReadyDialog(pPath, pName, false, pDur)
        end
    end)
end

-- ================= ISOLATED task() PROCESSING ENGINE (ZERO JIESHUO CRASHES!) =================
local VIDEO_QUALITY_LABELS = {
    "Original Quality (Fastest)",
    "Ultra HD 4K / 8K (High Bitrate)",
    "Full HD 1080p (High Quality)",
    "HD 720p (Standard HD)",
    "SD 480p (Medium Quality)",
    "Low 360p (Small File Size)"
}

local function encodeField(s)
    if not s then return "" end
    return tostring(s):gsub("|", "_"):gsub("\n", " "):gsub("\r", "")
end

local function packFileItem(f)
    if not f then return "" end
    local uStr = f.uri and tostring(f.uri) or ""
    local pStr = f.path and tostring(f.path) or ""
    local nStr = encodeField(f.name or "media")
    local dStr = tostring(math.floor(f.duration or 0))
    return uStr .. "\t" .. pStr .. "\t" .. nStr .. "\t" .. dStr
end

local function runProcess(processType)
    vibrate(35)
    stopPreview()

    if processType == "music_to_voice" then
        if not voice_file then speak("Please select or record a Voice file first"); Toast.makeText(ctx, "Please select Voice file first", Toast.LENGTH_SHORT).show(); return end
        if not music_file then speak("Please select a Music file first"); Toast.makeText(ctx, "Please select Music file first", Toast.LENGTH_SHORT).show(); return end
    elseif processType == "voice_recorder" then
        if not voice_file then speak("Please record or select a Voice file first"); Toast.makeText(ctx, "Please record a Voice file first", Toast.LENGTH_SHORT).show(); return end
    elseif processType == "merge" then
        if #merge_list < 2 then speak("Please add at least 2 files to merge"); Toast.makeText(ctx, "Please add at least 2 files to merge", Toast.LENGTH_SHORT).show(); return end
    elseif processType == "split_video" then
        if not primary_file or not secondary_file then speak("Please select both 1st Video and 2nd Video first"); Toast.makeText(ctx, "Please select both videos first", Toast.LENGTH_SHORT).show(); return end
    elseif processType == "change_audio" then
        if not primary_file or not secondary_file then speak("Please select both Video and Audio files first"); Toast.makeText(ctx, "Please select both Video and Audio first", Toast.LENGTH_SHORT).show(); return end
    else
        if not primary_file then speak("Please select a file first"); Toast.makeText(ctx, "Please select a file first", Toast.LENGTH_SHORT).show(); return end
    end

    local isHiddenInBackground = false
    local isJobRunning = true

    local progCard = LinearLayout(ctx)
    progCard.setOrientation(1)
    progCard.setPadding(28, 26, 28, 26)
    progCard.setBackground(gradBrd(0xFF12101B, 0xFF1F1934, STUDIO_NEON_CYAN, 28, 3))

    local hdrBox = createStyledCard(0xFF3B0764, STUDIO_NEON_CYAN, 18)
    local titleTV = TextView(ctx)
    setT(titleTV, "STUDIO PROCESSING")
    titleTV.setTextSize(18)
    titleTV.setTypeface(nil, Typeface.BOLD)
    titleTV.setTextColor(STUDIO_NEON_CYAN)
    titleTV.setGravity(Gravity.CENTER)
    pcall(function() titleTV.setFocusable(true) end)
    hdrBox.addView(titleTV)
    progCard.addView(hdrBox)
    addSpacer(progCard, 10)

    local statusDetailTV = TextView(ctx)
    setT(statusDetailTV, "Processing... 1%")
    statusDetailTV.setTextSize(16)
    statusDetailTV.setTypeface(nil, Typeface.BOLD)
    statusDetailTV.setTextColor(STUDIO_WARM_GOLD)
    statusDetailTV.setGravity(Gravity.CENTER)
    pcall(function() statusDetailTV.setFocusable(true) end)
    progCard.addView(statusDetailTV)
    addSpacer(progCard, 12)

    local horizBar = ProgressBar(ctx, nil, android.R.attr.progressBarStyleHorizontal)
    horizBar.setMax(100)
    horizBar.setProgress(1)
    progCard.addView(horizBar)
    addSpacer(progCard, 18)

    local hideBtn = createStyledButton("Hide", 0xFF0891B2, 0xFFFFFFFF, 0xFF155E75, 22)
    progCard.addView(hideBtn)

    local progDlg = AlertDialog.Builder(ctx).setView(progCard).setCancelable(false).create()
    styleDialogWindow(progDlg)
    progDlg.show()

    pcall(function() hideBtn.requestFocus() end)

    local uiPollRunnable = nil
    uiPollRunnable = Runnable{
        run = function()
            if isJobRunning then
                pcall(function()
                    local curP = horizBar.getProgress()
                    if curP < 1 then curP = 1 end
                    if curP > 100 then curP = 100 end
                    statusDetailTV.setText("Processing... " .. tostring(curP) .. "%")
                end)
                uiHandler.postDelayed(uiPollRunnable, 200)
            end
        end
    }
    uiHandler.postDelayed(uiPollRunnable, 200)

    hideBtn.setOnClickListener(function()
        vibrate(35)
        isHiddenInBackground = true
        speak("Running in background")
        pcall(function() activity.moveTaskToBack(true) end)
        pcall(function()
            local homeIntent = Intent(Intent.ACTION_MAIN)
            homeIntent.addCategory(Intent.CATEGORY_HOME)
            homeIntent.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            ctx.startActivity(homeIntent)
        end)
    end)

    local timestamp = SimpleDateFormat("HHmmss").format(Date())
    local cacheDirStr = getTempCacheDir()
    local recFlags = (rec_clean_noise and 1 or 0) + (rec_add_echo and 2 or 0) + (music_file and 4 or 0)
    local headerLine = table.concat({
        tostring(processType),
        tostring(timestamp),
        tostring(cacheDirStr),
        tostring(math.floor(start_time_ms or 0)),
        tostring(math.floor(end_time_ms or 0)),
        tostring(math.floor(video_quality_idx or 0)),
        tostring(math.floor(split_layout_mode or 0)),
        tostring(math.floor(media_type or 0)),
        tostring(smart_filtering_enabled and 1 or 0),
        tostring(math.floor(voice_vol_pct or 100)),
        tostring(math.floor(music_high_pct or 75)),
        tostring(math.floor(music_duck_pct or 28)),
        tostring(math.floor(master_boost_pct or 100)),
        tostring(math.floor(conv_format_idx or 0)),
        tostring(math.floor(conv_bitrate_idx or 0)),
        tostring(math.floor(echo_delay_ms or 220)),
        tostring(math.floor(echo_decay_pct or 45)),
        tostring(math.floor(echo_voice_boost_pct or 120)),
        tostring(math.floor(noise_strength_pct or 80)),
        tostring(math.floor(vol_booster_pct or 200)),
        tostring(math.floor(recFlags)),
        tostring(math.floor(noise_voice_boost_pct or 130)),
        tostring(math.floor(rec_voice_boost_pct or 130))
    }, "\t")

    local lines = { headerLine }
    if processType == "music_to_voice" or processType == "voice_recorder" then
        table.insert(lines, packFileItem(voice_file))
        if music_file then
            table.insert(lines, packFileItem(music_file))
        end
    elseif processType == "merge" then
        for _, it in ipairs(merge_list) do
            table.insert(lines, packFileItem(it))
        end
    elseif processType == "split_video" or processType == "change_audio" then
        table.insert(lines, packFileItem(primary_file))
        table.insert(lines, packFileItem(secondary_file))
    else
        table.insert(lines, packFileItem(primary_file))
    end
    local payloadStr = table.concat(lines, "\n")

    task(function(act, progressBarWidget, jobPayload)
        require "import"
        import "android.media.MediaExtractor"
        import "android.media.MediaMuxer"
        import "android.media.MediaFormat"
        import "android.media.MediaCodec"
        import "android.media.MediaCodecInfo"
        import "android.media.MediaMetadataRetriever"
        import "android.media.MediaPlayer"
        import "android.graphics.Bitmap"
        import "android.graphics.Canvas"
        import "android.graphics.Paint"
        import "android.graphics.Rect"
        import "android.os.Build"
        import "java.nio.ByteBuffer"
        import "java.nio.ByteOrder"
        import "java.io.File"
        import "java.io.FileInputStream"
        import "java.io.FileOutputStream"
        import "android.net.Uri"

        local function setPct(p)
            pcall(function()
                local v = math.min(99, math.max(1, math.floor(p or 1)))
                progressBarWidget.setProgress(v)
            end)
        end

        local function splitTabs(s)
            local t = {}
            local start = 1
            while true do
                local pos = s:find("\t", start, true)
                if not pos then
                    table.insert(t, s:sub(start))
                    break
                end
                table.insert(t, s:sub(start, pos - 1))
                start = pos + 1
            end
            return t
        end

        local allLines = {}
        for line in jobPayload:gmatch("[^\n]+") do
            table.insert(allLines, line)
        end

        local hdr = splitTabs(allLines[1] or "")
        local pType        = hdr[1] or ""
        local ts           = hdr[2] or "000000"
        local workDir      = hdr[3] or "/sdcard/"
        local sMs          = tonumber(hdr[4]) or 0
        local eMs          = tonumber(hdr[5]) or 0
        local qIdx         = tonumber(hdr[6]) or 0
        local layoutMode   = tonumber(hdr[7]) or 0
        local smartOn      = (tonumber(hdr[9]) or 1) == 1
        local voiceVolPct       = tonumber(hdr[10]) or 100
        local musicHighPct      = tonumber(hdr[11]) or 75
        local musicDuckPct      = tonumber(hdr[12]) or 28
        local masterPct         = tonumber(hdr[13]) or 100
        local convFmtIdx        = tonumber(hdr[14]) or 0
        local convBrIdx         = tonumber(hdr[15]) or 0
        local echoDelayMs       = tonumber(hdr[16]) or 220
        local echoDecayPct      = tonumber(hdr[17]) or 45
        local echoVoiceBoostPct = tonumber(hdr[18]) or 120
        local noiseStrengthPct  = tonumber(hdr[19]) or 80
        local volBoosterPct     = tonumber(hdr[20]) or 200
        local recFlags          = tonumber(hdr[21]) or 1
        local noiseVoiceBoost   = tonumber(hdr[22]) or 130
        local recVoiceBoost     = tonumber(hdr[23]) or 130

        local items = {}
        for i = 2, #allLines do
            local parts = splitTabs(allLines[i])
            local uStr = parts[1] or ""
            local pStr = parts[2] or ""
            local nStr = parts[3] or "Media"
            local dVal = tonumber(parts[4]) or 0
            local uObj = (uStr ~= "") and Uri.parse(uStr) or nil
            table.insert(items, {
                uri = uObj,
                path = (pStr ~= "") and pStr or nil,
                name = nStr,
                duration = dVal
            })
        end

        local function openEx(uri, filePath)
            local ex = nil
            local handle = nil
            if filePath and tostring(filePath) ~= "" then
                pcall(function()
                    local origF = File(tostring(filePath))
                    if not origF.exists() or origF.length() < 256 then
                        local cand = File(workDir .. tostring(origF.getName()))
                        if cand.exists() and cand.length() >= 256 then
                            filePath = cand.getAbsolutePath()
                        end
                    end
                end)
            end
            if not ex and filePath and tostring(filePath) ~= "" then
                pcall(function()
                    local f = File(tostring(filePath))
                    if f.exists() and f.length() >= 256 then
                        local fis = FileInputStream(f)
                        local ok = pcall(function()
                            local e = MediaExtractor()
                            e.setDataSource(fis.getFD())
                            if e.getTrackCount() > 0 then ex = e; handle = fis else e.release() end
                        end)
                        if not ok or not ex then pcall(function() fis.close() end) end
                    end
                end)
            end
            if not ex and filePath and tostring(filePath) ~= "" then
                pcall(function()
                    local f = File(tostring(filePath))
                    if f.exists() and f.length() >= 256 then
                        local e = MediaExtractor()
                        e.setDataSource(tostring(filePath))
                        if e.getTrackCount() > 0 then ex = e else e.release() end
                    end
                end)
            end
            if not ex and uri then
                pcall(function()
                    local pfd = act.getContentResolver().openFileDescriptor(uri, "r")
                    if pfd then
                        local ok = pcall(function()
                            local e = MediaExtractor()
                            e.setDataSource(pfd.getFileDescriptor())
                            if e.getTrackCount() > 0 then ex = e; handle = pfd else e.release() end
                        end)
                        if not ok or not ex then pcall(function() pfd.close() end) end
                    end
                end)
            end
            if not ex and uri then
                pcall(function()
                    local e = MediaExtractor()
                    e.setDataSource(act, uri, nil)
                    if e.getTrackCount() > 0 then ex = e else e.release() end
                end)
            end
            return ex, handle
        end

        local function detectMime(fileObj)
            local mime = ""
            local hasVid = false
            pcall(function()
                local ex, pfd = openEx(fileObj.uri, fileObj.path)
                if ex then
                    for i = 0, ex.getTrackCount() - 1 do
                        local m = ex.getTrackFormat(i).getString(MediaFormat.KEY_MIME)
                        if m then
                            if m:find("video/") then hasVid = true end
                            if m:find("audio/") and mime == "" then mime = m end
                        end
                    end
                    ex.release()
                end
                if pfd then pcall(function() pfd.close() end) end
            end)
            return mime, hasVid
        end

        local function getVidRot(uri, filePath)
            local rot = 0
            pcall(function()
                local mmr = MediaMetadataRetriever()
                local setOk = false
                if filePath and File(filePath).exists() then
                    pcall(function()
                        local fis = FileInputStream(File(filePath))
                        mmr.setDataSource(fis.getFD())
                        fis.close()
                        setOk = true
                    end)
                end
                if not setOk and uri then
                    pcall(function()
                        local pfd = act.getContentResolver().openFileDescriptor(uri, "r")
                        if pfd then
                            mmr.setDataSource(pfd.getFileDescriptor())
                            pfd.close()
                            setOk = true
                        end
                    end)
                end
                if setOk then
                    local rStr = mmr.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_ROTATION)
                    if rStr then rot = tonumber(rStr) or 0 end
                end
                mmr.release()
            end)
            return rot
        end

        local function decodeToPcm(fileObj, outPcmChan, startMsVal, endMsVal, onSubPct, allowSkip)
            local ex, pfd = openEx(fileObj.uri, fileObj.path)
            if not ex then
                if allowSkip then return nil, nil, false end
                error("Cannot open file: " .. tostring(fileObj.name))
            end
            local aTrack = -1
            local fmt = nil
            for i = 0, ex.getTrackCount() - 1 do
                local f = ex.getTrackFormat(i)
                local m = f.getString(MediaFormat.KEY_MIME)
                if m and m:find("audio/") then
                    aTrack = i; fmt = f; break
                end
            end
            if aTrack == -1 or not fmt then
                ex.release()
                if pfd then pcall(function() pfd.close() end) end
                if allowSkip then return nil, nil, false end
                error("No audio track in: " .. tostring(fileObj.name))
            end

            ex.selectTrack(aTrack)
            local mime = fmt.getString(MediaFormat.KEY_MIME)
            local sr = fmt.containsKey(MediaFormat.KEY_SAMPLE_RATE) and fmt.getInteger(MediaFormat.KEY_SAMPLE_RATE) or 44100
            local ch = fmt.containsKey(MediaFormat.KEY_CHANNEL_COUNT) and fmt.getInteger(MediaFormat.KEY_CHANNEL_COUNT) or 2

            local startUs = (startMsVal and startMsVal > 0) and (startMsVal * 1000) or 0
            local endUs = (endMsVal and endMsVal > 0) and (endMsVal * 1000) or 0
            local fDurMs = (fileObj.duration and fileObj.duration > 0) and fileObj.duration or 180000
            local spanUs = (endUs > startUs) and (endUs - startUs) or (fDurMs * 1000)
            if spanUs <= 0 then spanUs = 1000000 end

            ex.seekTo(startUs, MediaExtractor.SEEK_TO_CLOSEST_SYNC)

            local dec = MediaCodec.createDecoderByType(mime)
            dec.configure(fmt, nil, nil, 0)
            dec.start()

            local inBufs, outBufs = nil, nil
            pcall(function() inBufs = dec.getInputBuffers(); outBufs = dec.getOutputBuffers() end)

            local info = MediaCodec.BufferInfo()
            local isEOS = false
            local outDone = false
            local pktCount = 0
            local eosRetries = 0
            local stallRetries = 0

            while not outDone do
                local didWork = false
                if not isEOS then
                    local inIdx = dec.dequeueInputBuffer(5000)
                    if inIdx >= 0 then
                        didWork = true
                        local inBuf = nil
                        pcall(function() inBuf = dec.getInputBuffer(inIdx) end)
                        if not inBuf and inBufs then inBuf = inBufs[inIdx + 1] end
                        if inBuf then
                            inBuf.clear()
                            local sz = ex.readSampleData(inBuf, 0)
                            local pts = ex.getSampleTime()
                            if sz < 0 or (endUs > 0 and pts > endUs) then
                                dec.queueInputBuffer(inIdx, 0, 0, 0, MediaCodec.BUFFER_FLAG_END_OF_STREAM)
                                isEOS = true
                            else
                                dec.queueInputBuffer(inIdx, 0, sz, math.max(0, pts), 0)
                                ex.advance()
                            end
                        end
                    end
                end

                local outIdx = dec.dequeueOutputBuffer(info, 5000)
                if outIdx == MediaCodec.INFO_OUTPUT_BUFFERS_CHANGED then
                    didWork = true
                    pcall(function() outBufs = dec.getOutputBuffers() end)
                elseif outIdx == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED then
                    didWork = true
                    local nf = dec.getOutputFormat()
                    if nf.containsKey(MediaFormat.KEY_SAMPLE_RATE) then sr = nf.getInteger(MediaFormat.KEY_SAMPLE_RATE) end
                    if nf.containsKey(MediaFormat.KEY_CHANNEL_COUNT) then ch = nf.getInteger(MediaFormat.KEY_CHANNEL_COUNT) end
                elseif outIdx >= 0 then
                    didWork = true
                    eosRetries = 0
                    stallRetries = 0
                    local outBuf = nil
                    pcall(function() outBuf = dec.getOutputBuffer(outIdx) end)
                    if not outBuf and outBufs then outBuf = outBufs[outIdx + 1] end
                    if info.size > 0 and outBuf and info.presentationTimeUs >= startUs then
                        outBuf.position(info.offset)
                        outBuf.limit(info.offset + info.size)
                        while outBuf.hasRemaining() do
                            outPcmChan.write(outBuf)
                        end
                        pktCount = pktCount + 1
                        if onSubPct and (pktCount % 30 == 0) then
                            onSubPct(math.min(99, math.max(1, math.floor(((info.presentationTimeUs - startUs) * 100) / spanUs))))
                        end
                    end
                    dec.releaseOutputBuffer(outIdx, false)
                    if math.floor((info.flags or 0) / 4) % 2 == 1 then outDone = true end
                else
                    if isEOS then
                        eosRetries = eosRetries + 1
                        if eosRetries >= 20 then outDone = true end
                    elseif not didWork then
                        stallRetries = stallRetries + 1
                        if stallRetries >= 80 then outDone = true end
                    end
                end
            end

            pcall(function() dec.stop(); dec.release() end)
            pcall(function() ex.release() end)
            if pfd then pcall(function() pfd.close() end) end
            return sr, ch, true
        end

        local function encodePcmToM4A(pcmPath, outM4APath, sampleRate, channels, onSubPct, customBitrate)
            local sr = (sampleRate and sampleRate > 0) and sampleRate or 44100
            local ch = (channels and channels > 0) and channels or 2
            local br = (customBitrate and customBitrate > 0) and customBitrate or 128000
            local mime = "audio/mp4a-latm"

            local outFmt = MediaFormat.createAudioFormat(mime, sr, ch)
            outFmt.setInteger(MediaFormat.KEY_AAC_PROFILE, MediaCodecInfo.CodecProfileLevel.AACObjectLC)
            outFmt.setInteger(MediaFormat.KEY_BIT_RATE, br)
            outFmt.setInteger(MediaFormat.KEY_MAX_INPUT_SIZE, 32768)

            local enc = MediaCodec.createEncoderByType(mime)
            enc.configure(outFmt, nil, nil, MediaCodec.CONFIGURE_FLAG_ENCODE)
            enc.start()

            local inBufs, outBufs = nil, nil
            pcall(function() inBufs = enc.getInputBuffers(); outBufs = enc.getOutputBuffers() end)

            local muxer = MediaMuxer(outM4APath, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
            local muxTrack = -1
            local muxStarted = false

            local pcmF = File(tostring(pcmPath))
            local totalBytes = math.max(1, pcmF.length())
            local fis = FileInputStream(pcmF)
            local inChan = fis.getChannel()

            local info = MediaCodec.BufferInfo()
            local isEOS = false
            local encDone = false
            local bytesRead = 0
            local frameBytes = 2 * ch
            local lastPtsUs = -1
            local pktCount = 0
            local eosRetries = 0
            local stallRetries = 0

            pcall(function()
                while not encDone do
                    local didWork = false
                    if not isEOS then
                        local inIdx = enc.dequeueInputBuffer(5000)
                        if inIdx >= 0 then
                            didWork = true
                            local inBuf = nil
                            pcall(function() inBuf = enc.getInputBuffer(inIdx) end)
                            if not inBuf and inBufs then inBuf = inBufs[inIdx + 1] end
                            if inBuf then
                                inBuf.clear()
                                inBuf.limit(math.min(inBuf.capacity(), 4096))
                                local nRead = inChan.read(inBuf)
                                if nRead <= 0 then
                                    local ptsUs = math.floor((bytesRead / frameBytes) * 1000000 / sr)
                                    enc.queueInputBuffer(inIdx, 0, 0, ptsUs, MediaCodec.BUFFER_FLAG_END_OF_STREAM)
                                    isEOS = true
                                else
                                    inBuf.flip()
                                    local ptsUs = math.floor((bytesRead / frameBytes) * 1000000 / sr)
                                    bytesRead = bytesRead + nRead
                                    enc.queueInputBuffer(inIdx, 0, nRead, ptsUs, 0)
                                end
                            end
                        end
                    end

                    local outIdx = enc.dequeueOutputBuffer(info, 5000)
                    if outIdx == MediaCodec.INFO_OUTPUT_BUFFERS_CHANGED then
                        didWork = true
                        pcall(function() outBufs = enc.getOutputBuffers() end)
                    elseif outIdx == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED then
                        didWork = true
                        muxTrack = muxer.addTrack(enc.getOutputFormat())
                        muxer.start()
                        muxStarted = true
                    elseif outIdx >= 0 then
                        didWork = true
                        eosRetries = 0
                        stallRetries = 0
                        local outBuf = nil
                        pcall(function() outBuf = enc.getOutputBuffer(outIdx) end)
                        if not outBuf and outBufs then outBuf = outBufs[outIdx + 1] end
                        if math.floor((info.flags or 0) / 2) % 2 == 1 then info.size = 0 end
                        if info.size > 0 and muxStarted and outBuf then
                            if info.presentationTimeUs <= lastPtsUs then
                                info.presentationTimeUs = lastPtsUs + 1000
                            end
                            lastPtsUs = info.presentationTimeUs
                            outBuf.position(info.offset)
                            outBuf.limit(info.offset + info.size)
                            muxer.writeSampleData(muxTrack, outBuf, info)
                            pktCount = pktCount + 1
                            if onSubPct and (pktCount % 30 == 0) then
                                onSubPct(math.min(99, math.max(1, math.floor((bytesRead * 100) / totalBytes))))
                            end
                        end
                        enc.releaseOutputBuffer(outIdx, false)
                        if math.floor((info.flags or 0) / 4) % 2 == 1 then encDone = true end
                    else
                        if isEOS then
                            eosRetries = eosRetries + 1
                            if eosRetries >= 20 then encDone = true end
                        elseif not didWork then
                            stallRetries = stallRetries + 1
                            if stallRetries >= 80 then encDone = true end
                        end
                    end
                end
            end)

            pcall(function() inChan.close() end)
            pcall(function() fis.close() end)
            if muxStarted then pcall(function() muxer.stop() end) end
            pcall(function() muxer.release() end)
            pcall(function() enc.stop(); enc.release() end)
        end

        -- Write Standard 16-bit RIFF WAVE (.wav) Lossless Studio Audio
        local function encodePcmToWav(pcmPath, outWavPath, sampleRate, channels, onSubPct)
            local sr = (sampleRate and sampleRate > 0) and sampleRate or 44100
            local ch = (channels and channels > 0) and channels or 2
            local pcmF = File(tostring(pcmPath))
            local dataLen = pcmF.length()
            local totalDataLen = dataLen + 36
            local byteRate = sr * ch * 2
            local blockAlign = ch * 2

            local fos = FileOutputStream(outWavPath)
            local outChan = fos.getChannel()
            local hdrBuf = ByteBuffer.allocateDirect(44)
            hdrBuf.order(ByteOrder.LITTLE_ENDIAN)
            -- "RIFF"
            hdrBuf.put(0x52); hdrBuf.put(0x49); hdrBuf.put(0x46); hdrBuf.put(0x46)
            hdrBuf.putInt(math.floor(totalDataLen))
            -- "WAVEfmt "
            hdrBuf.put(0x57); hdrBuf.put(0x41); hdrBuf.put(0x56); hdrBuf.put(0x45)
            hdrBuf.put(0x66); hdrBuf.put(0x6D); hdrBuf.put(0x74); hdrBuf.put(0x20)
            hdrBuf.putInt(16) -- Subchunk1Size (16 for PCM)
            hdrBuf.putShort(1) -- AudioFormat (1 = PCM)
            hdrBuf.putShort(ch)
            hdrBuf.putInt(sr)
            hdrBuf.putInt(byteRate)
            hdrBuf.putShort(blockAlign)
            hdrBuf.putShort(16) -- BitsPerSample
            -- "data"
            hdrBuf.put(0x64); hdrBuf.put(0x61); hdrBuf.put(0x74); hdrBuf.put(0x61)
            hdrBuf.putInt(math.floor(dataLen))
            hdrBuf.flip()
            while hdrBuf.hasRemaining() do outChan.write(hdrBuf) end

            local fis = FileInputStream(pcmF)
            local inChan = fis.getChannel()
            local copyBuf = ByteBuffer.allocateDirect(65536)
            local copied = 0
            local chunkIdx = 0
            while true do
                copyBuf.clear()
                local nr = inChan.read(copyBuf)
                if nr <= 0 then break end
                copyBuf.flip()
                while copyBuf.hasRemaining() do outChan.write(copyBuf) end
                copied = copied + nr
                chunkIdx = chunkIdx + 1
                if onSubPct and (chunkIdx % 10 == 0) then
                    onSubPct(math.min(99, math.max(1, math.floor((copied * 100) / math.max(1, dataLen)))))
                end
            end
            outChan.force(true)
            outChan.close(); inChan.close()
            fos.close(); fis.close()
        end

        -- Studio PCM DSP Engine: Background Noise Removal + Studio Echo/Reverb + Volume Booster with Soft-Knee Anti-Clip
        local function processPcmDSP(inPcmPath, outPcmPath, sr, ch, dspOpts, onSubPct)
            sr = (sr and sr > 0) and sr or 44100
            ch = (ch and ch > 0) and ch or 2
            local inF = File(tostring(inPcmPath))
            local totalBytes = inF.length()
            if totalBytes <= 64 then
                return
            end

            local cleanNoise = dspOpts.cleanNoise == true
            local noiseStr = (dspOpts.noiseStrengthPct or 80) / 100.0
            local addEcho = dspOpts.addEcho == true
            local delayMs = math.max(40, math.min(600, dspOpts.echoDelayMs or 220))
            local decay = math.max(0.05, math.min(0.85, (dspOpts.echoDecayPct or 45) / 100.0))
            local gainMult = (dspOpts.gainPct or 100) / 100.0

            local frameBytes = 2 * ch
            local winFrames = math.max(256, math.floor(sr * 0.02)) -- 20ms window
            local winBytes = winFrames * frameBytes

            -- Pass 1: Auto-measure background noise floor across 32 evenly spaced windows if cleanNoise is enabled
            local gateThresh = 380
            if cleanNoise then
                pcall(function()
                    local fisP = FileInputStream(inF)
                    local chP = fisP.getChannel()
                    local pBuf = ByteBuffer.allocateDirect(winBytes)
                    pBuf.order(ByteOrder.LITTLE_ENDIAN)
                    local nProbe = 32
                    local stepBytes = math.floor(math.max(winBytes, (totalBytes - winBytes) / nProbe) / frameBytes) * frameBytes
                    local amps = {}
                    for i = 0, nProbe - 1 do
                        local pos = math.min(math.max(0, totalBytes - winBytes), i * stepBytes)
                        chP.position(pos)
                        pBuf.clear()
                        local nr = chP.read(pBuf)
                        if nr >= frameBytes then
                            pBuf.flip()
                            local nF = math.floor(nr / frameBytes)
                            local sAbs = 0
                            local cnt = 0
                            local stp = math.max(1, math.floor(nF / 16))
                            for f = 0, nF - 1, stp do
                                sAbs = sAbs + math.abs(pBuf.getShort(f * frameBytes))
                                cnt = cnt + 1
                            end
                            if cnt > 0 then table.insert(amps, sAbs / cnt) end
                        end
                    end
                    chP.close(); fisP.close()
                    if #amps >= 4 then
                        table.sort(amps)
                        -- 25th percentile represents background noise floor during pauses
                        local floorIdx = math.max(1, math.floor(#amps * 0.25))
                        local estFloor = amps[floorIdx]
                        gateThresh = math.max(160, math.min(2600, estFloor * (1.25 + noiseStr * 1.45)))
                    end
                end)
            end

            -- Prepare Echo Delay Line Buffer (if addEcho is enabled)
            local delayFrames = math.max(128, math.floor((sr * delayMs) / 1000))
            local earlyFrames = math.max(64, math.floor(delayFrames * 0.45))
            local delayBuf = {}
            local delayLen = delayFrames * ch
            if addEcho then
                for i = 1, delayLen do delayBuf[i] = 0 end
            end
            local delayWriteFrame = 0

            -- High-pass filter state per channel (removes <85Hz mic rumble/hum) and de-hiss state
            local hpPrevX = {0, 0, 0, 0}
            local hpPrevY = {0, 0, 0, 0}
            local lpPrevY = {0, 0, 0, 0}
            local curGateGain = 1.0
            local minGateFloor = math.max(0.02, 0.22 * (1.0 - noiseStr))

            local fis = FileInputStream(inF)
            local fos = FileOutputStream(outPcmPath)
            local inChan = fis.getChannel()
            local outChan = fos.getChannel()

            local buf = ByteBuffer.allocateDirect(winBytes)
            local outB = ByteBuffer.allocateDirect(winBytes)
            buf.order(ByteOrder.LITTLE_ENDIAN)
            outB.order(ByteOrder.LITTLE_ENDIAN)

            local bytesDone = 0
            local winCount = 0

            while true do
                buf.clear()
                local nr = inChan.read(buf)
                if nr <= 0 then break end
                buf.flip()
                local actualFrames = math.floor(nr / frameBytes)

                if cleanNoise and actualFrames > 0 then
                    local sumAbs = 0
                    local cnt = 0
                    local stp = math.max(1, math.floor(actualFrames / 16))
                    for f = 0, actualFrames - 1, stp do
                        sumAbs = sumAbs + math.abs(buf.getShort(f * frameBytes))
                        cnt = cnt + 1
                    end
                    local avgAmp = (cnt > 0) and (sumAbs / cnt) or 0
                    local targetGate = 1.0
                    if avgAmp < gateThresh then
                        local ratio = avgAmp / math.max(1, gateThresh)
                        targetGate = math.max(minGateFloor, ratio * ratio)
                    end
                    if targetGate > curGateGain then
                        -- Fast attack when voice starts speaking so syllables are never clipped
                        curGateGain = curGateGain * 0.25 + targetGate * 0.75
                    else
                        -- Smooth natural release when voice pauses
                        curGateGain = curGateGain * 0.80 + targetGate * 0.20
                    end
                end

                outB.clear()
                for f = 0, actualFrames - 1 do
                    local earlyReadFrame = (delayWriteFrame + delayFrames - earlyFrames) % delayFrames
                    for c = 0, ch - 1 do
                        local cIdx = c + 1
                        local raw = buf.getShort(f * frameBytes + c * 2)
                        local sample = raw

                        if cleanNoise then
                            -- 1st-order 85Hz High-Pass Filter to remove mic rumble, wind, & DC hum
                            local hpY = 0.985 * (hpPrevY[cIdx] + sample - hpPrevX[cIdx])
                            hpPrevX[cIdx] = sample
                            hpPrevY[cIdx] = hpY
                            -- Gentle high-frequency hiss smoothing when gate is attenuating noise
                            local lpAlpha = (curGateGain < 0.5) and 0.65 or 0.90
                            local cleaned = lpPrevY[cIdx] + lpAlpha * (hpY - lpPrevY[cIdx])
                            lpPrevY[cIdx] = cleaned
                            sample = cleaned * curGateGain
                        end

                        if addEcho then
                            local dIdx = delayWriteFrame * ch + cIdx
                            local eIdx = earlyReadFrame * ch + cIdx
                            local delayedMain = delayBuf[dIdx] or 0
                            local delayedEarly = delayBuf[eIdx] or 0
                            local echoMix = sample + delayedMain * decay + delayedEarly * (decay * 0.32)
                            local fbVal = sample + delayedMain * (decay * 0.72)
                            if fbVal > 30000 then fbVal = 30000 elseif fbVal < -30000 then fbVal = -30000 end
                            delayBuf[dIdx] = fbVal
                            sample = echoMix
                        end

                        -- Apply Volume Booster / Gain + Studio Soft-Knee Anti-Clip Limiter
                        sample = sample * gainMult
                        if sample > 26000 then
                            sample = 26000 + (sample - 26000) / (1.0 + ((sample - 26000) / 6767.0))
                            if sample > 32760 then sample = 32760 end
                        elseif sample < -26000 then
                            sample = -26000 + (sample + 26000) / (1.0 + ((-sample - 26000) / 6767.0))
                            if sample < -32760 then sample = -32760 end
                        end

                        outB.putShort(f * frameBytes + c * 2, math.floor(sample))
                    end
                    if addEcho then
                        delayWriteFrame = (delayWriteFrame + 1) % delayFrames
                    end
                end

                outB.position(0)
                outB.limit(actualFrames * frameBytes)
                while outB.hasRemaining() do
                    outChan.write(outB)
                end

                bytesDone = bytesDone + nr
                winCount = winCount + 1
                if onSubPct and (winCount % 20 == 0) then
                    onSubPct(math.min(99, math.max(1, math.floor((bytesDone * 100) / totalBytes))))
                end
            end

            outChan.force(true)
            outChan.close(); inChan.close()
            fos.close(); fis.close()
        end

        -- Losslessly Replace a Video's Audio Track with a Processed M4A Audio File
        local function remuxVideoWithNewAudio(vItem, newAudM4APath, outMp4Path, onSubPct)
            local vEx, vPfd = openEx(vItem.uri, vItem.path)
            if not vEx then error("Cannot open video file") end
            local aEx, aPfd = openEx(nil, newAudM4APath)
            if not aEx then
                vEx.release()
                if vPfd then pcall(function() vPfd.close() end) end
                error("Cannot open processed audio track")
            end

            local muxer = MediaMuxer(outMp4Path, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
            local rot = getVidRot(vItem.uri, vItem.path)
            if rot ~= 0 then pcall(function() muxer.setOrientationHint(rot) end) end

            local vTrackIn, vTrackOut = -1, -1
            for i = 0, vEx.getTrackCount() - 1 do
                local fmt = vEx.getTrackFormat(i)
                local m = fmt.getString(MediaFormat.KEY_MIME)
                if m and m:find("video/") then
                    vTrackIn = i
                    vTrackOut = muxer.addTrack(fmt)
                    break
                end
            end

            local aTrackIn, aTrackOut = -1, -1
            for i = 0, aEx.getTrackCount() - 1 do
                local fmt = aEx.getTrackFormat(i)
                local m = fmt.getString(MediaFormat.KEY_MIME)
                if m and m:find("audio/") then
                    aTrackIn = i
                    aTrackOut = muxer.addTrack(fmt)
                    break
                end
            end

            muxer.start()
            local buf = ByteBuffer.allocateDirect(1048576)
            local info = MediaCodec.BufferInfo()
            local vidDurUs = ((vItem.duration and vItem.duration > 0) and vItem.duration or 60000) * 1000

            if vTrackIn ~= -1 then
                vEx.selectTrack(vTrackIn)
                copyRangeAligned(vEx, muxer, {[vTrackIn] = vTrackOut}, 0, 0, 0, buf, info, vidDurUs, function(p)
                    if onSubPct then onSubPct(math.floor(p * 0.65)) end
                end)
            end
            if aTrackIn ~= -1 then
                aEx.selectTrack(aTrackIn)
                copyRangeAligned(aEx, muxer, {[aTrackIn] = aTrackOut}, 0, vidDurUs, 0, buf, info, vidDurUs, function(p)
                    if onSubPct then onSubPct(65 + math.floor(p * 0.34)) end
                end)
            end

            pcall(function() muxer.stop() end)
            pcall(function() muxer.release() end)
            pcall(function() vEx.release() end)
            pcall(function() aEx.release() end)
            if vPfd then pcall(function() vPfd.close() end) end
            if aPfd then pcall(function() aPfd.close() end) end
        end

        -- Convert Any Audio File (MP3/M4A/WAV) into a Studio MP4 Video with Visual Title Card
        local function renderAudioToMp4Video(audioItem, audioM4APath, outMp4Path, qVal, onSubPct)
            local outW, outH, bitRate = getQualityDims((qVal and qVal > 0) and qVal or 3, false)
            local fps = 10
            local stepUs = math.floor(1000000 / fps)
            local durMs = (audioItem.duration and audioItem.duration > 0) and audioItem.duration or 10000
            local totFrames = math.max(10, math.floor((durMs * fps) / 1000))

            local vFmt = MediaFormat.createVideoFormat("video/avc", outW, outH)
            vFmt.setInteger(MediaFormat.KEY_COLOR_FORMAT, MediaCodecInfo.CodecCapabilities.COLOR_FormatSurface)
            vFmt.setInteger(MediaFormat.KEY_BIT_RATE, bitRate)
            vFmt.setInteger(MediaFormat.KEY_FRAME_RATE, fps)
            vFmt.setInteger(MediaFormat.KEY_I_FRAME_INTERVAL, 2)

            local vEnc = MediaCodec.createEncoderByType("video/avc")
            vEnc.configure(vFmt, nil, nil, MediaCodec.CONFIGURE_FLAG_ENCODE)
            local inSurf = vEnc.createInputSurface()
            vEnc.start()

            local vOutBufs = nil
            pcall(function() vOutBufs = vEnc.getOutputBuffers() end)

            local muxer = MediaMuxer(outMp4Path, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
            local muxV, muxA = -1, -1
            local muxStarted = false

            local aEx, aPfd = openEx(nil, audioM4APath)
            local aFmt = nil
            if aEx then
                for i = 0, aEx.getTrackCount() - 1 do
                    local f = aEx.getTrackFormat(i)
                    local m = f.getString(MediaFormat.KEY_MIME)
                    if m and m:find("audio/") then aEx.selectTrack(i); aFmt = f; break end
                end
            end

            local vInfo = MediaCodec.BufferInfo()
            local function drainV(eos, ptsUs)
                if eos then pcall(function() vEnc.signalEndOfInputStream() end) end
                local tries = 0
                while tries < 30 do
                    local idx = vEnc.dequeueOutputBuffer(vInfo, 5000)
                    if idx == MediaCodec.INFO_TRY_AGAIN_LATER then
                        if not eos then break end
                        tries = tries + 1
                    elseif idx == MediaCodec.INFO_OUTPUT_BUFFERS_CHANGED then
                        pcall(function() vOutBufs = vEnc.getOutputBuffers() end)
                    elseif idx == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED then
                        muxV = muxer.addTrack(vEnc.getOutputFormat())
                        if aFmt then muxA = muxer.addTrack(aFmt) end
                        muxer.start()
                        muxStarted = true
                    elseif idx >= 0 then
                        local ob = nil
                        pcall(function() ob = vEnc.getOutputBuffer(idx) end)
                        if not ob and vOutBufs then ob = vOutBufs[idx + 1] end
                        if math.floor((vInfo.flags or 0) / 2) % 2 == 1 then vInfo.size = 0 end
                        if vInfo.size > 0 and muxStarted and ob then
                            vInfo.presentationTimeUs = ptsUs
                            ob.position(vInfo.offset)
                            ob.limit(vInfo.offset + vInfo.size)
                            muxer.writeSampleData(muxV, ob, vInfo)
                        end
                        vEnc.releaseOutputBuffer(idx, false)
                        if math.floor((vInfo.flags or 0) / 4) % 2 == 1 then break end
                    end
                end
            end

            local paintBg = Paint()
            local paintText = Paint(Paint.ANTI_ALIAS_FLAG)
            paintText.setColor(0xFF22D3EE)
            paintText.setTextSize(math.floor(outH * 0.06))
            paintText.setTextAlign(Paint.Align.CENTER)

            local paintSub = Paint(Paint.ANTI_ALIAS_FLAG)
            paintSub.setColor(0xFFFBBF24)
            paintSub.setTextSize(math.floor(outH * 0.04))
            paintSub.setTextAlign(Paint.Align.CENTER)

            local displayTitle = tostring(audioItem.name or "Audio Track")
            if #displayTitle > 38 then displayTitle = displayTitle:sub(1, 35) .. "..." end

            pcall(function()
                for f = 0, totFrames - 1 do
                    local ptsUs = f * stepUs
                    local canvas = inSurf.lockCanvas(nil)
                    if canvas then
                        canvas.drawColor(0xFF12101B)
                        canvas.drawText("SMART MEDIA STUDIO PRO", outW / 2, outH * 0.42, paintText)
                        canvas.drawText(displayTitle, outW / 2, outH * 0.56, paintSub)
                        inSurf.unlockCanvasAndPost(canvas)
                    end
                    drainV(false, ptsUs)
                    if onSubPct and (f % 6 == 0) then
                        onSubPct(math.min(90, math.floor((f * 85) / totFrames)))
                    end
                end
                drainV(true, totFrames * stepUs)

                if muxStarted and muxA ~= -1 and aEx then
                    local aBuf = ByteBuffer.allocateDirect(262144)
                    local aInfo = MediaCodec.BufferInfo()
                    while true do
                        aInfo.size = aEx.readSampleData(aBuf, 0)
                        if aInfo.size < 0 then break end
                        aInfo.offset = 0; aInfo.presentationTimeUs = math.max(0, aEx.getSampleTime()); aInfo.flags = aEx.getSampleFlags()
                        muxer.writeSampleData(muxA, aBuf, aInfo)
                        aEx.advance()
                    end
                end
            end)

            if aEx then pcall(function() aEx.release() end) end
            if aPfd then pcall(function() aPfd.close() end) end
            if muxStarted then pcall(function() muxer.stop() end) end
            pcall(function() muxer.release() end)
            pcall(function() inSurf.release() end)
            pcall(function() vEnc.stop(); vEnc.release() end)
        end

        local function copyRangeAligned(extractor, muxer, trackMap, rStartUs, rEndUs, baseOffUs, buf, info, totDurUs, onSubPct)
            extractor.seekTo(rStartUs > 0 and rStartUs or 0, MediaExtractor.SEEK_TO_CLOSEST_SYNC)
            local firstPts = nil
            local maxWritten = baseOffUs
            local pkt = 0
            local spanUs = (rEndUs > rStartUs) and (rEndUs - rStartUs) or math.max(1000000, totDurUs or 60000000)

            while true do
                info.size = extractor.readSampleData(buf, 0)
                if info.size < 0 then break end
                local pts = extractor.getSampleTime()
                if rEndUs > 0 and pts > rEndUs then break end
                local tr = extractor.getSampleTrackIndex()
                if trackMap[tr] and pts >= rStartUs then
                    if not firstPts then firstPts = pts end
                    local rel = math.max(0, pts - firstPts)
                    info.offset = 0
                    info.presentationTimeUs = baseOffUs + rel
                    info.flags = extractor.getSampleFlags()
                    if info.presentationTimeUs > maxWritten then maxWritten = info.presentationTimeUs end
                    muxer.writeSampleData(trackMap[tr], buf, info)
                    pkt = pkt + 1
                    if onSubPct and (pkt % 45 == 0) then
                        onSubPct(math.min(99, math.max(1, math.floor((rel * 100) / spanUs))))
                    end
                end
                extractor.advance()
            end
            return maxWritten
        end

        local function getQualityDims(qVal, isVert)
            local w, h, br = 1280, 720, 3500000
            if qVal == 1 then w, h, br = 1920, 1088, 12000000
            elseif qVal == 2 then w, h, br = 1920, 1088, 6000000
            elseif qVal == 3 or qVal == 0 then w, h, br = 1280, 720, 3500000
            elseif qVal == 4 then w, h, br = 848, 480, 1800000
            elseif qVal == 5 then w, h, br = 640, 368, 1000000 end
            if isVert then return h, w, br else return w, h, br end
        end

        local function openMmr(uri, filePath)
            local mmr = MediaMetadataRetriever()
            local ok = false
            if filePath and tostring(filePath) ~= "" then
                pcall(function()
                    local f = File(tostring(filePath))
                    if f.exists() and f.length() >= 256 then
                        local fis = FileInputStream(f)
                        mmr.setDataSource(fis.getFD())
                        fis.close()
                        ok = true
                    end
                end)
            end
            if not ok and uri then
                pcall(function()
                    local pfd = act.getContentResolver().openFileDescriptor(uri, "r")
                    if pfd then
                        mmr.setDataSource(pfd.getFileDescriptor())
                        pfd.close()
                        ok = true
                    end
                end)
            end
            if not ok and uri then
                pcall(function() mmr.setDataSource(act, uri); ok = true end)
            end
            if not ok then pcall(function() mmr.release() end); return nil end
            return mmr
        end

        local function grabFrame(mmr, tUs, tw, th)
            if not mmr then return nil end
            local bmp = nil
            if Build.VERSION.SDK_INT >= 27 then
                pcall(function()
                    bmp = mmr.getScaledFrameAtTime(tUs, MediaMetadataRetriever.OPTION_CLOSEST_SYNC, tw, th)
                end)
            end
            if not bmp then
                pcall(function()
                    bmp = mmr.getFrameAtTime(tUs, MediaMetadataRetriever.OPTION_CLOSEST_SYNC)
                end)
            end
            return bmp
        end

        local function renderSplitVideo(vid1, vid2, outMp4Path, layMode, qVal)
            local isTopBot = (layMode == 0)
            local effQ = (qVal and qVal > 0) and qVal or 3
            local outW, outH, bitRate = getQualityDims(effQ, isTopBot)
            local fps = 12
            local stepUs = math.floor(1000000 / fps)

            local dur1 = (vid1.duration and vid1.duration > 0) and vid1.duration or 10000
            local dur2 = (vid2.duration and vid2.duration > 0) and vid2.duration or 10000
            local totDurMs = math.max(dur1, dur2)
            local totFrames = math.max(12, math.floor((totDurMs * fps) / 1000))

            local tmpAudM4A = workDir .. "_tmp_split_aud.m4a"
            local hasAud = false
            pcall(function()
                local tmpPcm = workDir .. "_tmp_split_aud.pcm"
                local fos = FileOutputStream(tmpPcm)
                local pChan = fos.getChannel()
                local sr, ch, okDec = decodeToPcm(vid1, pChan, 0, 0, function(p) setPct(math.floor(p * 0.15)) end, true)
                pChan.force(true); pChan.close(); fos.close()
                if okDec and File(tmpPcm).length() > 512 then
                    encodePcmToM4A(tmpPcm, tmpAudM4A, sr, ch, function(p) setPct(15 + math.floor(p * 0.10)) end)
                    if File(tmpAudM4A).exists() and File(tmpAudM4A).length() > 512 then hasAud = true end
                end
                pcall(function() File(tmpPcm).delete() end)
            end)

            local vFmt = MediaFormat.createVideoFormat("video/avc", outW, outH)
            vFmt.setInteger(MediaFormat.KEY_COLOR_FORMAT, MediaCodecInfo.CodecCapabilities.COLOR_FormatSurface)
            vFmt.setInteger(MediaFormat.KEY_BIT_RATE, bitRate)
            vFmt.setInteger(MediaFormat.KEY_FRAME_RATE, fps)
            vFmt.setInteger(MediaFormat.KEY_I_FRAME_INTERVAL, 1)

            local vEnc = MediaCodec.createEncoderByType("video/avc")
            vEnc.configure(vFmt, nil, nil, MediaCodec.CONFIGURE_FLAG_ENCODE)
            local inSurf = vEnc.createInputSurface()
            vEnc.start()

            local outBufs = nil
            pcall(function() outBufs = vEnc.getOutputBuffers() end)

            local muxer = MediaMuxer(outMp4Path, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
            local muxV = -1
            local muxA = -1
            local muxStarted = false

            local aEx, aPfd = nil, nil
            if hasAud then
                aEx, aPfd = openEx(nil, tmpAudM4A)
                if aEx then
                    for i = 0, aEx.getTrackCount() - 1 do
                        local f = aEx.getTrackFormat(i)
                        local m = f.getString(MediaFormat.KEY_MIME)
                        if m and m:find("audio/") then
                            aEx.selectTrack(i); muxA = muxer.addTrack(f); break
                        end
                    end
                end
            end

            local mmr1 = openMmr(vid1.uri, vid1.path)
            local mmr2 = openMmr(vid2.uri, vid2.path)

            local rect1, rect2, cellW, cellH
            if isTopBot then
                cellW = outW; cellH = math.floor(outH / 2)
                rect1 = Rect(0, 0, outW, cellH)
                rect2 = Rect(0, cellH, outW, outH)
            else
                cellW = math.floor(outW / 2); cellH = outH
                rect1 = Rect(0, 0, cellW, outH)
                rect2 = Rect(cellW, 0, outW, outH)
            end

            local paint = Paint(Paint.FILTER_BITMAP_FLAG)
            local info = MediaCodec.BufferInfo()
            local lastVPts = -1

            local function drainV(isFinal, targetPts)
                if isFinal then pcall(function() vEnc.signalEndOfInputStream() end) end
                local retries = 0
                while true do
                    local outIdx = vEnc.dequeueOutputBuffer(info, isFinal and 5000 or 1000)
                    if outIdx == MediaCodec.INFO_TRY_AGAIN_LATER then
                        if not isFinal then break end
                        retries = retries + 1
                        if retries > 20 then break end
                    elseif outIdx == MediaCodec.INFO_OUTPUT_BUFFERS_CHANGED then
                        pcall(function() outBufs = vEnc.getOutputBuffers() end)
                    elseif outIdx == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED then
                        muxV = muxer.addTrack(vEnc.getOutputFormat())
                        muxer.start()
                        muxStarted = true
                    elseif outIdx >= 0 then
                        retries = 0
                        local outBuf = nil
                        pcall(function() outBuf = vEnc.getOutputBuffer(outIdx) end)
                        if not outBuf and outBufs then outBuf = outBufs[outIdx + 1] end
                        if math.floor((info.flags or 0) / 2) % 2 == 1 then info.size = 0 end
                        if info.size > 0 and muxStarted and outBuf then
                            local pts = targetPts or info.presentationTimeUs
                            if pts <= lastVPts then pts = lastVPts + stepUs end
                            lastVPts = pts
                            info.presentationTimeUs = pts
                            outBuf.position(info.offset)
                            outBuf.limit(info.offset + info.size)
                            muxer.writeSampleData(muxV, outBuf, info)
                        end
                        vEnc.releaseOutputBuffer(outIdx, false)
                        if math.floor((info.flags or 0) / 4) % 2 == 1 then break end
                    end
                end
            end

            pcall(function()
                for fIdx = 0, totFrames - 1 do
                    local tUs = fIdx * stepUs
                    local t1Us = (dur1 > 0) and (tUs % (dur1 * 1000)) or tUs
                    local t2Us = (dur2 > 0) and (tUs % (dur2 * 1000)) or tUs

                    local bmp1 = grabFrame(mmr1, t1Us, cellW, cellH)
                    local bmp2 = grabFrame(mmr2, t2Us, cellW, cellH)

                    local canvas = inSurf.lockCanvas(nil)
                    if canvas then
                        canvas.drawColor(0xFF000000)
                        if bmp1 then canvas.drawBitmap(bmp1, nil, rect1, paint) end
                        if bmp2 then canvas.drawBitmap(bmp2, nil, rect2, paint) end
                        inSurf.unlockCanvasAndPost(canvas)
                    end
                    if bmp1 then pcall(function() bmp1.recycle() end) end
                    if bmp2 then pcall(function() bmp2.recycle() end) end

                    drainV(false, tUs)
                    if fIdx % 4 == 0 then
                        setPct(25 + math.min(68, math.floor((fIdx * 68) / totFrames)))
                    end
                end
                drainV(true, totFrames * stepUs)

                if muxStarted and muxA ~= -1 and aEx then
                    local aBuf = ByteBuffer.allocateDirect(262144)
                    local aInfo = MediaCodec.BufferInfo()
                    local maxUs = totDurMs * 1000
                    while true do
                        aInfo.size = aEx.readSampleData(aBuf, 0)
                        if aInfo.size < 0 then break end
                        local aPts = math.max(0, aEx.getSampleTime())
                        if aPts > maxUs then break end
                        aInfo.offset = 0; aInfo.presentationTimeUs = aPts; aInfo.flags = aEx.getSampleFlags()
                        muxer.writeSampleData(muxA, aBuf, aInfo)
                        aEx.advance()
                    end
                end
            end)

            if mmr1 then pcall(function() mmr1.release() end) end
            if mmr2 then pcall(function() mmr2.release() end) end
            if aEx then pcall(function() aEx.release() end) end
            if aPfd then pcall(function() aPfd.close() end) end
            pcall(function() File(tmpAudM4A).delete() end)
            if muxStarted then pcall(function() muxer.stop() end) end
            pcall(function() muxer.release() end)
            pcall(function() inSurf.release() end)
            pcall(function() vEnc.stop(); vEnc.release() end)
            return totDurMs
        end

        local function renderTranscodedVideos(vList, outMp4Path, qVal, withAudio, sOverride, eOverride)
            local effQ = (qVal and qVal > 0) and qVal or 3
            local outW, outH, bitRate = getQualityDims(effQ, false)
            local fps = 15
            local stepUs = math.floor(1000000 / fps)

            local tmpAudM4A = workDir .. "_tmp_vlist_aud.m4a"
            local hasAud = false
            if withAudio then
                pcall(function()
                    local tmpPcm = workDir .. "_tmp_vlist_aud.pcm"
                    local fos = FileOutputStream(tmpPcm)
                    local pChan = fos.getChannel()
                    local tSr, tCh = 44100, 2
                    local anyOk = false
                    for idx, item in ipairs(vList) do
                        local sm = (idx == 1 and sOverride) and sOverride or 0
                        local em = (idx == 1 and eOverride) and eOverride or 0
                        local sr, ch, okDec = decodeToPcm(item, pChan, sm, em, function(p)
                            setPct(math.floor(p * 0.15 / #vList))
                        end, true)
                        if okDec then
                            anyOk = true
                            if sr and sr > 0 then tSr = sr end
                            if ch and ch > 0 then tCh = ch end
                        end
                    end
                    pChan.force(true); pChan.close(); fos.close()
                    if anyOk and File(tmpPcm).length() > 512 then
                        encodePcmToM4A(tmpPcm, tmpAudM4A, tSr, tCh, function(p) setPct(15 + math.floor(p * 0.10)) end)
                        if File(tmpAudM4A).exists() and File(tmpAudM4A).length() > 512 then hasAud = true end
                    end
                    pcall(function() File(tmpPcm).delete() end)
                end)
            end

            local vFmt = MediaFormat.createVideoFormat("video/avc", outW, outH)
            vFmt.setInteger(MediaFormat.KEY_COLOR_FORMAT, MediaCodecInfo.CodecCapabilities.COLOR_FormatSurface)
            vFmt.setInteger(MediaFormat.KEY_BIT_RATE, bitRate)
            vFmt.setInteger(MediaFormat.KEY_FRAME_RATE, fps)
            vFmt.setInteger(MediaFormat.KEY_I_FRAME_INTERVAL, 1)

            local vEnc = MediaCodec.createEncoderByType("video/avc")
            vEnc.configure(vFmt, nil, nil, MediaCodec.CONFIGURE_FLAG_ENCODE)
            local inSurf = vEnc.createInputSurface()
            vEnc.start()

            local outBufs = nil
            pcall(function() outBufs = vEnc.getOutputBuffers() end)

            local muxer = MediaMuxer(outMp4Path, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
            local muxV = -1
            local muxA = -1
            local muxStarted = false

            local aEx, aPfd = nil, nil
            if hasAud then
                aEx, aPfd = openEx(nil, tmpAudM4A)
                if aEx then
                    for i = 0, aEx.getTrackCount() - 1 do
                        local f = aEx.getTrackFormat(i)
                        local m = f.getString(MediaFormat.KEY_MIME)
                        if m and m:find("audio/") then
                            aEx.selectTrack(i); muxA = muxer.addTrack(f); break
                        end
                    end
                end
            end

            local fullRect = Rect(0, 0, outW, outH)
            local paint = Paint(Paint.FILTER_BITMAP_FLAG)
            local info = MediaCodec.BufferInfo()
            local lastVPts = -1
            local gFrame = 0

            local function drainV(isFinal, targetPts)
                if isFinal then pcall(function() vEnc.signalEndOfInputStream() end) end
                local retries = 0
                while true do
                    local outIdx = vEnc.dequeueOutputBuffer(info, isFinal and 5000 or 1000)
                    if outIdx == MediaCodec.INFO_TRY_AGAIN_LATER then
                        if not isFinal then break end
                        retries = retries + 1
                        if retries > 20 then break end
                    elseif outIdx == MediaCodec.INFO_OUTPUT_BUFFERS_CHANGED then
                        pcall(function() outBufs = vEnc.getOutputBuffers() end)
                    elseif outIdx == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED then
                        muxV = muxer.addTrack(vEnc.getOutputFormat())
                        muxer.start()
                        muxStarted = true
                    elseif outIdx >= 0 then
                        retries = 0
                        local outBuf = nil
                        pcall(function() outBuf = vEnc.getOutputBuffer(outIdx) end)
                        if not outBuf and outBufs then outBuf = outBufs[outIdx + 1] end
                        if math.floor((info.flags or 0) / 2) % 2 == 1 then info.size = 0 end
                        if info.size > 0 and muxStarted and outBuf then
                            local pts = targetPts or info.presentationTimeUs
                            if pts <= lastVPts then pts = lastVPts + stepUs end
                            lastVPts = pts
                            info.presentationTimeUs = pts
                            outBuf.position(info.offset)
                            outBuf.limit(info.offset + info.size)
                            muxer.writeSampleData(muxV, outBuf, info)
                        end
                        vEnc.releaseOutputBuffer(outIdx, false)
                        if math.floor((info.flags or 0) / 4) % 2 == 1 then break end
                    end
                end
            end

            pcall(function()
                local nVids = #vList
                for idx, item in ipairs(vList) do
                    local mmr = openMmr(item.uri, item.path)
                    if mmr then
                        local clipDur = (item.duration and item.duration > 0) and item.duration or 10000
                        local sm = (idx == 1 and sOverride and sOverride > 0) and sOverride or 0
                        local em = (idx == 1 and eOverride and eOverride > sm) and eOverride or clipDur
                        local spanMs = math.max(500, em - sm)
                        local cFrames = math.max(5, math.floor((spanMs * fps) / 1000))

                        for f = 0, cFrames - 1 do
                            local locUs = (sm * 1000) + (f * stepUs)
                            local outPts = gFrame * stepUs
                            gFrame = gFrame + 1

                            local bmp = grabFrame(mmr, locUs, outW, outH)
                            local canvas = inSurf.lockCanvas(nil)
                            if canvas then
                                canvas.drawColor(0xFF000000)
                                if bmp then canvas.drawBitmap(bmp, nil, fullRect, paint) end
                                inSurf.unlockCanvasAndPost(canvas)
                            end
                            if bmp then pcall(function() bmp.recycle() end) end
                            drainV(false, outPts)

                            if f % 4 == 0 then
                                local baseP = 25 + math.floor(((idx - 1) * 68) / nVids)
                                local shareP = math.floor(68 / nVids)
                                setPct(baseP + math.floor((f * shareP) / cFrames))
                            end
                        end
                        pcall(function() mmr.release() end)
                    end
                end
                drainV(true, gFrame * stepUs)

                if muxStarted and muxA ~= -1 and aEx then
                    local aBuf = ByteBuffer.allocateDirect(262144)
                    local aInfo = MediaCodec.BufferInfo()
                    while true do
                        aInfo.size = aEx.readSampleData(aBuf, 0)
                        if aInfo.size < 0 then break end
                        aInfo.offset = 0; aInfo.presentationTimeUs = math.max(0, aEx.getSampleTime()); aInfo.flags = aEx.getSampleFlags()
                        muxer.writeSampleData(muxA, aBuf, aInfo)
                        aEx.advance()
                    end
                end
            end)

            if aEx then pcall(function() aEx.release() end) end
            if aPfd then pcall(function() aPfd.close() end) end
            pcall(function() File(tmpAudM4A).delete() end)
            if muxStarted then pcall(function() muxer.stop() end) end
            pcall(function() muxer.release() end)
            pcall(function() inSurf.release() end)
            pcall(function() vEnc.stop(); vEnc.release() end)
        end

        local outName = ""
        local tempOutPath = ""
        local expectedTotalDur = 0

        local okJob, jobErr = pcall(function()
            setPct(2)

            -- 1. ADD MUSIC TO VOICE (True Smart-Ducked PCM Mixer + AAC M4A Encoder!)
            if pType == "music_to_voice" then
                local vFile = items[1]
                local mFile = items[2]
                expectedTotalDur = vFile.duration or 0
                outName = "VoiceWithMusic_" .. ts .. ".m4a"
                tempOutPath = workDir .. outName

                local vPcmPath = workDir .. "_tmp_v_only.pcm"
                local mPcmPath = workDir .. "_tmp_m_only.pcm"
                local mixPcmPath = workDir .. "_tmp_vm_mixed.pcm"

                local fosV = FileOutputStream(vPcmPath)
                local chVOut = fosV.getChannel()
                local srV, chV = decodeToPcm(vFile, chVOut, 0, 0, function(p) setPct(math.floor(p * 0.28)) end, false)
                chVOut.force(true); chVOut.close(); fosV.close()

                local fosM = FileOutputStream(mPcmPath)
                local chMOut = fosM.getChannel()
                local srM, chM = decodeToPcm(mFile, chMOut, 0, 0, function(p) setPct(28 + math.floor(p * 0.22)) end, false)
                chMOut.force(true); chMOut.close(); fosM.close()

                srV = (srV and srV > 0) and srV or 44100
                chV = (chV and chV > 0) and chV or 2
                srM = (srM and srM > 0) and srM or srV
                chM = (chM and chM > 0) and chM or chV

                -- Mix Voice PCM + Ducked Background Music PCM in 50ms windows
                local vLen = File(vPcmPath).length()
                local mLen = File(mPcmPath).length()
                if mLen > 64 and vLen > 64 then
                    local fisV = FileInputStream(vPcmPath)
                    local fisM = FileInputStream(mPcmPath)
                    local fosMix = FileOutputStream(mixPcmPath)
                    local inCV = fisV.getChannel()
                    local inCM = fisM.getChannel()
                    local outCMix = fosMix.getChannel()

                    local vFrameBytes = 2 * chV
                    local mFrameBytes = 2 * chM
                    local winFramesV = math.max(256, math.floor(srV * 0.05))
                    local winFramesM = math.max(256, math.floor(srM * 0.05))
                    local vBuf = ByteBuffer.allocateDirect(winFramesV * vFrameBytes)
                    local mBuf = ByteBuffer.allocateDirect(winFramesM * mFrameBytes)
                    local outBuf = ByteBuffer.allocateDirect(winFramesV * vFrameBytes)
                    vBuf.order(ByteOrder.LITTLE_ENDIAN)
                    mBuf.order(ByteOrder.LITTLE_ENDIAN)
                    outBuf.order(ByteOrder.LITTLE_ENDIAN)

                    local masterGain = (masterPct or 100) / 100.0
                    local vGain = ((voiceVolPct or 100) / 100.0) * masterGain
                    local highMGain = ((musicHighPct or 75) / 100.0) * masterGain
                    local lowMGain = ((musicDuckPct or 28) / 100.0) * masterGain
                    local curMGain = smartOn and lowMGain or highMGain

                    local totalWins = math.max(1, math.floor(vLen / (winFramesV * vFrameBytes)))
                    local winIdx = 0

                    while true do
                        vBuf.clear()
                        local nrV = inCV.read(vBuf)
                        if nrV <= 0 then break end
                        vBuf.flip()

                        mBuf.clear()
                        local nrM = inCM.read(mBuf)
                        if nrM <= 0 then
                            inCM.position(0)
                            mBuf.clear()
                            nrM = inCM.read(mBuf)
                        end
                        mBuf.flip()

                        local actualFramesV = math.floor(nrV / vFrameBytes)
                        local actualFramesM = math.max(1, math.floor(nrM / mFrameBytes))

                        -- Fast speech energy check on 16 evenly spaced samples in this 50ms window
                        local sumAbs = 0
                        local chkCount = 0
                        local chkStep = math.max(1, math.floor(actualFramesV / 16))
                        for f = 0, actualFramesV - 1, chkStep do
                            local s = vBuf.getShort(f * vFrameBytes)
                            sumAbs = sumAbs + math.abs(s)
                            chkCount = chkCount + 1
                        end
                        local avgAmp = (chkCount > 0) and (sumAbs / chkCount) or 0
                        if smartOn then
                            local targetG = (avgAmp > 320) and lowMGain or highMGain
                            if targetG < curMGain then
                                curMGain = curMGain * 0.35 + targetG * 0.65
                            else
                                curMGain = curMGain * 0.75 + targetG * 0.25
                            end
                        else
                            curMGain = highMGain
                        end

                        outBuf.clear()
                        for f = 0, actualFramesV - 1 do
                            local mIdx = math.floor((f * actualFramesM) / actualFramesV)
                            if mIdx >= actualFramesM then mIdx = actualFramesM - 1 end
                            for c = 0, chV - 1 do
                                local vS = vBuf.getShort(f * vFrameBytes + c * 2)
                                local mCh = (c < chM) and c or 0
                                local mS = (nrM > 0) and mBuf.getShort(mIdx * mFrameBytes + mCh * 2) or 0
                                local mixed = math.floor(vS * vGain + mS * curMGain)
                                if mixed > 32767 then mixed = 32767
                                elseif mixed < -32768 then mixed = -32768 end
                                outBuf.putShort(f * vFrameBytes + c * 2, mixed)
                            end
                        end
                        outBuf.position(0)
                        outBuf.limit(actualFramesV * vFrameBytes)
                        while outBuf.hasRemaining() do
                            outCMix.write(outBuf)
                        end

                        winIdx = winIdx + 1
                        if winIdx % 12 == 0 then
                            setPct(50 + math.min(24, math.floor((winIdx * 24) / totalWins)))
                        end
                    end

                    outCMix.force(true)
                    outCMix.close(); inCV.close(); inCM.close()
                    fosMix.close(); fisV.close(); fisM.close()
                else
                    mixPcmPath = vPcmPath
                end

                encodePcmToM4A(mixPcmPath, tempOutPath, srV, chV, function(p) setPct(74 + math.floor(p * 0.25)) end)
                pcall(function() File(vPcmPath).delete() end)
                pcall(function() File(mPcmPath).delete() end)
                pcall(function() File(mixPcmPath).delete() end)

            elseif pType == "extract" then
                local pFile = items[1]
                expectedTotalDur = pFile.duration or 0
                outName = "ExtractedAudio_" .. ts .. ".m4a"
                tempOutPath = workDir .. outName

                local fastOk = pcall(function()
                    local ex, pfd = openEx(pFile.uri, pFile.path)
                    if not ex then error("Cannot open") end
                    local aTr = -1
                    local fmt = nil
                    for i = 0, ex.getTrackCount() - 1 do
                        local f = ex.getTrackFormat(i)
                        local m = f.getString(MediaFormat.KEY_MIME)
                        if m and m:find("audio/") then
                            if m == "audio/mpeg" or m == "audio/raw" or m == "audio/x-wav" then
                                ex.release()
                                if pfd then pcall(function() pfd.close() end) end
                                error("Needs PCM")
                            end
                            aTr = i; fmt = f; break
                        end
                    end
                    if aTr == -1 then
                        ex.release()
                        if pfd then pcall(function() pfd.close() end) end
                        error("No audio")
                    end
                    ex.selectTrack(aTr)
                    local muxer = MediaMuxer(tempOutPath, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
                    local outTr = muxer.addTrack(fmt)
                    muxer.start()
                    local buf = ByteBuffer.allocateDirect(1024 * 1024)
                    local info = MediaCodec.BufferInfo()
                    local totUs = math.max(1000000, expectedTotalDur * 1000)
                    local pkt = 0
                    while true do
                        info.size = ex.readSampleData(buf, 0)
                        if info.size < 0 then break end
                        info.offset = 0; info.presentationTimeUs = math.max(0, ex.getSampleTime()); info.flags = ex.getSampleFlags()
                        muxer.writeSampleData(outTr, buf, info)
                        pkt = pkt + 1
                        if pkt % 45 == 0 then setPct(math.floor((info.presentationTimeUs * 100) / totUs)) end
                        ex.advance()
                    end
                    muxer.stop(); muxer.release(); ex.release()
                    if pfd then pcall(function() pfd.close() end) end
                end)

                if not fastOk then
                    local tmpPcm = workDir .. "_tmp_ext.pcm"
                    local fos = FileOutputStream(tmpPcm)
                    local pChan = fos.getChannel()
                    local sr, ch = decodeToPcm(pFile, pChan, 0, 0, function(p) setPct(math.floor(p / 2)) end, false)
                    pChan.force(true); pChan.close(); fos.close()
                    encodePcmToM4A(tmpPcm, tempOutPath, sr, ch, function(p) setPct(50 + math.floor(p / 2)) end)
                    pcall(function() File(tmpPcm).delete() end)
                end

            elseif pType == "cut" or pType == "trim" then
                local pFile = items[1]
                local endLimit = (eMs > 0) and eMs or (pFile.duration or 0)
                if endLimit <= sMs and endLimit ~= 0 then error("End Time must be greater than Start Time") end
                if pType == "trim" then
                    expectedTotalDur = math.max(0, endLimit - sMs)
                else
                    expectedTotalDur = math.max(0, (pFile.duration or 0) - (endLimit - sMs))
                end

                local aMime, hasVid = detectMime(pFile)
                if not hasVid and (aMime == "audio/mpeg" or aMime == "audio/raw" or aMime == "audio/x-wav") then
                    outName = (pType == "cut" and "Cut_" or "Trimmed_") .. ts .. ".m4a"
                    tempOutPath = workDir .. outName
                    local tmpPcm = workDir .. "_tmp_ct.pcm"
                    local fos = FileOutputStream(tmpPcm)
                    local pChan = fos.getChannel()
                    local sr, ch = 44100, 2
                    if pType == "trim" then
                        sr, ch = decodeToPcm(pFile, pChan, sMs, endLimit, function(p) setPct(math.floor(p / 2)) end, false)
                    else
                        if sMs > 0 then
                            sr, ch = decodeToPcm(pFile, pChan, 0, sMs, function(p) setPct(math.floor(p / 4)) end, false)
                        end
                        sr, ch = decodeToPcm(pFile, pChan, endLimit, 0, function(p) setPct(25 + math.floor(p / 4)) end, false)
                    end
                    pChan.force(true); pChan.close(); fos.close()
                    encodePcmToM4A(tmpPcm, tempOutPath, sr, ch, function(p) setPct(50 + math.floor(p / 2)) end)
                    pcall(function() File(tmpPcm).delete() end)
                else
                    local ext = hasVid and ".mp4" or ".m4a"
                    outName = (pType == "cut" and "Cut_" or "Trimmed_") .. ts .. ext
                    tempOutPath = workDir .. outName
                    local needQ = (hasVid and qIdx and qIdx > 0)
                    local muxTarget = needQ and (workDir .. "_tmp_ct_raw.mp4") or tempOutPath

                    local ex, pfd = openEx(pFile.uri, pFile.path)
                    if not ex then error("Cannot open file") end
                    local muxer = MediaMuxer(muxTarget, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
                    local muxStarted = false
                    pcall(function()
                        if hasVid then
                            local rot = getVidRot(pFile.uri, pFile.path)
                            if rot and rot ~= 0 then pcall(function() muxer.setOrientationHint(rot) end) end
                        end
                        local trackMap = {}
                        for i = 0, ex.getTrackCount() - 1 do
                            local f = ex.getTrackFormat(i)
                            local m = f.getString(MediaFormat.KEY_MIME)
                            if m and (m:find("video/") or m:find("audio/")) then
                                trackMap[i] = muxer.addTrack(f)
                                ex.selectTrack(i)
                            end
                        end
                        muxer.start()
                        muxStarted = true
                        local buf = ByteBuffer.allocateDirect(1024 * 1024)
                        local info = MediaCodec.BufferInfo()
                        local sUs = sMs * 1000
                        local eUs = (endLimit > 0) and (endLimit * 1000) or (999999999 * 1000)
                        local totUs = math.max(1000000, (pFile.duration or 60000) * 1000)
                        if pType == "trim" then
                            copyRangeAligned(ex, muxer, trackMap, sUs, eUs, 0, buf, info, totUs, function(p)
                                setPct(needQ and math.floor(p / 2) or p)
                            end)
                        else
                            local lastPts = 0
                            if sUs > 0 then
                                lastPts = copyRangeAligned(ex, muxer, trackMap, 0, sUs, 0, buf, info, totUs, function(p)
                                    setPct(math.floor(p / 4))
                                end) + 33000
                            end
                            copyRangeAligned(ex, muxer, trackMap, eUs, 0, lastPts, buf, info, totUs, function(p)
                                setPct(25 + math.floor(p / 4))
                            end)
                        end
                    end)
                    if muxStarted then pcall(function() muxer.stop() end) end
                    pcall(function() muxer.release() end)
                    pcall(function() ex.release() end)
                    if pfd then pcall(function() pfd.close() end) end

                    if needQ then
                        local rawObj = {uri = nil, path = muxTarget, name = outName, duration = expectedTotalDur}
                        renderTranscodedVideos({rawObj}, tempOutPath, qIdx, true, 0, 0)
                        pcall(function() File(muxTarget).delete() end)
                    end
                end

            elseif pType == "silent" then
                local pFile = items[1]
                expectedTotalDur = pFile.duration or 0
                outName = "SilentVideo_" .. ts .. ".mp4"
                tempOutPath = workDir .. outName
                if qIdx and qIdx > 0 then
                    renderTranscodedVideos({pFile}, tempOutPath, qIdx, false, 0, 0)
                else
                    local ex, pfd = openEx(pFile.uri, pFile.path)
                    if not ex then error("Cannot open video file") end
                    local vTr = -1
                    local fmt = nil
                    for i = 0, ex.getTrackCount() - 1 do
                        local f = ex.getTrackFormat(i)
                        local m = f.getString(MediaFormat.KEY_MIME)
                        if m and m:find("video/") then vTr = i; fmt = f; break end
                    end
                    if vTr == -1 then
                        ex.release()
                        if pfd then pcall(function() pfd.close() end) end
                        error("No video track found")
                    end
                    ex.selectTrack(vTr)
                    local muxer = MediaMuxer(tempOutPath, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
                    local muxStarted = false
                    pcall(function()
                        local rot = getVidRot(pFile.uri, pFile.path)
                        if rot and rot ~= 0 then pcall(function() muxer.setOrientationHint(rot) end) end
                        local outTr = muxer.addTrack(fmt)
                        muxer.start()
                        muxStarted = true
                        local buf = ByteBuffer.allocateDirect(1024 * 1024)
                        local info = MediaCodec.BufferInfo()
                        local totUs = math.max(1000000, expectedTotalDur * 1000)
                        local pkt = 0
                        while true do
                            info.size = ex.readSampleData(buf, 0)
                            if info.size < 0 then break end
                            info.offset = 0; info.presentationTimeUs = math.max(0, ex.getSampleTime()); info.flags = ex.getSampleFlags()
                            muxer.writeSampleData(outTr, buf, info)
                            pkt = pkt + 1
                            if pkt % 45 == 0 then setPct(math.floor((info.presentationTimeUs * 100) / totUs)) end
                            ex.advance()
                        end
                    end)
                    if muxStarted then pcall(function() muxer.stop() end) end
                    pcall(function() muxer.release() end)
                    pcall(function() ex.release() end)
                    if pfd then pcall(function() pfd.close() end) end
                end

            elseif pType == "merge" then
                local totalFiles = #items
                for _, it in ipairs(items) do expectedTotalDur = expectedTotalDur + (it.duration or 0) end
                local first = items[1]
                local _, hasVid = detectMime(first)

                if not hasVid then
                    outName = "Merged_" .. tostring(totalFiles) .. "Audios_" .. ts .. ".m4a"
                    tempOutPath = workDir .. outName
                    local combinedPcm = workDir .. "_tmp_merged_all.pcm"
                    local fos = FileOutputStream(combinedPcm)
                    local pChan = fos.getChannel()
                    local tSr, tCh = 44100, 2
                    local validCount = 0

                    for idx, item in ipairs(items) do
                        local basePct = math.floor(((idx - 1) * 65) / totalFiles)
                        local sharePct = math.floor(65 / totalFiles)
                        setPct(basePct)
                        local sr, ch, okDec = decodeToPcm(item, pChan, 0, 0, function(fPct)
                            setPct(basePct + math.floor((fPct * sharePct) / 100))
                        end, true)
                        if okDec then
                            validCount = validCount + 1
                            if validCount == 1 then
                                if sr and sr > 0 then tSr = sr end
                                if ch and ch > 0 then tCh = ch end
                            end
                        end
                    end

                    pcall(function() pChan.force(true); pChan.close(); fos.flush(); fos.close() end)
                    if validCount == 0 or File(combinedPcm).length() < 512 then
                        pcall(function() File(combinedPcm).delete() end)
                        error("Selected audio files are empty or corrupted.")
                    end
                    setPct(65)
                    encodePcmToM4A(combinedPcm, tempOutPath, tSr, tCh, function(ePct)
                        setPct(65 + math.floor((ePct * 34) / 100))
                    end)
                    pcall(function() File(combinedPcm).delete() end)
                else
                    outName = "Merged_" .. tostring(totalFiles) .. "Videos_" .. ts .. ".mp4"
                    tempOutPath = workDir .. outName

                    local canFast = (qIdx == 0)
                    local refW, refH, refVM, refAM = nil, nil, nil, nil
                    if canFast then
                        for _, it in ipairs(items) do
                            local exC, pfdC = openEx(it.uri, it.path)
                            if exC then
                                local vw, vh, vm, am = 0, 0, "", ""
                                for t = 0, exC.getTrackCount() - 1 do
                                    local f = exC.getTrackFormat(t)
                                    local m = f.getString(MediaFormat.KEY_MIME)
                                    if m and m:find("video/") and vm == "" then
                                        vm = m
                                        vw = f.containsKey(MediaFormat.KEY_WIDTH) and f.getInteger(MediaFormat.KEY_WIDTH) or 0
                                        vh = f.containsKey(MediaFormat.KEY_HEIGHT) and f.getInteger(MediaFormat.KEY_HEIGHT) or 0
                                    elseif m and m:find("audio/") and am == "" then
                                        am = m
                                    end
                                end
                                pcall(function() exC.release() end)
                                if pfdC then pcall(function() pfdC.close() end) end
                                if not refW then refW, refH, refVM, refAM = vw, vh, vm, am
                                elseif vw ~= refW or vh ~= refH or vm ~= refVM or am ~= refAM then canFast = false end
                                if am == "audio/mpeg" or am == "audio/raw" or am == "audio/x-wav" then canFast = false end
                            else
                                if pfdC then pcall(function() pfdC.close() end) end
                                canFast = false
                            end
                        end
                    end

                    local fastDone = false
                    if canFast then
                        pcall(function()
                            local exF, pfdF = openEx(first.uri, first.path)
                            if not exF then error("Cannot open first video") end
                            local muxer = MediaMuxer(tempOutPath, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
                            local muxStarted = false
                            local rot = getVidRot(first.uri, first.path)
                            if rot and rot ~= 0 then pcall(function() muxer.setOrientationHint(rot) end) end
                            local outV, outA = -1, -1
                            for i = 0, exF.getTrackCount() - 1 do
                                local f = exF.getTrackFormat(i)
                                local m = f.getString(MediaFormat.KEY_MIME)
                                if m and m:find("video/") and outV == -1 then outV = muxer.addTrack(f)
                                elseif m and m:find("audio/") and outA == -1 then outA = muxer.addTrack(f) end
                            end
                            pcall(function() exF.release() end)
                            if pfdF then pcall(function() pfdF.close() end) end

                            muxer.start()
                            muxStarted = true
                            local buf = ByteBuffer.allocateDirect(2 * 1024 * 1024)
                            local info = MediaCodec.BufferInfo()
                            local baseV, baseA = 0, 0
                            local lastV, lastA = -1, -1

                            for idx, it in ipairs(items) do
                                local basePct = math.floor(((idx - 1) * 100) / totalFiles)
                                local sharePct = math.floor(100 / totalFiles)
                                setPct(basePct)
                                local ex, pfd = openEx(it.uri, it.path)
                                if ex then
                                    local vIn, aIn = -1, -1
                                    for t = 0, ex.getTrackCount() - 1 do
                                        local m = ex.getTrackFormat(t).getString(MediaFormat.KEY_MIME)
                                        if m and m:find("video/") and outV ~= -1 and vIn == -1 then vIn = t; ex.selectTrack(t)
                                        elseif m and m:find("audio/") and outA ~= -1 and aIn == -1 then aIn = t; ex.selectTrack(t) end
                                    end
                                    ex.seekTo(0, MediaExtractor.SEEK_TO_CLOSEST_SYNC)
                                    local fV, fA = nil, nil
                                    local maxV, maxA = baseV, baseA
                                    local cDurUs = math.max(1000000, (it.duration or 60000) * 1000)
                                    local pkt = 0
                                    while true do
                                        info.size = ex.readSampleData(buf, 0)
                                        if info.size < 0 then break end
                                        local tr = ex.getSampleTrackIndex()
                                        local rawPts = math.max(0, ex.getSampleTime())
                                        info.offset = 0; info.flags = ex.getSampleFlags()
                                        if tr == vIn and outV ~= -1 then
                                            if not fV then fV = rawPts end
                                            local rel = math.max(0, rawPts - fV)
                                            local nPts = baseV + rel
                                            if nPts <= lastV then nPts = lastV + 33333 end
                                            lastV = nPts
                                            if nPts > maxV then maxV = nPts end
                                            info.presentationTimeUs = nPts
                                            pcall(function() muxer.writeSampleData(outV, buf, info) end)
                                            pkt = pkt + 1
                                            if pkt % 45 == 0 then
                                                setPct(basePct + math.floor((math.min(99, math.floor((rel * 100) / cDurUs)) * sharePct) / 100))
                                            end
                                        elseif tr == aIn and outA ~= -1 then
                                            if not fA then fA = rawPts end
                                            local nPts = baseA + math.max(0, rawPts - fA)
                                            if nPts <= lastA then nPts = lastA + 23219 end
                                            lastA = nPts
                                            if nPts > maxA then maxA = nPts end
                                            info.presentationTimeUs = nPts
                                            pcall(function() muxer.writeSampleData(outA, buf, info) end)
                                        end
                                        ex.advance()
                                    end
                                    local endClip = math.max(maxV, maxA) + 33333
                                    baseV = endClip; baseA = endClip
                                    pcall(function() ex.release() end)
                                end
                                if pfd then pcall(function() pfd.close() end) end
                            end
                            if muxStarted then pcall(function() muxer.stop() end) end
                            pcall(function() muxer.release() end)
                            if File(tempOutPath).exists() and File(tempOutPath).length() > 4096 then fastDone = true end
                        end)
                    end

                    if not fastDone then
                        renderTranscodedVideos(items, tempOutPath, qIdx, true, 0, 0)
                    end
                end

            elseif pType == "change_audio" then
                local vFile = items[1]
                local aFile = items[2]
                expectedTotalDur = vFile.duration or 0
                outName = "AudioChanged_" .. ts .. ".mp4"
                tempOutPath = workDir .. outName

                local secMime = detectMime(aFile)
                local wUri = aFile.uri
                local wPath = aFile.path
                local tmpSecM4A = nil
                if secMime == "audio/mpeg" or secMime == "audio/raw" or secMime == "audio/x-wav" then
                    local tmpPcm = workDir .. "_tmp_ca.pcm"
                    tmpSecM4A = workDir .. "_tmp_ca.m4a"
                    local fos = FileOutputStream(tmpPcm)
                    local pChan = fos.getChannel()
                    local sr, ch = decodeToPcm(aFile, pChan, 0, 0, function(p) setPct(math.floor(p / 3)) end, false)
                    pChan.force(true); pChan.close(); fos.close()
                    encodePcmToM4A(tmpPcm, tmpSecM4A, sr, ch, function(p) setPct(33 + math.floor(p / 3)) end)
                    pcall(function() File(tmpPcm).delete() end)
                    wUri = nil; wPath = tmpSecM4A
                end

                local vEx, vPfd = openEx(vFile.uri, vFile.path)
                local aEx, aPfd = openEx(wUri, wPath)
                if not vEx or not aEx then
                    if vEx then pcall(function() vEx.release() end) end
                    if aEx then pcall(function() aEx.release() end) end
                    if vPfd then pcall(function() vPfd.close() end) end
                    if aPfd then pcall(function() aPfd.close() end) end
                    error("Cannot open Video or Audio file")
                end

                local muxer = MediaMuxer(tempOutPath, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
                local muxStarted = false
                pcall(function()
                    local rot = getVidRot(vFile.uri, vFile.path)
                    if rot and rot ~= 0 then pcall(function() muxer.setOrientationHint(rot) end) end
                    local vOut, aOut = -1, -1
                    for i = 0, vEx.getTrackCount() - 1 do
                        local f = vEx.getTrackFormat(i)
                        if f.getString(MediaFormat.KEY_MIME):find("video/") then
                            vEx.selectTrack(i); vOut = muxer.addTrack(f); break
                        end
                    end
                    for i = 0, aEx.getTrackCount() - 1 do
                        local f = aEx.getTrackFormat(i)
                        if f.getString(MediaFormat.KEY_MIME):find("audio/") then
                            aEx.selectTrack(i); aOut = muxer.addTrack(f); break
                        end
                    end
                    muxer.start()
                    muxStarted = true
                    local buf = ByteBuffer.allocateDirect(1024 * 1024)
                    local info = MediaCodec.BufferInfo()
                    local vDone, aDone = false, false
                    local totUs = math.max(1000000, expectedTotalDur * 1000)
                    local pkt = 0
                    while not vDone or not aDone do
                        local vPts = (not vDone) and vEx.getSampleTime() or -1
                        if vPts < 0 then vDone = true end
                        local aPts = (not aDone) and aEx.getSampleTime() or -1
                        if aPts < 0 then aDone = true end
                        if vDone and aDone then break end
                        if not vDone and (aDone or vPts <= aPts) then
                            info.size = vEx.readSampleData(buf, 0)
                            if info.size >= 0 then
                                info.offset = 0; info.presentationTimeUs = vPts; info.flags = vEx.getSampleFlags()
                                muxer.writeSampleData(vOut, buf, info)
                                pkt = pkt + 1
                                if pkt % 45 == 0 then setPct(66 + math.min(33, math.floor((vPts * 33) / totUs))) end
                                vEx.advance()
                            else vDone = true end
                        elseif not aDone then
                            info.size = aEx.readSampleData(buf, 0)
                            if info.size >= 0 then
                                info.offset = 0; info.presentationTimeUs = aPts; info.flags = aEx.getSampleFlags()
                                muxer.writeSampleData(aOut, buf, info)
                                aEx.advance()
                            else aDone = true end
                        end
                    end
                end)
                if muxStarted then pcall(function() muxer.stop() end) end
                pcall(function() muxer.release() end)
                pcall(function() vEx.release() end)
                pcall(function() aEx.release() end)
                if vPfd then pcall(function() vPfd.close() end) end
                if aPfd then pcall(function() aPfd.close() end) end
                if tmpSecM4A then pcall(function() File(tmpSecM4A).delete() end) end

            elseif pType == "split_video" then
                local v1 = items[1]
                local v2 = items[2]
                outName = "SplitVideo_" .. ts .. ".mp4"
                tempOutPath = workDir .. outName
                expectedTotalDur = renderSplitVideo(v1, v2, tempOutPath, layoutMode, qIdx)

            elseif pType == "noise_remover" then
                local pFile = items[1]
                expectedTotalDur = pFile.duration or 0
                local _, hasVid = detectMime(pFile)
                local rawPcm = workDir .. "_tmp_nr_raw.pcm"
                local cleanPcm = workDir .. "_tmp_nr_clean.pcm"

                local fos = FileOutputStream(rawPcm)
                local chOut = fos.getChannel()
                local sr, ch = decodeToPcm(pFile, chOut, 0, 0, function(p) setPct(math.floor(p * 0.30)) end, false)
                chOut.force(true); chOut.close(); fos.close()

                processPcmDSP(rawPcm, cleanPcm, sr, ch, {
                    cleanNoise = true,
                    noiseStrengthPct = noiseStrengthPct,
                    addEcho = false,
                    gainPct = noiseVoiceBoost
                }, function(p) setPct(30 + math.floor(p * 0.35)) end)

                if hasVid then
                    outName = "NoiseCleanedVideo_" .. ts .. ".mp4"
                    tempOutPath = workDir .. outName
                    local tmpCleanM4A = workDir .. "_tmp_nr_aud.m4a"
                    encodePcmToM4A(cleanPcm, tmpCleanM4A, sr, ch, function(p) setPct(65 + math.floor(p * 0.18)) end, 192000)
                    remuxVideoWithNewAudio(pFile, tmpCleanM4A, tempOutPath, function(p) setPct(83 + math.floor(p * 0.16)) end)
                    pcall(function() File(tmpCleanM4A).delete() end)
                else
                    outName = "NoiseCleanedAudio_" .. ts .. ".m4a"
                    tempOutPath = workDir .. outName
                    encodePcmToM4A(cleanPcm, tempOutPath, sr, ch, function(p) setPct(65 + math.floor(p * 0.34)) end, 192000)
                end
                pcall(function() File(rawPcm).delete() end)
                pcall(function() File(cleanPcm).delete() end)

            elseif pType == "echo_studio" then
                local pFile = items[1]
                expectedTotalDur = pFile.duration or 0
                local _, hasVid = detectMime(pFile)
                local rawPcm = workDir .. "_tmp_echo_raw.pcm"
                local echoPcm = workDir .. "_tmp_echo_out.pcm"

                local fos = FileOutputStream(rawPcm)
                local chOut = fos.getChannel()
                local sr, ch = decodeToPcm(pFile, chOut, 0, 0, function(p) setPct(math.floor(p * 0.30)) end, false)
                chOut.force(true); chOut.close(); fos.close()

                processPcmDSP(rawPcm, echoPcm, sr, ch, {
                    cleanNoise = false,
                    addEcho = true,
                    echoDelayMs = echoDelayMs,
                    echoDecayPct = echoDecayPct,
                    gainPct = echoVoiceBoostPct
                }, function(p) setPct(30 + math.floor(p * 0.35)) end)

                if hasVid then
                    outName = "EchoStudioVideo_" .. ts .. ".mp4"
                    tempOutPath = workDir .. outName
                    local tmpEchoM4A = workDir .. "_tmp_echo_aud.m4a"
                    encodePcmToM4A(echoPcm, tmpEchoM4A, sr, ch, function(p) setPct(65 + math.floor(p * 0.18)) end, 192000)
                    remuxVideoWithNewAudio(pFile, tmpEchoM4A, tempOutPath, function(p) setPct(83 + math.floor(p * 0.16)) end)
                    pcall(function() File(tmpEchoM4A).delete() end)
                else
                    outName = "EchoStudioAudio_" .. ts .. ".m4a"
                    tempOutPath = workDir .. outName
                    encodePcmToM4A(echoPcm, tempOutPath, sr, ch, function(p) setPct(65 + math.floor(p * 0.34)) end, 192000)
                end
                pcall(function() File(rawPcm).delete() end)
                pcall(function() File(echoPcm).delete() end)

            elseif pType == "volume_booster" then
                local pFile = items[1]
                expectedTotalDur = pFile.duration or 0
                local _, hasVid = detectMime(pFile)
                local rawPcm = workDir .. "_tmp_vb_raw.pcm"
                local boostPcm = workDir .. "_tmp_vb_out.pcm"

                local fos = FileOutputStream(rawPcm)
                local chOut = fos.getChannel()
                local sr, ch = decodeToPcm(pFile, chOut, 0, 0, function(p) setPct(math.floor(p * 0.32)) end, false)
                chOut.force(true); chOut.close(); fos.close()

                processPcmDSP(rawPcm, boostPcm, sr, ch, {
                    cleanNoise = false,
                    addEcho = false,
                    gainPct = volBoosterPct
                }, function(p) setPct(32 + math.floor(p * 0.33)) end)

                if hasVid then
                    outName = "BoostedVideo_" .. tostring(volBoosterPct) .. "pct_" .. ts .. ".mp4"
                    tempOutPath = workDir .. outName
                    local tmpBoostM4A = workDir .. "_tmp_vb_aud.m4a"
                    encodePcmToM4A(boostPcm, tmpBoostM4A, sr, ch, function(p) setPct(65 + math.floor(p * 0.18)) end, 192000)
                    remuxVideoWithNewAudio(pFile, tmpBoostM4A, tempOutPath, function(p) setPct(83 + math.floor(p * 0.16)) end)
                    pcall(function() File(tmpBoostM4A).delete() end)
                else
                    outName = "BoostedAudio_" .. tostring(volBoosterPct) .. "pct_" .. ts .. ".m4a"
                    tempOutPath = workDir .. outName
                    encodePcmToM4A(boostPcm, tempOutPath, sr, ch, function(p) setPct(65 + math.floor(p * 0.34)) end, 192000)
                end
                pcall(function() File(rawPcm).delete() end)
                pcall(function() File(boostPcm).delete() end)

            elseif pType == "converter" then
                local pFile = items[1]
                expectedTotalDur = pFile.duration or 0
                local _, hasVid = detectMime(pFile)
                local brTable = { [0] = 320000, [1] = 256000, [2] = 192000, [3] = 128000, [4] = 64000 }
                local targetBr = brTable[convBrIdx] or 192000
                local extTable = { [0] = ".m4a", [1] = ".mp3", [2] = ".wav", [3] = ".aac", [4] = ".mp4" }
                local targetExt = extTable[convFmtIdx] or ".m4a"

                if convFmtIdx == 4 then
                    -- Convert to MP4 Video (either transcode Video quality OR convert MP3/Audio to MP4 Video!)
                    outName = "ConvertedVideo_" .. ts .. ".mp4"
                    tempOutPath = workDir .. outName
                    if hasVid then
                        renderVideoFromSegments({pFile}, tempOutPath, (qIdx > 0) and qIdx or 3, 0, 0)
                    else
                        local rawPcm = workDir .. "_tmp_conv_a2v.pcm"
                        local tmpM4A = workDir .. "_tmp_conv_a2v.m4a"
                        local fos = FileOutputStream(rawPcm)
                        local chOut = fos.getChannel()
                        local sr, ch = decodeToPcm(pFile, chOut, 0, 0, function(p) setPct(math.floor(p * 0.25)) end, false)
                        chOut.force(true); chOut.close(); fos.close()
                        encodePcmToM4A(rawPcm, tmpM4A, sr, ch, function(p) setPct(25 + math.floor(p * 0.15)) end, targetBr)
                        renderAudioToMp4Video(pFile, tmpM4A, tempOutPath, qIdx, function(p) setPct(40 + math.floor(p * 0.58)) end)
                        pcall(function() File(rawPcm).delete() end)
                        pcall(function() File(tmpM4A).delete() end)
                    end
                else
                    outName = "ConvertedAudio_" .. ts .. targetExt
                    tempOutPath = workDir .. outName
                    local rawPcm = workDir .. "_tmp_conv_aud.pcm"
                    local fos = FileOutputStream(rawPcm)
                    local chOut = fos.getChannel()
                    local sr, ch = decodeToPcm(pFile, chOut, 0, 0, function(p) setPct(math.floor(p * 0.45)) end, false)
                    chOut.force(true); chOut.close(); fos.close()

                    if convFmtIdx == 2 then
                        encodePcmToWav(rawPcm, tempOutPath, sr, ch, function(p) setPct(45 + math.floor(p * 0.54)) end)
                    else
                        encodePcmToM4A(rawPcm, tempOutPath, sr, ch, function(p) setPct(45 + math.floor(p * 0.54)) end, targetBr)
                    end
                    pcall(function() File(rawPcm).delete() end)
                end

            elseif pType == "voice_recorder" then
                local vFile = items[1]
                local mFile = items[2]
                expectedTotalDur = vFile.duration or 0
                outName = "StudioRecording_" .. ts .. ".m4a"
                tempOutPath = workDir .. outName

                local doClean = (math.floor(recFlags / 1) % 2) == 1
                local doEcho  = (math.floor(recFlags / 2) % 2) == 1
                local rawVPcm = workDir .. "_tmp_rec_v_raw.pcm"
                local dspVPcm = workDir .. "_tmp_rec_v_dsp.pcm"

                local fosV = FileOutputStream(rawVPcm)
                local chVOut = fosV.getChannel()
                local srV, chV = decodeToPcm(vFile, chVOut, 0, 0, function(p) setPct(math.floor(p * 0.25)) end, false)
                chVOut.force(true); chVOut.close(); fosV.close()

                processPcmDSP(rawVPcm, dspVPcm, srV, chV, {
                    cleanNoise = doClean,
                    noiseStrengthPct = noiseStrengthPct,
                    addEcho = doEcho,
                    echoDelayMs = echoDelayMs,
                    echoDecayPct = echoDecayPct,
                    gainPct = recVoiceBoost
                }, function(p) setPct(25 + math.floor(p * 0.25)) end)

                local finalPcmToEncode = dspVPcm
                local mPcmPath = workDir .. "_tmp_rec_m.pcm"
                local mixPcmPath = workDir .. "_tmp_rec_mix.pcm"

                if mFile then
                    local fosM = FileOutputStream(mPcmPath)
                    local chMOut = fosM.getChannel()
                    local srM, chM = decodeToPcm(mFile, chMOut, 0, 0, function(p) setPct(50 + math.floor(p * 0.15)) end, true)
                    chMOut.force(true); chMOut.close(); fosM.close()

                    local vLen = File(dspVPcm).length()
                    local mLen = File(mPcmPath).length()
                    if mLen > 64 and vLen > 64 then
                        srM = (srM and srM > 0) and srM or srV
                        chM = (chM and chM > 0) and chM or chV
                        local fisV = FileInputStream(dspVPcm)
                        local fisM = FileInputStream(mPcmPath)
                        local fosMix = FileOutputStream(mixPcmPath)
                        local inCV = fisV.getChannel()
                        local inCM = fisM.getChannel()
                        local outCMix = fosMix.getChannel()

                        local vFrameBytes = 2 * chV
                        local mFrameBytes = 2 * chM
                        local winFramesV = math.max(256, math.floor(srV * 0.05))
                        local winFramesM = math.max(256, math.floor(srM * 0.05))
                        local vBuf = ByteBuffer.allocateDirect(winFramesV * vFrameBytes)
                        local mBuf = ByteBuffer.allocateDirect(winFramesM * mFrameBytes)
                        local outBuf = ByteBuffer.allocateDirect(winFramesV * vFrameBytes)
                        vBuf.order(ByteOrder.LITTLE_ENDIAN)
                        mBuf.order(ByteOrder.LITTLE_ENDIAN)
                        outBuf.order(ByteOrder.LITTLE_ENDIAN)

                        local highMGain = (musicHighPct or 75) / 100.0
                        local lowMGain = (musicDuckPct or 28) / 100.0
                        local curMGain = lowMGain

                        while true do
                            vBuf.clear()
                            local nrV = inCV.read(vBuf)
                            if nrV <= 0 then break end
                            vBuf.flip()

                            mBuf.clear()
                            local nrM = inCM.read(mBuf)
                            if nrM <= 0 then
                                inCM.position(0)
                                mBuf.clear()
                                nrM = inCM.read(mBuf)
                            end
                            mBuf.flip()

                            local actualFramesV = math.floor(nrV / vFrameBytes)
                            local actualFramesM = math.max(1, math.floor(nrM / mFrameBytes))

                            local sumAbs = 0
                            local chkCount = 0
                            local chkStep = math.max(1, math.floor(actualFramesV / 16))
                            for f = 0, actualFramesV - 1, chkStep do
                                sumAbs = sumAbs + math.abs(vBuf.getShort(f * vFrameBytes))
                                chkCount = chkCount + 1
                            end
                            local avgAmp = (chkCount > 0) and (sumAbs / chkCount) or 0
                            local targetG = (avgAmp > 320) and lowMGain or highMGain
                            if targetG < curMGain then
                                curMGain = curMGain * 0.35 + targetG * 0.65
                            else
                                curMGain = curMGain * 0.75 + targetG * 0.25
                            end

                            outBuf.clear()
                            for f = 0, actualFramesV - 1 do
                                local mIdx = math.floor((f * actualFramesM) / actualFramesV)
                                if mIdx >= actualFramesM then mIdx = actualFramesM - 1 end
                                for c = 0, chV - 1 do
                                    local vS = vBuf.getShort(f * vFrameBytes + c * 2)
                                    local mCh = (c < chM) and c or 0
                                    local mS = (nrM > 0) and mBuf.getShort(mIdx * mFrameBytes + mCh * 2) or 0
                                    local mixed = math.floor(vS + mS * curMGain)
                                    if mixed > 32767 then mixed = 32767
                                    elseif mixed < -32768 then mixed = -32768 end
                                    outBuf.putShort(f * vFrameBytes + c * 2, mixed)
                                end
                            end
                            outBuf.position(0)
                            outBuf.limit(actualFramesV * vFrameBytes)
                            while outBuf.hasRemaining() do outCMix.write(outBuf) end
                        end
                        outCMix.force(true)
                        outCMix.close(); inCV.close(); inCM.close()
                        fosMix.close(); fisV.close(); fisM.close()
                        finalPcmToEncode = mixPcmPath
                    end
                end

                encodePcmToM4A(finalPcmToEncode, tempOutPath, srV, chV, function(p) setPct(70 + math.floor(p * 0.29)) end, 192000)
                pcall(function() File(rawVPcm).delete() end)
                pcall(function() File(dspVPcm).delete() end)
                pcall(function() File(mPcmPath).delete() end)
                pcall(function() File(mixPcmPath).delete() end)
            end

            pcall(function() progressBarWidget.setProgress(100) end)
        end)

        if not okJob then
            return "ERR\t" .. tostring(jobErr)
        end
        return "OK\t" .. tostring(tempOutPath) .. "\t" .. tostring(outName) .. "\t" .. tostring(math.floor(expectedTotalDur or 0))
    end, ctx, horizBar, payloadStr, function(resStr)
        isJobRunning = false
        if uiPollRunnable then uiHandler.removeCallbacks(uiPollRunnable) end
        pcall(function() progDlg.dismiss() end)
        vibrate(35)

        local rParts = {}
        local st = 1
        local s = tostring(resStr or "")
        while true do
            local pos = s:find("\t", st, true)
            if not pos then
                table.insert(rParts, s:sub(st))
                break
            end
            table.insert(rParts, s:sub(st, pos - 1))
            st = pos + 1
        end

        if rParts[1] == "OK" then
            local tempOutPath = rParts[2] or ""
            local outName = rParts[3] or "Output.m4a"
            local expectedTotalDur = tonumber(rParts[4]) or 0

            if isHiddenInBackground then
                local finalDest = getDownloadPath(outName)
                pcall(function()
                    copyFileReliable(tempOutPath, finalDest)
                    scanMediaFile(finalDest)
                end)
                prefs.edit()
                    .putString("bg_ready_path", tempOutPath)
                    .putString("bg_ready_name", outName)
                    .putLong("bg_ready_dur", expectedTotalDur)
                    .commit()
                sendCompletionNotification("Process Completed!", "Your file " .. tostring(outName) .. " is ready.")
                pcall(function()
                    local reopenIntent = Intent(ctx, ctx.getClass())
                    reopenIntent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
                    reopenIntent.addFlags(Intent.FLAG_ACTIVITY_REORDER_TO_FRONT)
                    reopenIntent.addFlags(Intent.FLAG_ACTIVITY_SINGLE_TOP)
                    ctx.startActivity(reopenIntent)
                end)
                showOutputReadyDialog(tempOutPath, outName, false, expectedTotalDur)
            else
                showOutputReadyDialog(tempOutPath, outName, false, expectedTotalDur)
            end
        else
            local errMsg = rParts[2] or "Processing failed"
            speak("Error: " .. tostring(errMsg))
            Toast.makeText(ctx, tostring(errMsg), Toast.LENGTH_LONG).show()
        end
    end)
end

-- ================= ABOUT POPUP (Pro Media Studio Theme + Complete A-to-Z Feature Guide + WhatsApp Feedback) =================
local function showAbout()
    vibrate(35)

    local function card(title, body, borderHex)
        return {
            LinearLayout, orientation = "vertical", layout_width = "fill", padding = "16dp",
            background = brd(0xFF1F1934, borderHex or 0xFFA855F7, 18, 3),
            {TextView, text = title, textSize = "14sp", textColor = STUDIO_WARM_GOLD, typeface = Typeface.DEFAULT_BOLD, focusable = true},
            {View, layout_width = "fill", layout_height = "10dp"},
            {TextView, text = body, textSize = "12sp", textColor = STUDIO_PURE_TEXT, focusable = true}
        }
    end

    local aboutLayout = {
        LinearLayout, orientation = "vertical", layout_width = "fill", padding = "20dp",
        background = gradBrd(0xFF12101B, 0xFF1E1B2E, STUDIO_NEON_CYAN, 28, 3),
        {
            LinearLayout, orientation = "vertical", layout_width = "fill", padding = "16dp",
            background = gradBrd(0xFF3B0764, 0xFF1E1B4B, STUDIO_WARM_GOLD, 20, 3),
            {TextView, text = "SMART MEDIA STUDIO PRO", textSize = "20sp", textColor = STUDIO_NEON_CYAN, typeface = Typeface.DEFAULT_BOLD, gravity = "center", focusable = true},
            {View, layout_width = "fill", layout_height = "6dp"},
            {TextView, text = "Developer Name: Abdul Rehman", textSize = "13sp", textColor = STUDIO_WARM_GOLD, typeface = Typeface.DEFAULT_BOLD, gravity = "center", singleLine = true, focusable = true}
        },
        {View, layout_width = "fill", layout_height = "16dp"},
        {
            ScrollView, layout_width = "fill", layout_height = "430dp",
            {
                LinearLayout, orientation = "vertical", layout_width = "fill", paddingRight = "4dp",
                card("TOOL OVERVIEW", "Smart Media Studio Pro is a complete Android Audio and Video editing studio. Every tool opens in its own custom-colored studio window with live preview, background processing (Hide), and zero-crash reliability.", 0xFF22D3EE),
                {View, layout_width = "fill", layout_height = "12dp"},
                card("ADD MUSIC TO VOICE", "Mixes background music with any recorded or selected voice file.\n\nWhen Smart Filtering is ON, the background music automatically lowers while speaking and rises during silent pauses, with 4 independent volume sliders.", 0xFFF472B6),
                {View, layout_width = "fill", layout_height = "12dp"},
                card("REMOVE NOISE", "Removes background hiss, fan noise, wind, and hum from any existing Audio or Video file, or lets you record live voice directly from the microphone and clean its background noise automatically.\n\nIncludes adjustable Noise Reduction Strength (10% to 100%) and Voice Clarity Boost (100% to 200%).", 0xFF38BDF8),
                {View, layout_width = "fill", layout_height = "12dp"},
                card("CHANGE AUDIO & CONVERT FORMAT", "Change Audio replaces a video's original audio track with a new audio file.\n\nConvert Format & Quality converts between MP3, M4A, WAV (Lossless), AAC, and MP4 Video, and lets you change Audio Bitrate (64 kbps to 320 kbps Ultra HD) or Video Quality (360p to 4K/8K). You can even convert MP3 audio into an MP4 video or MP4 video into MP3/M4A/WAV!", 0xFF818CF8),
                {View, layout_width = "fill", layout_height = "12dp"},
                card("CUT & TRIM", "Cut removes the selected middle section between Start Time and End Time and joins the remaining parts together.\n\nTrim keeps only the selected section between Start Time and End Time and removes the rest.", 0xFF2DD4BF),
                {View, layout_width = "fill", layout_height = "12dp"},
                card("ECHO EFFECTS & EXTRACT AUDIO", "Echo & Voice Effects applies professional studio Echo and Hall Reverb (Madinah Hall, Studio Vocal Reverb, Deep Mosque Echo, Double Chorus, or Custom Delay & Decay sliders) to any Audio, Video, or live Mic recording.\n\nExtract Audio saves the audio track from any video as a clean audio file.", 0xFF34D399),
                {View, layout_width = "fill", layout_height = "12dp"},
                card("MERGE, SILENT VIDEO & SPLIT VIDEO", "Merge combines 2, 3, 4, or unlimited Audio or Video files into one continuous file.\n\nSilent Video removes the audio track from any video.\n\nSplit Video combines 2 videos onto 1 screen playing simultaneously (Top & Bottom or Left & Right).", 0xFFC084FC),
                {View, layout_width = "fill", layout_height = "12dp"},
                card("RECORD VOICE & VOLUME BOOSTER", "Voice Recorder Studio lets you record HD voice from the microphone with a live timer, optional Background Music mixing, automatic Background Noise Removal, and optional Studio Echo.\n\nVolume Booster amplifies quiet Audio or Video files up to 300% (or lowers loud files down to 20%) with an anti-distortion soft-knee limiter.", 0xFFFB923C),
                {View, layout_width = "fill", layout_height = "12dp"},
                card("HIDE AND BACKGROUND PROCESSING", "During processing, tap Hide to return to your phone Home Screen while processing continues in the background. When completed, you receive a notification and the File Ready window opens automatically.", 0xFF8B5CF6),
                {View, layout_width = "fill", layout_height = "12dp"},
                card("CONTACT AND FEEDBACK", "Feedback, suggestions, and bug reports are welcome. Tap the WhatsApp button below to send feedback directly to Abdul Rehman with a pre-filled greeting message.", STUDIO_WARM_GOLD)
            }
        },
        {View, layout_width = "fill", layout_height = "16dp"},
        {Button, text = "FEEDBACK VIA WHATSAPP", layout_width = "fill", layout_height = "48dp", background = gradBrd(0xFF059669, 0xFF065F46, 0xFF34D399, 24, 2), textColor = 0xFFFFFFFF, textSize = "12sp", typeface = Typeface.DEFAULT_BOLD, onClick = function() openWhatsAppFeedback() end},
        {View, layout_width = "fill", layout_height = "8dp"},
        {Button, id = "btnAboutClose", text = "CLOSE", layout_width = "fill", layout_height = "46dp", background = gradBrd(0xFF334155, 0xFF1E293B, 0xFF64748B, 24, 2), textColor = 0xFFF1F5F9, textSize = "12sp", typeface = Typeface.DEFAULT_BOLD}
    }

    local d = AlertDialog.Builder(activity).setView(loadlayout(aboutLayout)).create()
    styleDialogWindow(d)
    pcall(function()
        btnAboutClose.onClick = function() vibrate(35); d.dismiss() end
    end)
    d.show()
end

-- Helper to add Video Quality Spinner Card to any Video Operation Window
local function addVideoQualityCard(parentLayout, isForSplitVideo, cardBg, borderCol)
    local qCard = createStyledCard(cardBg or STUDIO_MAIN_CARD, borderCol or STUDIO_NEON_CYAN, 20)
    local qLabel = TextView(ctx)
    setT(qLabel, "Video Quality:")
    qLabel.setTextColor(STUDIO_WARM_GOLD)
    qLabel.setTypeface(nil, Typeface.BOLD)
    qLabel.setTextSize(14)
    pcall(function() qLabel.setFocusable(true) end)
    qCard.addView(qLabel)
    addSpacer(qCard, 8)

    local qSpinner = Spinner(ctx)
    local qAdapter = ArrayAdapter(ctx, android.R.layout.simple_spinner_dropdown_item, String(VIDEO_QUALITY_LABELS))
    qSpinner.setAdapter(qAdapter)
    if isForSplitVideo and video_quality_idx == 0 then
        video_quality_idx = 3
    end
    qSpinner.setSelection(video_quality_idx)
    qSpinner.setOnItemSelectedListener(AdapterView.OnItemSelectedListener{
        onItemSelected = function(p, v, pos, id)
            video_quality_idx = pos
        end
    })
    qCard.addView(createSpinnerContainer(qSpinner, borderCol or STUDIO_NEON_CYAN))
    parentLayout.addView(qCard)
end

-- ================= MODE 2 / ADD MUSIC TO VOICE UI BUILDER =================
local function buildMusicToVoiceCardUI(container)
    container.removeAllViews()

    local previewPlayBtnRef = nil
    local previewPosTVRef = nil

    local step1Card = createStyledCard(0xFF2B1532, 0xFFF472B6, 22)
    local voiceStatusTV = TextView(ctx)
    setT(voiceStatusTV, voice_file and ("Voice: " .. voice_file.name .. " (" .. formatDurationMs(voice_file.duration) .. ")") or "Voice: Not Selected")
    voiceStatusTV.setTextColor(STUDIO_WARM_GOLD)
    voiceStatusTV.setTypeface(nil, Typeface.BOLD)
    voiceStatusTV.setPadding(14, 14, 14, 14)
    voiceStatusTV.setBackground(brd(0xFF1A0D1E, 0xFFF472B6, 14))
    pcall(function() voiceStatusTV.setFocusable(true) end)
    step1Card.addView(voiceStatusTV)
    addSpacer(step1Card, 10)

    local vRow = LinearLayout(ctx)
    vRow.setOrientation(0)
    local lpLeft = LinearLayout.LayoutParams(0, -2, 1.0)
    lpLeft.setMargins(0, 0, 8, 0)
    local lpRight = LinearLayout.LayoutParams(0, -2, 1.0)
    lpRight.setMargins(8, 0, 0, 0)

    local addVoiceBtn = createStyledButton("Add Voice", 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
    addVoiceBtn.setLayoutParams(lpLeft)
    addVoiceBtn.setOnClickListener(function()
        vibrate(35)
        showMediaListDialog(0, "Select Voice Audio", function(chosen)
            stopPreview()
            voice_file = chosen
            setT(voiceStatusTV, "Voice: " .. chosen.name .. " (Scanning pauses...)")
            scanVoiceSilenceAndSpeechAsync(voice_file, function()
                setT(voiceStatusTV, "Voice: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
    end)
    vRow.addView(addVoiceBtn)

    local recVoiceBtn = createStyledButton("Record Voice", 0xFFE11D48, 0xFFFFFFFF, 0xFF9F1239, 18)
    recVoiceBtn.setLayoutParams(lpRight)
    recVoiceBtn.setOnClickListener(function()
        vibrate(35)
        showRecordVoiceDialog(function(recObj)
            stopPreview()
            voice_file = recObj
            setT(voiceStatusTV, "Voice: " .. recObj.name .. " (Scanning pauses...)")
            scanVoiceSilenceAndSpeechAsync(voice_file, function()
                setT(voiceStatusTV, "Voice: " .. recObj.name .. " (" .. formatDurationMs(recObj.duration) .. ")")
            end)
        end, true)
    end)
    vRow.addView(recVoiceBtn)
    step1Card.addView(vRow)
    container.addView(step1Card)

    local step2Card = createStyledCard(0xFF2B1532, 0xFFE879F9, 22)
    local musicStatusTV = TextView(ctx)
    setT(musicStatusTV, music_file and ("Music: " .. music_file.name .. " (" .. formatDurationMs(music_file.duration) .. ")") or "Music: Not Selected")
    musicStatusTV.setTextColor(STUDIO_NEON_CYAN)
    musicStatusTV.setTypeface(nil, Typeface.BOLD)
    musicStatusTV.setPadding(14, 14, 14, 14)
    musicStatusTV.setBackground(brd(0xFF1A0D1E, 0xFFE879F9, 14))
    pcall(function() musicStatusTV.setFocusable(true) end)
    step2Card.addView(musicStatusTV)
    addSpacer(step2Card, 10)

    local addMusicBtn = createStyledButton("Add Music", 0xFF9333EA, 0xFFFFFFFF, 0xFF6B21A8, 18)
    addMusicBtn.setOnClickListener(function()
        vibrate(35)
        showMediaListDialog(0, "Select Background Music", function(chosen)
            stopPreview()
            music_file = chosen
            setT(musicStatusTV, "Music: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
        end)
    end)
    step2Card.addView(addMusicBtn)
    container.addView(step2Card)

    local step3Card = createStyledCard(0xFF2B1532, 0xFF34D399, 22)

    local smartFilterBtn = createStyledButton("", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 20)
    local function updateSmartBtn()
        if smart_filtering_enabled then
            setT(smartFilterBtn, "Smart Filtering: ON")
            smartFilterBtn.setBackground(gradBrd(0xFF059669, 0xFF047857, 0xFF34D399, 20, 2))
        else
            setT(smartFilterBtn, "Smart Filtering: OFF")
            smartFilterBtn.setBackground(gradBrd(0xFF475569, 0xFF334155, 0xFF94A3B8, 20, 2))
        end
    end
    updateSmartBtn()

    smartFilterBtn.setOnClickListener(function()
        vibrate(35)
        smart_filtering_enabled = not smart_filtering_enabled
        updateSmartBtn()
        speak(smart_filtering_enabled and "Smart Filtering On" or "Smart Filtering Off")
        if voice_file and music_file and not is_playing then
            startPreviewForFile(voice_file, 0, 0, previewPlayBtnRef, previewPosTVRef, music_file)
        end
    end)
    step3Card.addView(smartFilterBtn)
    addSpacer(step3Card, 14)

    local vVolTV = TextView(ctx)
    setT(vVolTV, "1. Voice Volume (Up to 200% Boost): " .. tostring(voice_vol_pct) .. "%")
    vVolTV.setTextColor(STUDIO_NEON_CYAN)
    vVolTV.setTypeface(nil, Typeface.BOLD)
    pcall(function() vVolTV.setFocusable(true) end)
    step3Card.addView(vVolTV)

    local vSeek = SeekBar(ctx)
    vSeek.setMax(200)
    vSeek.setProgress(voice_vol_pct)
    vSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
        onProgressChanged = function(sb, prog, fromUser)
            voice_vol_pct = math.max(10, prog)
            setT(vVolTV, "1. Voice Volume (Up to 200% Boost): " .. tostring(voice_vol_pct) .. "%")
            updateLivePlayerVolumes(true)
        end
    })
    step3Card.addView(vSeek)
    addSpacer(step3Card, 12)

    local mHighTV = TextView(ctx)
    setT(mHighTV, "2. Music Volume in Pauses (High): " .. tostring(music_high_pct) .. "%")
    mHighTV.setTextColor(STUDIO_WARM_GOLD)
    mHighTV.setTypeface(nil, Typeface.BOLD)
    pcall(function() mHighTV.setFocusable(true) end)
    step3Card.addView(mHighTV)

    local mHighSeek = SeekBar(ctx)
    mHighSeek.setMax(200)
    mHighSeek.setProgress(music_high_pct)
    mHighSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
        onProgressChanged = function(sb, prog, fromUser)
            music_high_pct = math.max(10, prog)
            setT(mHighTV, "2. Music Volume in Pauses (High): " .. tostring(music_high_pct) .. "%")
            updateLivePlayerVolumes(false)
        end
    })
    step3Card.addView(mHighSeek)
    addSpacer(step3Card, 12)

    local mLowTV = TextView(ctx)
    setT(mLowTV, "3. Music Volume While Speaking (Background): " .. tostring(music_duck_pct) .. "%")
    mLowTV.setTextColor(STUDIO_NEON_CYAN)
    mLowTV.setTypeface(nil, Typeface.BOLD)
    pcall(function() mLowTV.setFocusable(true) end)
    step3Card.addView(mLowTV)

    local mLowSeek = SeekBar(ctx)
    mLowSeek.setMax(150)
    mLowSeek.setProgress(music_duck_pct)
    mLowSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
        onProgressChanged = function(sb, prog, fromUser)
            music_duck_pct = math.max(5, prog)
            setT(mLowTV, "3. Music Volume While Speaking (Background): " .. tostring(music_duck_pct) .. "%")
            updateLivePlayerVolumes(true)
        end
    })
    step3Card.addView(mLowSeek)
    addSpacer(step3Card, 12)

    local masterTV = TextView(ctx)
    setT(masterTV, "4. Master Volume Booster (Overall Loudness): " .. tostring(master_boost_pct) .. "%")
    masterTV.setTextColor(STUDIO_WARM_GOLD)
    masterTV.setTypeface(nil, Typeface.BOLD)
    pcall(function() masterTV.setFocusable(true) end)
    step3Card.addView(masterTV)

    local masterSeek = SeekBar(ctx)
    masterSeek.setMax(200)
    masterSeek.setProgress(master_boost_pct)
    masterSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
        onProgressChanged = function(sb, prog, fromUser)
            master_boost_pct = math.max(50, prog)
            setT(masterTV, "4. Master Volume Booster (Overall Loudness): " .. tostring(master_boost_pct) .. "%")
            updateLivePlayerVolumes(true)
        end
    })
    step3Card.addView(masterSeek)
    container.addView(step3Card)

    previewPlayBtnRef, previewPosTVRef = addProfessionalPlayerCard(
        container,
        function() return voice_file or music_file end,
        false,
        nil,
        nil,
        function() return (voice_file and music_file) and music_file or nil end,
        nil,
        0xFF2B1532,
        0xFFF472B6
    )

    local startMixBtn = createStyledButton("Save Voice with Music", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
    startMixBtn.setOnClickListener(function()
        runProcess("music_to_voice")
    end)
    container.addView(startMixBtn)
end

-- ================= SEPARATE FULL-SCREEN STUDIO WINDOWS (Each With Its Own Custom Studio Theme!) =================
openOperationWindow = function(op)
    vibrate(35)
    stopPreview()
    current_op = op
    local typeWord = (media_type == 0) and "Audio" or "Video"

    -- 13 Distinct Pro Studio Color Palettes Tailored to Each Operation Situation!
    local winPalettes = {
        add_music      = { bg = 0xFF1A0D1E, card = 0xFF2B1532, hdr1 = 0xFF9D174D, hdr2 = 0xFF500724, border = 0xFFF472B6 },
        noise_remover  = { bg = 0xFF081B26, card = 0xFF0F2D3E, hdr1 = 0xFF0284C7, hdr2 = 0xFF0C4A6E, border = 0xFF38BDF8 },
        change_audio   = { bg = 0xFF1A1025, card = 0xFF2A1B3D, hdr1 = 0xFF6D28D9, hdr2 = 0xFF4C1D95, border = 0xFFA78BFA },
        converter      = { bg = 0xFF0F1329, card = 0xFF1B2244, hdr1 = 0xFF4338CA, hdr2 = 0xFF312E81, border = 0xFF818CF8 },
        cut            = { bg = 0xFF0A191E, card = 0xFF122B34, hdr1 = 0xFF0F766E, hdr2 = 0xFF115E59, border = 0xFF2DD4BF },
        echo_studio    = { bg = 0xFF071F18, card = 0xFF10352A, hdr1 = 0xFF059669, hdr2 = 0xFF064E3B, border = 0xFF34D399 },
        extract        = { bg = 0xFF1F1409, card = 0xFF302010, hdr1 = 0xFFB45309, hdr2 = 0xFF78350F, border = 0xFFFBBF24 },
        merge          = { bg = 0xFF170F26, card = 0xFF24173B, hdr1 = 0xFF7E22CE, hdr2 = 0xFF3B0764, border = 0xFFC084FC },
        silent         = { bg = 0xFF1F0E16, card = 0xFF331824, hdr1 = 0xFFBE123C, hdr2 = 0xFF881337, border = 0xFFFB7185 },
        split_video    = { bg = 0xFF0B1F17, card = 0xFF133326, hdr1 = 0xFF047857, hdr2 = 0xFF064E3B, border = 0xFF10B981 },
        trim           = { bg = 0xFF0C1726, card = 0xFF152740, hdr1 = 0xFF1D4ED8, hdr2 = 0xFF1E3A8A, border = 0xFF60A5FA },
        voice_recorder = { bg = 0xFF210B12, card = 0xFF36141F, hdr1 = 0xFFE11D48, hdr2 = 0xFF881337, border = 0xFFFB7185 },
        volume_booster = { bg = 0xFF211008, card = 0xFF361C10, hdr1 = 0xFFEA580C, hdr2 = 0xFF7C2D12, border = 0xFFFB923C }
    }
    local pal = winPalettes[op] or winPalettes.cut

    local scrollView = ScrollView(ctx)
    scrollView.setLayoutParams(LinearLayout.LayoutParams(-1, -1))
    scrollView.setFillViewport(true)
    scrollView.setBackgroundColor(pal.bg)

    local root = LinearLayout(ctx)
    root.setOrientation(1)
    root.setPadding(24, 22, 24, 32)
    root.setBackgroundColor(pal.bg)
    scrollView.addView(root)

    local navBar = LinearLayout(ctx)
    navBar.setOrientation(1)
    navBar.setPadding(20, 18, 20, 18)
    navBar.setBackground(gradBrd(pal.hdr1, pal.hdr2, pal.border, 22, 3))
    local navLp = LinearLayout.LayoutParams(-1, -2)
    navLp.setMargins(0, 6, 0, 14)
    navBar.setLayoutParams(navLp)

    local navRow = LinearLayout(ctx)
    navRow.setOrientation(0)
    navRow.setGravity(Gravity.CENTER_VERTICAL)

    local backBtn = createStyledButton("Back", 0xFF334155, 0xFFFFFFFF, 0xFF1E293B, 18)
    backBtn.setOnClickListener(function()
        vibrate(35)
        stopPreview()
        showMainWindow()
    end)
    navRow.addView(backBtn)

    local winTitleTV = TextView(ctx)
    local titleMap = {
        add_music      = "ADD MUSIC TO VOICE",
        noise_remover  = "BACKGROUND NOISE REMOVER",
        change_audio   = "CHANGE VIDEO AUDIO",
        converter      = "CONVERT FORMAT & QUALITY",
        cut            = "CUT " .. typeWord:upper(),
        echo_studio    = "ECHO & VOICE EFFECTS",
        extract        = "EXTRACT AUDIO",
        merge          = "MERGE " .. typeWord:upper(),
        silent         = "SILENT VIDEO MAKER",
        split_video    = "SPLIT VIDEO STUDIO",
        trim           = "TRIM " .. typeWord:upper(),
        voice_recorder = "VOICE RECORDER STUDIO",
        volume_booster = "VOLUME BOOSTER (300%)"
    }
    setT(winTitleTV, "   " .. (titleMap[op] or "STUDIO EDITOR"))
    winTitleTV.setTextColor(STUDIO_WARM_GOLD)
    winTitleTV.setTextSize(17)
    winTitleTV.setTypeface(nil, Typeface.BOLD)
    pcall(function() winTitleTV.setFocusable(true) end)
    navRow.addView(winTitleTV)
    navBar.addView(navRow)
    root.addView(navBar)

    -- 1. ADD MUSIC TO VOICE WINDOW
    if op == "add_music" then
        local mvContainer = LinearLayout(ctx)
        mvContainer.setOrientation(1)
        buildMusicToVoiceCardUI(mvContainer)
        root.addView(mvContainer)

    -- 2. BACKGROUND NOISE REMOVER WINDOW (File OR Live Mic Recording!)
    elseif op == "noise_remover" then
        local nrCard = createStyledCard(pal.card, pal.border, 22)

        local fileTV = TextView(ctx)
        setT(fileTV, primary_file and ("Selected: " .. primary_file.name .. " (" .. formatDurationMs(primary_file.duration) .. ")") or "Select an Audio/Video file OR Record Voice below:")
        fileTV.setTextColor(STUDIO_WARM_GOLD)
        fileTV.setTypeface(nil, Typeface.BOLD)
        fileTV.setPadding(16, 14, 16, 14)
        fileTV.setBackground(brd(pal.bg, pal.border, 14))
        pcall(function() fileTV.setFocusable(true) end)
        nrCard.addView(fileTV)
        addSpacer(nrCard, 12)

        local btnRow = LinearLayout(ctx)
        btnRow.setOrientation(0)
        local lpL = LinearLayout.LayoutParams(0, -2, 1.0)
        lpL.setMargins(0, 0, 8, 0)
        local lpR = LinearLayout.LayoutParams(0, -2, 1.0)
        lpR.setMargins(8, 0, 0, 0)

        local pickBtn = createStyledButton("Select " .. typeWord, 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
        pickBtn.setLayoutParams(lpL)
        pickBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(media_type, "Select " .. typeWord .. " to Clean Noise", function(chosen)
                stopPreview()
                primary_file = chosen
                setT(fileTV, "Selected: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        btnRow.addView(pickBtn)

        local recCleanBtn = createStyledButton("Record Mic Voice", 0xFFE11D48, 0xFFFFFFFF, 0xFF9F1239, 18)
        recCleanBtn.setLayoutParams(lpR)
        recCleanBtn.setOnClickListener(function()
            vibrate(35)
            showRecordVoiceDialog(function(recObj)
                stopPreview()
                primary_file = recObj
                setT(fileTV, "Recorded: " .. recObj.name .. " (" .. formatDurationMs(recObj.duration) .. ")")
                speak("Voice recorded. Ready to remove background noise.")
            end, true)
        end)
        btnRow.addView(recCleanBtn)
        nrCard.addView(btnRow)
        addSpacer(nrCard, 16)

        local strTV = TextView(ctx)
        setT(strTV, "1. Noise Reduction Strength: " .. tostring(noise_strength_pct) .. "%")
        strTV.setTextColor(STUDIO_NEON_CYAN)
        strTV.setTypeface(nil, Typeface.BOLD)
        pcall(function() strTV.setFocusable(true) end)
        nrCard.addView(strTV)

        local strSeek = SeekBar(ctx)
        strSeek.setMax(100)
        strSeek.setProgress(noise_strength_pct)
        strSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
            onProgressChanged = function(sb, prog, fromUser)
                noise_strength_pct = math.max(15, prog)
                setT(strTV, "1. Noise Reduction Strength: " .. tostring(noise_strength_pct) .. "%")
            end
        })
        nrCard.addView(strSeek)
        addSpacer(nrCard, 12)

        local clrTV = TextView(ctx)
        setT(clrTV, "2. Voice Clarity & Volume Boost: " .. tostring(noise_voice_boost_pct) .. "%")
        clrTV.setTextColor(STUDIO_WARM_GOLD)
        clrTV.setTypeface(nil, Typeface.BOLD)
        pcall(function() clrTV.setFocusable(true) end)
        nrCard.addView(clrTV)

        local clrSeek = SeekBar(ctx)
        clrSeek.setMax(220)
        clrSeek.setProgress(noise_voice_boost_pct)
        clrSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
            onProgressChanged = function(sb, prog, fromUser)
                noise_voice_boost_pct = math.max(80, prog)
                setT(clrTV, "2. Voice Clarity & Volume Boost: " .. tostring(noise_voice_boost_pct) .. "%")
            end
        })
        nrCard.addView(clrSeek)
        root.addView(nrCard)

        addProfessionalPlayerCard(root, function() return primary_file end, false, nil, nil, nil, nil, pal.card, pal.border)

        local cleanNowBtn = createStyledButton("Remove Background Noise Now", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        cleanNowBtn.setOnClickListener(function() runProcess("noise_remover") end)
        root.addView(cleanNowBtn)

    -- 3. CONVERT FORMAT & QUALITY WINDOW (MP3 / M4A / WAV / AAC / MP4 Video + Bitrate + Resolution)
    elseif op == "converter" then
        local cvCard = createStyledCard(pal.card, pal.border, 22)

        local fileTV = TextView(ctx)
        setT(fileTV, primary_file and ("Selected: " .. primary_file.name .. " (" .. formatDurationMs(primary_file.duration) .. ")") or "No File Selected")
        fileTV.setTextColor(STUDIO_WARM_GOLD)
        fileTV.setTypeface(nil, Typeface.BOLD)
        fileTV.setPadding(16, 14, 16, 14)
        fileTV.setBackground(brd(pal.bg, pal.border, 14))
        pcall(function() fileTV.setFocusable(true) end)
        cvCard.addView(fileTV)
        addSpacer(cvCard, 10)

        local pickRow = LinearLayout(ctx)
        pickRow.setOrientation(0)
        local lpL = LinearLayout.LayoutParams(0, -2, 1.0)
        lpL.setMargins(0, 0, 8, 0)
        local lpR = LinearLayout.LayoutParams(0, -2, 1.0)
        lpR.setMargins(8, 0, 0, 0)

        local pickAudBtn = createStyledButton("Select Audio", 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
        pickAudBtn.setLayoutParams(lpL)
        pickAudBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(0, "Select Audio File", function(chosen)
                stopPreview()
                primary_file = chosen
                setT(fileTV, "Selected Audio: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        pickRow.addView(pickAudBtn)

        local pickVidBtn = createStyledButton("Select Video", 0xFF7C3AED, 0xFFFFFFFF, 0xFF5B21B6, 18)
        pickVidBtn.setLayoutParams(lpR)
        pickVidBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(1, "Select Video File", function(chosen)
                stopPreview()
                primary_file = chosen
                setT(fileTV, "Selected Video: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        pickRow.addView(pickVidBtn)
        cvCard.addView(pickRow)
        addSpacer(cvCard, 14)

        local fmtLbl = TextView(ctx)
        setT(fmtLbl, "Target Output Format (MP3 / M4A / WAV / AAC / MP4):")
        fmtLbl.setTextColor(STUDIO_WARM_GOLD)
        fmtLbl.setTypeface(nil, Typeface.BOLD)
        pcall(function() fmtLbl.setFocusable(true) end)
        cvCard.addView(fmtLbl)
        addSpacer(cvCard, 6)

        local fmtSpin = Spinner(ctx)
        local fmtItems = String{
            "M4A Studio Audio (.m4a - Fast & Universal)",
            "MP3 Audio Format (.mp3 - Universal Audio)",
            "WAV Lossless Audio (.wav - Uncompressed Studio CD)",
            "AAC Audio Format (.aac - High Efficiency)",
            "MP4 Video Format (.mp4 - Convert Audio to Video / Video Quality)"
        }
        fmtSpin.setAdapter(ArrayAdapter(ctx, android.R.layout.simple_spinner_dropdown_item, fmtItems))
        fmtSpin.setSelection(conv_format_idx)
        fmtSpin.setOnItemSelectedListener(AdapterView.OnItemSelectedListener{
            onItemSelected = function(p, v, pos, id)
                conv_format_idx = pos
            end
        })
        cvCard.addView(createSpinnerContainer(fmtSpin, pal.border))
        addSpacer(cvCard, 14)

        local brLbl = TextView(ctx)
        setT(brLbl, "Audio Quality / Bitrate:")
        brLbl.setTextColor(STUDIO_NEON_CYAN)
        brLbl.setTypeface(nil, Typeface.BOLD)
        pcall(function() brLbl.setFocusable(true) end)
        cvCard.addView(brLbl)
        addSpacer(cvCard, 6)

        local brSpin = Spinner(ctx)
        local brItems = String{
            "320 kbps (Ultra Studio HD Quality)",
            "256 kbps (Studio High Quality)",
            "192 kbps (Standard High Quality)",
            "128 kbps (Balanced Size & Quality)",
            "64 kbps (Compact Voice Size)"
        }
        brSpin.setAdapter(ArrayAdapter(ctx, android.R.layout.simple_spinner_dropdown_item, brItems))
        brSpin.setSelection(conv_bitrate_idx)
        brSpin.setOnItemSelectedListener(AdapterView.OnItemSelectedListener{
            onItemSelected = function(p, v, pos, id)
                conv_bitrate_idx = pos
            end
        })
        cvCard.addView(createSpinnerContainer(brSpin, pal.border))
        root.addView(cvCard)

        addVideoQualityCard(root, false, pal.card, pal.border)

        addProfessionalPlayerCard(root, function() return primary_file end, false, nil, nil, nil, nil, pal.card, pal.border)

        local convNowBtn = createStyledButton("Convert Format & Quality Now", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        convNowBtn.setOnClickListener(function() runProcess("converter") end)
        root.addView(convNowBtn)

    -- 4. ECHO & VOICE EFFECTS STUDIO WINDOW
    elseif op == "echo_studio" then
        local ecCard = createStyledCard(pal.card, pal.border, 22)

        local fileTV = TextView(ctx)
        setT(fileTV, primary_file and ("Selected: " .. primary_file.name .. " (" .. formatDurationMs(primary_file.duration) .. ")") or "Select File or Record Voice for Studio Echo:")
        fileTV.setTextColor(STUDIO_WARM_GOLD)
        fileTV.setTypeface(nil, Typeface.BOLD)
        fileTV.setPadding(16, 14, 16, 14)
        fileTV.setBackground(brd(pal.bg, pal.border, 14))
        pcall(function() fileTV.setFocusable(true) end)
        ecCard.addView(fileTV)
        addSpacer(ecCard, 10)

        local btnRow = LinearLayout(ctx)
        btnRow.setOrientation(0)
        local lpL = LinearLayout.LayoutParams(0, -2, 1.0)
        lpL.setMargins(0, 0, 8, 0)
        local lpR = LinearLayout.LayoutParams(0, -2, 1.0)
        lpR.setMargins(8, 0, 0, 0)

        local pickBtn = createStyledButton("Select " .. typeWord, 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
        pickBtn.setLayoutParams(lpL)
        pickBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(media_type, "Select " .. typeWord .. " for Echo", function(chosen)
                stopPreview()
                primary_file = chosen
                setT(fileTV, "Selected: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        btnRow.addView(pickBtn)

        local recEchoBtn = createStyledButton("Record Voice", 0xFFE11D48, 0xFFFFFFFF, 0xFF9F1239, 18)
        recEchoBtn.setLayoutParams(lpR)
        recEchoBtn.setOnClickListener(function()
            vibrate(35)
            showRecordVoiceDialog(function(recObj)
                stopPreview()
                primary_file = recObj
                setT(fileTV, "Recorded: " .. recObj.name .. " (" .. formatDurationMs(recObj.duration) .. ")")
            end, true)
        end)
        btnRow.addView(recEchoBtn)
        ecCard.addView(btnRow)
        addSpacer(ecCard, 14)

        local dlyTV = TextView(ctx)
        local decTV = TextView(ctx)
        local dlySeek = SeekBar(ctx)
        local decSeek = SeekBar(ctx)

        local presetLbl = TextView(ctx)
        setT(presetLbl, "Echo Studio Preset:")
        presetLbl.setTextColor(STUDIO_WARM_GOLD)
        presetLbl.setTypeface(nil, Typeface.BOLD)
        pcall(function() presetLbl.setFocusable(true) end)
        ecCard.addView(presetLbl)
        addSpacer(ecCard, 6)

        local presetSpin = Spinner(ctx)
        local presetItems = String{
            "Naat & Tilawat Madinah Hall (220ms / 45%)",
            "Studio Vocal Reverb - Warm & Soft (120ms / 35%)",
            "Deep Mosque / Mehfil Long Echo (320ms / 55%)",
            "Double Voice Chorus Effect (65ms / 40%)",
            "Custom Echo Settings (Adjust Sliders Below)"
        }
        presetSpin.setAdapter(ArrayAdapter(ctx, android.R.layout.simple_spinner_dropdown_item, presetItems))
        presetSpin.setSelection(echo_preset_idx)
        presetSpin.setOnItemSelectedListener(AdapterView.OnItemSelectedListener{
            onItemSelected = function(p, v, pos, id)
                echo_preset_idx = pos
                if pos == 0 then echo_delay_ms = 220; echo_decay_pct = 45
                elseif pos == 1 then echo_delay_ms = 120; echo_decay_pct = 35
                elseif pos == 2 then echo_delay_ms = 320; echo_decay_pct = 55
                elseif pos == 3 then echo_delay_ms = 65;  echo_decay_pct = 40 end
                pcall(function()
                    dlySeek.setProgress(echo_delay_ms)
                    decSeek.setProgress(echo_decay_pct)
                    setT(dlyTV, "1. Echo Delay Time (Space Between Repeats): " .. tostring(echo_delay_ms) .. " ms")
                    setT(decTV, "2. Echo Repeat / Decay Strength: " .. tostring(echo_decay_pct) .. "%")
                end)
            end
        })
        ecCard.addView(createSpinnerContainer(presetSpin, pal.border))
        addSpacer(ecCard, 14)

        setT(dlyTV, "1. Echo Delay Time (Space Between Repeats): " .. tostring(echo_delay_ms) .. " ms")
        dlyTV.setTextColor(STUDIO_NEON_CYAN)
        dlyTV.setTypeface(nil, Typeface.BOLD)
        pcall(function() dlyTV.setFocusable(true) end)
        ecCard.addView(dlyTV)

        dlySeek.setMax(600)
        dlySeek.setProgress(echo_delay_ms)
        dlySeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
            onProgressChanged = function(sb, prog, fromUser)
                echo_delay_ms = math.max(40, prog)
                setT(dlyTV, "1. Echo Delay Time (Space Between Repeats): " .. tostring(echo_delay_ms) .. " ms")
            end
        })
        ecCard.addView(dlySeek)
        addSpacer(ecCard, 12)

        setT(decTV, "2. Echo Repeat / Decay Strength: " .. tostring(echo_decay_pct) .. "%")
        decTV.setTextColor(STUDIO_WARM_GOLD)
        decTV.setTypeface(nil, Typeface.BOLD)
        pcall(function() decTV.setFocusable(true) end)
        ecCard.addView(decTV)

        decSeek.setMax(85)
        decSeek.setProgress(echo_decay_pct)
        decSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
            onProgressChanged = function(sb, prog, fromUser)
                echo_decay_pct = math.max(10, prog)
                setT(decTV, "2. Echo Repeat / Decay Strength: " .. tostring(echo_decay_pct) .. "%")
            end
        })
        ecCard.addView(decSeek)
        addSpacer(ecCard, 12)

        local vBoostTV = TextView(ctx)
        setT(vBoostTV, "3. Voice Clarity & Loudness Boost: " .. tostring(echo_voice_boost_pct) .. "%")
        vBoostTV.setTextColor(STUDIO_NEON_CYAN)
        vBoostTV.setTypeface(nil, Typeface.BOLD)
        pcall(function() vBoostTV.setFocusable(true) end)
        ecCard.addView(vBoostTV)

        local vBoostSeek = SeekBar(ctx)
        vBoostSeek.setMax(200)
        vBoostSeek.setProgress(echo_voice_boost_pct)
        vBoostSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
            onProgressChanged = function(sb, prog, fromUser)
                echo_voice_boost_pct = math.max(50, prog)
                setT(vBoostTV, "3. Voice Clarity & Loudness Boost: " .. tostring(echo_voice_boost_pct) .. "%")
            end
        })
        ecCard.addView(vBoostSeek)
        root.addView(ecCard)

        addProfessionalPlayerCard(root, function() return primary_file end, false, nil, nil, nil, nil, pal.card, pal.border)

        local applyEchoBtn = createStyledButton("Apply Echo & Save Now", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        applyEchoBtn.setOnClickListener(function() runProcess("echo_studio") end)
        root.addView(applyEchoBtn)

    -- 5. VOICE RECORDER STUDIO WINDOW (Mic + Background Music + Noise Clean + Echo)
    elseif op == "voice_recorder" then
        local vrCard = createStyledCard(pal.card, pal.border, 22)

        local vStatTV = TextView(ctx)
        setT(vStatTV, voice_file and ("Recorded / Selected Voice: " .. voice_file.name .. " (" .. formatDurationMs(voice_file.duration) .. ")") or "Step 1: Tap Record Microphone Voice below")
        vStatTV.setTextColor(STUDIO_WARM_GOLD)
        vStatTV.setTypeface(nil, Typeface.BOLD)
        vStatTV.setPadding(16, 14, 16, 14)
        vStatTV.setBackground(brd(pal.bg, pal.border, 14))
        pcall(function() vStatTV.setFocusable(true) end)
        vrCard.addView(vStatTV)
        addSpacer(vrCard, 10)

        local recRow = LinearLayout(ctx)
        recRow.setOrientation(0)
        local lpL = LinearLayout.LayoutParams(0, -2, 1.0)
        lpL.setMargins(0, 0, 8, 0)
        local lpR = LinearLayout.LayoutParams(0, -2, 1.0)
        lpR.setMargins(8, 0, 0, 0)

        local startMicBtn = createStyledButton("Record Mic Voice", 0xFFE11D48, 0xFFFFFFFF, 0xFF9F1239, 18)
        startMicBtn.setLayoutParams(lpL)
        startMicBtn.setOnClickListener(function()
            vibrate(35)
            showRecordVoiceDialog(function(recObj)
                stopPreview()
                voice_file = recObj
                setT(vStatTV, "Recorded Voice: " .. recObj.name .. " (" .. formatDurationMs(recObj.duration) .. ")")
                speak("Recording ready")
            end, true)
        end)
        recRow.addView(startMicBtn)

        local pickExistingVoiceBtn = createStyledButton("Select Audio File", 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
        pickExistingVoiceBtn.setLayoutParams(lpR)
        pickExistingVoiceBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(0, "Select Voice File", function(chosen)
                stopPreview()
                voice_file = chosen
                setT(vStatTV, "Selected Voice: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        recRow.addView(pickExistingVoiceBtn)
        vrCard.addView(recRow)
        addSpacer(vrCard, 14)

        local mStatTV = TextView(ctx)
        setT(mStatTV, music_file and ("Background Music: " .. music_file.name .. " (" .. formatDurationMs(music_file.duration) .. ")") or "Optional Background Music: None")
        mStatTV.setTextColor(STUDIO_NEON_CYAN)
        mStatTV.setTypeface(nil, Typeface.BOLD)
        mStatTV.setPadding(14, 12, 14, 12)
        mStatTV.setBackground(brd(pal.bg, 0xFFA855F7, 14))
        pcall(function() mStatTV.setFocusable(true) end)
        vrCard.addView(mStatTV)
        addSpacer(vrCard, 8)

        local mBtnRow = LinearLayout(ctx)
        mBtnRow.setOrientation(0)
        local selBgMusicBtn = createStyledButton("Add Background Music", 0xFF7C3AED, 0xFFFFFFFF, 0xFF5B21B6, 18)
        selBgMusicBtn.setLayoutParams(lpL)
        selBgMusicBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(0, "Select Background Music", function(chosen)
                stopPreview()
                music_file = chosen
                setT(mStatTV, "Background Music: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        mBtnRow.addView(selBgMusicBtn)

        local clrBgMusicBtn = createStyledButton("No Music", 0xFF475569, 0xFFFFFFFF, 0xFF334155, 18)
        clrBgMusicBtn.setLayoutParams(lpR)
        clrBgMusicBtn.setOnClickListener(function()
            vibrate(35)
            music_file = nil
            setT(mStatTV, "Optional Background Music: None")
            speak("Background music removed")
        end)
        mBtnRow.addView(clrBgMusicBtn)
        vrCard.addView(mBtnRow)
        addSpacer(vrCard, 14)

        local toggleNoiseBtn = createStyledButton("", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 18)
        local function refreshToggleNoise()
            if rec_clean_noise then
                setT(toggleNoiseBtn, "Auto Remove Background Noise: ON")
                toggleNoiseBtn.setBackground(gradBrd(0xFF059669, 0xFF047857, 0xFF34D399, 18, 2))
            else
                setT(toggleNoiseBtn, "Auto Remove Background Noise: OFF")
                toggleNoiseBtn.setBackground(gradBrd(0xFF475569, 0xFF334155, 0xFF94A3B8, 18, 2))
            end
        end
        refreshToggleNoise()
        toggleNoiseBtn.setOnClickListener(function()
            vibrate(35)
            rec_clean_noise = not rec_clean_noise
            refreshToggleNoise()
            speak(rec_clean_noise and "Background noise removal On" or "Background noise removal Off")
        end)
        vrCard.addView(toggleNoiseBtn)
        addSpacer(vrCard, 10)

        local toggleEchoBtn = createStyledButton("", 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
        local function refreshToggleEcho()
            if rec_add_echo then
                setT(toggleEchoBtn, "Studio Echo Effect (Madinah Hall): ON")
                toggleEchoBtn.setBackground(gradBrd(0xFF0284C7, 0xFF0369A1, 0xFF38BDF8, 18, 2))
            else
                setT(toggleEchoBtn, "Studio Echo Effect (Madinah Hall): OFF")
                toggleEchoBtn.setBackground(gradBrd(0xFF475569, 0xFF334155, 0xFF94A3B8, 18, 2))
            end
        end
        refreshToggleEcho()
        toggleEchoBtn.setOnClickListener(function()
            vibrate(35)
            rec_add_echo = not rec_add_echo
            refreshToggleEcho()
            speak(rec_add_echo and "Studio Echo On" or "Studio Echo Off")
        end)
        vrCard.addView(toggleEchoBtn)
        addSpacer(vrCard, 12)

        local rvBoostTV = TextView(ctx)
        setT(rvBoostTV, "Voice Volume Boost: " .. tostring(rec_voice_boost_pct) .. "%")
        rvBoostTV.setTextColor(STUDIO_WARM_GOLD)
        rvBoostTV.setTypeface(nil, Typeface.BOLD)
        pcall(function() rvBoostTV.setFocusable(true) end)
        vrCard.addView(rvBoostTV)

        local rvBoostSeek = SeekBar(ctx)
        rvBoostSeek.setMax(250)
        rvBoostSeek.setProgress(rec_voice_boost_pct)
        rvBoostSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
            onProgressChanged = function(sb, prog, fromUser)
                rec_voice_boost_pct = math.max(50, prog)
                setT(rvBoostTV, "Voice Volume Boost: " .. tostring(rec_voice_boost_pct) .. "%")
            end
        })
        vrCard.addView(rvBoostSeek)
        root.addView(vrCard)

        addProfessionalPlayerCard(
            root,
            function() return voice_file end,
            false,
            nil,
            nil,
            function() return (voice_file and music_file) and music_file or nil end,
            nil,
            pal.card,
            pal.border
        )

        local saveRecStudioBtn = createStyledButton("Process & Save Studio Recording", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        saveRecStudioBtn.setOnClickListener(function() runProcess("voice_recorder") end)
        root.addView(saveRecStudioBtn)

    -- 6. VOLUME BOOSTER WINDOW (20% to 300% Loudness Amplifier)
    elseif op == "volume_booster" then
        local vbCard = createStyledCard(pal.card, pal.border, 22)

        local fileTV = TextView(ctx)
        setT(fileTV, primary_file and ("Selected: " .. primary_file.name .. " (" .. formatDurationMs(primary_file.duration) .. ")") or "No File Selected")
        fileTV.setTextColor(STUDIO_WARM_GOLD)
        fileTV.setTypeface(nil, Typeface.BOLD)
        fileTV.setPadding(16, 14, 16, 14)
        fileTV.setBackground(brd(pal.bg, pal.border, 14))
        pcall(function() fileTV.setFocusable(true) end)
        vbCard.addView(fileTV)
        addSpacer(vbCard, 10)

        local changeBtn = createStyledButton("Select / Change " .. typeWord, 0xFFD97706, 0xFFFFFFFF, 0xFFB45309, 18)
        changeBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(media_type, "Select " .. typeWord .. " to Adjust Volume", function(chosen)
                stopPreview()
                primary_file = chosen
                setT(fileTV, "Selected: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        vbCard.addView(changeBtn)
        addSpacer(vbCard, 14)

        local vbTV = TextView(ctx)
        local vbSeek = SeekBar(ctx)

        local pLbl = TextView(ctx)
        setT(pLbl, "Quick Volume Preset:")
        pLbl.setTextColor(STUDIO_WARM_GOLD)
        pLbl.setTypeface(nil, Typeface.BOLD)
        pcall(function() pLbl.setFocusable(true) end)
        vbCard.addView(pLbl)
        addSpacer(vbCard, 6)

        local pSpin = Spinner(ctx)
        local pItems = String{
            "200% - Double Loudness (Recommended Boost)",
            "300% - Maximum Ultra Boost (3x Loudness)",
            "150% - Clear Medium Boost",
            "100% - Normal Original Volume",
            "50% - Quiet Volume (Reduce Loud Audio)"
        }
        pSpin.setAdapter(ArrayAdapter(ctx, android.R.layout.simple_spinner_dropdown_item, pItems))
        pSpin.setSelection(0)
        pSpin.setOnItemSelectedListener(AdapterView.OnItemSelectedListener{
            onItemSelected = function(p, v, pos, id)
                if pos == 0 then vol_booster_pct = 200
                elseif pos == 1 then vol_booster_pct = 300
                elseif pos == 2 then vol_booster_pct = 150
                elseif pos == 3 then vol_booster_pct = 100
                elseif pos == 4 then vol_booster_pct = 50 end
                pcall(function()
                    vbSeek.setProgress(vol_booster_pct)
                    setT(vbTV, "Target Volume Level (20% to 300%): " .. tostring(vol_booster_pct) .. "%")
                end)
            end
        })
        vbCard.addView(createSpinnerContainer(pSpin, pal.border))
        addSpacer(vbCard, 14)

        setT(vbTV, "Target Volume Level (20% to 300%): " .. tostring(vol_booster_pct) .. "%")
        vbTV.setTextColor(STUDIO_NEON_CYAN)
        vbTV.setTypeface(nil, Typeface.BOLD)
        pcall(function() vbTV.setFocusable(true) end)
        vbCard.addView(vbTV)

        vbSeek.setMax(300)
        vbSeek.setProgress(vol_booster_pct)
        vbSeek.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
            onProgressChanged = function(sb, prog, fromUser)
                vol_booster_pct = math.max(20, prog)
                setT(vbTV, "Target Volume Level (20% to 300%): " .. tostring(vol_booster_pct) .. "%")
            end
        })
        vbCard.addView(vbSeek)
        root.addView(vbCard)

        addProfessionalPlayerCard(root, function() return primary_file end, false, nil, nil, nil, nil, pal.card, pal.border)

        local boostNowBtn = createStyledButton("Boost Volume & Save Now", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        boostNowBtn.setOnClickListener(function() runProcess("volume_booster") end)
        root.addView(boostNowBtn)

    -- 7. MERGE WINDOW
    elseif op == "merge" then
        local mergeCard = createStyledCard(pal.card, pal.border, 22)

        local subTitle = TextView(ctx)
        setT(subTitle, "Selected " .. typeWord .. " Files:")
        subTitle.setTextSize(15)
        subTitle.setTypeface(nil, Typeface.BOLD)
        subTitle.setTextColor(STUDIO_WARM_GOLD)
        pcall(function() subTitle.setFocusable(true) end)
        mergeCard.addView(subTitle)
        addSpacer(mergeCard, 8)

        local listContainer = LinearLayout(ctx)
        listContainer.setOrientation(1)
        mergeCard.addView(listContainer)
        addSpacer(mergeCard, 12)

        local addNextBtn = createStyledButton("Add 2 " .. typeWord, 0xFF7C3AED, 0xFFFFFFFF, 0xFF5B21B6, 20)
        mergeCard.addView(addNextBtn)

        local function refreshMergeUI()
            listContainer.removeAllViews()
            local totalMergedDur = 0
            for i, f in ipairs(merge_list) do
                totalMergedDur = totalMergedDur + (f.duration or 0)
                local itemCard = createStyledCard(0xFF170F26, pal.border, 14)
                local row = LinearLayout(ctx)
                row.setOrientation(0)
                row.setGravity(Gravity.CENTER_VERTICAL)

                local tv = TextView(ctx)
                setT(tv, tostring(i) .. ". " .. tostring(f.name) .. " (" .. formatDurationMs(f.duration) .. ")")
                tv.setTextColor(STUDIO_PURE_TEXT)
                tv.setTypeface(nil, Typeface.BOLD)
                tv.setLayoutParams(LinearLayout.LayoutParams(0, -2, 1.0))
                pcall(function() tv.setFocusable(true) end)
                row.addView(tv)

                local delBtn = createStyledButton("Remove", 0xFFE11D48, 0xFFFFFFFF, 0xFF9F1239, 14)
                delBtn.setOnClickListener(function()
                    vibrate(35)
                    stopPreview()
                    table.remove(merge_list, i)
                    refreshMergeUI()
                end)
                row.addView(delBtn)
                itemCard.addView(row)
                listContainer.addView(itemCard)
            end

            setT(subTitle, "Selected " .. tostring(#merge_list) .. " " .. typeWord .. " Files (Total: " .. formatDurationMs(totalMergedDur) .. "):")
            local nextNum = #merge_list + 1
            setT(addNextBtn, "Add " .. tostring(nextNum) .. " " .. typeWord)
        end

        addNextBtn.setOnClickListener(function()
            vibrate(35)
            local nextNum = #merge_list + 1
            showMediaListDialog(media_type, "Select " .. tostring(nextNum) .. " " .. typeWord, function(chosen)
                stopPreview()
                table.insert(merge_list, chosen)
                refreshMergeUI()
            end)
        end)

        refreshMergeUI()
        root.addView(mergeCard)

        if media_type == 1 then
            addVideoQualityCard(root, false, pal.card, pal.border)
        end

        addProfessionalPlayerCard(
            root,
            function() return merge_list[1] end,
            false,
            nil,
            nil,
            nil,
            function() return merge_list end,
            pal.card,
            pal.border
        )

        local startMergeBtn = createStyledButton("Merge Now", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        startMergeBtn.setOnClickListener(function() runProcess("merge") end)
        root.addView(startMergeBtn)

    -- 8. CUT OR TRIM WINDOW
    elseif op == "cut" or op == "trim" then
        local infoCard = createStyledCard(pal.card, pal.border, 22)

        local fileTV = TextView(ctx)
        setT(fileTV, primary_file and ("Selected: " .. primary_file.name .. " (" .. formatDurationMs(primary_file.duration) .. ")") or "No file selected")
        fileTV.setTextColor(STUDIO_WARM_GOLD)
        fileTV.setTypeface(nil, Typeface.BOLD)
        fileTV.setPadding(16, 14, 16, 14)
        fileTV.setBackground(brd(pal.bg, pal.border, 14))
        pcall(function() fileTV.setFocusable(true) end)
        infoCard.addView(fileTV)
        addSpacer(infoCard, 12)

        local changeFileBtn = createStyledButton("Change " .. typeWord, 0xFFD97706, 0xFFFFFFFF, 0xFFB45309, 18)
        infoCard.addView(changeFileBtn)
        addSpacer(infoCard, 12)

        local sBtn = createStyledButton("Start Time: " .. formatDurationMs(start_time_ms), 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
        infoCard.addView(sBtn)
        addSpacer(infoCard, 10)

        local eBtn = createStyledButton("End Time: " .. formatDurationMs(end_time_ms), 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
        infoCard.addView(eBtn)

        changeFileBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(media_type, "Select " .. typeWord, function(chosen)
                stopPreview()
                primary_file = chosen
                start_time_ms = 0
                end_time_ms = chosen.duration or 0
                setT(fileTV, "Selected: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
                setT(sBtn, "Start Time: 00:00.000")
                setT(eBtn, "End Time: " .. formatDurationMs(end_time_ms))
            end)
        end)

        sBtn.setOnClickListener(function()
            vibrate(35)
            local dur = primary_file and primary_file.duration or 0
            showTimeInputDialog(true, dur, function(val)
                start_time_ms = val
                setT(sBtn, "Start Time: " .. formatDurationMs(val))
                speak("Start time " .. formatDurationMs(val))
            end)
        end)

        eBtn.setOnClickListener(function()
            vibrate(35)
            local dur = primary_file and primary_file.duration or 0
            showTimeInputDialog(false, dur, function(val)
                end_time_ms = val
                setT(eBtn, "End Time: " .. formatDurationMs(val))
                speak("End time " .. formatDurationMs(val))
            end)
        end)

        root.addView(infoCard)

        if media_type == 1 then
            addVideoQualityCard(root, false, pal.card, pal.border)
        end

        addProfessionalPlayerCard(
            root,
            function() return primary_file end,
            true,
            function(pos)
                start_time_ms = pos
                setT(sBtn, "Start Time: " .. formatDurationMs(pos))
                speak("Start marked at " .. formatDurationMs(pos))
            end,
            function(pos)
                end_time_ms = pos
                setT(eBtn, "End Time: " .. formatDurationMs(pos))
                speak("End marked at " .. formatDurationMs(pos))
            end,
            nil,
            nil,
            pal.card,
            pal.border
        )

        local startOpBtn = createStyledButton(op == "cut" and "Cut Now" or "Trim Now", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        startOpBtn.setOnClickListener(function() runProcess(op) end)
        root.addView(startOpBtn)

    -- 9. SPLIT VIDEO WINDOW (2 VIDEOS ON 1 SCREEN)
    elseif op == "split_video" then
        local spCard = createStyledCard(pal.card, pal.border, 22)

        local v1TV = TextView(ctx)
        setT(v1TV, primary_file and ("1st Video: " .. primary_file.name .. " (" .. formatDurationMs(primary_file.duration) .. ")") or "1st Video: Not Selected")
        v1TV.setTextColor(STUDIO_WARM_GOLD)
        v1TV.setTypeface(nil, Typeface.BOLD)
        v1TV.setPadding(16, 14, 16, 14)
        v1TV.setBackground(brd(pal.bg, 0xFF10B981, 14))
        pcall(function() v1TV.setFocusable(true) end)
        spCard.addView(v1TV)
        addSpacer(spCard, 10)

        local pickV1Btn = createStyledButton("Select 1st Video", 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 18)
        pickV1Btn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(1, "Select 1st Video", function(chosen)
                stopPreview()
                primary_file = chosen
                setT(v1TV, "1st Video: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        spCard.addView(pickV1Btn)
        addSpacer(spCard, 14)

        local v2TV = TextView(ctx)
        setT(v2TV, secondary_file and ("2nd Video: " .. secondary_file.name .. " (" .. formatDurationMs(secondary_file.duration) .. ")") or "2nd Video: Not Selected")
        v2TV.setTextColor(STUDIO_NEON_CYAN)
        v2TV.setTypeface(nil, Typeface.BOLD)
        v2TV.setPadding(16, 14, 16, 14)
        v2TV.setBackground(brd(pal.bg, 0xFFA855F7, 14))
        pcall(function() v2TV.setFocusable(true) end)
        spCard.addView(v2TV)
        addSpacer(spCard, 10)

        local pickV2Btn = createStyledButton("Select 2nd Video", 0xFF7C3AED, 0xFFFFFFFF, 0xFF5B21B6, 18)
        pickV2Btn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(1, "Select 2nd Video", function(chosen)
                stopPreview()
                secondary_file = chosen
                setT(v2TV, "2nd Video: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        spCard.addView(pickV2Btn)
        addSpacer(spCard, 14)

        local layoutLbl = TextView(ctx)
        setT(layoutLbl, "Split Screen Layout:")
        layoutLbl.setTextColor(STUDIO_WARM_GOLD)
        layoutLbl.setTypeface(nil, Typeface.BOLD)
        pcall(function() layoutLbl.setFocusable(true) end)
        spCard.addView(layoutLbl)
        addSpacer(spCard, 6)

        local layoutSpin = Spinner(ctx)
        local layoutItems = String{
            "Top & Bottom (Upper & Lower Half Screen)",
            "Left & Right (Side by Side Half Screen)"
        }
        local lAdap = ArrayAdapter(ctx, android.R.layout.simple_spinner_dropdown_item, layoutItems)
        layoutSpin.setAdapter(lAdap)
        layoutSpin.setSelection(split_layout_mode)
        layoutSpin.setOnItemSelectedListener(AdapterView.OnItemSelectedListener{
            onItemSelected = function(p, v, pos, id)
                split_layout_mode = pos
            end
        })
        spCard.addView(createSpinnerContainer(layoutSpin, pal.border))
        root.addView(spCard)

        addVideoQualityCard(root, true, pal.card, pal.border)

        addProfessionalPlayerCard(
            root,
            function() return primary_file or secondary_file end,
            false,
            nil,
            nil,
            nil,
            nil,
            pal.card,
            pal.border
        )

        local startSplitVideoBtn = createStyledButton("Split Video Now", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        startSplitVideoBtn.setOnClickListener(function()
            vibrate(35)
            if not primary_file then
                Toast.makeText(ctx, "Please select 1st Video first", Toast.LENGTH_SHORT).show()
                speak("Please select 1st Video first")
                return
            end
            if not secondary_file then
                showMediaListDialog(1, "Select 2nd Video", function(chosen)
                    secondary_file = chosen
                    setT(v2TV, "2nd Video: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
                    runProcess("split_video")
                end)
                return
            end
            runProcess("split_video")
        end)
        root.addView(startSplitVideoBtn)

    -- 10. CHANGE AUDIO WINDOW
    elseif op == "change_audio" then
        local caCard = createStyledCard(pal.card, pal.border, 22)

        local vidTV = TextView(ctx)
        setT(vidTV, primary_file and ("Video: " .. primary_file.name) or "Video: Not Selected")
        vidTV.setTextColor(STUDIO_WARM_GOLD)
        vidTV.setTypeface(nil, Typeface.BOLD)
        vidTV.setPadding(16, 14, 16, 14)
        vidTV.setBackground(brd(pal.bg, 0xFF38BDF8, 14))
        pcall(function() vidTV.setFocusable(true) end)
        caCard.addView(vidTV)
        addSpacer(caCard, 10)

        local pickVidBtn = createStyledButton("Select Video", 0xFFD97706, 0xFFFFFFFF, 0xFFB45309, 18)
        pickVidBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(1, "Select Video", function(chosen)
                stopPreview()
                primary_file = chosen
                setT(vidTV, "Video: " .. chosen.name)
            end)
        end)
        caCard.addView(pickVidBtn)
        addSpacer(caCard, 14)

        local audTV = TextView(ctx)
        setT(audTV, secondary_file and ("New Audio: " .. secondary_file.name) or "New Audio: Not Selected")
        audTV.setTextColor(STUDIO_NEON_CYAN)
        audTV.setTypeface(nil, Typeface.BOLD)
        audTV.setPadding(16, 14, 16, 14)
        audTV.setBackground(brd(pal.bg, pal.border, 14))
        pcall(function() audTV.setFocusable(true) end)
        caCard.addView(audTV)
        addSpacer(caCard, 10)

        local pickAudBtn = createStyledButton("Select Audio", 0xFF7C3AED, 0xFFFFFFFF, 0xFF5B21B6, 18)
        pickAudBtn.setOnClickListener(function()
            vibrate(35)
            showMediaListDialog(0, "Select Audio", function(chosen)
                stopPreview()
                secondary_file = chosen
                setT(audTV, "New Audio: " .. chosen.name)
            end)
        end)
        caCard.addView(pickAudBtn)
        root.addView(caCard)

        addVideoQualityCard(root, false, pal.card, pal.border)

        addProfessionalPlayerCard(root, function() return primary_file end, false, nil, nil, nil, nil, pal.card, pal.border)

        local goBtn = createStyledButton("Change Audio Now", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        goBtn.setOnClickListener(function() runProcess("change_audio") end)
        root.addView(goBtn)

    -- 11. EXTRACT AUDIO OR SILENT VIDEO WINDOW
    elseif op == "extract" or op == "silent" then
        local exCard = createStyledCard(pal.card, pal.border, 22)

        local fileTV = TextView(ctx)
        setT(fileTV, primary_file and ("Selected: " .. primary_file.name .. " (" .. formatDurationMs(primary_file.duration) .. ")") or "No File Selected")
        fileTV.setTextColor(STUDIO_WARM_GOLD)
        fileTV.setTypeface(nil, Typeface.BOLD)
        fileTV.setPadding(16, 14, 16, 14)
        fileTV.setBackground(brd(pal.bg, pal.border, 14))
        pcall(function() fileTV.setFocusable(true) end)
        exCard.addView(fileTV)
        addSpacer(exCard, 12)

        local changeBtn = createStyledButton("Change File", 0xFFD97706, 0xFFFFFFFF, 0xFFB45309, 18)
        changeBtn.setOnClickListener(function()
            vibrate(35)
            local targetCat = (op == "silent" or op == "extract") and 1 or media_type
            showMediaListDialog(targetCat, "Select File", function(chosen)
                stopPreview()
                primary_file = chosen
                setT(fileTV, "Selected: " .. chosen.name .. " (" .. formatDurationMs(chosen.duration) .. ")")
            end)
        end)
        exCard.addView(changeBtn)
        root.addView(exCard)

        if op == "silent" then
            addVideoQualityCard(root, false, pal.card, pal.border)
        end

        addProfessionalPlayerCard(root, function() return primary_file end, false, nil, nil, nil, nil, pal.card, pal.border)

        local goBtn = createStyledButton(op == "extract" and "Extract Audio Now" or "Mute Video Now", 0xFF059669, 0xFFFFFFFF, 0xFF047857, 24)
        goBtn.setOnClickListener(function() runProcess(op) end)
        root.addView(goBtn)
    end

    activity.setContentView(scrollView)
end

local function onMainOperationButtonTap(op)
    vibrate(35)
    stopPreview()
    if op == "add_music" then
        openOperationWindow("add_music")
    elseif op == "voice_recorder" then
        openOperationWindow("voice_recorder")
    elseif op == "noise_remover" then
        -- Opens directly so user can EITHER Record Mic Voice OR Select Audio/Video!
        openOperationWindow("noise_remover")
    elseif op == "echo_studio" then
        -- Opens directly so user can EITHER Record Voice OR Select File!
        openOperationWindow("echo_studio")
    elseif op == "merge" then
        merge_list = {}
        local typeWord = (media_type == 0) and "Audio" or "Video"
        showMediaListDialog(media_type, "Select 1 " .. typeWord, function(chosen)
            table.insert(merge_list, chosen)
            openOperationWindow("merge")
        end)
    elseif op == "split_video" then
        primary_file = nil
        secondary_file = nil
        showMediaListDialog(1, "Select 1st Video", function(chosen1)
            primary_file = chosen1
            openOperationWindow("split_video")
        end)
    elseif op == "change_audio" then
        showMediaListDialog(1, "Select Video", function(chosen)
            primary_file = chosen
            openOperationWindow("change_audio")
        end)
    elseif op == "silent" or op == "extract" then
        showMediaListDialog(1, "Select Video", function(chosen)
            primary_file = chosen
            openOperationWindow(op)
        end)
    else
        local typeWord = (media_type == 0) and "Audio" or "Video"
        showMediaListDialog(media_type, "Select " .. typeWord, function(chosen)
            primary_file = chosen
            start_time_ms = 0
            end_time_ms = chosen.duration or 0
            openOperationWindow(op)
        end)
    end
end

-- ================= MAIN STUDIO WINDOW UI (Strict A-to-Z Alphabetical Studio Grid!) =================
showMainWindow = function()
    vibrate(35)
    stopPreview()
    activity.setTitle("Smart Media Studio Pro")

    local scrollView = ScrollView(ctx)
    scrollView.setLayoutParams(LinearLayout.LayoutParams(-1, -1))
    scrollView.setFillViewport(true)
    scrollView.setBackgroundColor(STUDIO_MAIN_BG)

    local root = LinearLayout(ctx)
    root.setOrientation(1)
    root.setPadding(24, 22, 24, 30)
    root.setBackgroundColor(STUDIO_MAIN_BG)
    scrollView.addView(root)

    local headerCard = LinearLayout(ctx)
    headerCard.setOrientation(1)
    headerCard.setPadding(24, 24, 24, 24)
    headerCard.setBackground(gradBrd(STUDIO_MAIN_HDR1, STUDIO_MAIN_HDR2, STUDIO_WARM_GOLD, 24, 3))
    local hdrLp = LinearLayout.LayoutParams(-1, -2)
    hdrLp.setMargins(0, 6, 0, 14)
    headerCard.setLayoutParams(hdrLp)

    local appTitleTV = TextView(ctx)
    setT(appTitleTV, "Smart Media Studio Pro")
    appTitleTV.setGravity(Gravity.CENTER)
    appTitleTV.setTextSize(22)
    appTitleTV.setTypeface(nil, Typeface.BOLD)
    appTitleTV.setTextColor(STUDIO_NEON_CYAN)
    pcall(function()
        appTitleTV.setFocusable(true)
        appTitleTV.setFocusableInTouchMode(true)
    end)
    headerCard.addView(appTitleTV)

    local subBannerTV = TextView(ctx)
    setT(subBannerTV, "Audio & Video Editor  |  Developer: Abdul Rehman")
    subBannerTV.setGravity(Gravity.CENTER)
    subBannerTV.setTextSize(13)
    subBannerTV.setTypeface(nil, Typeface.BOLD)
    subBannerTV.setTextColor(STUDIO_WARM_GOLD)
    subBannerTV.setPadding(0, 6, 0, 0)
    pcall(function() subBannerTV.setFocusable(true) end)
    headerCard.addView(subBannerTV)
    root.addView(headerCard)

    local topConfigCard = createStyledCard(STUDIO_MAIN_CARD, 0xFFA855F7, 22)

    local mediaLabel = TextView(ctx)
    setT(mediaLabel, "Media Type:")
    mediaLabel.setTextColor(STUDIO_WARM_GOLD)
    mediaLabel.setTypeface(nil, Typeface.BOLD)
    mediaLabel.setTextSize(14)
    pcall(function() mediaLabel.setFocusable(true) end)
    topConfigCard.addView(mediaLabel)
    addSpacer(topConfigCard, 6)

    local mediaSpinner = Spinner(ctx)
    local mediaItems = String{"Audio", "Video"}
    local mAdapter = ArrayAdapter(ctx, android.R.layout.simple_spinner_dropdown_item, mediaItems)
    mediaSpinner.setAdapter(mAdapter)
    mediaSpinner.setSelection(media_type)
    topConfigCard.addView(createSpinnerContainer(mediaSpinner, STUDIO_NEON_CYAN))

    addSpacer(topConfigCard, 12)

    local modeLabel = TextView(ctx)
    setT(modeLabel, "Select Mode:")
    modeLabel.setTextColor(STUDIO_WARM_GOLD)
    modeLabel.setTypeface(nil, Typeface.BOLD)
    modeLabel.setTextSize(14)
    pcall(function() modeLabel.setFocusable(true) end)
    topConfigCard.addView(modeLabel)
    addSpacer(topConfigCard, 6)

    local modeSpinner = Spinner(ctx)
    local modeItems = String{"Editing", "Add Music to Voice"}
    local modeAdapter = ArrayAdapter(ctx, android.R.layout.simple_spinner_dropdown_item, modeItems)
    modeSpinner.setAdapter(modeAdapter)
    modeSpinner.setSelection(app_mode)
    topConfigCard.addView(createSpinnerContainer(modeSpinner, 0xFFA855F7))

    root.addView(topConfigCard)

    local mainModeContainer = LinearLayout(ctx)
    mainModeContainer.setOrientation(1)
    root.addView(mainModeContainer)

    local editingCard = createStyledCard(STUDIO_MAIN_CARD, STUDIO_NEON_CYAN, 22)
    local musicToVoiceLayout = LinearLayout(ctx)
    musicToVoiceLayout.setOrientation(1)

    local lpLeft = LinearLayout.LayoutParams(0, -2, 1.0)
    lpLeft.setMargins(0, 0, 8, 0)
    local lpRight = LinearLayout.LayoutParams(0, -2, 1.0)
    lpRight.setMargins(8, 0, 0, 0)

    local function makeGridOpBtn(label, c1, c2, opKey, isLeft, isFullRow)
        local b = createStyledButton(label, c1, 0xFFFFFFFF, c2, 20)
        if isFullRow then
            b.setLayoutParams(LinearLayout.LayoutParams(-1, -2))
        else
            b.setLayoutParams(isLeft and lpLeft or lpRight)
        end
        b.setOnClickListener(function()
            onMainOperationButtonTap(opKey)
        end)
        return b
    end

    local function rebuildEditingButtons()
        editingCard.removeAllViews()

        local btnHintTV = TextView(ctx)
        setT(btnHintTV, (media_type == 0) and "Audio Tools:" or "Video Tools:")
        btnHintTV.setTextColor(STUDIO_NEON_CYAN)
        btnHintTV.setTypeface(nil, Typeface.BOLD)
        btnHintTV.setTextSize(15)
        btnHintTV.setPadding(0, 0, 0, 12)
        pcall(function() btnHintTV.setFocusable(true) end)
        editingCard.addView(btnHintTV)

        -- Clean, Simple Button Names in Alphabetical Order (C -> E -> M -> R -> S -> T -> V)
        local toolsList = {}
        if media_type == 0 then
            toolsList = {
                { label = "Convert Format", c1 = 0xFF4F46E5, c2 = 0xFF312E81, key = "converter" },
                { label = "Cut",            c1 = 0xFF0D9488, c2 = 0xFF115E59, key = "cut" },
                { label = "Echo Effects",   c1 = 0xFF059669, c2 = 0xFF064E3B, key = "echo_studio" },
                { label = "Extract Audio",  c1 = 0xFFD97706, c2 = 0xFF78350F, key = "extract" },
                { label = "Merge",          c1 = 0xFF7C3AED, c2 = 0xFF4C1D95, key = "merge" },
                { label = "Record Voice",   c1 = 0xFFE11D48, c2 = 0xFF881337, key = "voice_recorder" },
                { label = "Remove Noise",   c1 = 0xFF0284C7, c2 = 0xFF0C4A6E, key = "noise_remover" },
                { label = "Trim",           c1 = 0xFF2563EB, c2 = 0xFF1E3A8A, key = "trim" },
                { label = "Volume Booster", c1 = 0xFFEA580C, c2 = 0xFF7C2D12, key = "volume_booster" }
            }
        else
            toolsList = {
                { label = "Change Audio",   c1 = 0xFF6D28D9, c2 = 0xFF4C1D95, key = "change_audio" },
                { label = "Convert Format", c1 = 0xFF4F46E5, c2 = 0xFF312E81, key = "converter" },
                { label = "Cut",            c1 = 0xFF0D9488, c2 = 0xFF115E59, key = "cut" },
                { label = "Echo Effects",   c1 = 0xFF059669, c2 = 0xFF064E3B, key = "echo_studio" },
                { label = "Extract Audio",  c1 = 0xFFD97706, c2 = 0xFF78350F, key = "extract" },
                { label = "Merge",          c1 = 0xFF7C3AED, c2 = 0xFF4C1D95, key = "merge" },
                { label = "Record Voice",   c1 = 0xFFE11D48, c2 = 0xFF881337, key = "voice_recorder" },
                { label = "Remove Noise",   c1 = 0xFF0284C7, c2 = 0xFF0C4A6E, key = "noise_remover" },
                { label = "Silent Video",   c1 = 0xFFBE123C, c2 = 0xFF881337, key = "silent" },
                { label = "Split Video",    c1 = 0xFF047857, c2 = 0xFF064E3B, key = "split_video" },
                { label = "Trim",           c1 = 0xFF2563EB, c2 = 0xFF1E3A8A, key = "trim" },
                { label = "Volume Booster", c1 = 0xFFEA580C, c2 = 0xFF7C2D12, key = "volume_booster" }
            }
        end

        local i = 1
        while i <= #toolsList do
            local row = LinearLayout(ctx)
            row.setOrientation(0)
            local t1 = toolsList[i]
            local t2 = toolsList[i + 1]
            if t2 then
                row.addView(makeGridOpBtn(t1.label, t1.c1, t1.c2, t1.key, true, false))
                row.addView(makeGridOpBtn(t2.label, t2.c1, t2.c2, t2.key, false, false))
                i = i + 2
            else
                row.addView(makeGridOpBtn(t1.label, t1.c1, t1.c2, t1.key, true, true))
                i = i + 1
            end
            editingCard.addView(row)
            if i <= #toolsList then
                addSpacer(editingCard, 12)
            end
        end
    end

    local function renderSelectedMode(mIdx)
        stopPreview()
        app_mode = mIdx
        mainModeContainer.removeAllViews()
        if mIdx == 0 then
            rebuildEditingButtons()
            mainModeContainer.addView(editingCard)
        else
            buildMusicToVoiceCardUI(musicToVoiceLayout)
            mainModeContainer.addView(musicToVoiceLayout)
        end
    end

    mediaSpinner.setOnItemSelectedListener(AdapterView.OnItemSelectedListener{
        onItemSelected = function(p, v, pos, id)
            if media_type ~= pos then vibrate(35) end
            media_type = pos
            if app_mode == 0 then
                rebuildEditingButtons()
            end
        end
    })

    modeSpinner.setOnItemSelectedListener(AdapterView.OnItemSelectedListener{
        onItemSelected = function(p, v, pos, id)
            if app_mode ~= pos then vibrate(35) end
            renderSelectedMode(pos)
        end
    })

    addSpacer(root, 14)

    -- Bottom Row: [ ABOUT ] (Left)  |  [ EXIT ] (Right)
    local bottomRow = LinearLayout(ctx)
    bottomRow.setOrientation(0)
    bottomRow.setGravity(Gravity.CENTER)

    local aboutBtn = createStyledButton("ABOUT", 0xFF0284C7, 0xFFFFFFFF, 0xFF0369A1, 22)
    aboutBtn.setLayoutParams(lpLeft)
    aboutBtn.setOnClickListener(function()
        showAbout()
    end)
    bottomRow.addView(aboutBtn)

    local exitBtn = createStyledButton("EXIT", 0xFFE11D48, 0xFFFFFFFF, 0xFF9F1239, 22)
    exitBtn.setLayoutParams(lpRight)
    exitBtn.setOnClickListener(function()
        vibrate(40)
        stopPreview()
        stopOutputPreview()
        activity.finish()
    end)
    bottomRow.addView(exitBtn)

    root.addView(bottomRow)

    activity.setContentView(scrollView)
    task(50, function() pcall(function() if appTitleTV then appTitleTV.requestFocus() end end) end)
    renderSelectedMode(app_mode)
    checkPendingBackgroundTask()
end

function onDestroy()
    pcall(function() stopPreview() end)
    pcall(function() stopOutputPreview() end)
    pcall(function()
        if previewPlayer then previewPlayer.release() end
        if bgMusicPlayer then bgMusicPlayer.release() end
        if outVoicePlayer then outVoicePlayer.release() end
        if outMusicPlayer then outMusicPlayer.release() end
    end)
    pcall(function()
        if is_recording and mediaRecorder then
            mediaRecorder.stop()
            mediaRecorder.release()
        end
    end)
    pcall(function()
        if tts then tts.stop(); tts.shutdown() end
    end)
end

showMainWindow()
return true
