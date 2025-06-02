#include <M5Unified.h>
#include <WiFi.h>
#include <WebSocketsClient.h>
#include <ArduinoJson.h>
#include <mbedtls/sha256.h>
#include <uECC.h>  // micro-ecc ライブラリ
#include <time.h>  // 時刻取得用
#include "config.h"

#define NTP_TIMEZONE "JST-9"
#define NTP_SERVER1 "pool.ntp.org"
#define NTP_SERVER2 "ntp.nict.jp"
#define NTP_SERVER3 "time.google.com"

// WiFi設定
const char* ssid = WIFI_SSID;
const char* password = WIFI_PASSWORD;

// 秘密鍵（テスト用 - 本番では適切に生成・管理してください）
const char* private_key_hex = NOSTR_PRIVATE_KEY;
const int relay_port = 443;
const bool use_ssl = true;

// Nostr設定
const char* relay_url = "relay.damus.io";
WebSocketsClient webSocket;

// 秘密鍵と公開鍵
uint8_t private_key_bytes[32];
uint8_t public_key_bytes[64];  // 非圧縮形式
bool keys_initialized = false;


// mbedTLS用の構造体
mbedtls_ecp_group secp256k1_group;
mbedtls_entropy_context entropy;
mbedtls_ctr_drbg_context ctr_drbg;

// ESP32のハードウェアRNG使用（シグネチャ修正）
static int hardware_random(void* data, unsigned char* output, size_t len, size_t* olen) {
  esp_fill_random(output, len);
  *olen = len;  // 実際に生成されたバイト数
  return 0;     // 成功
}

// 決定論的ノンスkと公開鍵PのY座標のパリティ調整を考慮したBIP-340 Schnorr署名
String schnorrSign(const String& messageHash) {
  uint8_t msg[32];
  uint8_t privkey[32];
  hexStringToBytes(messageHash.c_str(), msg, 32);
  hexStringToBytes(NOSTR_PRIVATE_KEY, privkey, 32);

  mbedtls_ecp_group grp;
  mbedtls_ecp_group_init(&grp);
  mbedtls_ecp_group_load(&grp, MBEDTLS_ECP_DP_SECP256K1);

  mbedtls_mpi d, k, n, s, e;
  mbedtls_ecp_point R, P;
  mbedtls_mpi_init(&d);
  mbedtls_mpi_init(&k);
  mbedtls_mpi_init(&n);
  mbedtls_mpi_init(&s);
  mbedtls_mpi_init(&e);
  mbedtls_ecp_point_init(&R);
  mbedtls_ecp_point_init(&P);

  // 秘密鍵dと曲線の位数n
  mbedtls_mpi_read_binary(&d, privkey, 32);
  mbedtls_mpi_copy(&n, &grp.N);  // 曲線の位数Nを取得

  // 公開鍵P = d*G
  mbedtls_ecp_mul(&grp, &P, &d, &grp.G, NULL, NULL);  // P点の計算

  // BIP-340の決定論的ノンスkの生成 (RFC6979相当)
  // tag_hash = SHA256("BIP0340/challenge")
  uint8_t tag_hash[32];
  mbedtls_sha256_context sha_tag;
  mbedtls_sha256_init(&sha_tag);
  mbedtls_sha256_starts(&sha_tag, 0);
  mbedtls_sha256_update(&sha_tag, (const uint8_t*)"BIP0340/challenge", strlen("BIP0340/challenge"));
  mbedtls_sha256_finish(&sha_tag, tag_hash);
  mbedtls_sha256_free(&sha_tag);

  uint8_t hmac_key[64];  // PrivKey || tag_hash
  memcpy(hmac_key, privkey, 32);
  memcpy(hmac_key + 32, tag_hash, 32);

  mbedtls_md_context_t ctx_hmac;
  const mbedtls_md_info_t* md_info = mbedtls_md_info_from_type(MBEDTLS_MD_SHA256);
  mbedtls_md_init(&ctx_hmac);
  mbedtls_md_setup(&ctx_hmac, md_info, 1);  // hmac
  mbedtls_md_hmac_starts(&ctx_hmac, hmac_key, 64);
  mbedtls_md_hmac_update(&ctx_hmac, msg, 32);  // メッセージハッシュ
  uint8_t k_bytes[32];
  mbedtls_md_hmac_finish(&ctx_hmac, k_bytes);
  mbedtls_md_free(&ctx_hmac);

  mbedtls_mpi_read_binary(&k, k_bytes, 32);
  mbedtls_mpi_mod_mpi(&k, &k, &n);  // k = k mod N

  // R = k*G を計算
  mbedtls_ecp_mul(&grp, &R, &k, &grp.G, NULL, NULL);

  // R点のY座標が奇数であれば k = N - k とする
  uint8_t Ry_bytes[32];
  mbedtls_mpi_write_binary(&R.MBEDTLS_PRIVATE(Y), Ry_bytes, 32);
  if (Ry_bytes[31] % 2 != 0) {  // 最下位バイトの最下位ビットで判定
    mbedtls_mpi_sub_mpi(&k, &n, &k);
  }
  // R.xを再度計算 (R.xが更新された場合のため、または必要に応じて)
  mbedtls_ecp_mul(&grp, &R, &k, &grp.G, NULL, NULL);


  // e = H(R.x || P.x || msg)
  uint8_t Rx[32], Px[32];
  mbedtls_mpi_write_binary(&R.MBEDTLS_PRIVATE(X), Rx, 32);
  mbedtls_mpi_write_binary(&P.MBEDTLS_PRIVATE(X), Px, 32);

  uint8_t buf[96];  // R.x || P.x || msg
  memcpy(buf, Rx, 32);
  memcpy(buf + 32, Px, 32);
  memcpy(buf + 64, msg, 32);

  uint8_t e_bytes[32];
  mbedtls_sha256_context sha_e;
  mbedtls_sha256_init(&sha_e);
  mbedtls_sha256_starts(&sha_e, 0);
  mbedtls_sha256_update(&sha_e, buf, 96);
  mbedtls_sha256_finish(&sha_e, e_bytes);
  mbedtls_sha256_free(&sha_e);
  mbedtls_mpi_read_binary(&e, e_bytes, 32);
  mbedtls_mpi_mod_mpi(&e, &e, &n);  // e = e mod N

  // s = (k + e*d) mod N
  mbedtls_mpi_mul_mpi(&s, &e, &d);
  mbedtls_mpi_add_mpi(&s, &k, &s);
  mbedtls_mpi_mod_mpi(&s, &s, &n);

  // 署名 = (R.x, s)
  uint8_t signature[64];
  mbedtls_mpi_write_binary(&R.MBEDTLS_PRIVATE(X), signature, 32);
  mbedtls_mpi_write_binary(&s, signature + 32, 32);

  // クリーンアップ
  mbedtls_mpi_free(&d);
  mbedtls_mpi_free(&k);
  mbedtls_mpi_free(&n);
  mbedtls_mpi_free(&s);
  mbedtls_mpi_free(&e);
  mbedtls_ecp_point_free(&R);
  mbedtls_ecp_point_free(&P);
  mbedtls_ecp_group_free(&grp);

  return bytesToHexString(signature, 64);
}

// 16進文字列を小文字で返す関数
String bytesToHexString_lowercase(const uint8_t* byteArray, size_t length) {
  String result = "";
  for (size_t i = 0; i < length; i++) {
    if (byteArray[i] < 16) result += "0";
    result += String(byteArray[i], HEX);
  }
  result.toLowerCase();
  return result;
}


// SHA256計算
String calculateSHA256(const String& input) {
  uint8_t hash[32];
  mbedtls_sha256_context ctx;

  mbedtls_sha256_init(&ctx);
  mbedtls_sha256_starts(&ctx, 0);

  const uint8_t* input_bytes = (const uint8_t*)input.c_str();
  size_t input_len = input.length();

  Serial.printf("SHA256 input: %s\n", input.c_str());
  Serial.printf("SHA256 input byte length: %d\n", input_len);

  mbedtls_sha256_update(&ctx, input_bytes, input_len);
  mbedtls_sha256_finish(&ctx, hash);
  mbedtls_sha256_free(&ctx);

  String result = bytesToHexString_lowercase(hash, 32);
  Serial.println("SHA256 result: " + result);

  return result;
}
// イベント作成・送信関数の修正
void sendNostrEvent(const String& content) {
  time_t created_at = time(nullptr);
  String pubkey = NOSTR_PUBLIC_KEY;

  // イベントID計算用の文字列を生成
  String serialized = createEventForSigning(pubkey, created_at, 1, content);
  String id = calculateSHA256(serialized);

  // Schnorr署名
  String sig = schnorrSign(id);

  // イベントJSON作成
  String event = "{\"id\":\"" + id + "\",\"pubkey\":\"" + pubkey + "\",\"created_at\":" + String(created_at) + ",\"kind\":1,\"tags\":[],\"content\":\"" + content + "\",\"sig\":\"" + sig + "\"}";

  // WebSocketで送信
  String message = "[\"EVENT\"," + event + "]";
  webSocket.sendTXT(message);
}

void syncTimeAndSetRTC() {
  Serial.println("Starting NTP sync...");
  configTzTime(NTP_TIMEZONE, NTP_SERVER1, NTP_SERVER2, NTP_SERVER3);

  M5.Lcd.println("NTP同期中...");
  Serial.print("Sync status: ");

#if SNTP_ENABLED
  while (sntp_get_sync_status() != SNTP_SYNC_STATUS_COMPLETED) {
    Serial.print(".");
    M5.Lcd.print(".");
    delay(1000);
  }
#else
  struct tm timeinfo;
  int retries = 0;
  while (!getLocalTime(&timeinfo, 1000) && retries < 60) {
    Serial.print(".");
    M5.Lcd.print(".");
    delay(1000);
    retries++;
  }
#endif

  Serial.println("\nTime synchronized!");
  M5.Lcd.println("\n時刻同期完了!");

  time_t now = time(nullptr);
  Serial.printf("Unix timestamp: %lu\n", (unsigned long)now);

  struct tm* p_timeinfo = localtime(&now);
  if (p_timeinfo != nullptr) {
    Serial.printf("JST: %04d/%02d/%02d %02d:%02d:%02d\n",
                  p_timeinfo->tm_year + 1900,
                  p_timeinfo->tm_mon + 1,
                  p_timeinfo->tm_mday,
                  p_timeinfo->tm_hour,
                  p_timeinfo->tm_min,
                  p_timeinfo->tm_sec);

    M5.Rtc.setDateTime({ { (uint16_t)(p_timeinfo->tm_year + 1900),
                           (uint8_t)(p_timeinfo->tm_mon + 1),
                           (uint8_t)p_timeinfo->tm_mday },
                         { (uint8_t)p_timeinfo->tm_hour,
                           (uint8_t)p_timeinfo->tm_min,
                           (uint8_t)p_timeinfo->tm_sec } });
  }
}
// uECC用の乱数生成関数
static int rng_function(uint8_t* dest, unsigned size) {
  // ESP32のハードウェアRNGを使用
  esp_fill_random(dest, size);
  return 1;  // 成功を示す
}
String createEventForSigning(const String& pubkey, uint64_t created_at, int kind, const String& content) {
  // NIP-01仕様：[0,"<pubkey>",created_at,kind,[],"<content>"]
  // スペースなし、数値は文字列化しない
  String eventString = "[0,\"" + pubkey + "\"," + String(created_at) + "," + String(kind) + ",[],\"" + escapeJsonString(content) + "\"]";

  return eventString;
}

// JSON文字列エスケープ
String escapeJsonString(const String& input) {
  String escaped = "";
  for (unsigned int i = 0; i < input.length(); i++) {
    char c = input.charAt(i);
    switch (c) {
      case '"': escaped += "\\\""; break;
      case '\\': escaped += "\\\\"; break;
      case '\b': escaped += "\\b"; break;
      case '\f': escaped += "\\f"; break;
      case '\n': escaped += "\\n"; break;
      case '\r': escaped += "\\r"; break;
      case '\t': escaped += "\\t"; break;
      default:
        if (c < 0x20) {
          char buf[7];
          snprintf(buf, sizeof(buf), "\\u%04x", c);
          escaped += buf;
        } else {
          escaped += c;
        }
    }
  }
  return escaped;
}
void setup() {
  M5.begin();
  Serial.begin(115200);
  delay(1000);  // シリアル初期化待ち

  M5.Lcd.setTextSize(2);
  M5.Lcd.println("Nostr Client Starting...");

  // micro-ecc ライブラリの初期化
  Serial.println("Initializing micro-ecc...");
  uECC_set_rng(&rng_function);  // RNG関数を設定

  // WiFi接続
  WiFi.begin(ssid, password);
  while (WiFi.status() != WL_CONNECTED) {
    delay(1000);
    M5.Lcd.println("Connecting to WiFi...");
  }
  M5.Lcd.println("WiFi Connected!");

  // NTP時刻同期の設定
  syncTimeAndSetRTC();
  M5.Lcd.println("Time sync started...");

  // 時刻同期を待つ
  struct tm timeinfo;
  int retry = 0;
  while (!getLocalTime(&timeinfo) && retry < 10) {
    delay(1000);
    retry++;
    M5.Lcd.print(".");
  }
  if (retry < 10) {
    M5.Lcd.println("\nTime synchronized!");
  } else {
    M5.Lcd.println("\nTime sync failed!");
  }

  // 秘密鍵と公開鍵の設定
  setupKeys();

  // WebSocket接続
  webSocket.setReconnectInterval(5000);
  if (use_ssl) {
    webSocket.beginSSL(relay_url, relay_port, "/");
  } else {
    webSocket.begin(relay_url, relay_port, "/");
  }

  webSocket.onEvent(webSocketEvent);

  M5.Lcd.println("Press Button A to post!");
}

void loop() {
  M5.update();
  webSocket.loop();

  // ボタンAで投稿
  if (M5.BtnA.wasPressed()) {
    if (keys_initialized) {
      String content = "Hello from M5Stack!";
      sendNostrEvent(content);
    } else {
      M5.Lcd.println("Keys not initialized!");
    }
    delay(1000);  // デバウンス
  }
}

void setupKeys() {

  Serial.println("Setting up keys...");

  M5.Lcd.println("Setting up keys...");



  // micro-eccライブラリの初期化

  if (!uECC_make_key(public_key_bytes, private_key_bytes, uECC_secp256k1())) {

    Serial.println("Failed to initialize uECC");

    return;
  }



  // 秘密鍵を16進文字列からバイト配列に変換

  if (strlen(private_key_hex) != 64) {

    Serial.println("Invalid private key length!");

    M5.Lcd.println("Invalid key length!");

    return;
  }



  hexStringToBytes(private_key_hex, private_key_bytes, 32);



  // 秘密鍵が有効かチェック

  const struct uECC_Curve_t* curve = uECC_secp256k1();



  // デバッグ: 秘密鍵の確認

  Serial.print("Private key: ");

  for (int i = 0; i < 32; i++) {

    Serial.printf("%02x", private_key_bytes[i]);
  }

  Serial.println();



  // 公開鍵の生成

  if (!uECC_compute_public_key(private_key_bytes, public_key_bytes, curve)) {

    Serial.println("Failed to compute public key!");

    return;
  }





  keys_initialized = true;

  Serial.println("Keys initialized successfully");

  M5.Lcd.println("Keys initialized");



  // デバッグ: 公開鍵の確認

  Serial.print("Public key: ");

  for (int i = 0; i < 64; i++) {

    Serial.printf("%02x", public_key_bytes[i]);
  }

  Serial.println();



  String pubkey_hex = getPublicKeyHex();

  Serial.println("Pubkey hex: " + pubkey_hex);

  M5.Lcd.println("Pubkey: " + pubkey_hex.substring(0, 16) + "...");
}



String createEventForSigning(DynamicJsonDocument& event) {
  // Nostr仕様に従った署名用配列の作成
  DynamicJsonDocument signing_array(1024);
  signing_array.add(0);  // reserved
  signing_array.add(event["pubkey"]);
  signing_array.add(event["created_at"]);
  signing_array.add(event["kind"]);
  signing_array.add(event["tags"]);
  signing_array.add(event["content"]);

  String result;
  serializeJson(signing_array, result);
  return result;
}

String calculateEventId(String event_json) {
  // SHA256ハッシュの計算
  uint8_t hash[32];
  mbedtls_sha256_context ctx;
  mbedtls_sha256_init(&ctx);
  mbedtls_sha256_starts(&ctx, 0);
  mbedtls_sha256_update(&ctx, (uint8_t*)event_json.c_str(), event_json.length());
  mbedtls_sha256_finish(&ctx, hash);
  mbedtls_sha256_free(&ctx);

  return bytesToHexString(hash, 32);
}

String signEvent(String event_id) {
  Serial.println("Starting signature generation...");

  // イベントIDをバイト配列に変換
  uint8_t hash[32];
  hexStringToBytes(event_id.c_str(), hash, 32);

  Serial.print("Hash to sign: ");
  for (int i = 0; i < 32; i++) {
    Serial.printf("%02x", hash[i]);
  }
  Serial.println();

  // 秘密鍵が有効かもう一度確認
  const struct uECC_Curve_t* curve = uECC_secp256k1();


  // 公開鍵も再確認
  uint8_t test_pubkey[64];
  if (!uECC_compute_public_key(private_key_bytes, test_pubkey, curve)) {
    Serial.println("Cannot compute public key from private key!");
    return "";
  }

  Serial.print("Private key for signing: ");
  for (int i = 0; i < 32; i++) {
    Serial.printf("%02x", private_key_bytes[i]);
  }
  Serial.println();

  // 署名バッファ
  uint8_t signature[64];

  // 単一の署名試行（より詳細なデバッグ付き）
  Serial.println("Attempting signature...");

  // RNGの初期化（必要に応じて）
  randomSeed(analogRead(0) + millis());

  if (uECC_sign(private_key_bytes, hash, 32, signature, curve)) {
    Serial.println("Signature generation successful!");

    // 署名を表示
    Serial.print("Generated signature: ");
    for (int i = 0; i < 64; i++) {
      Serial.printf("%02x", signature[i]);
    }
    Serial.println();

    // 署名の検証
    if (uECC_verify(public_key_bytes, hash, 32, signature, curve)) {
      Serial.println("Signature verification successful!");
      return bytesToHexString(signature, 64);
    } else {
      Serial.println("Signature verification failed!");

      // 公開鍵での再検証を試行
      if (uECC_verify(test_pubkey, hash, 32, signature, curve)) {
        Serial.println("Signature verified with recomputed public key!");
        return bytesToHexString(signature, 64);
      } else {
        Serial.println("Signature verification failed even with recomputed public key!");
      }
    }
  } else {
    Serial.println("Signature generation failed!");

    // エラー診断
    Serial.println("Diagnostic information:");
    Serial.printf("Curve pointer: %p\n", curve);
    Serial.printf("Hash pointer: %p\n", hash);
    Serial.printf("Private key pointer: %p\n", private_key_bytes);
    Serial.printf("Signature pointer: %p\n", signature);

    // メモリ確認
    Serial.printf("Free heap: %d bytes\n", ESP.getFreeHeap());
  }

  return "";  // 署名失敗
}

void sendToRelay(DynamicJsonDocument& event) {
  // REQメッセージの作成
  DynamicJsonDocument message(1536);
  message.add("EVENT");
  message.add(event);

  String json_string;
  serializeJson(message, json_string);

  Serial.println("Sending to relay: " + json_string);

  // WebSocketで送信
  webSocket.sendTXT(json_string);

  M5.Lcd.println("Note posted!");
  M5.Lcd.println("Content:");
  M5.Lcd.println(event["content"].as<String>());
}

void webSocketEvent(WStype_t type, uint8_t* payload, size_t length) {
  switch (type) {
    case WStype_DISCONNECTED:
      Serial.println("WebSocket Disconnected");
      M5.Lcd.println("WebSocket Disconnected");
      break;
    case WStype_CONNECTED:
      Serial.printf("WebSocket Connected to: %s\n", payload);
      M5.Lcd.println("WebSocket Connected");
      break;
    case WStype_TEXT:
      Serial.printf("Received: %s\n", payload);
      M5.Lcd.printf("Received: %s\n", payload);
      break;
    case WStype_ERROR:
      Serial.printf("WebSocket Error: %s\n", payload);
      M5.Lcd.println("WebSocket Error");
      break;
    default:
      break;
  }
}

// ユーティリティ関数
long getCurrentTimestamp() {
  struct tm timeinfo;
  if (!getLocalTime(&timeinfo)) {
    // NTP同期失敗時は概算値を返す
    Serial.println("Failed to get local time, using approximate timestamp");
    return millis() / 1000 + 1640000000;  // 2022年1月1日からの概算
  }
  time_t timestamp = mktime(&timeinfo);
  return (long)timestamp;
}

String getPublicKeyHex() {
  // x座標のみを返す（Nostr仕様）
  return bytesToHexString(public_key_bytes, 32);
}

void hexStringToBytes(const char* hex_string, uint8_t* bytes, size_t length) {
  for (size_t i = 0; i < length; i++) {
    char temp[3] = { 0 };
    temp[0] = hex_string[i * 2];
    temp[1] = hex_string[i * 2 + 1];
    bytes[i] = (uint8_t)strtol(temp, NULL, 16);
  }
}

String bytesToHexString(const uint8_t* bytes, size_t length) {
  String result = "";
  for (size_t i = 0; i < length; i++) {
    if (bytes[i] < 16) result += "0";
    result += String(bytes[i], HEX);
  }
  result.toLowerCase();  // Nostrでは小文字が標準
  return result;
}