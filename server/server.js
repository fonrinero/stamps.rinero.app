'use strict';

const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const os = require('node:os');
const zlib = require('node:zlib');
const { execFileSync } = require('node:child_process');
const http2 = require('node:http2');
const mysql = require('mysql2/promise');
const QRCode = require('qrcode');
const { PNG } = require('pngjs');

const root = __dirname;
// Keep secrets beside the backend, outside htdocs: /home/<site-user>/rinero-platform/.env.
// Process environment values override the private file when configured by a runner.
try {
  const envFile = fs.readFileSync(process.env.RINERO_ENV_FILE || path.join(root, '.env'), 'utf8');
  for (const line of envFile.split(/\r?\n/)) {
    const match = line.match(/^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)\s*$/);
    if (!match || process.env[match[1]]) continue;
    const value = match[2].replace(/^(['"])(.*)\1$/, '$2');
    process.env[match[1]] = value;
  }
} catch (error) {
  if (error.code !== 'ENOENT') throw error;
}
const port = Number.parseInt(process.env.PORT || '3000', 10);
const publicRoot = path.resolve(process.env.RINERO_PUBLIC_DIR || path.join(root, 'public'));
const pool = mysql.createPool({
  host: process.env.DB_HOST,
  port: Number.parseInt(process.env.DB_PORT || '3306', 10),
  user: process.env.DB_USER,
  password: process.env.DB_PASSWORD,
  database: process.env.DB_NAME,
  waitForConnections: true,
  connectionLimit: 10,
  queueLimit: 0,
  charset: 'utf8mb4',
});
const mimeTypes = { '.html':'text/html; charset=utf-8','.css':'text/css; charset=utf-8','.js':'text/javascript; charset=utf-8','.json':'application/json; charset=utf-8','.svg':'image/svg+xml','.png':'image/png','.ico':'image/x-icon' };
const id = () => crypto.randomUUID();
const hash = value => crypto.createHash('sha256').update(value).digest();
const randomToken = () => crypto.randomBytes(32).toString('base64url');
const ISO_COUNTRY_CODES = new Set('AD AE AF AG AI AL AM AO AQ AR AS AT AU AW AX AZ BA BB BD BE BF BG BH BI BJ BL BM BN BO BQ BR BS BT BV BW BY BZ CA CC CD CF CG CH CI CK CL CM CN CO CR CU CV CW CX CY CZ DE DJ DM DO DZ EC EE EG ES FI FK FM FO FR GB GD GE GG GI GL GM GP GQ GR GT GU GY HK HN HR HT HU ID IE IL IM IN IO IS IT JE JM JO JP KE KG KN KP KR KW KZ LA LC LI LK LR LT LU LV MA MC MD ME MF MG MH MK ML MM MN MO MP MQ MR MS MT MU MV MW MX MY MZ NA NC NE NF NG NI NL NO NP NR NU NZ OM PA PE PF PG PH PK PL PM PN PR PS PT PW PY QA RE RO RS RU RW SA SB SC SG SI SK SL SM SN SO SR SV SX SY SZ TC TF TH TJ TK TL TM TN TR TT TW TZ UA UG US UY UZ VA VC VE VG VN VU WF WS YE YT ZA ZW'.split(' '));
const base64url = value => Buffer.from(value).toString('base64url');
const walletConfig = {
  applePassType: process.env.APPLE_PASS_TYPE_IDENTIFIER || '',
  appleTeam: process.env.APPLE_TEAM_IDENTIFIER || '',
  appleOrg: process.env.APPLE_ORGANIZATION_NAME || 'Rinero Stamps',
  appleCert: process.env.APPLE_SIGNER_CERT_PATH || '',
  appleKey: process.env.APPLE_SIGNER_KEY_PATH || '',
  appleWwdr: process.env.APPLE_WWDR_CERT_PATH || '',
  appleAuthSecret: process.env.APPLE_AUTH_SECRET || '',
  googleIssuer: process.env.GOOGLE_WALLET_ISSUER_ID || '',
  googleEmail: process.env.GOOGLE_WALLET_SERVICE_ACCOUNT_EMAIL || '',
  googleKeyPath: process.env.GOOGLE_WALLET_PRIVATE_KEY_PATH || '',
  cardTokenSecret: process.env.CARD_TOKEN_SECRET || '',
  appleApnsKey: process.env.APPLE_APNS_KEY_PATH || '',
  appleApnsKeyId: process.env.APPLE_APNS_KEY_ID || '',
  appleApnsEnvironment: process.env.APPLE_APNS_ENV === 'sandbox' ? 'sandbox' : 'production',
};
const sessionCookie = 'rinero_session';
const customerCardCookie = 'rinero_customer_card';
const production = process.env.NODE_ENV === 'production';
const isAgencyRole = role => role === 'owner' || role === 'admin';
const requestLimits = new Map();
const appleWalletHandoffTickets = new Map();
const stampCooldownDurationSeconds = 3 * 60 * 60;
function isLimited(key, max, duration) {
  const now=Date.now();const entry=requestLimits.get(key);
  if(requestLimits.size>5000){for(const [stored,value] of requestLimits)if(now-value.start>60*60_000)requestLimits.delete(stored);}
  if(!entry||now-entry.start>duration){requestLimits.set(key,{start:now,count:1});return false;}
  entry.count+=1;return entry.count>max;
}
function remoteAddress(req) {
  const cloudflare=req.headers['cf-connecting-ip'];
  return typeof cloudflare==='string'&&cloudflare.length<64?cloudflare:req.socket.remoteAddress||'unknown';
}
function stampCooldownRemaining(lastStampAt) {
  const last = Number(lastStampAt || 0);
  return last ? Math.max(0, last + stampCooldownDurationSeconds - Math.floor(Date.now() / 1000)) : 0;
}
function stampCooldownMessage(remainingSeconds) {
  const minutes = Math.max(1, Math.ceil(remainingSeconds / 60));
  const hours = Math.floor(minutes / 60);
  const remainder = minutes % 60;
  return `One stamp per card every 3 hours. Try again in ${hours ? `${hours}h ` : ''}${remainder}m.`;
}

function send(res, status, data, headers = {}) {
  const body = Buffer.from(JSON.stringify(data));
  res.writeHead(status, { 'Content-Type':'application/json; charset=utf-8','Content-Length':body.length,'Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Referrer-Policy':'strict-origin-when-cross-origin',...headers });
  res.end(body);
}
function getCookie(req, name) {
  const item = (req.headers.cookie || '').split(';').map(part => part.trim()).find(part => part.startsWith(`${name}=`));
  return item ? decodeURIComponent(item.slice(name.length + 1)) : '';
}
function setCookie(res, token, expires) {
  const age = Math.max(0, Math.floor((expires.getTime() - Date.now()) / 1000));
  res.setHeader('Set-Cookie', `${sessionCookie}=${encodeURIComponent(token)}; Path=/; HttpOnly; SameSite=Lax; Max-Age=${age}${production ? '; Secure' : ''}`);
}
function setAnonymousCookie(res, token) {
  res.setHeader('Set-Cookie', `rinero_anon=${encodeURIComponent(token)}; Path=/; HttpOnly; SameSite=Lax; Max-Age=63072000${production ? '; Secure' : ''}`);
}
function setCustomerCardCookie(res, cardId) {
  const expires=Math.floor(Date.now()/1000)+63072000,payload=`${cardId}.${expires}`;
  const signature=crypto.createHmac('sha256',walletConfig.cardTokenSecret).update(`customer-card:${payload}`).digest('base64url');
  res.setHeader('Set-Cookie', `${customerCardCookie}=${encodeURIComponent(`${payload}.${signature}`)}; Path=/api; HttpOnly; SameSite=Lax; Max-Age=63072000${production ? '; Secure' : ''}`);
}
function clearCustomerCardCookie(res) {
  res.setHeader('Set-Cookie', `${customerCardCookie}=; Path=/api; HttpOnly; SameSite=Lax; Max-Age=0${production ? '; Secure' : ''}`);
}
function customerCardIdFromCookie(req) {
  const [cardId,expiresText,signature]=getCookie(req,customerCardCookie).split('.');
  if(!/^[0-9a-f-]{36}$/i.test(cardId||'')||!/^\d{10}$/.test(expiresText||'')||Number(expiresText)<=Math.floor(Date.now()/1000)||!signature||walletConfig.cardTokenSecret.length<32)return '';
  const payload=`${cardId}.${expiresText}`,expected=crypto.createHmac('sha256',walletConfig.cardTokenSecret).update(`customer-card:${payload}`).digest('base64url');
  const actualBuffer=Buffer.from(signature),expectedBuffer=Buffer.from(expected);
  return actualBuffer.length===expectedBuffer.length&&crypto.timingSafeEqual(actualBuffer,expectedBuffer)?cardId:'';
}
async function resolveCustomerCardId(req,res,suppliedToken='') {
  const token=text(suppliedToken,100);
  if(!token)return customerCardIdFromCookie(req);
  if(!/^[A-Za-z0-9_-]{40,50}$/.test(token))return '';
  const [rows]=await pool.execute('SELECT c.id FROM loyalty_cards c LEFT JOIN wallet_card_tokens wt ON wt.card_id=c.id WHERE c.token_hash=? OR wt.token_hash=? LIMIT 1',[hash(token),hash(token)]);
  if(!rows.length)return '';
  setCustomerCardCookie(res,rows[0].id);
  return rows[0].id;
}
function clearCookie(res) { res.setHeader('Set-Cookie', `${sessionCookie}=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0${production ? '; Secure' : ''}`); }
async function readJson(req, maxBytes = 16_384) {
  let size = 0; const chunks = [];
  for await (const chunk of req) { size += chunk.length; if (size > maxBytes) throw Object.assign(new Error('Request too large.'), { status:413 }); chunks.push(chunk); }
  if (!size) return {};
  try { return JSON.parse(Buffer.concat(chunks).toString('utf8')); } catch { throw Object.assign(new Error('Invalid JSON.'), { status:400 }); }
}
function text(value, max = 160) { return typeof value === 'string' ? value.trim().slice(0, max) : ''; }
function email(value) { const candidate = text(value, 254).toLowerCase(); return /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(candidate) ? candidate : ''; }
function encryptCustomerContact(value) {
  const secret=process.env.CUSTOMER_DATA_KEY||'';
  if(secret.length<32)throw Object.assign(new Error('Identified cards are not available yet: the administrator must configure the customer-data encryption key.'),{status:503});
  const key=crypto.createHash('sha256').update(secret).digest();const iv=crypto.randomBytes(12);const cipher=crypto.createCipheriv('aes-256-gcm',key,iv);const encrypted=Buffer.concat([cipher.update(value,'utf8'),cipher.final()]);return Buffer.concat([iv,cipher.getAuthTag(),encrypted]);
}
function anonymousCardToken(browserToken,cardId) { return crypto.createHmac('sha256',browserToken).update(`rinero-card:${cardId}`).digest('base64url'); }
function cardExpiryDate(firstStampAt,months) {
  const duration=Number(months);if(!firstStampAt||![1,3,6,12].includes(duration))return null;
  const date=new Date(firstStampAt);if(Number.isNaN(date.getTime()))return null;
  const day=date.getDate();date.setDate(1);date.setMonth(date.getMonth()+duration);const lastDay=new Date(date.getFullYear(),date.getMonth()+1,0).getDate();date.setDate(Math.min(day,lastDay));return date;
}
function rewardExpiryDate(lastStampAt,progress,required) { const last=Number(lastStampAt||0);if(!last||Number(progress)<Number(required))return null;return new Date(last*1000+3*60*60*1000); }
function cardValidUntil(card) { const dates=[cardExpiryDate(card.first_stamp_at,card.expiry_months),card.collection_mode==='anonymous'?null:rewardExpiryDate(card.last_stamp_at,card.progress,card.stamps_required)].filter(Boolean);return dates.length?new Date(Math.min(...dates.map(date=>date.getTime()))):null; }
function cardIsExpired(firstStampAt,months,lastStampAt=0,progress=0,required=Infinity,collectionMode='identified') { const expiresAt=cardExpiryDate(firstStampAt,months),rewardExpiresAt=collectionMode==='anonymous'?null:rewardExpiryDate(lastStampAt,progress,required);return Boolean((expiresAt&&Date.now()>=expiresAt.getTime())||(rewardExpiresAt&&Date.now()>=rewardExpiresAt.getTime())); }
async function refreshCardExpiry(card) { if(card&&card.card_status==='active'&&cardIsExpired(card.first_stamp_at,card.expiry_months,card.last_stamp_at,card.progress,card.stamps_required,card.collection_mode)){await pool.execute("UPDATE loyalty_cards SET card_status='expired' WHERE id=? AND card_status='active'",[card.id]);card.card_status='expired';}return card; }
async function passwordHash(password) {
  const salt = crypto.randomBytes(16);
  const key = await new Promise((resolve, reject) => crypto.scrypt(password, salt, 64, { N:32768,r:8,p:1,maxmem:64*1024*1024 }, (error, result) => error ? reject(error) : resolve(result)));
  return `scrypt$32768$${salt.toString('base64url')}$${key.toString('base64url')}`;
}
async function passwordMatches(password, encoded) {
  const [algorithm, cost, saltValue, keyValue] = String(encoded || '').split('$');
  if (algorithm !== 'scrypt' || cost !== '32768' || !saltValue || !keyValue) return false;
  const salt = Buffer.from(saltValue, 'base64url'); const expected = Buffer.from(keyValue, 'base64url');
  const actual = await new Promise((resolve, reject) => crypto.scrypt(password, salt, expected.length, { N:32768,r:8,p:1,maxmem:64*1024*1024 }, (error, result) => error ? reject(error) : resolve(result)));
  return expected.length === actual.length && crypto.timingSafeEqual(expected, actual);
}
async function createSession(userId, agencyId, businessId, res) {
  const token = randomToken(); const expires = new Date(Date.now() + 14 * 86400_000);
  await pool.execute('INSERT INTO web_sessions (token_hash,user_id,agency_id,active_business_id,expires_at) VALUES (?,?,?,?,?)', [hash(token),userId,agencyId,businessId,expires]);
  setCookie(res, token, expires);
}
async function getSession(req) {
  const token = getCookie(req, sessionCookie); if (!token) return null;
  const [rows] = await pool.execute(
    `SELECT u.id AS user_id,u.email,s.agency_id,s.active_business_id AS business_id,
      am.access_role AS agency_role,bm.id AS business_membership_id,bm.access_role AS business_role
     FROM web_sessions s JOIN users u ON u.id=s.user_id
     LEFT JOIN agency_memberships am ON am.agency_id=s.agency_id AND am.user_id=u.id AND am.active=1
     LEFT JOIN business_memberships bm ON bm.business_id=s.active_business_id AND bm.user_id=u.id AND bm.active=1
     WHERE s.token_hash=? AND s.expires_at>CURRENT_TIMESTAMP AND u.active=1 LIMIT 1`, [hash(token)]);
  return rows[0] || null;
}
function requireAgencyAdmin(user) {
  if (!user || !user.agency_id || !['owner','admin'].includes(user.agency_role)) throw Object.assign(new Error('Agency owner access is required.'), { status:403 });
}
function requireBusinessAccess(user) {
  if (!user || !user.business_id || (!user.business_membership_id && !['owner','admin','support'].includes(user.agency_role))) throw Object.assign(new Error('Select a client business first.'), { status:403 });
}
function requireBusinessManager(user) {
  requireBusinessAccess(user);
  if (!['owner','manager'].includes(user.business_role) && !['owner','admin'].includes(user.agency_role)) throw Object.assign(new Error('Your account cannot make this change.'), { status:403 });
}

function crc32(buffer) {
  let crc = 0xffffffff;
  for (const byte of buffer) {
    crc ^= byte;
    for (let bit = 0; bit < 8; bit += 1) crc = (crc >>> 1) ^ (0xedb88320 & -(crc & 1));
  }
  return (crc ^ 0xffffffff) >>> 0;
}
function pngChunk(type, data) {
  const name=Buffer.from(type),chunk=Buffer.alloc(12+data.length);
  chunk.writeUInt32BE(data.length,0);name.copy(chunk,4);data.copy(chunk,8);chunk.writeUInt32BE(crc32(Buffer.concat([name,data])),8+data.length);return chunk;
}
function hexTriplet(value,fallback) {
  const hex=/^#[0-9a-f]{6}$/i.test(value||'')?value:fallback;
  return [parseInt(hex.slice(1,3),16),parseInt(hex.slice(3,5),16),parseInt(hex.slice(5,7),16)];
}
const artworkCache=new Map();
function defaultWalletArtwork(background='#101722',accent='#ff762e',width=716,height=896) {
  const cacheKey=`${background}:${accent}:${width}x${height}`;if(artworkCache.has(cacheKey))return artworkCache.get(cacheKey);
  const navy=hexTriplet(background,'#101722'),orange=hexTriplet(accent,'#ff762e'),cyan=[8,151,200];
  const raw=Buffer.alloc((width*3+1)*height);
  for(let y=0;y<height;y++){
    const row=y*(width*3+1);raw[row]=0;
    for(let x=0;x<width;x++){
      const nx=x/width,ny=y/height,pos=row+1+x*3;
      let color=navy;
      const cyanBand=nx*0.75+ny*0.5<0.82;
      if(cyanBand){const blend=Math.min(0.7,0.18+nx*0.28+ny*0.18);color=navy.map((v,i)=>Math.round(v*(1-blend)+cyan[i]*blend));}
      const ribbon=nx+ny>1.08&&nx+ny<1.33;
      if(ribbon){const shade=0.78+Math.min(0.2,nx*0.16);color=orange.map(v=>Math.round(v*shade));}
      if(ny>0.68&&!ribbon){const shade=Math.max(0.62,1-(ny-0.68)*0.75);color=color.map(v=>Math.round(v*shade));}
      raw[pos]=color[0];raw[pos+1]=color[1];raw[pos+2]=color[2];
    }
  }
  const ihdr=Buffer.alloc(13);ihdr.writeUInt32BE(width,0);ihdr.writeUInt32BE(height,4);ihdr[8]=8;ihdr[9]=2;
  const png=Buffer.concat([Buffer.from([137,80,78,71,13,10,26,10]),pngChunk('IHDR',ihdr),pngChunk('IDAT',zlib.deflateSync(raw,{level:7})),pngChunk('IEND',Buffer.alloc(0))]);
  if(artworkCache.size>30)artworkCache.clear();artworkCache.set(cacheKey,png);return png;
}
function zipFiles(files) {
  const local = [], central = [];
  let offset = 0;
  for (const [name, raw] of Object.entries(files)) {
    const filename = Buffer.from(name);
    const source = Buffer.isBuffer(raw) ? raw : Buffer.from(raw);
    const compressed = zlib.deflateRawSync(source);
    const checksum = crc32(source);
    const localHeader = Buffer.alloc(30);
    localHeader.writeUInt32LE(0x04034b50, 0); localHeader.writeUInt16LE(20, 4); localHeader.writeUInt16LE(0x0800, 6);
    localHeader.writeUInt16LE(8, 8); localHeader.writeUInt32LE(checksum, 14); localHeader.writeUInt32LE(compressed.length, 18);
    localHeader.writeUInt32LE(source.length, 22); localHeader.writeUInt16LE(filename.length, 26);
    local.push(localHeader, filename, compressed);
    const centralHeader = Buffer.alloc(46);
    centralHeader.writeUInt32LE(0x02014b50, 0); centralHeader.writeUInt16LE(20, 4); centralHeader.writeUInt16LE(20, 6);
    centralHeader.writeUInt16LE(0x0800, 8); centralHeader.writeUInt16LE(8, 10); centralHeader.writeUInt32LE(checksum, 16);
    centralHeader.writeUInt32LE(compressed.length, 20); centralHeader.writeUInt32LE(source.length, 24);
    centralHeader.writeUInt16LE(filename.length, 28); centralHeader.writeUInt32LE(offset, 42);
    central.push(centralHeader, filename);
    offset += localHeader.length + filename.length + compressed.length;
  }
  const centralBytes = Buffer.concat(central);
  const end = Buffer.alloc(22);
  end.writeUInt32LE(0x06054b50, 0); end.writeUInt16LE(Object.keys(files).length, 8); end.writeUInt16LE(Object.keys(files).length, 10);
  end.writeUInt32LE(centralBytes.length, 12); end.writeUInt32LE(offset, 16);
  return Buffer.concat([...local, centralBytes, end]);
}
function appleReady() {
  return Boolean(walletConfig.applePassType && walletConfig.appleTeam && walletConfig.appleCert && walletConfig.appleKey && walletConfig.appleWwdr && walletConfig.appleAuthSecret.length>=32 && walletConfig.appleApnsKey && walletConfig.appleApnsKeyId && [walletConfig.appleCert,walletConfig.appleKey,walletConfig.appleWwdr,walletConfig.appleApnsKey].every(file=>fs.existsSync(file)));
}
function googleReady() { return Boolean(walletConfig.googleIssuer && walletConfig.googleEmail && walletConfig.googleKeyPath && fs.existsSync(walletConfig.googleKeyPath)); }
function applePassToken(cardId) {
  if (!walletConfig.appleAuthSecret) return '';
  return crypto.createHmac('sha256', walletConfig.appleAuthSecret).update(cardId).digest('base64url');
}
function cssRgb(hex) {
  const value=/^#[0-9a-f]{6}$/i.test(hex||'')?hex:'#101722';
  return `rgb(${parseInt(value.slice(1,3),16)}, ${parseInt(value.slice(3,5),16)}, ${parseInt(value.slice(5,7),16)})`;
}
function resizePng(source,width,height) {
  const input=PNG.sync.read(source);
  const output=new PNG({width,height});
  const scale=Math.min(width/input.width,height/input.height);
  const drawWidth=Math.max(1,Math.round(input.width*scale));
  const drawHeight=Math.max(1,Math.round(input.height*scale));
  const offsetX=Math.floor((width-drawWidth)/2),offsetY=Math.floor((height-drawHeight)/2);
  for(let y=0;y<drawHeight;y++){
    const sy=(y+0.5)*input.height/drawHeight-0.5,y0=Math.max(0,Math.floor(sy)),y1=Math.min(input.height-1,y0+1),fy=Math.max(0,sy-y0);
    for(let x=0;x<drawWidth;x++){
      const sx=(x+0.5)*input.width/drawWidth-0.5,x0=Math.max(0,Math.floor(sx)),x1=Math.min(input.width-1,x0+1),fx=Math.max(0,sx-x0);
      const samples=[[y0*input.width+x0,(1-fx)*(1-fy)],[y0*input.width+x1,fx*(1-fy)],[y1*input.width+x0,(1-fx)*fy],[y1*input.width+x1,fx*fy]];
      let alpha=0,red=0,green=0,blue=0;
      for(const [pixel,weight] of samples){const at=pixel*4,a=input.data[at+3]/255,w=weight*a;alpha+=weight*a;red+=input.data[at]*w;green+=input.data[at+1]*w;blue+=input.data[at+2]*w;}
      const to=((y+offsetY)*width+x+offsetX)*4;
      output.data[to+3]=Math.round(alpha*255);
      if(alpha>0){output.data[to]=Math.round(red/alpha);output.data[to+1]=Math.round(green/alpha);output.data[to+2]=Math.round(blue/alpha);}
    }
  }
  return PNG.sync.write(output,{deflateLevel:9,filterType:4});
}
function artworkVariants(source) {
  const input=PNG.sync.read(source);
  const scale=Math.min(1,716/input.width,896/input.height);
  const width=Math.max(1,Math.round(input.width*scale)),height=Math.max(1,Math.round(input.height*scale));
  return {
    one:resizePng(source,Math.max(1,Math.round(width/2)),Math.max(1,Math.round(height/2))),
    two:resizePng(source,width,height),
    three:resizePng(source,Math.max(1,Math.round(width*1.5)),Math.max(1,Math.round(height*1.5))),
  };
}
function compositePng(baseSource,overlaySource,x,y) {
  const base=PNG.sync.read(baseSource),overlay=PNG.sync.read(overlaySource);
  for(let oy=0;oy<overlay.height;oy++)for(let ox=0;ox<overlay.width;ox++){
    const dx=x+ox,dy=y+oy;if(dx<0||dy<0||dx>=base.width||dy>=base.height)continue;
    const src=(oy*overlay.width+ox)*4,dst=(dy*base.width+dx)*4,alpha=overlay.data[src+3]/255;
    if(!alpha)continue;const oldAlpha=base.data[dst+3]/255,outAlpha=alpha+oldAlpha*(1-alpha);
    for(let channel=0;channel<3;channel++)base.data[dst+channel]=Math.round((overlay.data[src+channel]*alpha+base.data[dst+channel]*oldAlpha*(1-alpha))/outAlpha);
    base.data[dst+3]=Math.round(outAlpha*255);
  }
  return PNG.sync.write(base,{deflateLevel:9,filterType:4});
}
function googleWalletLogo(source,backgroundColor) {
  const square=defaultWalletArtwork(backgroundColor,'#ffffff',660,660);
  const logo=resizePng(source,462,462),image=PNG.sync.read(logo);
  return compositePng(square,logo,Math.floor((660-image.width)/2),Math.floor((660-image.height)/2));
}
function googleWalletHero(source,backgroundColor) {
  const frame=defaultWalletArtwork(backgroundColor,'#ffffff',1032,812),art=resizePng(source,1032,812),image=PNG.sync.read(art);
  return compositePng(frame,art,Math.floor((1032-image.width)/2),Math.floor((812-image.height)/2));
}
function decodePngDataUrl(value,label) {
  if(!value)return null;
  const match=String(value).match(/^data:image\/png;base64,([A-Za-z0-9+/=]+)$/);
  if(!match)throw Object.assign(new Error(`Choose a PNG ${label}.`),{status:400});
  const data=Buffer.from(match[1],'base64');
  const maxImageBytes=label==='card artwork'?700_000:750_000;if(data.length>maxImageBytes)throw Object.assign(new Error(`The ${label} exceeds the ${Math.round(maxImageBytes/1000)} KB Wallet limit.`),{status:413});
  if(data.length<24||!data.subarray(0,8).equals(Buffer.from([137,80,78,71,13,10,26,10])))throw Object.assign(new Error('That image file is invalid.'),{status:400});
  const width=data.readUInt32BE(16),height=data.readUInt32BE(20);
  if(!width||!height||width>4096||height>4096||width*height>24_000_000)throw Object.assign(new Error('The PNG dimensions are invalid or too large.'),{status:400});
  try{PNG.sync.read(data);}catch{throw Object.assign(new Error(`The ${label} PNG is damaged or cannot be decoded. Choose it again; the editor will prepare a valid Wallet image.`),{status:400});}
  return data;
}
function walletArtworkWithLiveStamps(source,card,logoSource) {
  const image=PNG.sync.read(resizePng(source,716,896));
  const accent=hexTriplet(card.accent_color,'#ff812f'),foreground=hexTriplet(card.foreground_color,'#f8f5ef');
  const progress=Math.max(0,Math.min(10,Number(card.progress)||0));
  const total=Math.max(1,Number(card.stamps_required)||10);
  const earned=Math.min(10,Math.round(progress/total*10));
  const setPixel=(x,y,color,alpha=1)=>{
    if(x<0||y<0||x>=image.width||y>=image.height)return;
    const at=(Math.floor(y)*image.width+Math.floor(x))*4,oldAlpha=image.data[at+3]/255,outAlpha=alpha+oldAlpha*(1-alpha);
    if(!outAlpha)return;
    image.data[at]=Math.round((color[0]*alpha+image.data[at]*oldAlpha*(1-alpha))/outAlpha);
    image.data[at+1]=Math.round((color[1]*alpha+image.data[at+1]*oldAlpha*(1-alpha))/outAlpha);
    image.data[at+2]=Math.round((color[2]*alpha+image.data[at+2]*oldAlpha*(1-alpha))/outAlpha);
    image.data[at+3]=Math.round(outAlpha*255);
  };
  const line=(x0,y0,x1,y1,color,width=4)=>{
    const steps=Math.max(Math.abs(x1-x0),Math.abs(y1-y0),1);
    for(let step=0;step<=steps;step++){
      const x=x0+(x1-x0)*step/steps,y=y0+(y1-y0)*step/steps,r=Math.ceil(width/2);
      for(let dy=-r;dy<=r;dy++)for(let dx=-r;dx<=r;dx++)if(dx*dx+dy*dy<=r*r)setPixel(Math.round(x+dx),Math.round(y+dy),color,1);
    }
  };
  let stampImage=null;
  try{
    const data=card.editor_config?.stampArtworkDataUrl;
    if(typeof data==='string'&&data.startsWith('data:image/png;base64,'))stampImage=PNG.sync.read(resizePng(decodePngDataUrl(data,'stamp artwork'),60,60));
  }catch{stampImage=null;}
  const diameter=76,gap=32,startX=(716-(5*diameter+4*gap))/2,radius=diameter/2;
  for(let index=0;index<10;index++){
    const row=Math.floor(index/5),column=index%5,cx=Math.round(startX+column*(diameter+gap)+radius),cy=Math.round((60+row*9)*896/100),isEarned=index<earned;
    for(let dy=-radius;dy<=radius;dy++)for(let dx=-radius;dx<=radius;dx++){
      const distance=Math.hypot(dx,dy);if(distance>radius)continue;
      if(distance>=radius-3)setPixel(cx+dx,cy+dy,accent,.98);
      else if(isEarned)setPixel(cx+dx,cy+dy,accent,.98);
      else setPixel(cx+dx,cy+dy,foreground,.08);
    }
    if(stampImage){
      const offsetX=cx-Math.floor(stampImage.width/2),offsetY=cy-Math.floor(stampImage.height/2);
      for(let y=0;y<stampImage.height;y++)for(let x=0;x<stampImage.width;x++){
        const at=(y*stampImage.width+x)*4,alpha=stampImage.data[at+3]/255;
        if(alpha)setPixel(offsetX+x,offsetY+y,[stampImage.data[at],stampImage.data[at+1],stampImage.data[at+2]],alpha*(isEarned?1:.28));
      }
    }else if(isEarned){
      const markColor=accent.reduce((sum,value)=>sum+value,0)>390?[20,37,54]:[255,248,238];
      line(cx-14,cy,cx-4,cy+11,markColor,7);line(cx-4,cy+11,cx+16,cy-14,markColor,7);
    }
  }
  // Poster Generic's native primary-logo slot is deliberately small (max 126 pt).
  // Bake the shop logo into the poster art instead, using the same editor placement
  // and size so the Wallet face can show it prominently without a duplicate.
  if(logoSource){
    const position=card.editor_config?.logoPosition||{};
    const savedX=Number(position.x)||50,savedY=Number(position.y)||10;
    // The previous editor's default was centered at 50%, 10%. Shift that
    // untouched default left while retaining any position the shop chose.
    const logoCenterX=savedX===50&&savedY===10?39:savedX;
    const centerX=Math.round(image.width*logoCenterX/100);
    const centerY=Math.round(image.height*(Number(position.y)||10)/100);
    const maxWidth=Math.round(image.width*Math.max(16,Math.min(94,Number(position.width)||82))/100);
    const maxHeight=Math.round(image.height*.44);
    const logo=PNG.sync.read(resizePng(logoSource,maxWidth,maxHeight));
    const offsetX=Math.round(centerX-logo.width/2),offsetY=Math.round(centerY-logo.height/2);
    for(let y=0;y<logo.height;y++)for(let x=0;x<logo.width;x++){
      const at=(y*logo.width+x)*4,alpha=logo.data[at+3]/255;
      if(!alpha)continue;
      const destX=offsetX+x,destY=offsetY+y;
      if(destX<0||destY<0||destX>=image.width||destY>=image.height)continue;
      const to=(destY*image.width+destX)*4,oldAlpha=image.data[to+3]/255,outAlpha=alpha+oldAlpha*(1-alpha);
      image.data[to]=Math.round((logo.data[at]*alpha+image.data[to]*oldAlpha*(1-alpha))/outAlpha);
      image.data[to+1]=Math.round((logo.data[at+1]*alpha+image.data[to+1]*oldAlpha*(1-alpha))/outAlpha);
      image.data[to+2]=Math.round((logo.data[at+2]*alpha+image.data[to+2]*oldAlpha*(1-alpha))/outAlpha);
      image.data[to+3]=Math.round(outAlpha*255);
    }
  }
  return PNG.sync.write(image,{deflateLevel:8,filterType:4});
}
function walletCardToken(cardId) {
  if (!walletConfig.cardTokenSecret) throw Object.assign(new Error('Wallet card links are not configured yet.'), { status:503 });
  return crypto.createHmac('sha256', walletConfig.cardTokenSecret).update(`wallet:${cardId}`).digest('base64url');
}
function googleArtworkSignature(cardId) {
  if (!walletConfig.cardTokenSecret) throw Object.assign(new Error('Wallet card links are not configured yet.'), { status:503 });
  return crypto.createHmac('sha256', walletConfig.cardTokenSecret).update(`google-artwork:${cardId}`).digest('base64url');
}
async function ensureWalletCardToken(cardId) {
  const token = walletCardToken(cardId);
  await pool.execute('INSERT INTO wallet_card_tokens (card_id,token_hash) VALUES (?,?) ON DUPLICATE KEY UPDATE token_hash=VALUES(token_hash)', [cardId, hash(token)]);
  return token;
}
function appleAuthorized(cardId, req) {
  const supplied = String(req.headers.authorization || '').replace(/^ApplePass\s+/, '');
  const expected = applePassToken(cardId);
  if (!supplied || !expected) return false;
  const actualBuffer = Buffer.from(supplied); const expectedBuffer = Buffer.from(expected);
  return actualBuffer.length === expectedBuffer.length && crypto.timingSafeEqual(actualBuffer, expectedBuffer);
}
async function getCardForWallet(token) {
  const [rows] = await pool.execute(`SELECT c.id,c.card_status,p.collection_mode,p.expiry_months,(SELECT MIN(se.created_at) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp') AS first_stamp_at,(SELECT UNIX_TIMESTAMP(MAX(se.created_at)) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp' AND (p.collection_mode<>'anonymous' OR se.created_at>COALESCE((SELECT MAX(r.created_at) FROM stamp_events r WHERE r.card_id=c.id AND r.event_type='reward_redeemed'),'1970-01-01'))) AS last_stamp_at,c.business_id,p.promotion_family_id,p.id AS program_id,p.name AS program_name,p.visit_label,p.stamps_required,p.reward_description,
      l.name AS location_name,b.name AS business_name,b.business_type,b.default_language,
      COALESCE(d.background_color,'#101722') AS background_color,COALESCE(d.foreground_color,'#ffffff') AS foreground_color,COALESCE(d.accent_color,'#4accff') AS accent_color,d.logo_mime,d.logo_data,d.artwork_mime,d.artwork_data,d.editor_config,UNIX_TIMESTAMP(d.updated_at) AS design_updated,
      (SELECT COUNT(*) FROM stamp_events e WHERE e.card_id=c.id AND e.event_type='stamp' AND (p.collection_mode<>'anonymous' OR e.created_at>COALESCE((SELECT MAX(r.created_at) FROM stamp_events r WHERE r.card_id=c.id AND r.event_type='reward_redeemed'),'1970-01-01'))) AS progress,
      COALESCE((SELECT UNIX_TIMESTAMP(MAX(e.created_at)) FROM stamp_events e WHERE e.card_id=c.id),UNIX_TIMESTAMP(c.created_at)) AS last_updated
    FROM loyalty_cards c JOIN loyalty_programs p ON p.id=c.program_id JOIN locations l ON l.id=p.location_id JOIN businesses b ON b.id=c.business_id LEFT JOIN loyalty_card_designs d ON d.promotion_family_id=p.promotion_family_id AND d.business_id=b.id
    LEFT JOIN wallet_card_tokens wt ON wt.card_id=c.id
    WHERE (c.token_hash=? OR wt.token_hash=?) AND l.active=1 AND b.active=1 LIMIT 1`, [hash(token), hash(token)]);
  if (!rows[0]) return null;
  if(typeof rows[0].editor_config==='string')try{rows[0].editor_config=JSON.parse(rows[0].editor_config);}catch{rows[0].editor_config=null;}
  await refreshCardExpiry(rows[0]);
  rows[0].customer_token = walletCardToken(rows[0].id);
  return rows[0];
}
async function buildApplePass(card) {
  if (!appleReady()) throw Object.assign(new Error('Apple Wallet is not configured yet. The Rinero administrator must add the Apple pass certificate and signing key.'), { status:503 });
  const token = applePassToken(card.id);
  const cardCopies=card.editor_config?.cardTextByLanguage||{};
  const localizedCopy=(language,key,fallback)=>String(cardCopies[language]?.[key]||cardCopies.en?.[key]||fallback);
  const appleString=value=>JSON.stringify(String(value));
  const localizedPassStrings=language=>{const contents=`\"CARD_STAMPS_LABEL\" = ${appleString(localizedCopy(language,'stampsLabel',language==='el'?'ΟΙ ΣΦΡΑΓΙΔΕΣ ΣΑΣ':language==='es'?'TUS SELLOS':'YOUR STAMPS'))};\n\"CARD_REWARD_LABEL\" = ${appleString(localizedCopy(language,'rewardLabel',language==='el'?'ΕΠΟΜΕΝΗ ΑΝΤΑΜΟΙΒΗ':language==='es'?'PRÓXIMO BENEFICIO':'NEXT REWARD'))};\n`;return Buffer.concat([Buffer.from([0xff,0xfe]),Buffer.from(contents,'utf16le')]);};
  const rewardReady=card.card_status==='active'&&Number(card.progress)>=Number(card.stamps_required);
  const rewardStatus=rewardReady?`🎉 REWARD READY · ${String(card.reward_description).slice(0,90)}`:card.card_status==='completed'?'Reward redeemed':card.card_status==='expired'?'Reward expired':card.reward_description;
  const pass = {
    formatVersion: 1,
    passTypeIdentifier: walletConfig.applePassType,
    serialNumber: card.id,
    teamIdentifier: walletConfig.appleTeam,
    organizationName: card.business_name,
    description: `${card.business_name} loyalty card`,
    foregroundColor: cssRgb(card.foreground_color),
    labelColor: cssRgb(card.accent_color),
    backgroundColor: cssRgb(card.background_color),
    generic: {
      headerFields: rewardReady ? [{ key:'reward_ready', label:'REWARD READY', value:String(card.reward_description).slice(0,90) }] : [],
      primaryFields: [{ key: 'progress', label: card.card_status==='completed'?'COMPLETED':'CARD_STAMPS_LABEL', value: `${Math.min(Number(card.progress),Number(card.stamps_required))} / ${Number(card.stamps_required)}` }],
      secondaryFields: [{ key: 'location', label: 'LOCATION', value: card.location_name }],
      auxiliaryFields: [{ key: 'reward', label: card.card_status==='completed'||card.card_status==='expired'?'STATUS':'CARD_REWARD_LABEL', value: rewardStatus }],
      backFields: [{ key: 'program', label: 'LOYALTY PROGRAM', value: card.program_name }, { key: 'business', label: 'BUSINESS', value: card.business_name }],
    },
    posterGeneric: {
      headerFields: [],
      primaryFields: [{ key: 'visits', label: card.card_status==='completed'?'COMPLETED':'CARD_STAMPS_LABEL', value: `${Math.min(Number(card.progress),Number(card.stamps_required))} / ${Number(card.stamps_required)}` }],
      footerFields: [{ key: 'reward', label: 'CARD_REWARD_LABEL', value: card.reward_description }],
      backFields: [{ key: 'location', label: 'LOCATION', value: card.location_name }, { key: 'program', label: 'PROGRAM', value: card.program_name }],
    },
    webServiceURL: `https://${process.env.PUBLIC_HOST || 'stamps.rinero.app'}/api/wallet/apple`,
    authenticationToken: token,
  };
  const passExpiry=cardValidUntil(card);if(card.card_status==='completed'||card.card_status==='expired')pass.expirationDate=(passExpiry&&passExpiry.getTime()<=Date.now()?passExpiry:new Date()).toISOString();else if(passExpiry)pass.expirationDate=passExpiry.toISOString();
  // No customer-card QR is embedded in Wallet. Shop QR/NFC touchpoints remain separate.
  const sourceLogo=card.logo_data?Buffer.from(card.logo_data):defaultWalletArtwork(card.background_color,card.accent_color,256,256);
  const icon1x=resizePng(sourceLogo,29,29),icon2x=resizePng(sourceLogo,58,58),icon3x=resizePng(sourceLogo,87,87);
  const logo1x=resizePng(sourceLogo,160,50),logo2x=resizePng(sourceLogo,320,100),logo3x=resizePng(sourceLogo,480,150);
  const artworkSource=card.artwork_data?Buffer.from(card.artwork_data):defaultWalletArtwork(card.background_color,card.accent_color,716,896);
  const artwork=artworkVariants(walletArtworkWithLiveStamps(artworkSource,card,card.logo_data?sourceLogo:null));
  const strip=defaultWalletArtwork(card.background_color,card.accent_color,375,144);
  const strip2x=defaultWalletArtwork(card.background_color,card.accent_color,750,288);
  const strip3x=defaultWalletArtwork(card.background_color,card.accent_color,1125,432);
  const files = {
    'pass.json': Buffer.from(JSON.stringify(pass)),
    'en.lproj/pass.strings': localizedPassStrings('en'),
    'el.lproj/pass.strings': localizedPassStrings('el'),
    'es.lproj/pass.strings': localizedPassStrings('es'),
    'icon.png': icon1x,
    'icon@2x.png': icon2x,
    'icon@3x.png': icon3x,
    'logo.png': logo1x,
    'logo@2x.png': logo2x,
    'logo@3x.png': logo3x,
    'artwork.png': artwork.one,
    'artwork@2x.png': artwork.two,
    'artwork@3x.png': artwork.three,
    'strip.png': strip,
    'strip@2x.png': strip2x,
    'strip@3x.png': strip3x,
  };
  const manifest = Object.fromEntries(Object.entries(files).map(([name, contents]) => [name, crypto.createHash('sha1').update(contents).digest('hex')]));
  files['manifest.json'] = Buffer.from(JSON.stringify(manifest));
  const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'rinero-pass-'));
  try {
    const manifestPath = path.join(tempDir, 'manifest.json'); const signaturePath = path.join(tempDir, 'signature');
    fs.writeFileSync(manifestPath, files['manifest.json']);
    // Keep CMS signed attributes: Apple Wallet requires the signingTime attribute.
    execFileSync('openssl', ['smime', '-sign', '-binary', '-in', manifestPath, '-signer', walletConfig.appleCert, '-inkey', walletConfig.appleKey, '-certfile', walletConfig.appleWwdr, '-out', signaturePath, '-outform', 'DER'], { stdio: 'pipe' });
    files.signature = fs.readFileSync(signaturePath);
  } catch (error) {
    console.error('Apple pass signing failed:', error.message);
    throw Object.assign(new Error('Apple Wallet signing failed. Check the certificate and private key files.'), { status:503 });
  } finally { fs.rmSync(tempDir, { recursive: true, force: true }); }
  return zipFiles(files);
}
function googleSign(payload, privateKey) {
  const header = base64url(JSON.stringify({ alg: 'RS256', typ: 'JWT' }));
  const body = base64url(JSON.stringify(payload));
  const unsigned = `${header}.${body}`;
  const signature = crypto.sign('RSA-SHA256', Buffer.from(unsigned), privateKey).toString('base64url');
  return `${unsigned}.${signature}`;
}
function googleObject(card) {
  const issuer = walletConfig.googleIssuer;
  // Keep the Loyalty IDs separate from any Generic passes issued by older builds.
  const classId = `${issuer}.loyalty_program_${card.program_id.replaceAll('-', '')}`;
  const objectId = `${issuer}.loyalty_card_${card.id.replaceAll('-', '')}`;
  const origin = `https://${process.env.PUBLIC_HOST || 'stamps.rinero.app'}`;
  const artworkVersion=[card.last_updated||0,card.progress||0,card.card_status||'active'].join('-');
  const cardArtworkUrl=`${origin}/api/wallet/google/artwork/${card.id}?sig=${encodeURIComponent(googleArtworkSignature(card.id))}&v=${encodeURIComponent(artworkVersion)}`;
  const expiresAt=cardValidUntil(card);
  const background=/^#[0-9a-f]{6}$/i.test(card.background_color||'')?card.background_color:'#101722';
  const imageDescription={defaultValue:{language:'en',value:`${card.business_name} logo`}};
  const rewardReady=card.card_status==='active'&&Number(card.progress)>=Number(card.stamps_required);
  const loyaltyClass={
    id:classId,
    issuerName:'Rinero Stamps',
    reviewStatus:'UNDER_REVIEW',
    programName:text(card.business_name,160)||'Loyalty card',
    programLogo:{sourceUri:{uri:`${origin}/api/loyalty-card-design/google-logo/${card.promotion_family_id}?v=${card.design_updated||0}`},contentDescription:imageDescription},
    heroImage:{sourceUri:{uri:`${origin}/api/loyalty-card-design/google-artwork/${card.promotion_family_id}?v=${card.design_updated||0}`},contentDescription:{defaultValue:{language:'en',value:`${card.business_name} loyalty card`}}},
    hexBackgroundColor:background,
  };
  const loyaltyObject={
    classId,
    id:objectId,
    state:card.card_status==='completed'?'COMPLETED':card.card_status==='expired'?'EXPIRED':'ACTIVE',
    loyaltyPoints:{label:text(card.editor_config?.cardTextByLanguage?.[card.default_language]?.stampsLabel,32)||text(card.editor_config?.cardTextByLanguage?.en?.stampsLabel,32)||text(card.visit_label,9)||'Visits',balance:{int:Math.min(Number(card.progress)||0,Number(card.stamps_required)||10)}},
    // Intentionally no accountName, accountId, barcode, or customer QR code.
    textModulesData:[
      {id:'offer',header:'Offer',body:text(card.program_name,160)},
      {id:'reward',header:rewardReady?'🎉 REWARD READY':text(card.editor_config?.cardTextByLanguage?.[card.default_language]?.rewardLabel,32)||text(card.editor_config?.cardTextByLanguage?.en?.rewardLabel,32)||'Reward',body:card.card_status==='expired'?'Reward expired':rewardReady?`${text(card.reward_description,300)} · Show this card at the till`:text(card.reward_description,500)},
      {id:'location',header:'Location',body:text(card.location_name,160)},
    ],
    ...(expiresAt?{validTimeInterval:{start:{dateTime:new Date(card.first_stamp_at).toISOString()},end:{dateTime:expiresAt.toISOString()}}}:{}),
    heroImage:{sourceUri:{uri:cardArtworkUrl},contentDescription:{defaultValue:{language:'en',value:`${card.business_name} loyalty card with current stamps`}}},
  };
  return {loyaltyClass,loyaltyObject};
}
let googleAccessToken = null;
async function googleToken() {
  if (googleAccessToken && googleAccessToken.expiry > Date.now() + 60_000) return googleAccessToken.value;
  const key = JSON.parse(fs.readFileSync(walletConfig.googleKeyPath, 'utf8'));
  if (key.client_email !== walletConfig.googleEmail || !key.private_key) throw new Error('Google Wallet service account file does not match its configured email.');
  const now = Math.floor(Date.now() / 1000);
  const assertion = googleSign({ iss: key.client_email, scope: 'https://www.googleapis.com/auth/wallet_object.issuer', aud: 'https://oauth2.googleapis.com/token', iat: now, exp: now + 3600 }, key.private_key);
  const response = await fetch('https://oauth2.googleapis.com/token', { method: 'POST', headers: { 'content-type': 'application/x-www-form-urlencoded' }, body: new URLSearchParams({ grant_type: 'urn:ietf:params:oauth:grant-type:jwt-bearer', assertion }) });
  const result = await response.json();
  if (!response.ok || !result.access_token) throw new Error(`Google Wallet authorization failed (${response.status}).`);
  googleAccessToken = { value: result.access_token, expiry: Date.now() + Number(result.expires_in || 3600) * 1000 };
  return result.access_token;
}
async function updateGooglePass(card) {
  if (!googleReady()) {
    console.warn('Google Wallet update skipped: issuer credentials are not fully configured.');
    return;
  }
  try {
    const accessToken = await googleToken();
    const {loyaltyClass,loyaltyObject}=googleObject(card);
    const classDesignPatch={programLogo:loyaltyClass.programLogo,hexBackgroundColor:loyaltyClass.hexBackgroundColor};
    const classResponse=await fetch(`https://walletobjects.googleapis.com/walletobjects/v1/loyaltyClass/${encodeURIComponent(loyaltyClass.id)}`,{method:'PATCH',headers:{authorization:`Bearer ${accessToken}`,'content-type':'application/json'},body:JSON.stringify(classDesignPatch)});
    if(!classResponse.ok){const details=await classResponse.text();console.error(`Google Wallet class design update failed (HTTP ${classResponse.status}):`,details.slice(0,1500));}
    loyaltyObject.notifyPreference='NOTIFY';
    const response = await fetch(`https://walletobjects.googleapis.com/walletobjects/v1/loyaltyObject/${encodeURIComponent(loyaltyObject.id)}`, { method: 'PATCH', headers: { authorization: `Bearer ${accessToken}`, 'content-type': 'application/json' }, body: JSON.stringify(loyaltyObject) });
    if (!response.ok) {
      const details = await response.text();
      console.error(`Google Wallet pass update failed (HTTP ${response.status}):`, details.slice(0, 2000));
    } else {
      console.info('Google Wallet pass update accepted (HTTP', response.status + ').');
    }
  } catch (error) { console.error('Google Wallet pass update failed:', error.message); }
}
function apnsJwt() {
  const key = fs.readFileSync(walletConfig.appleApnsKey, 'utf8');
  const now = Math.floor(Date.now() / 1000);
  const header = base64url(JSON.stringify({ alg: 'ES256', kid: walletConfig.appleApnsKeyId }));
  const payload = base64url(JSON.stringify({ iss: walletConfig.appleTeam, iat: now }));
  const unsigned = `${header}.${payload}`;
  const signature = crypto.sign('sha256', Buffer.from(unsigned), { key, dsaEncoding: 'ieee-p1363' }).toString('base64url');
  return `${unsigned}.${signature}`;
}
async function notifyApplePass(cardId) {
  if (!walletConfig.appleApnsKey || !walletConfig.appleApnsKeyId || !walletConfig.appleTeam || !walletConfig.applePassType) {
    console.warn('Apple Wallet update skipped: APNs settings are incomplete.');
    return;
  }
  const [devices] = await pool.execute('SELECT d.device_library_identifier,d.push_token FROM apple_wallet_devices d JOIN apple_wallet_registrations r ON r.device_library_identifier=d.device_library_identifier WHERE r.card_id=?', [cardId]);
  if (!devices.length) {
    console.warn('Apple Wallet update skipped: no registered Wallet device exists for this card.');
    return;
  }
  const token = apnsJwt();
  await Promise.all(devices.map(device => new Promise(resolve => {
    const client = http2.connect(walletConfig.appleApnsEnvironment==='sandbox'?'https://api.sandbox.push.apple.com':'https://api.push.apple.com');
    const request = client.request({ ':method': 'POST', ':path': `/3/device/${encodeURIComponent(device.push_token)}`, authorization: `bearer ${token}`, 'apns-topic': walletConfig.applePassType, 'apns-push-type': 'background' });
    let status = 0; let responseBody = '';
    request.on('response', headers => { status = Number(headers[':status'] || 0); });
    request.on('data', chunk => { responseBody += chunk.toString(); });
    request.on('error', error => console.error('Apple Wallet notification request failed:', error.message));
    request.on('close', async () => {
      client.close();
      if (status === 410 || status === 400) await pool.execute('DELETE FROM apple_wallet_devices WHERE device_library_identifier=?', [device.device_library_identifier]).catch(() => {});
      if (status < 200 || status >= 300) console.error(`Apple Wallet APNs push failed (HTTP ${status}):`, responseBody.slice(0, 1000));
      else console.info(`Apple Wallet APNs push accepted (HTTP ${status}) for one registered device.`);
      resolve();
    });
    request.end('{}');
  })));
}
async function cardForAppleSerial(serial) {
  if (!/^[0-9a-f-]{36}$/i.test(serial)) return null;
  const [rows] = await pool.execute(`SELECT c.id,c.card_status,p.collection_mode,p.expiry_months,(SELECT MIN(se.created_at) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp') AS first_stamp_at,(SELECT UNIX_TIMESTAMP(MAX(se.created_at)) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp' AND (p.collection_mode<>'anonymous' OR se.created_at>COALESCE((SELECT MAX(r.created_at) FROM stamp_events r WHERE r.card_id=c.id AND r.event_type='reward_redeemed'),'1970-01-01'))) AS last_stamp_at,c.business_id,p.promotion_family_id,p.id AS program_id,p.name AS program_name,p.visit_label,p.stamps_required,p.reward_description,
      l.name AS location_name,b.name AS business_name,b.business_type,b.default_language,
      COALESCE(d.background_color,'#101722') AS background_color,COALESCE(d.foreground_color,'#ffffff') AS foreground_color,COALESCE(d.accent_color,'#4accff') AS accent_color,d.logo_mime,d.logo_data,d.artwork_mime,d.artwork_data,d.editor_config,UNIX_TIMESTAMP(d.updated_at) AS design_updated,
      (SELECT COUNT(*) FROM stamp_events e WHERE e.card_id=c.id AND e.event_type='stamp' AND (p.collection_mode<>'anonymous' OR e.created_at>COALESCE((SELECT MAX(r.created_at) FROM stamp_events r WHERE r.card_id=c.id AND r.event_type='reward_redeemed'),'1970-01-01'))) AS progress,
      COALESCE((SELECT UNIX_TIMESTAMP(MAX(e.created_at)) FROM stamp_events e WHERE e.card_id=c.id),UNIX_TIMESTAMP(c.created_at)) AS last_updated
    FROM loyalty_cards c JOIN loyalty_programs p ON p.id=c.program_id JOIN locations l ON l.id=p.location_id JOIN businesses b ON b.id=c.business_id LEFT JOIN loyalty_card_designs d ON d.promotion_family_id=p.promotion_family_id AND d.business_id=b.id WHERE c.id=? LIMIT 1`, [serial]);
  if (!rows[0]) return null;
  if(typeof rows[0].editor_config==='string')try{rows[0].editor_config=JSON.parse(rows[0].editor_config);}catch{rows[0].editor_config=null;}
  await refreshCardExpiry(rows[0]);
  rows[0].customer_token = await ensureWalletCardToken(rows[0].id);
  return rows[0];
}

async function api(req, res, url) {
  const route = url.pathname;
  if(route==='/api/csp-report'&&req.method==='POST'){
    if(isLimited(`csp-report:${remoteAddress(req)}`,30,60_000)){
      res.writeHead(204,{'Cache-Control':'no-store','X-Content-Type-Options':'nosniff'});return res.end();
    }
    try{
      const report=await readJson(req,8192),entry=report?.['csp-report']||report?.body||report;
      const directive=text(entry?.['violated-directive']||entry?.effectiveDirective,80),blocked=text(entry?.['blocked-uri']||entry?.blockedURL,512).split('?')[0].split('#')[0];
      if(directive)console.warn('CSP report:',JSON.stringify({directive,blocked:blocked.slice(0,180)}));
    }catch{}
    res.writeHead(204,{'Cache-Control':'no-store','X-Content-Type-Options':'nosniff'});return res.end();
  }
  if (['POST','PUT','DELETE'].includes(req.method) && req.headers.origin) {
    let origin; try { origin = new URL(req.headers.origin); } catch { return send(res,403,{ error:'Request origin is not allowed.' }); }
    if (origin.host !== req.headers.host) return send(res,403,{ error:'Request origin is not allowed.' });
  }
  const googleCardArtworkMatch=route.match(/^\/api\/wallet\/google\/artwork\/([0-9a-f-]{36})$/i);
  if(googleCardArtworkMatch&&req.method==='GET'){
    const cardId=googleCardArtworkMatch[1],supplied=url.searchParams.get('sig')||'';
    if(!/^[A-Za-z0-9_-]{40,50}$/.test(supplied))return send(res,404,{error:'Wallet artwork not found.'});
    const expected=googleArtworkSignature(cardId),actualBuffer=Buffer.from(supplied),expectedBuffer=Buffer.from(expected);
    if(actualBuffer.length!==expectedBuffer.length||!crypto.timingSafeEqual(actualBuffer,expectedBuffer))return send(res,404,{error:'Wallet artwork not found.'});
    const card=await cardForAppleSerial(cardId);if(!card)return send(res,404,{error:'Wallet artwork not found.'});
    const source=card.artwork_data?Buffer.from(card.artwork_data):defaultWalletArtwork(card.background_color,card.accent_color,716,896);
    const liveArtwork=walletArtworkWithLiveStamps(source,card,card.logo_data?Buffer.from(card.logo_data):null);
    const image=googleWalletHero(liveArtwork,card.background_color);
    res.writeHead(200,{'Content-Type':'image/png','Content-Length':image.length,'Cache-Control':'public, max-age=300','X-Content-Type-Options':'nosniff','Referrer-Policy':'no-referrer'});return res.end(image);
  }
  const loyaltyDesignAsset=route.match(/^\/api\/loyalty-card-design\/(logo|artwork|google-logo|google-artwork)\/([0-9a-f-]{36})$/i);
  if(loyaltyDesignAsset&&req.method==='GET'){
    const [,kind,familyId]=loyaltyDesignAsset;
    const [rows]=await pool.execute(`SELECT d.background_color,d.accent_color,d.logo_data,d.artwork_data FROM loyalty_card_designs d JOIN businesses b ON b.id=d.business_id WHERE d.promotion_family_id=? AND b.active=1 LIMIT 1`,[familyId]);
    if(!rows.length){res.writeHead(404);return res.end();}
    const design=rows[0];let image;
    if(kind==='logo')image=design.logo_data?Buffer.from(design.logo_data):defaultWalletArtwork(design.background_color,design.accent_color,256,256);
    else if(kind==='google-logo'){const source=design.logo_data?Buffer.from(design.logo_data):defaultWalletArtwork(design.background_color,'#ffffff',256,256);image=googleWalletLogo(source,design.background_color);}
    else if(kind==='artwork')image=design.artwork_data?Buffer.from(design.artwork_data):defaultWalletArtwork(design.background_color,design.accent_color,716,896);
    else{const source=design.artwork_data?Buffer.from(design.artwork_data):defaultWalletArtwork(design.background_color,design.accent_color,716,896);image=googleWalletHero(source,design.background_color);}
    res.writeHead(200,{'Content-Type':'image/png','Content-Length':image.length,'Cache-Control':kind.startsWith('google-')?'public, max-age=3600':'no-store','X-Content-Type-Options':'nosniff'});return res.end(image);
  }
  const logoMatch=route.match(/^\/api\/business\/logo\/([0-9a-f-]{36})$/i);
  if(logoMatch&&req.method==='GET'){
    const [rows]=await pool.execute(`SELECT COALESCE(d.background_color,'#101722') AS background_color,COALESCE(d.accent_color,'#ff762e') AS accent_color,d.logo_data
      FROM businesses b LEFT JOIN business_card_designs d ON d.business_id=b.id WHERE b.id=? AND b.active=1 LIMIT 1`,[logoMatch[1]]);
    if(!rows.length){res.writeHead(404);return res.end();}
    const image=rows[0].logo_data?Buffer.from(rows[0].logo_data):defaultWalletArtwork(rows[0].background_color,rows[0].accent_color,256,256);res.writeHead(200,{'Content-Type':'image/png','Content-Length':image.length,'Cache-Control':'no-store','X-Content-Type-Options':'nosniff'});return res.end(image);
  }
  const googleLogoMatch=route.match(/^\/api\/business\/google-logo\/([0-9a-f-]{36})$/i);
  if(googleLogoMatch&&req.method==='GET'){
    const [rows]=await pool.execute(`SELECT COALESCE(d.background_color,'#101722') AS background_color,d.logo_data
      FROM businesses b LEFT JOIN business_card_designs d ON d.business_id=b.id WHERE b.id=? AND b.active=1 LIMIT 1`,[googleLogoMatch[1]]);
    if(!rows.length){res.writeHead(404);return res.end();}
    const source=rows[0].logo_data?Buffer.from(rows[0].logo_data):defaultWalletArtwork(rows[0].background_color,'#ffffff',256,256),image=googleWalletLogo(source,rows[0].background_color);
    res.writeHead(200,{'Content-Type':'image/png','Content-Length':image.length,'Cache-Control':'public, max-age=3600','X-Content-Type-Options':'nosniff'});return res.end(image);
  }
  const artworkMatch=route.match(/^\/api\/business\/artwork\/([0-9a-f-]{36})$/i);
  if(artworkMatch&&req.method==='GET'){
    const [rows]=await pool.execute(`SELECT b.id,COALESCE(d.background_color,'#101722') AS background_color,COALESCE(d.accent_color,'#ff762e') AS accent_color,d.artwork_data
      FROM businesses b LEFT JOIN business_card_designs d ON d.business_id=b.id WHERE b.id=? AND b.active=1 LIMIT 1`,[artworkMatch[1]]);
    if(!rows.length){res.writeHead(404);return res.end();}
    const image=rows[0].artwork_data?Buffer.from(rows[0].artwork_data):defaultWalletArtwork(rows[0].background_color,rows[0].accent_color,716,896);
    res.writeHead(200,{'Content-Type':'image/png','Content-Length':image.length,'Cache-Control':'no-store','X-Content-Type-Options':'nosniff'});return res.end(image);
  }
  const googleArtworkMatch=route.match(/^\/api\/business\/google-artwork\/([0-9a-f-]{36})$/i);
  if(googleArtworkMatch&&req.method==='GET'){
    const [rows]=await pool.execute(`SELECT COALESCE(d.background_color,'#101722') AS background_color,COALESCE(d.accent_color,'#ff762e') AS accent_color,d.artwork_data
      FROM businesses b LEFT JOIN business_card_designs d ON d.business_id=b.id WHERE b.id=? AND b.active=1 LIMIT 1`,[googleArtworkMatch[1]]);
    if(!rows.length){res.writeHead(404);return res.end();}
    const source=rows[0].artwork_data?Buffer.from(rows[0].artwork_data):defaultWalletArtwork(rows[0].background_color,rows[0].accent_color,716,896),image=googleWalletHero(source,rows[0].background_color);
    res.writeHead(200,{'Content-Type':'image/png','Content-Length':image.length,'Cache-Control':'public, max-age=3600','X-Content-Type-Options':'nosniff'});return res.end(image);
  }
  if(req.method==='GET'&&route==='/api/business/card-design'){
    const user=await getSession(req);requireBusinessManager(user);const promotionFamilyId=String(url.searchParams.get('promotionFamilyId')||'');
    if(!/^[0-9a-f-]{36}$/i.test(promotionFamilyId))return send(res,400,{error:'Choose a loyalty card to edit its design.'});
    const [offers]=await pool.execute('SELECT promotion_family_id FROM loyalty_programs WHERE promotion_family_id=? AND business_id=? AND active=1 LIMIT 1',[promotionFamilyId,user.business_id]);if(!offers.length)return send(res,404,{error:'This loyalty card was not found in the selected shop.'});
    const [rows]=await pool.execute('SELECT background_color,foreground_color,accent_color,logo_mime,artwork_mime,editor_config,UNIX_TIMESTAMP(updated_at) AS updated_at FROM loyalty_card_designs WHERE promotion_family_id=? AND business_id=? LIMIT 1',[promotionFamilyId,user.business_id]);
    return send(res,200,{design:rows[0]||{background_color:'#101722',foreground_color:'#ffffff',accent_color:'#4accff',logo_mime:null,artwork_mime:null,editor_config:null,updated_at:0}});
  }
  if(req.method==='PUT'&&route==='/api/business/card-design'){
    const user=await getSession(req);requireBusinessManager(user);const body=await readJson(req,6_000_000);const promotionFamilyId=text(body.promotionFamilyId,36);if(!/^[0-9a-f-]{36}$/i.test(promotionFamilyId))return send(res,400,{error:'Choose a loyalty card before saving its design.'});const [offers]=await pool.execute('SELECT promotion_family_id FROM loyalty_programs WHERE promotion_family_id=? AND business_id=? AND active=1 LIMIT 1',[promotionFamilyId,user.business_id]);if(!offers.length)return send(res,404,{error:'This loyalty card was not found in the selected shop.'});
    const background=text(body.backgroundColor,7),foreground=text(body.foregroundColor,7),accent=text(body.accentColor,7);
    if(!/^#[0-9a-f]{6}$/i.test(background)||!/^#[0-9a-f]{6}$/i.test(foreground)||!/^#[0-9a-f]{6}$/i.test(accent))return send(res,400,{error:'Choose valid colors for the card.'});
    const logoData=decodePngDataUrl(body.logoDataUrl,'shop logo'),artworkData=decodePngDataUrl(body.artworkDataUrl,'card artwork');
    const logoMime=logoData?'image/png':null,artworkMime=artworkData?'image/png':null,removeLogo=body.removeLogo===true,removeArtwork=body.removeArtwork===true;
    let editorConfigData=null;
    if(body.editorConfig!==undefined&&body.editorConfig!==null){
      const source=body.editorConfig;if(!source||typeof source!=='object'||Array.isArray(source))return send(res,400,{error:'The saved card editor settings are invalid.'});
      const finite=(value,min,max,fallback)=>Number.isFinite(Number(value))?Math.max(min,Math.min(max,Number(value))):fallback;
      const imageData=(value,label)=>{if(value==null||value==='')return'';if(typeof value!=='string'||!/^data:image\/(?:png|jpeg|webp);base64,[A-Za-z0-9+/]+={0,2}$/.test(value))throw Object.assign(new Error(`${label} must be a prepared PNG, JPEG, or WebP image.`),{status:400});const bytes=Buffer.from(value.slice(value.indexOf(',')+1),'base64');if(bytes.length>750_000)throw Object.assign(new Error(`${label} is still over 750 KB after image preparation.`),{status:413});if(value.startsWith('data:image/png;base64,'))try{PNG.sync.read(bytes);}catch{throw Object.assign(new Error(`${label} is a damaged PNG. Choose the image again so it can be prepared.`),{status:400});}return value;};
      const normalized={version:1,preset:text(source.preset,24),logoPosition:{x:finite(source.logoPosition?.x,2,98,50),y:finite(source.logoPosition?.y,2,98,10),width:finite(source.logoPosition?.width,16,94,82)},namePosition:{x:finite(source.namePosition?.x,2,98,50),y:finite(source.namePosition?.y,2,98,39)},fontSize:finite(source.fontSize,14,40,24),fontChoice:['avenir','futura','helvetica','arial-black','impact','comic','chalkboard','marker','brush','papyrus','copperplate','baskerville','didot','palatino','georgia','times','rockwell','typewriter','courier','optima','trebuchet','verdana','gill-sans','menlo'].includes(source.fontChoice)?source.fontChoice:(['modern','classic','rounded'].includes(source.fontChoice)?({modern:'avenir',classic:'baskerville',rounded:'chalkboard'}[source.fontChoice]):'avenir'),category:text(source.category,24),stampMark:text(source.stampMark,16),stampArtworkDataUrl:imageData(source.stampArtworkDataUrl,'Stamp artwork'),backgroundArtworkDataUrl:imageData(source.backgroundArtworkDataUrl,'Card artwork'),artworkLanguage:['en','el','es'].includes(source.artworkLanguage)?source.artworkLanguage:'en',cardTextByLanguage:Object.fromEntries(['en','el','es'].map(language=>{const copy=source.cardTextByLanguage?.[language]||{};return[language,{tagline:text(copy.tagline,60),stampsLabel:text(copy.stampsLabel,32),rewardLabel:text(copy.rewardLabel,32)}]}))};
      editorConfigData=JSON.stringify(normalized);if(Buffer.byteLength(editorConfigData,'utf8')>3_000_000)return send(res,413,{error:'The editable card settings are too large. Use smaller custom images.'});
    }
    await pool.execute(`INSERT INTO loyalty_card_designs (promotion_family_id,business_id,background_color,foreground_color,accent_color,logo_mime,logo_data,artwork_mime,artwork_data,editor_config) VALUES (?,?,?,?,?,?,?,?,?,?)
      ON DUPLICATE KEY UPDATE background_color=VALUES(background_color),foreground_color=VALUES(foreground_color),accent_color=VALUES(accent_color),logo_mime=IF(?,NULL,COALESCE(VALUES(logo_mime),logo_mime)),logo_data=IF(?,NULL,COALESCE(VALUES(logo_data),logo_data)),artwork_mime=IF(?,NULL,COALESCE(VALUES(artwork_mime),artwork_mime)),artwork_data=IF(?,NULL,COALESCE(VALUES(artwork_data),artwork_data)),editor_config=COALESCE(VALUES(editor_config),editor_config)`,[promotionFamilyId,user.business_id,background,foreground,accent,logoMime,logoData,artworkMime,artworkData,editorConfigData,removeLogo,removeLogo,removeArtwork,removeArtwork]);
    setImmediate(async()=>{try{const [cards]=await pool.execute('SELECT c.id FROM loyalty_cards c JOIN loyalty_programs p ON p.id=c.program_id WHERE c.business_id=? AND p.promotion_family_id=?',[user.business_id,promotionFamilyId]);for(const item of cards){notifyApplePass(item.id).catch(error=>console.error('Apple Wallet design update failed:',error.message));cardForAppleSerial(item.id).then(card=>card&&updateGooglePass(card)).catch(error=>console.error('Google Wallet design update failed:',error.message));}}catch(error){console.error('Wallet design refresh failed:',error.message);}});
    return send(res,200,{ok:true});
  }

  if(req.method==='GET'&&route==='/api/business/pro-analytics'){
    const user=await getSession(req);requireBusinessManager(user);
    const [plans]=await pool.execute(`SELECT 1 FROM business_billing WHERE business_id=? AND (billing_status='paid' OR (billing_status='promotional' AND (promo_ends_at IS NULL OR promo_ends_at>CURRENT_TIMESTAMP))) AND plan_code='pro' LIMIT 1`,[user.business_id]);
    if(!plans.length)return send(res,403,{error:'Pro analytics are available on active Pro plans or pilot promotions.'});
    const [totals]=await pool.execute(`SELECT COUNT(*) AS cards,COALESCE(SUM(stamps_30d>0),0) AS active_cards,COALESCE(SUM(stamps_30d>=2),0) AS repeat_cards,COALESCE(SUM(stamps_30d),0) AS stamps,COALESCE(SUM(rewards_30d),0) AS rewards,COALESCE(SUM(created_at>=CURRENT_DATE-INTERVAL 29 DAY),0) AS new_cards FROM (
      SELECT c.id,c.created_at,SUM(CASE WHEN e.event_type='stamp' AND e.created_at>=CURRENT_DATE-INTERVAL 29 DAY THEN 1 ELSE 0 END) AS stamps_30d,SUM(CASE WHEN e.event_type='reward_redeemed' AND e.created_at>=CURRENT_DATE-INTERVAL 29 DAY THEN 1 ELSE 0 END) AS rewards_30d
      FROM loyalty_cards c LEFT JOIN stamp_events e ON e.card_id=c.id WHERE c.business_id=? GROUP BY c.id,c.created_at
    ) card_totals`,[user.business_id]);
    const [daily]=await pool.execute(`SELECT DATE(e.created_at) AS day,SUM(e.event_type='stamp') AS stamps,SUM(e.event_type='reward_redeemed') AS rewards FROM stamp_events e WHERE e.business_id=? AND e.created_at>=CURRENT_DATE-INTERVAL 29 DAY GROUP BY DATE(e.created_at) ORDER BY day`,[user.business_id]);
    const stats=totals[0],active=Number(stats.active_cards),repeat=Number(stats.repeat_cards),stamps=Number(stats.stamps);
    return send(res,200,{periodDays:30,stats:{cards:Number(stats.cards),activeCards:active,repeatCards:repeat,repeatRate:active?Math.round(repeat/active*100):0,newCards:Number(stats.new_cards),stamps,rewards:Number(stats.rewards),redemptionRate:stamps?Math.round(Number(stats.rewards)/stamps*100):0},daily});
  }
  if (req.method === 'GET' && route === '/api/health') { await pool.query('SELECT 1'); return send(res,200,{ ok:true,database:'connected' }); }
  if(req.method==='GET'&&route==='/api/wallet/availability')return send(res,200,{apple:appleReady()&&walletConfig.cardTokenSecret.length>=32,google:googleReady()&&walletConfig.cardTokenSecret.length>=32});

  if(route==='/api/wallet/apple/handoff'&&req.method==='POST'){
    if(!appleReady()||walletConfig.cardTokenSecret.length<32)return send(res,503,{error:'Apple Wallet is not configured yet.'});
    const body=await readJson(req,1024),suppliedToken=text(body.token,100);let card=null;
    if(suppliedToken){if(!/^[A-Za-z0-9_-]{40,50}$/.test(suppliedToken))return send(res,401,{error:'Open your loyalty card before adding it to Apple Wallet.'});card=await getCardForWallet(suppliedToken);}
    else{const cardId=customerCardIdFromCookie(req);if(cardId)card=await cardForAppleSerial(cardId);}
    if(!card)return send(res,401,{error:'Open your loyalty card before adding it to Apple Wallet.'});
    const now=Date.now();for(const [key,value] of appleWalletHandoffTickets)if(value.expiresAt<=now)appleWalletHandoffTickets.delete(key);
    if(appleWalletHandoffTickets.size>=1000)return send(res,429,{error:'Too many Wallet requests. Please try again in a moment.'});
    const ticket=randomToken();appleWalletHandoffTickets.set(ticket,{token:card.customer_token||walletCardToken(card.id),expiresAt:now+60_000});
    return send(res,200,{downloadUrl:`/api/wallet/apple/download/${ticket}`,expiresInSeconds:60},{'Referrer-Policy':'no-referrer'});
  }
  const appleHandoffDownload=route.match(/^\/api\/wallet\/apple\/download\/([A-Za-z0-9_-]{40,50})$/);
  if(appleHandoffDownload&&req.method==='GET'){
    const handoff=appleWalletHandoffTickets.get(appleHandoffDownload[1]);appleWalletHandoffTickets.delete(appleHandoffDownload[1]);
    if(!handoff||handoff.expiresAt<=Date.now())return send(res,410,{error:'This Wallet download link expired. Tap Add to Apple Wallet again.'});
    const card=await getCardForWallet(handoff.token);if(!card)return send(res,404,{error:'Customer card not found.'});
    await ensureWalletCardToken(card.id);card.customer_token=walletCardToken(card.id);
    const pass=await buildApplePass(card);res.writeHead(200,{'Content-Type':'application/vnd.apple.pkpass','Content-Length':pass.length,'Content-Disposition':'attachment; filename=\"rinero-stamps.pkpass\"','Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Referrer-Policy':'no-referrer'});return res.end(pass);
  }
  const applePassDownload=route.match(/^\/api\/wallet\/apple\/([A-Za-z0-9_-]{40,50})$/);
  if((applePassDownload||route==='/api/wallet/apple')&&req.method==='GET'){
    const card=applePassDownload?await getCardForWallet(applePassDownload[1]):await cardForAppleSerial(customerCardIdFromCookie(req));
    if(!card)return send(res,401,{error:'Open your loyalty card before adding it to Apple Wallet.'});
    await ensureWalletCardToken(card.id);card.customer_token=walletCardToken(card.id);
    const pass=await buildApplePass(card);res.writeHead(200,{'Content-Type':'application/vnd.apple.pkpass','Content-Length':pass.length,'Content-Disposition':'attachment; filename="rinero-stamps.pkpass"','Cache-Control':'no-store','X-Content-Type-Options':'nosniff'});return res.end(pass);
  }
  const googlePassLink=route.match(/^\/api\/wallet\/google\/([A-Za-z0-9_-]{40,50})$/);
  if((googlePassLink||route==='/api/wallet/google')&&req.method==='GET'){
    if(!googleReady())return send(res,503,{error:'Google Wallet is not configured yet. The Rinero administrator must add a Wallet issuer and service account key.'});
    const card=googlePassLink?await getCardForWallet(googlePassLink[1]):await cardForAppleSerial(customerCardIdFromCookie(req));
    if(!card)return send(res,401,{error:'Open your loyalty card before adding it to Google Wallet.'});
    await ensureWalletCardToken(card.id);
    const [rawKey]=await Promise.all([fs.promises.readFile(walletConfig.googleKeyPath,'utf8')]);const key=JSON.parse(rawKey);
    if(key.client_email!==walletConfig.googleEmail||!key.private_key)return send(res,503,{error:'The Google Wallet service account file is incomplete.'});
    const now=Math.floor(Date.now()/1000),{loyaltyClass,loyaltyObject}=googleObject(card);
    const jwt=googleSign({iss:key.client_email,aud:'google',typ:'savetowallet',iat:now,origins:[url.origin],payload:{loyaltyClasses:[loyaltyClass],loyaltyObjects:[loyaltyObject]}},key.private_key);
    return send(res,200,{saveUrl:`https://pay.google.com/gp/v/save/${jwt}`});
  }
  const appleServiceBase='/api/wallet/apple/v1';
  // Apple appends /v1 to webServiceURL. Accept the duplicated-v1 URL used by
  // previously issued passes while new passes use the corrected base URL.
  const appleRoute=route.replace(/^\/api\/wallet\/apple\/v1\/v1(?=\/)/,'/api/wallet/apple/v1');
  const appleRegister=appleRoute.match(/^\/api\/wallet\/apple\/v1\/devices\/([^/]+)\/registrations\/([^/]+)\/([^/]+)$/);
  if(appleRegister&&(req.method==='POST'||req.method==='DELETE')){
    const [,deviceId,passType,serial]=appleRegister.map(decodeURIComponent);
    if(!appleReady()||passType!==walletConfig.applePassType){console.warn('Apple Wallet registration rejected: pass type or Apple configuration did not match.');return send(res,404,{error:'Wallet pass not found.'});}
    const card=await cardForAppleSerial(serial);if(!card){console.warn('Apple Wallet registration rejected: pass serial was not found.');return send(res,401,{error:'Wallet pass authorization failed.'});}
    if(!appleAuthorized(card.id,req)){console.warn('Apple Wallet registration rejected: pass authorization token did not match.');return send(res,401,{error:'Wallet pass authorization failed.'});}
    if(req.method==='POST'){
      const body=await readJson(req);const pushToken=text(body.pushToken,256);if(!pushToken)return send(res,400,{error:'Push token is missing.'});
      await pool.execute('INSERT INTO apple_wallet_devices (device_library_identifier,push_token) VALUES (?,?) ON DUPLICATE KEY UPDATE push_token=VALUES(push_token)',[deviceId,pushToken]);
      await pool.execute('INSERT IGNORE INTO apple_wallet_registrations (device_library_identifier,pass_type_identifier,serial_number,card_id) VALUES (?,?,?,?)',[deviceId,passType,serial,card.id]);
      console.info('Apple Wallet device registration succeeded.');
      res.writeHead(201);return res.end();
    }
    await pool.execute('DELETE FROM apple_wallet_registrations WHERE device_library_identifier=? AND pass_type_identifier=? AND serial_number=?',[deviceId,passType,serial]);
    const [remaining]=await pool.execute('SELECT 1 FROM apple_wallet_registrations WHERE device_library_identifier=? LIMIT 1',[deviceId]);
    if(!remaining.length)await pool.execute('DELETE FROM apple_wallet_devices WHERE device_library_identifier=?',[deviceId]);
    res.writeHead(200);return res.end();
  }
  const appleUpdates=appleRoute.match(/^\/api\/wallet\/apple\/v1\/devices\/([^/]+)\/registrations\/([^/]+)$/);
  if(appleUpdates&&req.method==='GET'){
    const [,deviceId,passType]=appleUpdates.map(decodeURIComponent);
    if(!appleReady()||passType!==walletConfig.applePassType)return send(res,404,{error:'Wallet pass type not found.'});
    const previous=Number(url.searchParams.get('passesUpdatedSince')||0);
    const [rows]=await pool.execute(`SELECT r.serial_number,COALESCE(MAX(UNIX_TIMESTAMP(e.created_at)),UNIX_TIMESTAMP(c.created_at)) AS changed_at
      FROM apple_wallet_registrations r JOIN loyalty_cards c ON c.id=r.card_id LEFT JOIN stamp_events e ON e.card_id=c.id
      WHERE r.device_library_identifier=? AND r.pass_type_identifier=? GROUP BY r.serial_number,c.created_at HAVING changed_at>?`,[deviceId,passType,previous]);
    console.info(`Apple Wallet update check completed: ${rows.length} changed pass(es) found.`);
    if(!rows.length){res.writeHead(204);return res.end();}
    return send(res,200,{serialNumbers:rows.map(row=>row.serial_number),lastUpdated:String(Math.floor(Date.now()/1000))},{'Content-Type':'application/json; charset=utf-8'});
  }
  const appleUpdatedPass=appleRoute.match(/^\/api\/wallet\/apple\/v1\/passes\/([^/]+)\/([^/]+)$/);
  if(appleUpdatedPass&&req.method==='GET'){
    const [,passType,serial]=appleUpdatedPass.map(decodeURIComponent);
    if(!appleReady()||passType!==walletConfig.applePassType)return send(res,404,{error:'Wallet pass not found.'});
    const card=await cardForAppleSerial(serial);if(!card)return send(res,404,{error:'Wallet pass not found.'});
    if(!appleAuthorized(card.id,req))return send(res,401,{error:'Wallet pass authorization failed.'});
    const pass=await buildApplePass(card);res.writeHead(200,{'Content-Type':'application/vnd.apple.pkpass','Content-Length':pass.length,'Cache-Control':'no-store','X-Content-Type-Options':'nosniff'});return res.end(pass);
  }
  if(appleRoute===`${appleServiceBase}/log`&&req.method==='POST'){
    const body=await readJson(req);if(Array.isArray(body.logs))console.info('Apple Wallet service log entries:',body.logs.slice(0,20).map(item=>text(item,500)));
    res.writeHead(200);return res.end();
  }

  if (req.method === 'POST' && route === '/api/register') {
    if(isLimited(`register:${remoteAddress(req)}`,5,60*60_000))return send(res,429,{error:'Too many agency sign-ups from this connection. Try again later.'});
    const body = await readJson(req); const agencyName = text(body.agencyName); const userEmail = email(body.email); const password = typeof body.password === 'string' ? body.password : '';
    if (!agencyName || !userEmail || password.length < 12 || password.length > 200) return send(res,400,{ error:'Enter your agency name and email. Passwords must be at least 12 characters.' });
    const connection = await pool.getConnection();
    try {
      await connection.beginTransaction();
      const [existing] = await connection.execute('SELECT id FROM users WHERE email=? LIMIT 1',[userEmail]);
      if (existing.length) { await connection.rollback(); return send(res,409,{ error:'An account already uses this email. Sign in instead.' }); }
      const userId=id(),agencyId=id(),membershipId=id(); const encoded=await passwordHash(password);
      await connection.execute('INSERT INTO users (id,email,password_hash) VALUES (?,?,?)',[userId,userEmail,encoded]);
      await connection.execute('INSERT INTO agencies (id,name) VALUES (?,?)',[agencyId,agencyName]);
      await connection.execute("INSERT INTO agency_memberships (id,agency_id,user_id,access_role) VALUES (?,?,?,'owner')",[membershipId,agencyId,userId]);
      await connection.commit(); await createSession(userId,agencyId,null,res);
      return send(res,201,{ agency:{ id:agencyId,name:agencyName },user:{ email:userEmail } });
    } catch(error) { await connection.rollback(); throw error; } finally { connection.release(); }
  }

  if (req.method === 'POST' && route === '/api/login') {
    if(isLimited(`login:${remoteAddress(req)}`,12,15*60_000))return send(res,429,{error:'Too many sign-in attempts. Wait 15 minutes and try again.'});
    const body=await readJson(req); const userEmail=email(body.email); const password=typeof body.password==='string'?body.password:'';
    const [users]=await pool.execute('SELECT id,email,password_hash FROM users WHERE email=? AND active=1 LIMIT 1',[userEmail||'']);
    const user=users[0]; if (!user || !(await passwordMatches(password,user.password_hash))) return send(res,401,{ error:'Email or password is incorrect.' });
    const [[agencyRows],[businessRows]]=await Promise.all([
      pool.execute('SELECT agency_id FROM agency_memberships WHERE user_id=? AND active=1 ORDER BY created_at LIMIT 1',[user.id]),
      pool.execute('SELECT b.agency_id,b.id AS business_id FROM business_memberships bm JOIN businesses b ON b.id=bm.business_id WHERE bm.user_id=? AND bm.active=1 ORDER BY bm.created_at LIMIT 1',[user.id]),
    ]);
    const agencyId=agencyRows[0]?.agency_id || businessRows[0]?.agency_id || null;
    const businessId=agencyRows.length ? null : (businessRows[0]?.business_id || null);
    if (!agencyId) return send(res,403,{ error:'This account has no active workspace.' });
    await createSession(user.id,agencyId,businessId,res); return send(res,200,{ ok:true });
  }

  if (req.method === 'POST' && route === '/api/logout') {
    const token=getCookie(req,sessionCookie); if (token) await pool.execute('DELETE FROM web_sessions WHERE token_hash=?',[hash(token)]); clearCookie(res); return send(res,200,{ ok:true });
  }

  if (req.method === 'GET' && route === '/api/activity') {
    const user=await getSession(req);
    if(!user)return send(res,401,{error:'Sign in to view activity.'});
    if(user.business_id)requireBusinessAccess(user);
    else if(!user.agency_id||!user.agency_role)return send(res,403,{error:'Workspace access is required.'});
    const week=url.searchParams.get('week')||'';
    if(!/^\d{4}-\d{2}-\d{2}$/.test(week))return send(res,400,{error:'Choose a valid Monday to Sunday week.'});
    const weekDate=new Date(`${week}T00:00:00.000Z`);
    if(Number.isNaN(weekDate.getTime())||weekDate.toISOString().slice(0,10)!==week||weekDate.getUTCDay()!==1)return send(res,400,{error:'Choose a valid Monday to Sunday week.'});
    const weekEnd=new Date(weekDate.getTime()+7*86400_000).toISOString().slice(0,10);
    const sql=user.business_id
      ? `SELECT DATE_FORMAT(created_at,'%Y-%m-%d') AS day,SUM(event_type='stamp') AS stamps,SUM(event_type='reward_redeemed') AS rewards FROM stamp_events WHERE business_id=? AND created_at>=? AND created_at<? GROUP BY DATE_FORMAT(created_at,'%Y-%m-%d') ORDER BY day`
      : `SELECT DATE_FORMAT(e.created_at,'%Y-%m-%d') AS day,SUM(e.event_type='stamp') AS stamps,SUM(e.event_type='reward_redeemed') AS rewards FROM stamp_events e JOIN businesses b ON b.id=e.business_id WHERE b.agency_id=? AND e.created_at>=? AND e.created_at<? GROUP BY DATE_FORMAT(e.created_at,'%Y-%m-%d') ORDER BY day`;
    const [activity]=await pool.execute(sql,user.business_id?[user.business_id,week,weekEnd]:[user.agency_id,week,weekEnd]);
    const firstSql=user.business_id
      ? `SELECT DATE_FORMAT(MIN(created_at),'%Y-%m-%d') AS first_day FROM stamp_events WHERE business_id=?`
      : `SELECT DATE_FORMAT(MIN(e.created_at),'%Y-%m-%d') AS first_day FROM stamp_events e JOIN businesses b ON b.id=e.business_id WHERE b.agency_id=?`;
    const [firstRows]=await pool.execute(firstSql,user.business_id?[user.business_id]:[user.agency_id]);
    return send(res,200,{activity,firstDay:firstRows[0]?.first_day||null});
  }

  if (req.method === 'GET' && route === '/api/me') {
    const user=await getSession(req); if (!user) return send(res,200,{ authenticated:false });
    const [agencies]=await pool.execute('SELECT id,name,default_language FROM agencies WHERE id=?',[user.agency_id]);
    if (!agencies.length) return send(res,401,{ authenticated:false });
    const clientSql=isAgencyRole(user.agency_role)
      ? `SELECT b.id,b.name,b.business_type,b.country_code,b.active,
          COALESCE(bb.plan_code,'free') AS plan_code,
          CASE WHEN bb.billing_status='promotional' AND (bb.promo_ends_at IS NULL OR bb.promo_ends_at>CURRENT_TIMESTAMP) THEN bb.plan_code ELSE 'free' END AS effective_plan,
          CASE WHEN bb.billing_status='promotional' AND bb.promo_ends_at IS NOT NULL AND bb.promo_ends_at<=CURRENT_TIMESTAMP THEN 'expired' ELSE COALESCE(bb.billing_status,'free') END AS billing_status,
          bb.promo_ends_at,NULL AS promo_note,
          (SELECT COUNT(*) FROM locations l WHERE l.business_id=b.id) AS location_count,
          (SELECT COUNT(*) FROM stamp_events e WHERE e.business_id=b.id AND e.event_type='stamp') AS stamps,
          (SELECT COUNT(*) FROM stamp_events e WHERE e.business_id=b.id AND e.event_type='reward_redeemed') AS rewards,
          (SELECT u.email FROM business_memberships bm JOIN users u ON u.id=bm.user_id WHERE bm.business_id=b.id AND bm.access_role='owner' AND bm.active=1 ORDER BY bm.created_at LIMIT 1) AS owner_email,
          (SELECT i.email FROM client_invites i WHERE i.business_id=b.id AND i.used_at IS NULL AND i.expires_at>CURRENT_TIMESTAMP ORDER BY i.created_at DESC LIMIT 1) AS invite_email
         FROM businesses b LEFT JOIN business_billing bb ON bb.business_id=b.id WHERE b.agency_id=? ORDER BY b.created_at DESC`
      : `SELECT b.id,b.name,b.business_type,b.country_code,b.active,
          COALESCE(bb.plan_code,'free') AS plan_code,
          CASE WHEN bb.billing_status='promotional' AND (bb.promo_ends_at IS NULL OR bb.promo_ends_at>CURRENT_TIMESTAMP) THEN bb.plan_code ELSE 'free' END AS effective_plan,
          CASE WHEN bb.billing_status='promotional' AND bb.promo_ends_at IS NOT NULL AND bb.promo_ends_at<=CURRENT_TIMESTAMP THEN 'expired' ELSE COALESCE(bb.billing_status,'free') END AS billing_status,
          bb.promo_ends_at,bb.promo_note,
          (SELECT COUNT(*) FROM locations l WHERE l.business_id=b.id) AS location_count,
          (SELECT COUNT(*) FROM stamp_events e WHERE e.business_id=b.id AND e.event_type='stamp') AS stamps,
          (SELECT COUNT(*) FROM stamp_events e WHERE e.business_id=b.id AND e.event_type='reward_redeemed') AS rewards,
          (SELECT u.email FROM business_memberships own JOIN users u ON u.id=own.user_id WHERE own.business_id=b.id AND own.access_role='owner' AND own.active=1 ORDER BY own.created_at LIMIT 1) AS owner_email,
          NULL AS invite_email
         FROM businesses b LEFT JOIN business_billing bb ON bb.business_id=b.id JOIN business_memberships bm ON bm.business_id=b.id AND bm.user_id=? AND bm.active=1 WHERE b.agency_id=? ORDER BY b.created_at DESC`;
    const [clients]=await pool.execute(clientSql,isAgencyRole(user.agency_role)?[user.agency_id]:[user.user_id,user.agency_id]);
    let selectedClient=null,locations=[],team=[];
    if (user.business_id) {
      requireBusinessAccess(user);
    const [businesses]=await pool.execute('SELECT id,name,business_type,country_code FROM businesses WHERE id=? AND agency_id=? AND active=1 LIMIT 1',[user.business_id,user.agency_id]);
      selectedClient=businesses[0]||null;
      if (selectedClient) {
        [locations]=await pool.execute(
          `SELECT l.id,l.name,l.country_code,l.active,
            (SELECT COUNT(*) FROM stamp_events e WHERE e.business_id=l.business_id AND e.location_id=l.id AND e.event_type='stamp') AS stamps,
            (SELECT COUNT(*) FROM stamp_events e WHERE e.business_id=l.business_id AND e.location_id=l.id AND e.event_type='reward_redeemed') AS rewards
           FROM locations l WHERE l.business_id=? ORDER BY l.created_at DESC`,[user.business_id]);
        const [programs]=await pool.execute(
          `SELECT p.id AS program_id,p.location_id,p.name AS program_name,p.visit_label,p.stamps_required,p.reward_description,p.collection_mode,p.expiry_months,p.promotion_family_id,
            (SELECT COUNT(*) FROM stamp_events e WHERE e.program_id=p.id AND e.event_type='stamp') AS program_stamps,
            (SELECT COUNT(*) FROM stamp_events e WHERE e.program_id=p.id AND e.event_type='reward_redeemed') AS program_rewards
           FROM loyalty_programs p JOIN locations l ON l.id=p.location_id WHERE p.business_id=? AND p.active=1 AND l.active=1 ORDER BY p.created_at,p.name`,[user.business_id]);
        const programsByLocation=new Map();
        for(const program of programs){const list=programsByLocation.get(program.location_id)||[];list.push(program);programsByLocation.set(program.location_id,list);}
        locations=locations.map(location=>({...location,programs:programsByLocation.get(location.id)||[]}));
      }
      if(selectedClient) [team]=await pool.execute('SELECT u.email,bm.access_role AS role FROM business_memberships bm JOIN users u ON u.id=bm.user_id WHERE bm.business_id=? AND bm.active=1 ORDER BY FIELD(bm.access_role,\'owner\',\'manager\',\'staff\'),bm.created_at',[user.business_id]);
    }
    const isAgencyAdmin=['owner','admin'].includes(user.agency_role);
    return send(res,200,{ authenticated:true,billingEnabled:false,user:{ email:user.email,agencyRole:user.agency_role,businessRole:user.business_role },agency:agencies[0],clients,selectedClient,locations,team,canManageClients:isAgencyAdmin });
  }

  if (req.method === 'POST' && route === '/api/clients') {
    const user=await getSession(req); requireAgencyAdmin(user); const body=await readJson(req);
    const businessName=text(body.businessName),clientEmail=email(body.clientEmail);
    if (!businessName||!clientEmail) return send(res,400,{ error:'Enter the shop name and owner email.' });
    const connection=await pool.getConnection(); const businessId=id(),inviteToken=randomToken();
    try {
      await connection.beginTransaction();
      await connection.execute('INSERT INTO businesses (id,agency_id,name,business_type,country_code) VALUES (?,?,?,?,?)',[businessId,user.agency_id,businessName,'Other','IE']);
      await connection.execute("INSERT INTO business_billing (business_id,plan_code,billing_status,billing_unit,billing_quantity) VALUES (?,'free','free','business',1)",[businessId]);
      await connection.execute('INSERT INTO client_invites (token_hash,agency_id,business_id,email,expires_at) VALUES (?,?,?,?,DATE_ADD(CURRENT_TIMESTAMP,INTERVAL 7 DAY))',[hash(inviteToken),user.agency_id,businessId,clientEmail]);
      await connection.commit();
      return send(res,201,{ client:{ id:businessId,name:businessName },inviteUrl:`/invite/#${inviteToken}` });
    } catch(error) { await connection.rollback(); throw error; } finally { connection.release(); }
  }

  const clientProfileMatch=route.match(/^\/api\/clients\/([0-9a-f-]{36})\/profile$/i);
  if(clientProfileMatch&&req.method==='PUT'){
    const user=await getSession(req);if(!user)return send(res,401,{error:'Sign in to edit this shop.'});
    const businessId=clientProfileMatch[1];
    if(isAgencyRole(user.agency_role)){
      const [owned]=await pool.execute('SELECT id FROM businesses WHERE id=? AND agency_id=? AND active=1 LIMIT 1',[businessId,user.agency_id]);
      if(!owned.length)return send(res,404,{error:'Shop not found.'});
    }else{
      requireBusinessManager(user);
      if(user.business_id!==businessId)return send(res,403,{error:'You can only edit your own shop.'});
    }
    const body=await readJson(req),name=text(body.name),businessType=text(body.businessType,80),country=text(body.countryCode,2).toUpperCase();
    if(!name||!businessType||!ISO_COUNTRY_CODES.has(country))return send(res,400,{error:'Enter the shop name, type, and a valid country.'});
    await pool.execute('UPDATE businesses SET name=?,business_type=?,country_code=? WHERE id=?',[name,businessType,country,businessId]);
    return send(res,200,{ok:true,shop:{id:businessId,name,businessType,countryCode:country}});
  }

  const promotionMatch=route.match(/^\/api\/clients\/([0-9a-f-]{36})\/promotion$/i);
  if(promotionMatch&&req.method==='POST'){
    const user=await getSession(req);requireAgencyAdmin(user);
    const businessId=promotionMatch[1],body=await readJson(req),days=Number(body.days),note=text(body.note,255);
    if(!Number.isInteger(days)||days<0||days>3650)return send(res,400,{error:'Choose a promotion from 1 to 3,650 days, or 0 for no end date.'});
    const [businesses]=await pool.execute('SELECT id FROM businesses WHERE id=? AND agency_id=? AND active=1 LIMIT 1',[businessId,user.agency_id]);
    if(!businesses.length)return send(res,404,{error:'Client business not found.'});
    const endsAt=days===0?null:new Date(Date.now()+days*86400_000);
    await pool.execute(`INSERT INTO business_billing (business_id,plan_code,billing_status,billing_unit,billing_quantity,promo_started_at,promo_ends_at,promo_note,promo_granted_by)
      VALUES (?,'pro','promotional','business',1,CURRENT_TIMESTAMP,?,?,?)
      ON DUPLICATE KEY UPDATE plan_code='pro',billing_status='promotional',promo_started_at=CURRENT_TIMESTAMP,promo_ends_at=VALUES(promo_ends_at),promo_note=VALUES(promo_note),promo_granted_by=VALUES(promo_granted_by)`,[businessId,endsAt,note||null,user.user_id]);
    return send(res,200,{ok:true,plan:'pro',billingStatus:'promotional',promoEndsAt:endsAt});
  }
  if(promotionMatch&&req.method==='DELETE'){
    const user=await getSession(req);requireAgencyAdmin(user);
    const businessId=promotionMatch[1];
    const [businesses]=await pool.execute('SELECT id FROM businesses WHERE id=? AND agency_id=? AND active=1 LIMIT 1',[businessId,user.agency_id]);
    if(!businesses.length)return send(res,404,{error:'Client business not found.'});
    const [result]=await pool.execute("UPDATE business_billing SET plan_code='free',billing_status='free',promo_started_at=NULL,promo_ends_at=NULL,promo_note=NULL,promo_granted_by=NULL WHERE business_id=? AND billing_status='promotional'",[businessId]);
    if(!result.affectedRows)return send(res,409,{error:'This shop has no active promotion to end.'});
    return send(res,200,{ok:true,plan:'free',billingStatus:'free'});
  }

  if(req.method==='POST'&&route==='/api/invites/lookup'){
    const body=await readJson(req),token=text(body.token,100);if(!/^[A-Za-z0-9_-]{40,50}$/.test(token))return send(res,400,{error:'This invitation is invalid or expired.'});
    const [rows]=await pool.execute('SELECT i.email,i.access_role AS role,b.name AS business_name,a.name AS agency_name FROM client_invites i JOIN businesses b ON b.id=i.business_id JOIN agencies a ON a.id=i.agency_id WHERE i.token_hash=? AND i.expires_at>CURRENT_TIMESTAMP AND i.used_at IS NULL LIMIT 1',[hash(token)]);
    return rows.length?send(res,200,{invite:rows[0]}):send(res,404,{error:'This invitation is invalid or expired.'});
  }
  if(req.method==='POST'&&route==='/api/invites/accept'){
    const body=await readJson(req);const token=text(body.token,100);const password=typeof body.password==='string'?body.password:'';if(!/^[A-Za-z0-9_-]{40,50}$/.test(token)||password.length<12||password.length>200)return send(res,400,{error:'This invitation is invalid or expired, or the password is too short.'});
    const connection=await pool.getConnection();
    try {
      await connection.beginTransaction();
      const [invites]=await connection.execute('SELECT agency_id,business_id,email,access_role AS role FROM client_invites WHERE token_hash=? AND expires_at>CURRENT_TIMESTAMP AND used_at IS NULL LIMIT 1 FOR UPDATE',[hash(token)]);
      if(!invites.length){await connection.rollback();return send(res,400,{error:'This invitation is invalid or expired.'});}
      const invite=invites[0]; let userId; const [existing]=await connection.execute('SELECT id,password_hash FROM users WHERE email=? AND active=1 LIMIT 1',[invite.email]);
      if(existing.length){userId=existing[0].id;if(!(await passwordMatches(password,existing[0].password_hash))){await connection.rollback();return send(res,401,{error:'This email already has an account. Enter its current password to accept the client invitation.'});}}
      else {userId=id();await connection.execute('INSERT INTO users (id,email,password_hash) VALUES (?,?,?)',[userId,invite.email,await passwordHash(password)]);}
      const membershipId=id();
      await connection.execute('INSERT INTO business_memberships (id,business_id,user_id,access_role) VALUES (?,?,?,?) ON DUPLICATE KEY UPDATE active=1',[membershipId,invite.business_id,userId,invite.role]);
      await connection.execute('UPDATE client_invites SET used_at=CURRENT_TIMESTAMP WHERE token_hash=?',[hash(token)]);
      await connection.commit(); await createSession(userId,invite.agency_id,invite.business_id,res); return send(res,200,{ok:true});
    }catch(error){await connection.rollback();throw error;}finally{connection.release();}
  }

  if (req.method==='POST' && route==='/api/business/select') {
    const user=await getSession(req); requireAgencyAdmin(user); const body=await readJson(req); const businessId=text(body.businessId,36);
    const [rows]=await pool.execute('SELECT id FROM businesses WHERE id=? AND agency_id=? AND active=1 LIMIT 1',[businessId,user.agency_id]); if(!rows.length)return send(res,404,{error:'Client business not found.'});
    const token=getCookie(req,sessionCookie); await pool.execute('UPDATE web_sessions SET active_business_id=? WHERE token_hash=?',[businessId,hash(token)]); return send(res,200,{ok:true});
  }

  if (req.method==='POST' && route==='/api/business/return') {
    const user=await getSession(req); requireAgencyAdmin(user); const token=getCookie(req,sessionCookie); await pool.execute('UPDATE web_sessions SET active_business_id=NULL WHERE token_hash=?',[hash(token)]); return send(res,200,{ok:true});
  }

  const resetRequestMatch=route.match(/^\/api\/clients\/([0-9a-f-]{36})\/password-reset$/i);
  if(resetRequestMatch&&req.method==='POST'){
    const user=await getSession(req);requireAgencyAdmin(user);const body=await readJson(req);const targetEmail=email(body.email);if(!targetEmail)return send(res,400,{error:'Enter the client account email.'});
    const [users]=await pool.execute('SELECT u.id FROM users u JOIN business_memberships bm ON bm.user_id=u.id JOIN businesses b ON b.id=bm.business_id WHERE u.email=? AND b.id=? AND b.agency_id=? AND bm.active=1 LIMIT 1',[targetEmail,resetRequestMatch[1],user.agency_id]);
    if(!users.length)return send(res,404,{error:'That email does not belong to a user of this client.'});
    const token=randomToken();await pool.execute('INSERT INTO password_resets (token_hash,user_id,agency_id,requested_by_user_id,expires_at) VALUES (?,?,?,?,DATE_ADD(CURRENT_TIMESTAMP,INTERVAL 30 MINUTE))',[hash(token),users[0].id,user.agency_id,user.user_id]);
    return send(res,201,{resetUrl:`/reset-password/#${token}`,expiresInMinutes:30});
  }

  if(req.method==='POST'&&route==='/api/reset-password'){
    const body=await readJson(req);const token=text(body.token,100);const password=typeof body.password==='string'?body.password:'';if(!/^[A-Za-z0-9_-]{40,50}$/.test(token)||password.length<12||password.length>200)return send(res,400,{error:'This reset link is invalid or expired, or the password is too short.'});
    const connection=await pool.getConnection();try{await connection.beginTransaction();const [resets]=await connection.execute('SELECT user_id FROM password_resets WHERE token_hash=? AND expires_at>CURRENT_TIMESTAMP AND used_at IS NULL LIMIT 1 FOR UPDATE',[hash(token)]);if(!resets.length){await connection.rollback();return send(res,400,{error:'This reset link is invalid or expired.'});}await connection.execute('UPDATE users SET password_hash=? WHERE id=?',[await passwordHash(password),resets[0].user_id]);await connection.execute('UPDATE password_resets SET used_at=CURRENT_TIMESTAMP WHERE user_id=? AND used_at IS NULL',[resets[0].user_id]);await connection.execute('DELETE FROM web_sessions WHERE user_id=?',[resets[0].user_id]);await connection.commit();clearCookie(res);return send(res,200,{ok:true});}catch(error){await connection.rollback();throw error;}finally{connection.release();}
  }

  if(req.method==='POST'&&route==='/api/locations'){
    const user=await getSession(req);requireBusinessManager(user);const body=await readJson(req);const name=text(body.name),country=text(body.countryCode,2).toUpperCase();if(!name||!ISO_COUNTRY_CODES.has(country))return send(res,400,{error:'Enter a location name and a valid country.'});const locationId=id();await pool.execute('INSERT INTO locations (id,business_id,name,country_code) VALUES (?,?,?,?)',[locationId,user.business_id,name,country]);return send(res,201,{location:{id:locationId,name,countryCode:country}});
  }
  if(req.method==='POST'&&route==='/api/staff/invites'){
    const user=await getSession(req);requireBusinessManager(user);const body=await readJson(req);const inviteEmail=email(body.email);if(!inviteEmail)return send(res,400,{error:'Enter a valid staff email address.'});
    const inviteToken=randomToken();await pool.execute("INSERT INTO client_invites (token_hash,agency_id,business_id,email,access_role,expires_at) VALUES (?,?,?,?,'staff',DATE_ADD(CURRENT_TIMESTAMP,INTERVAL 7 DAY))",[hash(inviteToken),user.agency_id,user.business_id,inviteEmail]);return send(res,201,{inviteUrl:`/invite/#${inviteToken}`,expiresInDays:7});
  }
  if(req.method==='POST'&&route==='/api/programs'){
    const user=await getSession(req);requireBusinessManager(user);const body=await readJson(req);const locationId=text(body.locationId,36),name=text(body.name),label=text(body.visitLabel,80)||'visit',stamps=Number(body.stampsRequired),reward=text(body.rewardDescription,255),mode=body.collectionMode==='identified'?'identified':'anonymous',expiryMonths=Number(body.expiryMonths||0);const [locations]=await pool.execute('SELECT id FROM locations WHERE id=? AND business_id=? AND active=1 LIMIT 1',[locationId,user.business_id]);if(!locations.length||!name||!Number.isInteger(stamps)||stamps<2||stamps>50||!reward||![0,1,3,6,12].includes(expiryMonths))return send(res,400,{error:'Check the location, reward, and expiry rule.'});if(mode==='identified'&&(process.env.CUSTOMER_DATA_KEY||'').length<32)return send(res,503,{error:'Identified cards need the customer-data encryption key configured first.'});const programId=id(),connection=await pool.getConnection();try{await connection.beginTransaction();await connection.execute('INSERT INTO loyalty_programs (id,promotion_family_id,business_id,location_id,name,visit_label,stamps_required,reward_description,collection_mode,expiry_months) VALUES (?,?,?,?,?,?,?,?,?,?)',[programId,programId,user.business_id,locationId,name,label,stamps,reward,mode,expiryMonths]);let [designs]=await connection.execute('SELECT background_color,foreground_color,accent_color,logo_mime,logo_data,artwork_mime,artwork_data,editor_config FROM loyalty_card_designs WHERE business_id=? ORDER BY updated_at DESC LIMIT 1',[user.business_id]);if(!designs.length)[designs]=await connection.execute('SELECT background_color,foreground_color,accent_color,logo_mime,logo_data,artwork_mime,artwork_data,editor_config FROM business_card_designs WHERE business_id=? LIMIT 1',[user.business_id]);const source=designs[0]||{background_color:'#101722',foreground_color:'#ffffff',accent_color:'#4accff',logo_mime:null,logo_data:null,artwork_mime:null,artwork_data:null,editor_config:null};await connection.execute('INSERT INTO loyalty_card_designs (promotion_family_id,business_id,background_color,foreground_color,accent_color,logo_mime,logo_data,artwork_mime,artwork_data,editor_config) VALUES (?,?,?,?,?,?,?,?,?,?)',[programId,user.business_id,source.background_color,source.foreground_color,source.accent_color,source.logo_mime,source.logo_data,source.artwork_mime,source.artwork_data,source.editor_config]);await connection.commit();return send(res,201,{program:{id:programId,collectionMode:mode,expiryMonths},customerUrl:`/join/${programId}`});}catch(error){await connection.rollback();throw error;}finally{connection.release();}
  }
  const programEdit=route.match(/^\/api\/programs\/([0-9a-f-]{36})$/i);
  if(programEdit&&req.method==='PUT'){
    const user=await getSession(req);requireBusinessManager(user);const body=await readJson(req),programId=programEdit[1],name=text(body.name),label=text(body.visitLabel,80)||'visit',stamps=Number(body.stampsRequired),reward=text(body.rewardDescription,255),mode=body.collectionMode==='identified'?'identified':'anonymous',expiryMonths=Number(body.expiryMonths||0);
    if(!name||!Number.isInteger(stamps)||stamps<2||stamps>50||!reward||![0,1,3,6,12].includes(expiryMonths))return send(res,400,{error:'Check the program name, stamp target, reward, and expiry rule.'});
    const connection=await pool.getConnection();
    try{
      await connection.beginTransaction();
      const [programs]=await connection.execute('SELECT id,business_id,location_id,promotion_family_id,active FROM loyalty_programs WHERE id=? AND business_id=? LIMIT 1 FOR UPDATE',[programId,user.business_id]);
      if(!programs.length){await connection.rollback();return send(res,404,{error:'Reward program not found.'});}
      if(!programs[0].active){await connection.rollback();return send(res,409,{error:'This reward version is no longer current. Refresh the page and edit the latest version.'});}
      const [locations]=await connection.execute('SELECT id FROM locations WHERE id=? AND business_id=? AND active=1 LIMIT 1',[programs[0].location_id,user.business_id]);
      if(!locations.length){await connection.rollback();return send(res,404,{error:'Shop location not found.'});}
      if(mode==='identified'&&(process.env.CUSTOMER_DATA_KEY||'').length<32){await connection.rollback();return send(res,503,{error:'Identified cards need the customer-data encryption key configured first.'});}
      await connection.execute('UPDATE loyalty_programs SET active=0 WHERE promotion_family_id=? AND business_id=?',[programs[0].promotion_family_id,user.business_id]);
      const newProgramId=id();
      await connection.execute('INSERT INTO loyalty_programs (id,promotion_family_id,business_id,location_id,name,visit_label,stamps_required,reward_description,collection_mode,expiry_months,active) VALUES (?,?,?,?,?,?,?,?,?,?,1)',[newProgramId,programs[0].promotion_family_id,user.business_id,programs[0].location_id,name,label,stamps,reward,mode,expiryMonths]);
      await connection.commit();return send(res,200,{ok:true,program:{id:newProgramId},customerUrl:`/join/${newProgramId}`,previousVersionKeepsExistingCards:true});
    }catch(error){await connection.rollback();throw error;}finally{connection.release();}
  }

  const programDelete=route.match(/^\/api\/programs\/([0-9a-f-]{36})$/i);
  if(programDelete&&req.method==='DELETE'){
    const user=await getSession(req);requireBusinessManager(user);const connection=await pool.getConnection();
    try{
      await connection.beginTransaction();
      const [rows]=await connection.execute('SELECT promotion_family_id FROM loyalty_programs WHERE id=? AND business_id=? LIMIT 1 FOR UPDATE',[programDelete[1],user.business_id]);
      if(!rows.length){await connection.rollback();return send(res,404,{error:'Promotion not found.'});}
      const [result]=await connection.execute('DELETE FROM loyalty_programs WHERE promotion_family_id=? AND business_id=?',[rows[0].promotion_family_id,user.business_id]);
      await connection.execute('DELETE FROM loyalty_card_designs WHERE promotion_family_id=? AND business_id=?',[rows[0].promotion_family_id,user.business_id]);
      await connection.commit();return send(res,200,{ok:true,deletedVersions:result.affectedRows});
    }catch(error){await connection.rollback();throw error;}finally{connection.release();}
  }

  const programQr=route.match(/^\/api\/programs\/([0-9a-f-]{36})\/qr$/i);
  if(programQr&&req.method==='GET'){
    const [rows]=await pool.execute('SELECT current.id FROM loyalty_programs requested JOIN loyalty_programs current ON current.promotion_family_id=requested.promotion_family_id AND current.business_id=requested.business_id AND current.active=1 WHERE requested.id=? AND requested.active=1 LIMIT 1',[programQr[1]]);
    if(!rows.length){
      const [oldRows]=await pool.execute('SELECT current.id FROM loyalty_programs requested JOIN loyalty_programs current ON current.promotion_family_id=requested.promotion_family_id AND current.business_id=requested.business_id AND current.active=1 WHERE requested.id=? LIMIT 1',[programQr[1]]);
      if(!oldRows.length){res.writeHead(404);return res.end();}rows.push(...oldRows);
    }
    const publicOrigin='https://stamps.rinero.app';
    const link=`${publicOrigin}/join/${rows[0].id}`;
    const image=await QRCode.toBuffer(link,{type:'png',width:640,margin:2,errorCorrectionLevel:'M',color:{dark:'#101722',light:'#ffffff'}});
    res.writeHead(200,{'Content-Type':'image/png','Content-Length':image.length,'Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Referrer-Policy':'strict-origin-when-cross-origin'});return res.end(image);
  }

  const joinMatch=route.match(/^\/api\/join\/([0-9a-f-]{36})$/i);
  if(joinMatch&&req.method==='GET'){
    const [rows]=await pool.execute('SELECT current.id,current.name,current.visit_label,current.stamps_required,current.reward_description,current.collection_mode,current.expiry_months,l.name AS location_name,b.name AS business_name,b.business_type FROM loyalty_programs requested JOIN loyalty_programs current ON current.promotion_family_id=requested.promotion_family_id AND current.business_id=requested.business_id AND current.active=1 JOIN businesses b ON b.id=current.business_id JOIN locations l ON l.id=current.location_id WHERE requested.id=? AND l.active=1 AND b.active=1 LIMIT 1',[joinMatch[1]]);return rows.length?send(res,200,{program:rows[0]}):send(res,404,{error:'This loyalty card is not available.'});
  }
  const joinCreate=route.match(/^\/api\/join\/([0-9a-f-]{36})\/cards$/i);
  if(joinCreate&&req.method==='POST'){
    if(isLimited(`cards:${remoteAddress(req)}:${joinCreate[1]}`,300,60*60_000))return send(res,429,{error:'Too many cards were created from this connection. Try again later.'});
    const body=await readJson(req),[programs]=await pool.execute('SELECT current.id,current.business_id,current.location_id,current.collection_mode FROM loyalty_programs requested JOIN loyalty_programs current ON current.promotion_family_id=requested.promotion_family_id AND current.business_id=requested.business_id AND current.active=1 JOIN locations l ON l.id=current.location_id JOIN businesses b ON b.id=current.business_id WHERE requested.id=? AND l.active=1 AND b.active=1 LIMIT 1',[joinCreate[1]]);if(!programs.length)return send(res,404,{error:'This loyalty card is not available.'});
    const program=programs[0],contactType=body.contactType==='phone'?'phone':'email';let contactValue='';
    if(program.collection_mode!=='identified')return send(res,409,{error:'Tap or scan the shop QR/NFC to collect an anonymous stamp.'});
    if(program.collection_mode==='identified'){
      contactValue=contactType==='phone'?text(body.contact,64):email(body.contact);
      if(!contactValue||contactType==='phone'&&!/^[+0-9().\-\s]{6,32}$/.test(contactValue))return send(res,400,{error:'Enter a valid phone number or email address.'});
    }
    const browserToken=program.collection_mode==='anonymous'?(getCookie(req,'rinero_anon')||randomToken()):'';if(browserToken)setAnonymousCookie(res,browserToken);
    const cardId=id(),token=program.collection_mode==='anonymous'?anonymousCardToken(browserToken,cardId):randomToken(),connection=await pool.getConnection();
    try{
      await connection.beginTransaction();
      await connection.execute('INSERT INTO loyalty_cards (id,business_id,program_id,token_hash) VALUES (?,?,?,?)',[cardId,program.business_id,program.id,hash(token)]);
      if(program.collection_mode==='anonymous')await connection.execute('INSERT INTO anonymous_card_devices (program_id,browser_token_hash,card_id) VALUES (?,?,?) ON DUPLICATE KEY UPDATE card_id=VALUES(card_id)',[program.id,hash(browserToken),cardId]);
      else await connection.execute('INSERT INTO customer_card_contacts (card_id,contact_type,contact_ciphertext) VALUES (?,?,?)',[cardId,contactType,encryptCustomerContact(contactValue)]);
      await connection.execute('INSERT INTO stamp_events (id,business_id,location_id,program_id,card_id,actor_user_id,event_type) VALUES (?,?,?,?,?,NULL,\'stamp\')',[id(),program.business_id,program.location_id,program.id,cardId]);
      await connection.commit();
    }catch(error){await connection.rollback();throw error;}finally{connection.release();}
    const updatedCard=await cardForAppleSerial(cardId).catch(()=>null);if(updatedCard){notifyApplePass(cardId).catch(error=>console.error('Apple Wallet update notification failed:',error.message));updateGooglePass(updatedCard).catch(error=>console.error('Google Wallet update failed:',error.message));}
    return send(res,201,{card:{id:cardId,token,url:`/card/#${token}`},firstStamp:true});
  }
  const joinVisit=route.match(/^\/api\/join\/([0-9a-f-]{36})\/visit$/i);
  if(joinVisit&&req.method==='POST'){
    if(isLimited(`anon-visit:${remoteAddress(req)}:${joinVisit[1]}`,600,60*60_000))return send(res,429,{error:'Please wait before tapping again.'});
    const body=await readJson(req,1024),installationId=typeof body.installationId==='string'&&/^[A-Za-z0-9_-]{32,50}$/.test(body.installationId)?body.installationId:'',cookieToken=getCookie(req,'rinero_anon'),browserToken=/^[A-Za-z0-9_-]{32,50}$/.test(cookieToken)?cookieToken:installationId||randomToken();setAnonymousCookie(res,browserToken);const [programs]=await pool.execute('SELECT current.id,current.promotion_family_id,current.business_id,current.location_id,current.stamps_required,current.collection_mode,current.expiry_months FROM loyalty_programs requested JOIN loyalty_programs current ON current.promotion_family_id=requested.promotion_family_id AND current.business_id=requested.business_id AND current.active=1 JOIN locations l ON l.id=current.location_id JOIN businesses b ON b.id=current.business_id WHERE requested.id=? AND l.active=1 AND b.active=1 LIMIT 1',[joinVisit[1]]);if(!programs.length||programs[0].collection_mode!=='anonymous')return send(res,404,{error:'This anonymous card link is unavailable.'});
    const program=programs[0],browserHash=hash(browserToken),connection=await pool.getConnection();let cardId='',progress=0,token='',lastStampAt=0,stampAdded=false,rewardRedeemed=false,expiredCardId='';
    try{
      await connection.beginTransaction();
    const [existing]=await connection.execute("SELECT c.id,c.card_status,p.id AS card_program_id,p.business_id AS card_business_id,p.location_id AS card_location_id,p.stamps_required,p.expiry_months,(SELECT MIN(se.created_at) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp') AS lifetime_first_stamp_at,(SELECT MIN(se.created_at) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp') AS first_stamp_at,(SELECT UNIX_TIMESTAMP(MAX(se.created_at)) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type IN ('stamp','reward_redeemed')) AS last_stamp_at,(SELECT COUNT(*) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp' AND se.created_at>COALESCE((SELECT MAX(r.created_at) FROM stamp_events r WHERE r.card_id=c.id AND r.event_type='reward_redeemed'),'1970-01-01')) AS progress,(SELECT MAX(r.created_at) FROM stamp_events r WHERE r.card_id=c.id AND r.event_type='reward_redeemed') AS last_reward_redeemed_at FROM anonymous_card_devices d JOIN loyalty_programs device_program ON device_program.id=d.program_id JOIN loyalty_cards c ON c.id=d.card_id JOIN loyalty_programs p ON p.id=c.program_id WHERE device_program.promotion_family_id=? AND d.browser_token_hash=? ORDER BY (c.card_status='active') DESC,d.updated_at DESC LIMIT 1 FOR UPDATE",[program.promotion_family_id,browserHash]);
      if(existing.length&&existing[0].card_status==='completed'&&existing[0].last_reward_redeemed_at&&(!cardExpiryDate(existing[0].lifetime_first_stamp_at,existing[0].expiry_months)||Date.now()<cardExpiryDate(existing[0].lifetime_first_stamp_at,existing[0].expiry_months).getTime())){await connection.execute("UPDATE loyalty_cards SET card_status='active' WHERE id=? AND card_status='completed'",[existing[0].id]);existing[0].card_status='active';}
      if(existing.length&&existing[0].card_status==='expired'&&Number(existing[0].progress)>=Number(existing[0].stamps_required)&&(!cardExpiryDate(existing[0].lifetime_first_stamp_at,existing[0].expiry_months)||Date.now()<cardExpiryDate(existing[0].lifetime_first_stamp_at,existing[0].expiry_months).getTime())){await connection.execute("UPDATE loyalty_cards SET card_status='active' WHERE id=? AND card_status='expired'",[existing[0].id]);existing[0].card_status='active';}
      if(existing.length&&existing[0].card_status==='active'&&cardIsExpired(existing[0].lifetime_first_stamp_at,existing[0].expiry_months,existing[0].last_stamp_at,existing[0].progress,existing[0].stamps_required,'anonymous')){await connection.execute("UPDATE loyalty_cards SET card_status='expired' WHERE id=?",[existing[0].id]);existing[0].card_status='expired';expiredCardId=existing[0].id;}
      let stampProgram={id:program.id,business_id:program.business_id,location_id:program.location_id,stamps_required:program.stamps_required};
      if(existing.length&&existing[0].card_status!=='completed'&&existing[0].card_status!=='expired'){cardId=existing[0].id;stampProgram={id:existing[0].card_program_id,business_id:existing[0].card_business_id,location_id:existing[0].card_location_id,stamps_required:existing[0].stamps_required};lastStampAt=Number(existing[0].last_stamp_at||0);progress=Number(existing[0].progress||0);}
      else{cardId=id();token=anonymousCardToken(browserToken,cardId);await connection.execute('INSERT INTO loyalty_cards (id,business_id,program_id,token_hash) VALUES (?,?,?,?)',[cardId,program.business_id,program.id,hash(token)]);await connection.execute('INSERT INTO anonymous_card_devices (program_id,browser_token_hash,card_id) VALUES (?,?,?) ON DUPLICATE KEY UPDATE card_id=VALUES(card_id)',[program.id,browserHash,cardId]);}
      if(progress>=Number(stampProgram.stamps_required)){
        await connection.execute("INSERT INTO stamp_events (id,business_id,location_id,program_id,card_id,actor_user_id,event_type) VALUES (?,?,?,?,?,NULL,'reward_redeemed')",[id(),stampProgram.business_id,stampProgram.location_id,stampProgram.id,cardId]);progress=0;lastStampAt=Math.floor(Date.now()/1000);rewardRedeemed=true;
      }
      if(!rewardRedeemed&&progress<Number(stampProgram.stamps_required)&&!stampCooldownRemaining(lastStampAt)){
        await connection.execute("INSERT INTO stamp_events (id,business_id,location_id,program_id,card_id,actor_user_id,event_type) VALUES (?,?,?,?,?,NULL,'stamp')",[id(),stampProgram.business_id,stampProgram.location_id,stampProgram.id,cardId]);progress+=1;stampAdded=true;lastStampAt=Math.floor(Date.now()/1000);
      }
      await connection.commit();
    }catch(error){await connection.rollback();throw error;}finally{connection.release();}
    if(!token)token=anonymousCardToken(browserToken,cardId);if(expiredCardId){const expiredCard=await cardForAppleSerial(expiredCardId).catch(()=>null);if(expiredCard){notifyApplePass(expiredCardId).catch(error=>console.error('Apple Wallet expiry update failed:',error.message));updateGooglePass(expiredCard).catch(error=>console.error('Google Wallet expiry update failed:',error.message));}}const updatedCard=stampAdded||rewardRedeemed?await cardForAppleSerial(cardId).catch(()=>null):null;if(updatedCard){notifyApplePass(cardId).catch(error=>console.error('Apple Wallet update notification failed:',error.message));updateGooglePass(updatedCard).catch(error=>console.error('Google Wallet update failed:',error.message));}
    const [cardPrograms]=await pool.execute('SELECT p.stamps_required FROM loyalty_cards c JOIN loyalty_programs p ON p.id=c.program_id WHERE c.id=? LIMIT 1',[cardId]);
    return send(res,200,{card:{id:cardId,token,url:`/card/#${token}`},installationId:browserToken,progress,rewardReady:progress>=Number(cardPrograms[0]?.stamps_required||program.stamps_required),stampAdded,rewardRedeemed,cooldownRemaining:stampAdded?0:stampCooldownRemaining(lastStampAt)});
  }
  if(route==='/api/card'&&req.method==='POST'){
    const body=await readJson(req);const cardId=await resolveCustomerCardId(req,res,body.token);if(!cardId)return send(res,404,{error:'Card not found.'});
    const [rows]=await pool.execute(`SELECT c.id,c.card_status,p.collection_mode,p.expiry_months,(SELECT MIN(se.created_at) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp') AS first_stamp_at,(SELECT UNIX_TIMESTAMP(MAX(se.created_at)) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp' AND (p.collection_mode<>'anonymous' OR se.created_at>COALESCE((SELECT MAX(r.created_at) FROM stamp_events r WHERE r.card_id=c.id AND r.event_type='reward_redeemed'),'1970-01-01'))) AS last_stamp_at,p.promotion_family_id,p.name,p.visit_label,p.stamps_required,p.reward_description,l.name AS location_name,b.id AS business_id,b.name AS business_name,
      COALESCE(d.background_color,'#101722') AS background_color,COALESCE(d.foreground_color,'#ffffff') AS foreground_color,COALESCE(d.accent_color,'#4accff') AS accent_color,d.logo_mime,d.editor_config,UNIX_TIMESTAMP(d.updated_at) AS design_updated,
      (SELECT COUNT(*) FROM stamp_events e WHERE e.card_id=c.id AND e.event_type='stamp' AND (p.collection_mode<>'anonymous' OR e.created_at>COALESCE((SELECT MAX(r.created_at) FROM stamp_events r WHERE r.card_id=c.id AND r.event_type='reward_redeemed'),'1970-01-01'))) AS progress
      FROM loyalty_cards c JOIN loyalty_programs p ON p.id=c.program_id JOIN locations l ON l.id=p.location_id JOIN businesses b ON b.id=c.business_id LEFT JOIN loyalty_card_designs d ON d.promotion_family_id=p.promotion_family_id AND d.business_id=b.id WHERE c.id=? LIMIT 1`,[cardId]);if(!rows.length)return send(res,404,{error:'Card not found.'});const row=await refreshCardExpiry(rows[0]);if(typeof row.editor_config==='string')try{row.editor_config=JSON.parse(row.editor_config);}catch{row.editor_config=null;}const storedConfig=row.editor_config;
    const finite=(value,min,max,fallback)=>Number.isFinite(Number(value))?Math.max(min,Math.min(max,Number(value))):fallback;
    const safeText=value=>typeof value==='string'?value.slice(0,60):'';
    const publicFonts=['avenir','futura','helvetica','arial-black','impact','comic','chalkboard','marker','brush','papyrus','copperplate','baskerville','didot','palatino','georgia','times','rockwell','typewriter','courier','optima','trebuchet','verdana','gill-sans','menlo'];
    const cardTextByLanguage=storedConfig?.cardTextByLanguage&&typeof storedConfig.cardTextByLanguage==='object'?Object.fromEntries(['en','el','es'].map(language=>{const copy=storedConfig.cardTextByLanguage[language]||{};return[language,{tagline:safeText(copy.tagline),stampsLabel:safeText(copy.stampsLabel),rewardLabel:safeText(copy.rewardLabel)}]})):{};
    const logoPosition=storedConfig?.logoPosition&&typeof storedConfig.logoPosition==='object'?{x:finite(storedConfig.logoPosition.x,2,98,39),y:finite(storedConfig.logoPosition.y,2,98,10),width:finite(storedConfig.logoPosition.width,16,94,82)}:null;
    const namePosition=storedConfig?.namePosition&&typeof storedConfig.namePosition==='object'?{x:finite(storedConfig.namePosition.x,2,98,50),y:finite(storedConfig.namePosition.y,2,98,39)}:null;
    row.editor_config=storedConfig&&typeof storedConfig==='object'?{logoPosition,namePosition,fontSize:finite(storedConfig.fontSize,14,40,24),fontChoice:publicFonts.includes(storedConfig.fontChoice)?storedConfig.fontChoice:'avenir',stampMark:typeof storedConfig.stampMark==='string'?storedConfig.stampMark.slice(0,16):'',stampArtworkDataUrl:typeof storedConfig.stampArtworkDataUrl==='string'&&/^data:image\/png;base64,[A-Za-z0-9+/=]+$/.test(storedConfig.stampArtworkDataUrl)&&storedConfig.stampArtworkDataUrl.length<=250_000?storedConfig.stampArtworkDataUrl:'',cardTextByLanguage}:null;
    row.logo_url=row.logo_mime?`/api/loyalty-card-design/logo/${row.promotion_family_id}?v=${row.design_updated||0}`:'';row.artwork_url=`/api/loyalty-card-design/artwork/${row.promotion_family_id}?v=${row.design_updated||0}`;row.artwork_includes_text=Boolean(row.design_updated);row.reward_expires_at=row.collection_mode==='anonymous'?null:rewardExpiryDate(row.last_stamp_at,row.progress,row.stamps_required)?.toISOString()||null;const offerExpiry=cardExpiryDate(row.first_stamp_at,row.expiry_months),rewardExpiry=row.reward_expires_at?new Date(row.reward_expires_at):null;row.expires_at=[offerExpiry,rewardExpiry].filter(Boolean).sort((a,b)=>a-b)[0]?.toISOString()||null;const {id:returnedId,last_stamp_at,logo_mime,...card}=row;return send(res,200,{card});
  }
  if(route==='/api/card/redeem'&&req.method==='POST'){
    return send(res,403,{error:'Customers cannot redeem their own reward. Show the completed card to shop staff.'});
  }
  if(route==='/api/card/qr'&&req.method==='GET'){
    const cardId=await resolveCustomerCardId(req,res,url.searchParams.get('token'));if(!cardId){res.writeHead(404);return res.end();}const token=await ensureWalletCardToken(cardId);
    const image=await QRCode.toBuffer(`${url.origin}/card/#${token}`,{type:'png',width:640,margin:2,errorCorrectionLevel:'M',color:{dark:'#101722',light:'#ffffff'}});
    res.writeHead(200,{'Content-Type':'image/png','Content-Length':image.length,'Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Referrer-Policy':'no-referrer'});return res.end(image);
  }
  if(route==='/api/card'&&req.method==='DELETE'){
    const body=await readJson(req),cardId=await resolveCustomerCardId(req,res,body.token);if(!cardId)return send(res,404,{error:'Card not found.'});
    const [cards]=await pool.execute('SELECT c.id FROM loyalty_cards c WHERE c.id=? LIMIT 1',[cardId]);
    if(!cards.length)return send(res,404,{error:'Card not found.'});
    await pool.execute('DELETE FROM loyalty_cards WHERE id=?',[cards[0].id]);
    clearCustomerCardCookie(res);
    return send(res,200,{ok:true});
  }
  if(route==='/api/staff/cards'&&req.method==='POST'){
    const user=await getSession(req);requireBusinessAccess(user);const body=await readJson(req);let token=text(body.token,100);const cardUrl=typeof body.cardUrl==='string'?body.cardUrl:'';const event=body.action;if(cardUrl){try{const parsed=new URL(cardUrl);if(parsed.origin!==url.origin||parsed.pathname!=='/card')throw new Error();token=parsed.hash.slice(1);}catch{return send(res,400,{error:'That is not a valid customer card. Ask them to open their card and scan again.'});}}if(!/^[A-Za-z0-9_-]{40,50}$/.test(token)||!['stamp','redeem'].includes(event))return send(res,400,{error:'Scan a customer card first, then choose an action.'});const connection=await pool.getConnection();
    try{
      await connection.beginTransaction();
      const [cards]=await connection.execute("SELECT c.id,c.card_status,c.business_id,c.program_id,p.location_id,p.stamps_required,p.collection_mode,p.expiry_months,(SELECT MIN(se.created_at) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp') AS first_stamp_at,(SELECT UNIX_TIMESTAMP(MAX(se.created_at)) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp') AS last_stamp_at,(SELECT COUNT(*) FROM stamp_events se WHERE se.card_id=c.id AND se.event_type='stamp') AS progress FROM loyalty_cards c JOIN loyalty_programs p ON p.id=c.program_id JOIN locations l ON l.id=p.location_id JOIN businesses b ON b.id=c.business_id LEFT JOIN wallet_card_tokens wt ON wt.card_id=c.id WHERE (c.token_hash=? OR wt.token_hash=?) AND c.business_id=? AND l.active=1 AND b.active=1 LIMIT 1 FOR UPDATE",[hash(token),hash(token),user.business_id]);
      if(!cards.length){await connection.rollback();return send(res,404,{error:'Card not found for this client business.'});}
      const card=cards[0];if(card.collection_mode!=='identified'){await connection.rollback();return send(res,409,{error:'This promotion uses anonymous QR/NFC taps. Staff scanning is not enabled for it.'});}if(card.card_status==='active'&&cardIsExpired(card.first_stamp_at,card.expiry_months,card.last_stamp_at,card.progress,card.stamps_required)){await connection.execute("UPDATE loyalty_cards SET card_status='expired' WHERE id=?",[card.id]);await connection.commit();return send(res,409,{error:'This card has expired.'});}if(card.card_status!=='active'){await connection.rollback();return send(res,409,{error:'This card is already completed or expired.'});}const [counts]=await connection.execute("SELECT COUNT(*) AS count FROM stamp_events WHERE card_id=? AND event_type='stamp'",[card.id]);const progress=Number(counts[0].count);
      if(event==='stamp'){const [lastStamps]=await connection.execute("SELECT UNIX_TIMESTAMP(MAX(created_at)) AS last_stamp_at FROM stamp_events WHERE card_id=? AND event_type='stamp'",[card.id]);const lastStampAt=Number(lastStamps[0]?.last_stamp_at||0);const remaining=stampCooldownRemaining(lastStampAt);if(remaining){await connection.rollback();return send(res,409,{error:stampCooldownMessage(remaining),nextStampAt:lastStampAt+stampCooldownDurationSeconds});}}
      if(event==='stamp'&&progress>=card.stamps_required){await connection.rollback();return send(res,409,{error:'This card has a reward ready to redeem first.'});}if(event==='redeem'&&progress<card.stamps_required){await connection.rollback();return send(res,409,{error:'This card has not earned a reward yet.'});}
      await connection.execute('INSERT INTO stamp_events (id,business_id,location_id,program_id,card_id,actor_user_id,event_type) VALUES (?,?,?,?,?,?,?)',[id(),user.business_id,card.location_id,card.program_id,card.id,user.user_id,event==='stamp'?'stamp':'reward_redeemed']);if(event==='redeem')await connection.execute("UPDATE loyalty_cards SET card_status='completed' WHERE id=?",[card.id]);await connection.commit();
      const updatedCard=await cardForAppleSerial(card.id).catch(()=>null);if(updatedCard){notifyApplePass(card.id).catch(error=>console.error('Apple Wallet update notification failed:',error.message));updateGooglePass(updatedCard).catch(error=>console.error('Google Wallet update failed:',error.message));}
      return send(res,200,{ok:true});
    }catch(error){await connection.rollback();throw error;}finally{connection.release();}
  }
  return send(res,404,{error:'Not found.'});
}

const server=http.createServer(async(req,res)=>{
  let url;try{url=new URL(req.url,'http://localhost');}catch{return send(res,400,{error:'Bad request.'});}
  if(url.pathname.startsWith('/api/')){try{await api(req,res,url);}catch(error){console.error('API request failed:',error.message);if(!res.headersSent)send(res,error.status||500,{error:error.status?error.message:'The service could not complete this request.'});else res.destroy();}return;}
  let pathname;try{pathname=decodeURIComponent(url.pathname);}catch{res.writeHead(400);return res.end('Bad Request');}
  if(req.method!=='GET'&&req.method!=='HEAD'){res.writeHead(405,{Allow:'GET, HEAD'});return res.end('Method Not Allowed');}
  if(pathname==='/favicon.ico'){
    res.writeHead(302,{Location:'/favicon.png'});return res.end();
  }
  if(pathname==='/apple-touch-icon-precomposed.png'){
    res.writeHead(302,{Location:'/apple-touch-icon.png'});return res.end();
  }
  const appRoute=/^\/(invite|card|reset-password|staff)\/?$/.test(pathname)||/^\/join\/[0-9a-f-]{36}$/i.test(pathname);
  const publicSiteRoute=/^\/site\/?$/.test(pathname);
  const requested=pathname==='/'||appRoute?'index.html':publicSiteRoute?'site/index.html':pathname.replace(/^\/+/, '');
  if(!['index.html','styles.css','app.js','rinero-logo.png','favicon.png','apple-touch-icon.png','vendor/html5-qrcode.min.js','site/index.html','site/rinero-logo.png','site/site.css','site/site.js'].includes(requested)){res.writeHead(404);return res.end('Not Found');}
  const filePath=path.resolve(publicRoot,requested);
  if(filePath!==publicRoot&&!filePath.startsWith(`${publicRoot}${path.sep}`)){res.writeHead(403);return res.end('Forbidden');}
  fs.stat(filePath,(error,stat)=>{if(error||!stat.isFile()){res.writeHead(404);return res.end('Not Found');}const headers={'Content-Type':mimeTypes[path.extname(filePath)]||'application/octet-stream','Content-Length':stat.size,'X-Content-Type-Options':'nosniff','Referrer-Policy':'strict-origin-when-cross-origin'};if(requested==='index.html'||requested==='site/index.html')headers['Content-Security-Policy-Report-Only']="default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; img-src 'self' data: blob: https:; font-src 'self' https://fonts.gstatic.com data:; connect-src 'self'; media-src 'self' blob:; worker-src 'self' blob:; object-src 'none'; base-uri 'self'; form-action 'self'; frame-ancestors 'none'; report-uri /api/csp-report";res.writeHead(200,headers);if(req.method==='HEAD')return res.end();fs.createReadStream(filePath).pipe(res);});
});

server.listen(port,'0.0.0.0',()=>console.log(`Rinero Stamps platform listening on port ${port}`));
