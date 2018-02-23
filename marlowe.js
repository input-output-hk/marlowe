"use strict";
var __haste_prog_id = 'a75a32c80dcccb29ca9098f0b2479102df74a641d0834513e7526bcce400a2b7';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=0,_1=new T(function(){return B(unCStr("IdentChoice "));}),_2=function(_3,_4){var _5=E(_3);return (_5._==0)?E(_4):new T2(1,_5.a,new T(function(){return B(_2(_5.b,_4));}));},_6=function(_7,_8){var _9=jsShowI(_7);return new F(function(){return _2(fromJSStr(_9),_8);});},_a=41,_b=40,_c=function(_d,_e,_f){if(_e>=0){return new F(function(){return _6(_e,_f);});}else{if(_d<=6){return new F(function(){return _6(_e,_f);});}else{return new T2(1,_b,new T(function(){var _g=jsShowI(_e);return B(_2(fromJSStr(_g),new T2(1,_a,_f)));}));}}},_h=function(_i,_j,_k){if(_i<11){return new F(function(){return _2(_1,new T(function(){return B(_c(11,E(_j),_k));},1));});}else{var _l=new T(function(){return B(_2(_1,new T(function(){return B(_c(11,E(_j),new T2(1,_a,_k)));},1)));});return new T2(1,_b,_l);}},_m=new T(function(){return B(unCStr("IdentCC "));}),_n=function(_o,_p,_q){if(_o<11){return new F(function(){return _2(_m,new T(function(){return B(_c(11,E(_p),_q));},1));});}else{var _r=new T(function(){return B(_2(_m,new T(function(){return B(_c(11,E(_p),new T2(1,_a,_q)));},1)));});return new T2(1,_b,_r);}},_s=new T(function(){return B(unCStr("ConstMoney "));}),_t=new T(function(){return B(unCStr("AddMoney "));}),_u=new T(function(){return B(unCStr("AvailableMoney "));}),_v=32,_w=function(_x,_y,_z){var _A=E(_y);switch(_A._){case 0:var _B=_A.a;if(_x<11){return new F(function(){return _2(_u,new T(function(){return B(_n(11,_B,_z));},1));});}else{var _C=new T(function(){return B(_2(_u,new T(function(){return B(_n(11,_B,new T2(1,_a,_z)));},1)));});return new T2(1,_b,_C);}break;case 1:var _D=function(_E){var _F=new T(function(){return B(_w(11,_A.a,new T2(1,_v,new T(function(){return B(_w(11,_A.b,_E));}))));},1);return new F(function(){return _2(_t,_F);});};if(_x<11){return new F(function(){return _D(_z);});}else{return new T2(1,_b,new T(function(){return B(_D(new T2(1,_a,_z)));}));}break;default:var _G=_A.a;if(_x<11){return new F(function(){return _2(_s,new T(function(){return B(_c(11,E(_G),_z));},1));});}else{var _H=new T(function(){return B(_2(_s,new T(function(){return B(_c(11,E(_G),new T2(1,_a,_z)));},1)));});return new T2(1,_b,_H);}}},_I=new T(function(){return B(unCStr("FalseObs"));}),_J=new T(function(){return B(unCStr("TrueObs"));}),_K=new T(function(){return B(unCStr("ValueGE "));}),_L=new T(function(){return B(unCStr("PersonChoseSomething "));}),_M=new T(function(){return B(unCStr("PersonChoseThis "));}),_N=new T(function(){return B(unCStr("NotObs "));}),_O=new T(function(){return B(unCStr("OrObs "));}),_P=new T(function(){return B(unCStr("AndObs "));}),_Q=new T(function(){return B(unCStr("BelowTimeout "));}),_R=function(_S,_T,_U){var _V=E(_T);switch(_V._){case 0:var _W=_V.a;if(_S<11){return new F(function(){return _2(_Q,new T(function(){return B(_c(11,E(_W),_U));},1));});}else{var _X=new T(function(){return B(_2(_Q,new T(function(){return B(_c(11,E(_W),new T2(1,_a,_U)));},1)));});return new T2(1,_b,_X);}break;case 1:var _Y=function(_Z){var _10=new T(function(){return B(_R(11,_V.a,new T2(1,_v,new T(function(){return B(_R(11,_V.b,_Z));}))));},1);return new F(function(){return _2(_P,_10);});};if(_S<11){return new F(function(){return _Y(_U);});}else{return new T2(1,_b,new T(function(){return B(_Y(new T2(1,_a,_U)));}));}break;case 2:var _11=function(_12){var _13=new T(function(){return B(_R(11,_V.a,new T2(1,_v,new T(function(){return B(_R(11,_V.b,_12));}))));},1);return new F(function(){return _2(_O,_13);});};if(_S<11){return new F(function(){return _11(_U);});}else{return new T2(1,_b,new T(function(){return B(_11(new T2(1,_a,_U)));}));}break;case 3:var _14=_V.a;if(_S<11){return new F(function(){return _2(_N,new T(function(){return B(_R(11,_14,_U));},1));});}else{var _15=new T(function(){return B(_2(_N,new T(function(){return B(_R(11,_14,new T2(1,_a,_U)));},1)));});return new T2(1,_b,_15);}break;case 4:var _16=function(_17){var _18=new T(function(){var _19=new T(function(){return B(_c(11,E(_V.b),new T2(1,_v,new T(function(){return B(_c(11,E(_V.c),_17));}))));});return B(_h(11,_V.a,new T2(1,_v,_19)));},1);return new F(function(){return _2(_M,_18);});};if(_S<11){return new F(function(){return _16(_U);});}else{return new T2(1,_b,new T(function(){return B(_16(new T2(1,_a,_U)));}));}break;case 5:var _1a=function(_1b){return new F(function(){return _h(11,_V.a,new T2(1,_v,new T(function(){return B(_c(11,E(_V.b),_1b));})));});};if(_S<11){return new F(function(){return _2(_L,new T(function(){return B(_1a(_U));},1));});}else{var _1c=new T(function(){return B(_2(_L,new T(function(){return B(_1a(new T2(1,_a,_U)));},1)));});return new T2(1,_b,_1c);}break;case 6:var _1d=function(_1e){return new F(function(){return _w(11,_V.a,new T2(1,_v,new T(function(){return B(_w(11,_V.b,_1e));})));});};if(_S<11){return new F(function(){return _2(_K,new T(function(){return B(_1d(_U));},1));});}else{var _1f=new T(function(){return B(_2(_K,new T(function(){return B(_1d(new T2(1,_a,_U)));},1)));});return new T2(1,_b,_1f);}break;case 7:return new F(function(){return _2(_J,_U);});break;default:return new F(function(){return _2(_I,_U);});}},_1g=new T(function(){return B(unCStr("IdentPay "));}),_1h=function(_1i,_1j,_1k){if(_1i<11){return new F(function(){return _2(_1g,new T(function(){return B(_c(11,E(_1j),_1k));},1));});}else{var _1l=new T(function(){return B(_2(_1g,new T(function(){return B(_c(11,E(_1j),new T2(1,_a,_1k)));},1)));});return new T2(1,_b,_1l);}},_1m=new T(function(){return B(unCStr("Null"));}),_1n=new T(function(){return B(unCStr("When "));}),_1o=new T(function(){return B(unCStr("CommitCash "));}),_1p=new T(function(){return B(unCStr("Choice "));}),_1q=new T(function(){return B(unCStr("Both "));}),_1r=new T(function(){return B(unCStr("Pay "));}),_1s=new T(function(){return B(unCStr("RedeemCC "));}),_1t=function(_1u,_1v,_1w){var _1x=E(_1v);switch(_1x._){case 0:return new F(function(){return _2(_1m,_1w);});break;case 1:var _1y=function(_1z){var _1A=new T(function(){return B(_n(11,_1x.a,new T2(1,_v,new T(function(){return B(_1t(11,_1x.b,_1z));}))));},1);return new F(function(){return _2(_1s,_1A);});};if(_1u<11){return new F(function(){return _1y(_1w);});}else{return new T2(1,_b,new T(function(){return B(_1y(new T2(1,_a,_1w)));}));}break;case 2:var _1B=function(_1C){var _1D=new T(function(){var _1E=new T(function(){var _1F=new T(function(){var _1G=new T(function(){var _1H=new T(function(){return B(_c(11,E(_1x.e),new T2(1,_v,new T(function(){return B(_1t(11,_1x.f,_1C));}))));});return B(_c(11,E(_1x.d),new T2(1,_v,_1H)));});return B(_c(11,E(_1x.c),new T2(1,_v,_1G)));});return B(_c(11,E(_1x.b),new T2(1,_v,_1F)));});return B(_1h(11,_1x.a,new T2(1,_v,_1E)));},1);return new F(function(){return _2(_1r,_1D);});};if(_1u<11){return new F(function(){return _1B(_1w);});}else{return new T2(1,_b,new T(function(){return B(_1B(new T2(1,_a,_1w)));}));}break;case 3:var _1I=function(_1J){var _1K=new T(function(){return B(_1t(11,_1x.a,new T2(1,_v,new T(function(){return B(_1t(11,_1x.b,_1J));}))));},1);return new F(function(){return _2(_1q,_1K);});};if(_1u<11){return new F(function(){return _1I(_1w);});}else{return new T2(1,_b,new T(function(){return B(_1I(new T2(1,_a,_1w)));}));}break;case 4:var _1L=function(_1M){var _1N=new T(function(){return B(_1t(11,_1x.b,new T2(1,_v,new T(function(){return B(_1t(11,_1x.c,_1M));}))));});return new F(function(){return _R(11,_1x.a,new T2(1,_v,_1N));});};if(_1u<11){return new F(function(){return _2(_1p,new T(function(){return B(_1L(_1w));},1));});}else{var _1O=new T(function(){return B(_2(_1p,new T(function(){return B(_1L(new T2(1,_a,_1w)));},1)));});return new T2(1,_b,_1O);}break;case 5:var _1P=function(_1Q){var _1R=new T(function(){var _1S=new T(function(){var _1T=new T(function(){var _1U=new T(function(){var _1V=new T(function(){return B(_c(11,E(_1x.e),new T2(1,_v,new T(function(){return B(_1t(11,_1x.f,_1Q));}))));});return B(_c(11,E(_1x.d),new T2(1,_v,_1V)));});return B(_c(11,E(_1x.c),new T2(1,_v,_1U)));});return B(_c(11,E(_1x.b),new T2(1,_v,_1T)));});return B(_n(11,_1x.a,new T2(1,_v,_1S)));},1);return new F(function(){return _2(_1o,_1R);});};if(_1u<11){return new F(function(){return _1P(_1w);});}else{return new T2(1,_b,new T(function(){return B(_1P(new T2(1,_a,_1w)));}));}break;default:var _1W=function(_1X){var _1Y=new T(function(){var _1Z=new T(function(){var _20=new T(function(){return B(_1t(11,_1x.c,new T2(1,_v,new T(function(){return B(_1t(11,_1x.d,_1X));}))));});return B(_c(11,E(_1x.b),new T2(1,_v,_20)));});return B(_R(11,_1x.a,new T2(1,_v,_1Z)));},1);return new F(function(){return _2(_1n,_1Y);});};if(_1u<11){return new F(function(){return _1W(_1w);});}else{return new T2(1,_b,new T(function(){return B(_1W(new T2(1,_a,_1w)));}));}}},_21=__Z,_22=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_23=new T(function(){return B(err(_22));}),_24=new T(function(){return B(unCStr("codeArea"));}),_25=function(_){return _0;},_26="(function (t, s) {document.getElementById(t).value = s})",_27=function(_28,_29,_){var _2a=eval(E(_26)),_2b=__app2(E(_2a),toJSStr(E(_28)),toJSStr(E(_29)));return new F(function(){return _25(_);});},_2c=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_2d=new T(function(){return B(err(_2c));}),_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2g=new T(function(){return B(unCStr("PatternMatchFail"));}),_2h=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_2e,_2f,_2g),_2i=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_2h,_21,_21),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=function(_2z){return E(E(_2z).a);},_2A=function(_2B){return new T2(0,_2C,_2B);},_2D=function(_2E,_2F){return new F(function(){return _2(E(_2E).a,_2F);});},_2G=44,_2H=93,_2I=91,_2J=function(_2K,_2L,_2M){var _2N=E(_2L);if(!_2N._){return new F(function(){return unAppCStr("[]",_2M);});}else{var _2O=new T(function(){var _2P=new T(function(){var _2Q=function(_2R){var _2S=E(_2R);if(!_2S._){return E(new T2(1,_2H,_2M));}else{var _2T=new T(function(){return B(A2(_2K,_2S.a,new T(function(){return B(_2Q(_2S.b));})));});return new T2(1,_2G,_2T);}};return B(_2Q(_2N.b));});return B(A2(_2K,_2N.a,_2P));});return new T2(1,_2I,_2O);}},_2U=function(_2V,_2W){return new F(function(){return _2J(_2D,_2V,_2W);});},_2X=function(_2Y,_2Z,_30){return new F(function(){return _2(E(_2Z).a,_30);});},_31=new T3(0,_2X,_2y,_2U),_2C=new T(function(){return new T5(0,_2j,_31,_2A,_2v,_2y);}),_32=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_33=function(_34){return E(E(_34).c);},_35=function(_36,_37){return new F(function(){return die(new T(function(){return B(A2(_33,_37,_36));}));});},_38=function(_39,_3a){return new F(function(){return _35(_39,_3a);});},_3b=function(_3c,_3d){var _3e=E(_3d);if(!_3e._){return new T2(0,_21,_21);}else{var _3f=_3e.a;if(!B(A1(_3c,_3f))){return new T2(0,_21,_3e);}else{var _3g=new T(function(){var _3h=B(_3b(_3c,_3e.b));return new T2(0,_3h.a,_3h.b);});return new T2(0,new T2(1,_3f,new T(function(){return E(E(_3g).a);})),new T(function(){return E(E(_3g).b);}));}}},_3i=32,_3j=new T(function(){return B(unCStr("\n"));}),_3k=function(_3l){return (E(_3l)==124)?false:true;},_3m=function(_3n,_3o){var _3p=B(_3b(_3k,B(unCStr(_3n)))),_3q=_3p.a,_3r=function(_3s,_3t){var _3u=new T(function(){var _3v=new T(function(){return B(_2(_3o,new T(function(){return B(_2(_3t,_3j));},1)));});return B(unAppCStr(": ",_3v));},1);return new F(function(){return _2(_3s,_3u);});},_3w=E(_3p.b);if(!_3w._){return new F(function(){return _3r(_3q,_21);});}else{if(E(_3w.a)==124){return new F(function(){return _3r(_3q,new T2(1,_3i,_3w.b));});}else{return new F(function(){return _3r(_3q,_21);});}}},_3x=function(_3y){return new F(function(){return _38(new T1(0,new T(function(){return B(_3m(_3y,_32));})),_2C);});},_3z=new T(function(){return B(_3x("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_3A=function(_3B,_3C){while(1){var _3D=B((function(_3E,_3F){var _3G=E(_3E);switch(_3G._){case 0:var _3H=E(_3F);if(!_3H._){return __Z;}else{_3B=B(A1(_3G.a,_3H.a));_3C=_3H.b;return __continue;}break;case 1:var _3I=B(A1(_3G.a,_3F)),_3J=_3F;_3B=_3I;_3C=_3J;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_3G.a,_3F),new T(function(){return B(_3A(_3G.b,_3F));}));default:return E(_3G.a);}})(_3B,_3C));if(_3D!=__continue){return _3D;}}},_3K=function(_3L,_3M){var _3N=function(_3O){var _3P=E(_3M);if(_3P._==3){return new T2(3,_3P.a,new T(function(){return B(_3K(_3L,_3P.b));}));}else{var _3Q=E(_3L);if(_3Q._==2){return E(_3P);}else{var _3R=E(_3P);if(_3R._==2){return E(_3Q);}else{var _3S=function(_3T){var _3U=E(_3R);if(_3U._==4){var _3V=function(_3W){return new T1(4,new T(function(){return B(_2(B(_3A(_3Q,_3W)),_3U.a));}));};return new T1(1,_3V);}else{var _3X=E(_3Q);if(_3X._==1){var _3Y=_3X.a,_3Z=E(_3U);if(!_3Z._){return new T1(1,function(_40){return new F(function(){return _3K(B(A1(_3Y,_40)),_3Z);});});}else{var _41=function(_42){return new F(function(){return _3K(B(A1(_3Y,_42)),new T(function(){return B(A1(_3Z.a,_42));}));});};return new T1(1,_41);}}else{var _43=E(_3U);if(!_43._){return E(_3z);}else{var _44=function(_45){return new F(function(){return _3K(_3X,new T(function(){return B(A1(_43.a,_45));}));});};return new T1(1,_44);}}}},_46=E(_3Q);switch(_46._){case 1:var _47=E(_3R);if(_47._==4){var _48=function(_49){return new T1(4,new T(function(){return B(_2(B(_3A(B(A1(_46.a,_49)),_49)),_47.a));}));};return new T1(1,_48);}else{return new F(function(){return _3S(_);});}break;case 4:var _4a=_46.a,_4b=E(_3R);switch(_4b._){case 0:var _4c=function(_4d){var _4e=new T(function(){return B(_2(_4a,new T(function(){return B(_3A(_4b,_4d));},1)));});return new T1(4,_4e);};return new T1(1,_4c);case 1:var _4f=function(_4g){var _4h=new T(function(){return B(_2(_4a,new T(function(){return B(_3A(B(A1(_4b.a,_4g)),_4g));},1)));});return new T1(4,_4h);};return new T1(1,_4f);default:return new T1(4,new T(function(){return B(_2(_4a,_4b.a));}));}break;default:return new F(function(){return _3S(_);});}}}}},_4i=E(_3L);switch(_4i._){case 0:var _4j=E(_3M);if(!_4j._){var _4k=function(_4l){return new F(function(){return _3K(B(A1(_4i.a,_4l)),new T(function(){return B(A1(_4j.a,_4l));}));});};return new T1(0,_4k);}else{return new F(function(){return _3N(_);});}break;case 3:return new T2(3,_4i.a,new T(function(){return B(_3K(_4i.b,_3M));}));default:return new F(function(){return _3N(_);});}},_4m=11,_4n=new T(function(){return B(unCStr("IdentCC"));}),_4o=new T(function(){return B(unCStr("("));}),_4p=new T(function(){return B(unCStr(")"));}),_4q=function(_4r,_4s){while(1){var _4t=E(_4r);if(!_4t._){return (E(_4s)._==0)?true:false;}else{var _4u=E(_4s);if(!_4u._){return false;}else{if(E(_4t.a)!=E(_4u.a)){return false;}else{_4r=_4t.b;_4s=_4u.b;continue;}}}}},_4v=function(_4w,_4x){return E(_4w)!=E(_4x);},_4y=function(_4z,_4A){return E(_4z)==E(_4A);},_4B=new T2(0,_4y,_4v),_4C=function(_4D,_4E){while(1){var _4F=E(_4D);if(!_4F._){return (E(_4E)._==0)?true:false;}else{var _4G=E(_4E);if(!_4G._){return false;}else{if(E(_4F.a)!=E(_4G.a)){return false;}else{_4D=_4F.b;_4E=_4G.b;continue;}}}}},_4H=function(_4I,_4J){return (!B(_4C(_4I,_4J)))?true:false;},_4K=new T2(0,_4C,_4H),_4L=function(_4M,_4N){var _4O=E(_4M);switch(_4O._){case 0:return new T1(0,function(_4P){return new F(function(){return _4L(B(A1(_4O.a,_4P)),_4N);});});case 1:return new T1(1,function(_4Q){return new F(function(){return _4L(B(A1(_4O.a,_4Q)),_4N);});});case 2:return new T0(2);case 3:return new F(function(){return _3K(B(A1(_4N,_4O.a)),new T(function(){return B(_4L(_4O.b,_4N));}));});break;default:var _4R=function(_4S){var _4T=E(_4S);if(!_4T._){return __Z;}else{var _4U=E(_4T.a);return new F(function(){return _2(B(_3A(B(A1(_4N,_4U.a)),_4U.b)),new T(function(){return B(_4R(_4T.b));},1));});}},_4V=B(_4R(_4O.a));return (_4V._==0)?new T0(2):new T1(4,_4V);}},_4W=new T0(2),_4X=function(_4Y){return new T2(3,_4Y,_4W);},_4Z=function(_50,_51){var _52=E(_50);if(!_52){return new F(function(){return A1(_51,_0);});}else{var _53=new T(function(){return B(_4Z(_52-1|0,_51));});return new T1(0,function(_54){return E(_53);});}},_55=function(_56,_57,_58){var _59=new T(function(){return B(A1(_56,_4X));}),_5a=function(_5b,_5c,_5d,_5e){while(1){var _5f=B((function(_5g,_5h,_5i,_5j){var _5k=E(_5g);switch(_5k._){case 0:var _5l=E(_5h);if(!_5l._){return new F(function(){return A1(_57,_5j);});}else{var _5m=_5i+1|0,_5n=_5j;_5b=B(A1(_5k.a,_5l.a));_5c=_5l.b;_5d=_5m;_5e=_5n;return __continue;}break;case 1:var _5o=B(A1(_5k.a,_5h)),_5p=_5h,_5m=_5i,_5n=_5j;_5b=_5o;_5c=_5p;_5d=_5m;_5e=_5n;return __continue;case 2:return new F(function(){return A1(_57,_5j);});break;case 3:var _5q=new T(function(){return B(_4L(_5k,_5j));});return new F(function(){return _4Z(_5i,function(_5r){return E(_5q);});});break;default:return new F(function(){return _4L(_5k,_5j);});}})(_5b,_5c,_5d,_5e));if(_5f!=__continue){return _5f;}}};return function(_5s){return new F(function(){return _5a(_59,_5s,0,_58);});};},_5t=function(_5u){return new F(function(){return A1(_5u,_21);});},_5v=function(_5w,_5x){var _5y=function(_5z){var _5A=E(_5z);if(!_5A._){return E(_5t);}else{var _5B=_5A.a;if(!B(A1(_5w,_5B))){return E(_5t);}else{var _5C=new T(function(){return B(_5y(_5A.b));}),_5D=function(_5E){var _5F=new T(function(){return B(A1(_5C,function(_5G){return new F(function(){return A1(_5E,new T2(1,_5B,_5G));});}));});return new T1(0,function(_5H){return E(_5F);});};return E(_5D);}}};return function(_5I){return new F(function(){return A2(_5y,_5I,_5x);});};},_5J=new T0(6),_5K=function(_5L){return E(_5L);},_5M=new T(function(){return B(unCStr("valDig: Bad base"));}),_5N=new T(function(){return B(err(_5M));}),_5O=function(_5P,_5Q){var _5R=function(_5S,_5T){var _5U=E(_5S);if(!_5U._){var _5V=new T(function(){return B(A1(_5T,_21));});return function(_5W){return new F(function(){return A1(_5W,_5V);});};}else{var _5X=E(_5U.a),_5Y=function(_5Z){var _60=new T(function(){return B(_5R(_5U.b,function(_61){return new F(function(){return A1(_5T,new T2(1,_5Z,_61));});}));}),_62=function(_63){var _64=new T(function(){return B(A1(_60,_63));});return new T1(0,function(_65){return E(_64);});};return E(_62);};switch(E(_5P)){case 8:if(48>_5X){var _66=new T(function(){return B(A1(_5T,_21));});return function(_67){return new F(function(){return A1(_67,_66);});};}else{if(_5X>55){var _68=new T(function(){return B(A1(_5T,_21));});return function(_69){return new F(function(){return A1(_69,_68);});};}else{return new F(function(){return _5Y(_5X-48|0);});}}break;case 10:if(48>_5X){var _6a=new T(function(){return B(A1(_5T,_21));});return function(_6b){return new F(function(){return A1(_6b,_6a);});};}else{if(_5X>57){var _6c=new T(function(){return B(A1(_5T,_21));});return function(_6d){return new F(function(){return A1(_6d,_6c);});};}else{return new F(function(){return _5Y(_5X-48|0);});}}break;case 16:if(48>_5X){if(97>_5X){if(65>_5X){var _6e=new T(function(){return B(A1(_5T,_21));});return function(_6f){return new F(function(){return A1(_6f,_6e);});};}else{if(_5X>70){var _6g=new T(function(){return B(A1(_5T,_21));});return function(_6h){return new F(function(){return A1(_6h,_6g);});};}else{return new F(function(){return _5Y((_5X-65|0)+10|0);});}}}else{if(_5X>102){if(65>_5X){var _6i=new T(function(){return B(A1(_5T,_21));});return function(_6j){return new F(function(){return A1(_6j,_6i);});};}else{if(_5X>70){var _6k=new T(function(){return B(A1(_5T,_21));});return function(_6l){return new F(function(){return A1(_6l,_6k);});};}else{return new F(function(){return _5Y((_5X-65|0)+10|0);});}}}else{return new F(function(){return _5Y((_5X-97|0)+10|0);});}}}else{if(_5X>57){if(97>_5X){if(65>_5X){var _6m=new T(function(){return B(A1(_5T,_21));});return function(_6n){return new F(function(){return A1(_6n,_6m);});};}else{if(_5X>70){var _6o=new T(function(){return B(A1(_5T,_21));});return function(_6p){return new F(function(){return A1(_6p,_6o);});};}else{return new F(function(){return _5Y((_5X-65|0)+10|0);});}}}else{if(_5X>102){if(65>_5X){var _6q=new T(function(){return B(A1(_5T,_21));});return function(_6r){return new F(function(){return A1(_6r,_6q);});};}else{if(_5X>70){var _6s=new T(function(){return B(A1(_5T,_21));});return function(_6t){return new F(function(){return A1(_6t,_6s);});};}else{return new F(function(){return _5Y((_5X-65|0)+10|0);});}}}else{return new F(function(){return _5Y((_5X-97|0)+10|0);});}}}else{return new F(function(){return _5Y(_5X-48|0);});}}break;default:return E(_5N);}}},_6u=function(_6v){var _6w=E(_6v);if(!_6w._){return new T0(2);}else{return new F(function(){return A1(_5Q,_6w);});}};return function(_6x){return new F(function(){return A3(_5R,_6x,_5K,_6u);});};},_6y=16,_6z=8,_6A=function(_6B){var _6C=function(_6D){return new F(function(){return A1(_6B,new T1(5,new T2(0,_6z,_6D)));});},_6E=function(_6F){return new F(function(){return A1(_6B,new T1(5,new T2(0,_6y,_6F)));});},_6G=function(_6H){switch(E(_6H)){case 79:return new T1(1,B(_5O(_6z,_6C)));case 88:return new T1(1,B(_5O(_6y,_6E)));case 111:return new T1(1,B(_5O(_6z,_6C)));case 120:return new T1(1,B(_5O(_6y,_6E)));default:return new T0(2);}};return function(_6I){return (E(_6I)==48)?E(new T1(0,_6G)):new T0(2);};},_6J=function(_6K){return new T1(0,B(_6A(_6K)));},_6L=__Z,_6M=function(_6N){return new F(function(){return A1(_6N,_6L);});},_6O=function(_6P){return new F(function(){return A1(_6P,_6L);});},_6Q=10,_6R=new T1(0,1),_6S=new T1(0,2147483647),_6T=function(_6U,_6V){while(1){var _6W=E(_6U);if(!_6W._){var _6X=_6W.a,_6Y=E(_6V);if(!_6Y._){var _6Z=_6Y.a,_70=addC(_6X,_6Z);if(!E(_70.b)){return new T1(0,_70.a);}else{_6U=new T1(1,I_fromInt(_6X));_6V=new T1(1,I_fromInt(_6Z));continue;}}else{_6U=new T1(1,I_fromInt(_6X));_6V=_6Y;continue;}}else{var _71=E(_6V);if(!_71._){_6U=_6W;_6V=new T1(1,I_fromInt(_71.a));continue;}else{return new T1(1,I_add(_6W.a,_71.a));}}}},_72=new T(function(){return B(_6T(_6S,_6R));}),_73=function(_74){var _75=E(_74);if(!_75._){var _76=E(_75.a);return (_76==( -2147483648))?E(_72):new T1(0, -_76);}else{return new T1(1,I_negate(_75.a));}},_77=new T1(0,10),_78=function(_79,_7a){while(1){var _7b=E(_79);if(!_7b._){return E(_7a);}else{var _7c=_7a+1|0;_79=_7b.b;_7a=_7c;continue;}}},_7d=function(_7e,_7f){var _7g=E(_7f);return (_7g._==0)?__Z:new T2(1,new T(function(){return B(A1(_7e,_7g.a));}),new T(function(){return B(_7d(_7e,_7g.b));}));},_7h=function(_7i){return new T1(0,_7i);},_7j=function(_7k){return new F(function(){return _7h(E(_7k));});},_7l=new T(function(){return B(unCStr("this should not happen"));}),_7m=new T(function(){return B(err(_7l));}),_7n=function(_7o,_7p){while(1){var _7q=E(_7o);if(!_7q._){var _7r=_7q.a,_7s=E(_7p);if(!_7s._){var _7t=_7s.a;if(!(imul(_7r,_7t)|0)){return new T1(0,imul(_7r,_7t)|0);}else{_7o=new T1(1,I_fromInt(_7r));_7p=new T1(1,I_fromInt(_7t));continue;}}else{_7o=new T1(1,I_fromInt(_7r));_7p=_7s;continue;}}else{var _7u=E(_7p);if(!_7u._){_7o=_7q;_7p=new T1(1,I_fromInt(_7u.a));continue;}else{return new T1(1,I_mul(_7q.a,_7u.a));}}}},_7v=function(_7w,_7x){var _7y=E(_7x);if(!_7y._){return __Z;}else{var _7z=E(_7y.b);return (_7z._==0)?E(_7m):new T2(1,B(_6T(B(_7n(_7y.a,_7w)),_7z.a)),new T(function(){return B(_7v(_7w,_7z.b));}));}},_7A=new T1(0,0),_7B=function(_7C,_7D,_7E){while(1){var _7F=B((function(_7G,_7H,_7I){var _7J=E(_7I);if(!_7J._){return E(_7A);}else{if(!E(_7J.b)._){return E(_7J.a);}else{var _7K=E(_7H);if(_7K<=40){var _7L=function(_7M,_7N){while(1){var _7O=E(_7N);if(!_7O._){return E(_7M);}else{var _7P=B(_6T(B(_7n(_7M,_7G)),_7O.a));_7M=_7P;_7N=_7O.b;continue;}}};return new F(function(){return _7L(_7A,_7J);});}else{var _7Q=B(_7n(_7G,_7G));if(!(_7K%2)){var _7R=B(_7v(_7G,_7J));_7C=_7Q;_7D=quot(_7K+1|0,2);_7E=_7R;return __continue;}else{var _7R=B(_7v(_7G,new T2(1,_7A,_7J)));_7C=_7Q;_7D=quot(_7K+1|0,2);_7E=_7R;return __continue;}}}}})(_7C,_7D,_7E));if(_7F!=__continue){return _7F;}}},_7S=function(_7T,_7U){return new F(function(){return _7B(_7T,new T(function(){return B(_78(_7U,0));},1),B(_7d(_7j,_7U)));});},_7V=function(_7W){var _7X=new T(function(){var _7Y=new T(function(){var _7Z=function(_80){return new F(function(){return A1(_7W,new T1(1,new T(function(){return B(_7S(_77,_80));})));});};return new T1(1,B(_5O(_6Q,_7Z)));}),_81=function(_82){if(E(_82)==43){var _83=function(_84){return new F(function(){return A1(_7W,new T1(1,new T(function(){return B(_7S(_77,_84));})));});};return new T1(1,B(_5O(_6Q,_83)));}else{return new T0(2);}},_85=function(_86){if(E(_86)==45){var _87=function(_88){return new F(function(){return A1(_7W,new T1(1,new T(function(){return B(_73(B(_7S(_77,_88))));})));});};return new T1(1,B(_5O(_6Q,_87)));}else{return new T0(2);}};return B(_3K(B(_3K(new T1(0,_85),new T1(0,_81))),_7Y));});return new F(function(){return _3K(new T1(0,function(_89){return (E(_89)==101)?E(_7X):new T0(2);}),new T1(0,function(_8a){return (E(_8a)==69)?E(_7X):new T0(2);}));});},_8b=function(_8c){var _8d=function(_8e){return new F(function(){return A1(_8c,new T1(1,_8e));});};return function(_8f){return (E(_8f)==46)?new T1(1,B(_5O(_6Q,_8d))):new T0(2);};},_8g=function(_8h){return new T1(0,B(_8b(_8h)));},_8i=function(_8j){var _8k=function(_8l){var _8m=function(_8n){return new T1(1,B(_55(_7V,_6M,function(_8o){return new F(function(){return A1(_8j,new T1(5,new T3(1,_8l,_8n,_8o)));});})));};return new T1(1,B(_55(_8g,_6O,_8m)));};return new F(function(){return _5O(_6Q,_8k);});},_8p=function(_8q){return new T1(1,B(_8i(_8q)));},_8r=function(_8s){return E(E(_8s).a);},_8t=function(_8u,_8v,_8w){while(1){var _8x=E(_8w);if(!_8x._){return false;}else{if(!B(A3(_8r,_8u,_8v,_8x.a))){_8w=_8x.b;continue;}else{return true;}}}},_8y=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_8z=function(_8A){return new F(function(){return _8t(_4B,_8A,_8y);});},_8B=false,_8C=true,_8D=function(_8E){var _8F=new T(function(){return B(A1(_8E,_6z));}),_8G=new T(function(){return B(A1(_8E,_6y));});return function(_8H){switch(E(_8H)){case 79:return E(_8F);case 88:return E(_8G);case 111:return E(_8F);case 120:return E(_8G);default:return new T0(2);}};},_8I=function(_8J){return new T1(0,B(_8D(_8J)));},_8K=function(_8L){return new F(function(){return A1(_8L,_6Q);});},_8M=function(_8N){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_c(9,_8N,_21));}))));});},_8O=function(_8P){var _8Q=E(_8P);if(!_8Q._){return E(_8Q.a);}else{return new F(function(){return I_toInt(_8Q.a);});}},_8R=function(_8S,_8T){var _8U=E(_8S);if(!_8U._){var _8V=_8U.a,_8W=E(_8T);return (_8W._==0)?_8V<=_8W.a:I_compareInt(_8W.a,_8V)>=0;}else{var _8X=_8U.a,_8Y=E(_8T);return (_8Y._==0)?I_compareInt(_8X,_8Y.a)<=0:I_compare(_8X,_8Y.a)<=0;}},_8Z=function(_90){return new T0(2);},_91=function(_92){var _93=E(_92);if(!_93._){return E(_8Z);}else{var _94=_93.a,_95=E(_93.b);if(!_95._){return E(_94);}else{var _96=new T(function(){return B(_91(_95));}),_97=function(_98){return new F(function(){return _3K(B(A1(_94,_98)),new T(function(){return B(A1(_96,_98));}));});};return E(_97);}}},_99=function(_9a,_9b){var _9c=function(_9d,_9e,_9f){var _9g=E(_9d);if(!_9g._){return new F(function(){return A1(_9f,_9a);});}else{var _9h=E(_9e);if(!_9h._){return new T0(2);}else{if(E(_9g.a)!=E(_9h.a)){return new T0(2);}else{var _9i=new T(function(){return B(_9c(_9g.b,_9h.b,_9f));});return new T1(0,function(_9j){return E(_9i);});}}}};return function(_9k){return new F(function(){return _9c(_9a,_9k,_9b);});};},_9l=new T(function(){return B(unCStr("SO"));}),_9m=14,_9n=function(_9o){var _9p=new T(function(){return B(A1(_9o,_9m));});return new T1(1,B(_99(_9l,function(_9q){return E(_9p);})));},_9r=new T(function(){return B(unCStr("SOH"));}),_9s=1,_9t=function(_9u){var _9v=new T(function(){return B(A1(_9u,_9s));});return new T1(1,B(_99(_9r,function(_9w){return E(_9v);})));},_9x=function(_9y){return new T1(1,B(_55(_9t,_9n,_9y)));},_9z=new T(function(){return B(unCStr("NUL"));}),_9A=0,_9B=function(_9C){var _9D=new T(function(){return B(A1(_9C,_9A));});return new T1(1,B(_99(_9z,function(_9E){return E(_9D);})));},_9F=new T(function(){return B(unCStr("STX"));}),_9G=2,_9H=function(_9I){var _9J=new T(function(){return B(A1(_9I,_9G));});return new T1(1,B(_99(_9F,function(_9K){return E(_9J);})));},_9L=new T(function(){return B(unCStr("ETX"));}),_9M=3,_9N=function(_9O){var _9P=new T(function(){return B(A1(_9O,_9M));});return new T1(1,B(_99(_9L,function(_9Q){return E(_9P);})));},_9R=new T(function(){return B(unCStr("EOT"));}),_9S=4,_9T=function(_9U){var _9V=new T(function(){return B(A1(_9U,_9S));});return new T1(1,B(_99(_9R,function(_9W){return E(_9V);})));},_9X=new T(function(){return B(unCStr("ENQ"));}),_9Y=5,_9Z=function(_a0){var _a1=new T(function(){return B(A1(_a0,_9Y));});return new T1(1,B(_99(_9X,function(_a2){return E(_a1);})));},_a3=new T(function(){return B(unCStr("ACK"));}),_a4=6,_a5=function(_a6){var _a7=new T(function(){return B(A1(_a6,_a4));});return new T1(1,B(_99(_a3,function(_a8){return E(_a7);})));},_a9=new T(function(){return B(unCStr("BEL"));}),_aa=7,_ab=function(_ac){var _ad=new T(function(){return B(A1(_ac,_aa));});return new T1(1,B(_99(_a9,function(_ae){return E(_ad);})));},_af=new T(function(){return B(unCStr("BS"));}),_ag=8,_ah=function(_ai){var _aj=new T(function(){return B(A1(_ai,_ag));});return new T1(1,B(_99(_af,function(_ak){return E(_aj);})));},_al=new T(function(){return B(unCStr("HT"));}),_am=9,_an=function(_ao){var _ap=new T(function(){return B(A1(_ao,_am));});return new T1(1,B(_99(_al,function(_aq){return E(_ap);})));},_ar=new T(function(){return B(unCStr("LF"));}),_as=10,_at=function(_au){var _av=new T(function(){return B(A1(_au,_as));});return new T1(1,B(_99(_ar,function(_aw){return E(_av);})));},_ax=new T(function(){return B(unCStr("VT"));}),_ay=11,_az=function(_aA){var _aB=new T(function(){return B(A1(_aA,_ay));});return new T1(1,B(_99(_ax,function(_aC){return E(_aB);})));},_aD=new T(function(){return B(unCStr("FF"));}),_aE=12,_aF=function(_aG){var _aH=new T(function(){return B(A1(_aG,_aE));});return new T1(1,B(_99(_aD,function(_aI){return E(_aH);})));},_aJ=new T(function(){return B(unCStr("CR"));}),_aK=13,_aL=function(_aM){var _aN=new T(function(){return B(A1(_aM,_aK));});return new T1(1,B(_99(_aJ,function(_aO){return E(_aN);})));},_aP=new T(function(){return B(unCStr("SI"));}),_aQ=15,_aR=function(_aS){var _aT=new T(function(){return B(A1(_aS,_aQ));});return new T1(1,B(_99(_aP,function(_aU){return E(_aT);})));},_aV=new T(function(){return B(unCStr("DLE"));}),_aW=16,_aX=function(_aY){var _aZ=new T(function(){return B(A1(_aY,_aW));});return new T1(1,B(_99(_aV,function(_b0){return E(_aZ);})));},_b1=new T(function(){return B(unCStr("DC1"));}),_b2=17,_b3=function(_b4){var _b5=new T(function(){return B(A1(_b4,_b2));});return new T1(1,B(_99(_b1,function(_b6){return E(_b5);})));},_b7=new T(function(){return B(unCStr("DC2"));}),_b8=18,_b9=function(_ba){var _bb=new T(function(){return B(A1(_ba,_b8));});return new T1(1,B(_99(_b7,function(_bc){return E(_bb);})));},_bd=new T(function(){return B(unCStr("DC3"));}),_be=19,_bf=function(_bg){var _bh=new T(function(){return B(A1(_bg,_be));});return new T1(1,B(_99(_bd,function(_bi){return E(_bh);})));},_bj=new T(function(){return B(unCStr("DC4"));}),_bk=20,_bl=function(_bm){var _bn=new T(function(){return B(A1(_bm,_bk));});return new T1(1,B(_99(_bj,function(_bo){return E(_bn);})));},_bp=new T(function(){return B(unCStr("NAK"));}),_bq=21,_br=function(_bs){var _bt=new T(function(){return B(A1(_bs,_bq));});return new T1(1,B(_99(_bp,function(_bu){return E(_bt);})));},_bv=new T(function(){return B(unCStr("SYN"));}),_bw=22,_bx=function(_by){var _bz=new T(function(){return B(A1(_by,_bw));});return new T1(1,B(_99(_bv,function(_bA){return E(_bz);})));},_bB=new T(function(){return B(unCStr("ETB"));}),_bC=23,_bD=function(_bE){var _bF=new T(function(){return B(A1(_bE,_bC));});return new T1(1,B(_99(_bB,function(_bG){return E(_bF);})));},_bH=new T(function(){return B(unCStr("CAN"));}),_bI=24,_bJ=function(_bK){var _bL=new T(function(){return B(A1(_bK,_bI));});return new T1(1,B(_99(_bH,function(_bM){return E(_bL);})));},_bN=new T(function(){return B(unCStr("EM"));}),_bO=25,_bP=function(_bQ){var _bR=new T(function(){return B(A1(_bQ,_bO));});return new T1(1,B(_99(_bN,function(_bS){return E(_bR);})));},_bT=new T(function(){return B(unCStr("SUB"));}),_bU=26,_bV=function(_bW){var _bX=new T(function(){return B(A1(_bW,_bU));});return new T1(1,B(_99(_bT,function(_bY){return E(_bX);})));},_bZ=new T(function(){return B(unCStr("ESC"));}),_c0=27,_c1=function(_c2){var _c3=new T(function(){return B(A1(_c2,_c0));});return new T1(1,B(_99(_bZ,function(_c4){return E(_c3);})));},_c5=new T(function(){return B(unCStr("FS"));}),_c6=28,_c7=function(_c8){var _c9=new T(function(){return B(A1(_c8,_c6));});return new T1(1,B(_99(_c5,function(_ca){return E(_c9);})));},_cb=new T(function(){return B(unCStr("GS"));}),_cc=29,_cd=function(_ce){var _cf=new T(function(){return B(A1(_ce,_cc));});return new T1(1,B(_99(_cb,function(_cg){return E(_cf);})));},_ch=new T(function(){return B(unCStr("RS"));}),_ci=30,_cj=function(_ck){var _cl=new T(function(){return B(A1(_ck,_ci));});return new T1(1,B(_99(_ch,function(_cm){return E(_cl);})));},_cn=new T(function(){return B(unCStr("US"));}),_co=31,_cp=function(_cq){var _cr=new T(function(){return B(A1(_cq,_co));});return new T1(1,B(_99(_cn,function(_cs){return E(_cr);})));},_ct=new T(function(){return B(unCStr("SP"));}),_cu=32,_cv=function(_cw){var _cx=new T(function(){return B(A1(_cw,_cu));});return new T1(1,B(_99(_ct,function(_cy){return E(_cx);})));},_cz=new T(function(){return B(unCStr("DEL"));}),_cA=127,_cB=function(_cC){var _cD=new T(function(){return B(A1(_cC,_cA));});return new T1(1,B(_99(_cz,function(_cE){return E(_cD);})));},_cF=new T2(1,_cB,_21),_cG=new T2(1,_cv,_cF),_cH=new T2(1,_cp,_cG),_cI=new T2(1,_cj,_cH),_cJ=new T2(1,_cd,_cI),_cK=new T2(1,_c7,_cJ),_cL=new T2(1,_c1,_cK),_cM=new T2(1,_bV,_cL),_cN=new T2(1,_bP,_cM),_cO=new T2(1,_bJ,_cN),_cP=new T2(1,_bD,_cO),_cQ=new T2(1,_bx,_cP),_cR=new T2(1,_br,_cQ),_cS=new T2(1,_bl,_cR),_cT=new T2(1,_bf,_cS),_cU=new T2(1,_b9,_cT),_cV=new T2(1,_b3,_cU),_cW=new T2(1,_aX,_cV),_cX=new T2(1,_aR,_cW),_cY=new T2(1,_aL,_cX),_cZ=new T2(1,_aF,_cY),_d0=new T2(1,_az,_cZ),_d1=new T2(1,_at,_d0),_d2=new T2(1,_an,_d1),_d3=new T2(1,_ah,_d2),_d4=new T2(1,_ab,_d3),_d5=new T2(1,_a5,_d4),_d6=new T2(1,_9Z,_d5),_d7=new T2(1,_9T,_d6),_d8=new T2(1,_9N,_d7),_d9=new T2(1,_9H,_d8),_da=new T2(1,_9B,_d9),_db=new T2(1,_9x,_da),_dc=new T(function(){return B(_91(_db));}),_dd=34,_de=new T1(0,1114111),_df=92,_dg=39,_dh=function(_di){var _dj=new T(function(){return B(A1(_di,_aa));}),_dk=new T(function(){return B(A1(_di,_ag));}),_dl=new T(function(){return B(A1(_di,_am));}),_dm=new T(function(){return B(A1(_di,_as));}),_dn=new T(function(){return B(A1(_di,_ay));}),_do=new T(function(){return B(A1(_di,_aE));}),_dp=new T(function(){return B(A1(_di,_aK));}),_dq=new T(function(){return B(A1(_di,_df));}),_dr=new T(function(){return B(A1(_di,_dg));}),_ds=new T(function(){return B(A1(_di,_dd));}),_dt=new T(function(){var _du=function(_dv){var _dw=new T(function(){return B(_7h(E(_dv)));}),_dx=function(_dy){var _dz=B(_7S(_dw,_dy));if(!B(_8R(_dz,_de))){return new T0(2);}else{return new F(function(){return A1(_di,new T(function(){var _dA=B(_8O(_dz));if(_dA>>>0>1114111){return B(_8M(_dA));}else{return _dA;}}));});}};return new T1(1,B(_5O(_dv,_dx)));},_dB=new T(function(){var _dC=new T(function(){return B(A1(_di,_co));}),_dD=new T(function(){return B(A1(_di,_ci));}),_dE=new T(function(){return B(A1(_di,_cc));}),_dF=new T(function(){return B(A1(_di,_c6));}),_dG=new T(function(){return B(A1(_di,_c0));}),_dH=new T(function(){return B(A1(_di,_bU));}),_dI=new T(function(){return B(A1(_di,_bO));}),_dJ=new T(function(){return B(A1(_di,_bI));}),_dK=new T(function(){return B(A1(_di,_bC));}),_dL=new T(function(){return B(A1(_di,_bw));}),_dM=new T(function(){return B(A1(_di,_bq));}),_dN=new T(function(){return B(A1(_di,_bk));}),_dO=new T(function(){return B(A1(_di,_be));}),_dP=new T(function(){return B(A1(_di,_b8));}),_dQ=new T(function(){return B(A1(_di,_b2));}),_dR=new T(function(){return B(A1(_di,_aW));}),_dS=new T(function(){return B(A1(_di,_aQ));}),_dT=new T(function(){return B(A1(_di,_9m));}),_dU=new T(function(){return B(A1(_di,_a4));}),_dV=new T(function(){return B(A1(_di,_9Y));}),_dW=new T(function(){return B(A1(_di,_9S));}),_dX=new T(function(){return B(A1(_di,_9M));}),_dY=new T(function(){return B(A1(_di,_9G));}),_dZ=new T(function(){return B(A1(_di,_9s));}),_e0=new T(function(){return B(A1(_di,_9A));}),_e1=function(_e2){switch(E(_e2)){case 64:return E(_e0);case 65:return E(_dZ);case 66:return E(_dY);case 67:return E(_dX);case 68:return E(_dW);case 69:return E(_dV);case 70:return E(_dU);case 71:return E(_dj);case 72:return E(_dk);case 73:return E(_dl);case 74:return E(_dm);case 75:return E(_dn);case 76:return E(_do);case 77:return E(_dp);case 78:return E(_dT);case 79:return E(_dS);case 80:return E(_dR);case 81:return E(_dQ);case 82:return E(_dP);case 83:return E(_dO);case 84:return E(_dN);case 85:return E(_dM);case 86:return E(_dL);case 87:return E(_dK);case 88:return E(_dJ);case 89:return E(_dI);case 90:return E(_dH);case 91:return E(_dG);case 92:return E(_dF);case 93:return E(_dE);case 94:return E(_dD);case 95:return E(_dC);default:return new T0(2);}};return B(_3K(new T1(0,function(_e3){return (E(_e3)==94)?E(new T1(0,_e1)):new T0(2);}),new T(function(){return B(A1(_dc,_di));})));});return B(_3K(new T1(1,B(_55(_8I,_8K,_du))),_dB));});return new F(function(){return _3K(new T1(0,function(_e4){switch(E(_e4)){case 34:return E(_ds);case 39:return E(_dr);case 92:return E(_dq);case 97:return E(_dj);case 98:return E(_dk);case 102:return E(_do);case 110:return E(_dm);case 114:return E(_dp);case 116:return E(_dl);case 118:return E(_dn);default:return new T0(2);}}),_dt);});},_e5=function(_e6){return new F(function(){return A1(_e6,_0);});},_e7=function(_e8){var _e9=E(_e8);if(!_e9._){return E(_e5);}else{var _ea=E(_e9.a),_eb=_ea>>>0,_ec=new T(function(){return B(_e7(_e9.b));});if(_eb>887){var _ed=u_iswspace(_ea);if(!E(_ed)){return E(_e5);}else{var _ee=function(_ef){var _eg=new T(function(){return B(A1(_ec,_ef));});return new T1(0,function(_eh){return E(_eg);});};return E(_ee);}}else{var _ei=E(_eb);if(_ei==32){var _ej=function(_ek){var _el=new T(function(){return B(A1(_ec,_ek));});return new T1(0,function(_em){return E(_el);});};return E(_ej);}else{if(_ei-9>>>0>4){if(E(_ei)==160){var _en=function(_eo){var _ep=new T(function(){return B(A1(_ec,_eo));});return new T1(0,function(_eq){return E(_ep);});};return E(_en);}else{return E(_e5);}}else{var _er=function(_es){var _et=new T(function(){return B(A1(_ec,_es));});return new T1(0,function(_eu){return E(_et);});};return E(_er);}}}}},_ev=function(_ew){var _ex=new T(function(){return B(_ev(_ew));}),_ey=function(_ez){return (E(_ez)==92)?E(_ex):new T0(2);},_eA=function(_eB){return E(new T1(0,_ey));},_eC=new T1(1,function(_eD){return new F(function(){return A2(_e7,_eD,_eA);});}),_eE=new T(function(){return B(_dh(function(_eF){return new F(function(){return A1(_ew,new T2(0,_eF,_8C));});}));}),_eG=function(_eH){var _eI=E(_eH);if(_eI==38){return E(_ex);}else{var _eJ=_eI>>>0;if(_eJ>887){var _eK=u_iswspace(_eI);return (E(_eK)==0)?new T0(2):E(_eC);}else{var _eL=E(_eJ);return (_eL==32)?E(_eC):(_eL-9>>>0>4)?(E(_eL)==160)?E(_eC):new T0(2):E(_eC);}}};return new F(function(){return _3K(new T1(0,function(_eM){return (E(_eM)==92)?E(new T1(0,_eG)):new T0(2);}),new T1(0,function(_eN){var _eO=E(_eN);if(E(_eO)==92){return E(_eE);}else{return new F(function(){return A1(_ew,new T2(0,_eO,_8B));});}}));});},_eP=function(_eQ,_eR){var _eS=new T(function(){return B(A1(_eR,new T1(1,new T(function(){return B(A1(_eQ,_21));}))));}),_eT=function(_eU){var _eV=E(_eU),_eW=E(_eV.a);if(E(_eW)==34){if(!E(_eV.b)){return E(_eS);}else{return new F(function(){return _eP(function(_eX){return new F(function(){return A1(_eQ,new T2(1,_eW,_eX));});},_eR);});}}else{return new F(function(){return _eP(function(_eY){return new F(function(){return A1(_eQ,new T2(1,_eW,_eY));});},_eR);});}};return new F(function(){return _ev(_eT);});},_eZ=new T(function(){return B(unCStr("_\'"));}),_f0=function(_f1){var _f2=u_iswalnum(_f1);if(!E(_f2)){return new F(function(){return _8t(_4B,_f1,_eZ);});}else{return true;}},_f3=function(_f4){return new F(function(){return _f0(E(_f4));});},_f5=new T(function(){return B(unCStr(",;()[]{}`"));}),_f6=new T(function(){return B(unCStr("=>"));}),_f7=new T2(1,_f6,_21),_f8=new T(function(){return B(unCStr("~"));}),_f9=new T2(1,_f8,_f7),_fa=new T(function(){return B(unCStr("@"));}),_fb=new T2(1,_fa,_f9),_fc=new T(function(){return B(unCStr("->"));}),_fd=new T2(1,_fc,_fb),_fe=new T(function(){return B(unCStr("<-"));}),_ff=new T2(1,_fe,_fd),_fg=new T(function(){return B(unCStr("|"));}),_fh=new T2(1,_fg,_ff),_fi=new T(function(){return B(unCStr("\\"));}),_fj=new T2(1,_fi,_fh),_fk=new T(function(){return B(unCStr("="));}),_fl=new T2(1,_fk,_fj),_fm=new T(function(){return B(unCStr("::"));}),_fn=new T2(1,_fm,_fl),_fo=new T(function(){return B(unCStr(".."));}),_fp=new T2(1,_fo,_fn),_fq=function(_fr){var _fs=new T(function(){return B(A1(_fr,_5J));}),_ft=new T(function(){var _fu=new T(function(){var _fv=function(_fw){var _fx=new T(function(){return B(A1(_fr,new T1(0,_fw)));});return new T1(0,function(_fy){return (E(_fy)==39)?E(_fx):new T0(2);});};return B(_dh(_fv));}),_fz=function(_fA){var _fB=E(_fA);switch(E(_fB)){case 39:return new T0(2);case 92:return E(_fu);default:var _fC=new T(function(){return B(A1(_fr,new T1(0,_fB)));});return new T1(0,function(_fD){return (E(_fD)==39)?E(_fC):new T0(2);});}},_fE=new T(function(){var _fF=new T(function(){return B(_eP(_5K,_fr));}),_fG=new T(function(){var _fH=new T(function(){var _fI=new T(function(){var _fJ=function(_fK){var _fL=E(_fK),_fM=u_iswalpha(_fL);return (E(_fM)==0)?(E(_fL)==95)?new T1(1,B(_5v(_f3,function(_fN){return new F(function(){return A1(_fr,new T1(3,new T2(1,_fL,_fN)));});}))):new T0(2):new T1(1,B(_5v(_f3,function(_fO){return new F(function(){return A1(_fr,new T1(3,new T2(1,_fL,_fO)));});})));};return B(_3K(new T1(0,_fJ),new T(function(){return new T1(1,B(_55(_6J,_8p,_fr)));})));}),_fP=function(_fQ){return (!B(_8t(_4B,_fQ,_8y)))?new T0(2):new T1(1,B(_5v(_8z,function(_fR){var _fS=new T2(1,_fQ,_fR);if(!B(_8t(_4K,_fS,_fp))){return new F(function(){return A1(_fr,new T1(4,_fS));});}else{return new F(function(){return A1(_fr,new T1(2,_fS));});}})));};return B(_3K(new T1(0,_fP),_fI));});return B(_3K(new T1(0,function(_fT){if(!B(_8t(_4B,_fT,_f5))){return new T0(2);}else{return new F(function(){return A1(_fr,new T1(2,new T2(1,_fT,_21)));});}}),_fH));});return B(_3K(new T1(0,function(_fU){return (E(_fU)==34)?E(_fF):new T0(2);}),_fG));});return B(_3K(new T1(0,function(_fV){return (E(_fV)==39)?E(new T1(0,_fz)):new T0(2);}),_fE));});return new F(function(){return _3K(new T1(1,function(_fW){return (E(_fW)._==0)?E(_fs):new T0(2);}),_ft);});},_fX=0,_fY=function(_fZ,_g0){var _g1=new T(function(){var _g2=new T(function(){var _g3=function(_g4){var _g5=new T(function(){var _g6=new T(function(){return B(A1(_g0,_g4));});return B(_fq(function(_g7){var _g8=E(_g7);return (_g8._==2)?(!B(_4q(_g8.a,_4p)))?new T0(2):E(_g6):new T0(2);}));}),_g9=function(_ga){return E(_g5);};return new T1(1,function(_gb){return new F(function(){return A2(_e7,_gb,_g9);});});};return B(A2(_fZ,_fX,_g3));});return B(_fq(function(_gc){var _gd=E(_gc);return (_gd._==2)?(!B(_4q(_gd.a,_4o)))?new T0(2):E(_g2):new T0(2);}));}),_ge=function(_gf){return E(_g1);};return function(_gg){return new F(function(){return A2(_e7,_gg,_ge);});};},_gh=function(_gi,_gj){var _gk=function(_gl){var _gm=new T(function(){return B(A1(_gi,_gl));}),_gn=function(_go){return new F(function(){return _3K(B(A1(_gm,_go)),new T(function(){return new T1(1,B(_fY(_gk,_go)));}));});};return E(_gn);},_gp=new T(function(){return B(A1(_gi,_gj));}),_gq=function(_gr){return new F(function(){return _3K(B(A1(_gp,_gr)),new T(function(){return new T1(1,B(_fY(_gk,_gr)));}));});};return E(_gq);},_gs=function(_gt,_gu){var _gv=function(_gw,_gx){var _gy=function(_gz){return new F(function(){return A1(_gx,new T(function(){return  -E(_gz);}));});},_gA=new T(function(){return B(_fq(function(_gB){return new F(function(){return A3(_gt,_gB,_gw,_gy);});}));}),_gC=function(_gD){return E(_gA);},_gE=function(_gF){return new F(function(){return A2(_e7,_gF,_gC);});},_gG=new T(function(){return B(_fq(function(_gH){var _gI=E(_gH);if(_gI._==4){var _gJ=E(_gI.a);if(!_gJ._){return new F(function(){return A3(_gt,_gI,_gw,_gx);});}else{if(E(_gJ.a)==45){if(!E(_gJ.b)._){return E(new T1(1,_gE));}else{return new F(function(){return A3(_gt,_gI,_gw,_gx);});}}else{return new F(function(){return A3(_gt,_gI,_gw,_gx);});}}}else{return new F(function(){return A3(_gt,_gI,_gw,_gx);});}}));}),_gK=function(_gL){return E(_gG);};return new T1(1,function(_gM){return new F(function(){return A2(_e7,_gM,_gK);});});};return new F(function(){return _gh(_gv,_gu);});},_gN=function(_gO){var _gP=E(_gO);if(!_gP._){var _gQ=_gP.b,_gR=new T(function(){return B(_7B(new T(function(){return B(_7h(E(_gP.a)));}),new T(function(){return B(_78(_gQ,0));},1),B(_7d(_7j,_gQ))));});return new T1(1,_gR);}else{return (E(_gP.b)._==0)?(E(_gP.c)._==0)?new T1(1,new T(function(){return B(_7S(_77,_gP.a));})):__Z:__Z;}},_gS=function(_gT,_gU){return new T0(2);},_gV=function(_gW){var _gX=E(_gW);if(_gX._==5){var _gY=B(_gN(_gX.a));if(!_gY._){return E(_gS);}else{var _gZ=new T(function(){return B(_8O(_gY.a));});return function(_h0,_h1){return new F(function(){return A1(_h1,_gZ);});};}}else{return E(_gS);}},_h2=function(_h3,_h4){if(_h3>10){return new T0(2);}else{var _h5=new T(function(){var _h6=new T(function(){return B(A3(_gs,_gV,_4m,function(_h7){return new F(function(){return A1(_h4,_h7);});}));});return B(_fq(function(_h8){var _h9=E(_h8);return (_h9._==3)?(!B(_4q(_h9.a,_4n)))?new T0(2):E(_h6):new T0(2);}));}),_ha=function(_hb){return E(_h5);};return new T1(1,function(_hc){return new F(function(){return A2(_e7,_hc,_ha);});});}},_hd=function(_he,_hf){return new F(function(){return _h2(E(_he),_hf);});},_hg=new T(function(){return B(unCStr("IdentPay"));}),_hh=function(_hi,_hj){if(_hi>10){return new T0(2);}else{var _hk=new T(function(){var _hl=new T(function(){return B(A3(_gs,_gV,_4m,function(_hm){return new F(function(){return A1(_hj,_hm);});}));});return B(_fq(function(_hn){var _ho=E(_hn);return (_ho._==3)?(!B(_4q(_ho.a,_hg)))?new T0(2):E(_hl):new T0(2);}));}),_hp=function(_hq){return E(_hk);};return new T1(1,function(_hr){return new F(function(){return A2(_e7,_hr,_hp);});});}},_hs=function(_ht,_hu){return new F(function(){return _hh(E(_ht),_hu);});},_hv=new T(function(){return B(unCStr("IdentChoice"));}),_hw=function(_hx,_hy){if(_hx>10){return new T0(2);}else{var _hz=new T(function(){var _hA=new T(function(){return B(A3(_gs,_gV,_4m,function(_hB){return new F(function(){return A1(_hy,_hB);});}));});return B(_fq(function(_hC){var _hD=E(_hC);return (_hD._==3)?(!B(_4q(_hD.a,_hv)))?new T0(2):E(_hA):new T0(2);}));}),_hE=function(_hF){return E(_hz);};return new T1(1,function(_hG){return new F(function(){return A2(_e7,_hG,_hE);});});}},_hH=function(_hI,_hJ){return new F(function(){return _hw(E(_hI),_hJ);});},_hK=new T(function(){return B(unCStr("ConstMoney"));}),_hL=new T(function(){return B(unCStr("AvailableMoney"));}),_hM=new T(function(){return B(unCStr("AddMoney"));}),_hN=function(_hO,_hP){var _hQ=new T(function(){var _hR=new T(function(){if(_hO>10){return new T0(2);}else{var _hS=new T(function(){var _hT=new T(function(){return B(A3(_gs,_gV,_4m,function(_hU){return new F(function(){return A1(_hP,new T1(2,_hU));});}));});return B(_fq(function(_hV){var _hW=E(_hV);return (_hW._==3)?(!B(_4q(_hW.a,_hK)))?new T0(2):E(_hT):new T0(2);}));}),_hX=function(_hY){return E(_hS);};return new T1(1,function(_hZ){return new F(function(){return A2(_e7,_hZ,_hX);});});}});if(_hO>10){return B(_3K(_4W,_hR));}else{var _i0=new T(function(){var _i1=new T(function(){var _i2=function(_i3){return new F(function(){return A3(_gh,_i4,_4m,function(_i5){return new F(function(){return A1(_hP,new T2(1,_i3,_i5));});});});};return B(A3(_gh,_i4,_4m,_i2));});return B(_fq(function(_i6){var _i7=E(_i6);return (_i7._==3)?(!B(_4q(_i7.a,_hM)))?new T0(2):E(_i1):new T0(2);}));}),_i8=function(_i9){return E(_i0);};return B(_3K(new T1(1,function(_ia){return new F(function(){return A2(_e7,_ia,_i8);});}),_hR));}});if(_hO>10){return new F(function(){return _3K(_4W,_hQ);});}else{var _ib=new T(function(){var _ic=new T(function(){return B(A3(_gh,_hd,_4m,function(_id){return new F(function(){return A1(_hP,new T1(0,_id));});}));});return B(_fq(function(_ie){var _if=E(_ie);return (_if._==3)?(!B(_4q(_if.a,_hL)))?new T0(2):E(_ic):new T0(2);}));}),_ig=function(_ih){return E(_ib);};return new F(function(){return _3K(new T1(1,function(_ii){return new F(function(){return A2(_e7,_ii,_ig);});}),_hQ);});}},_i4=function(_ij,_ik){return new F(function(){return _hN(E(_ij),_ik);});},_il=new T0(7),_im=function(_in,_io){return new F(function(){return A1(_io,_il);});},_ip=new T2(0,_J,_im),_iq=new T0(8),_ir=function(_is,_it){return new F(function(){return A1(_it,_iq);});},_iu=new T2(0,_I,_ir),_iv=new T2(1,_iu,_21),_iw=new T2(1,_ip,_iv),_ix=function(_iy,_iz,_iA){var _iB=E(_iy);if(!_iB._){return new T0(2);}else{var _iC=E(_iB.a),_iD=_iC.a,_iE=new T(function(){return B(A2(_iC.b,_iz,_iA));}),_iF=new T(function(){return B(_fq(function(_iG){var _iH=E(_iG);switch(_iH._){case 3:return (!B(_4q(_iD,_iH.a)))?new T0(2):E(_iE);case 4:return (!B(_4q(_iD,_iH.a)))?new T0(2):E(_iE);default:return new T0(2);}}));}),_iI=function(_iJ){return E(_iF);};return new F(function(){return _3K(new T1(1,function(_iK){return new F(function(){return A2(_e7,_iK,_iI);});}),new T(function(){return B(_ix(_iB.b,_iz,_iA));}));});}},_iL=new T(function(){return B(unCStr("ValueGE"));}),_iM=new T(function(){return B(unCStr("PersonChoseSomething"));}),_iN=new T(function(){return B(unCStr("PersonChoseThis"));}),_iO=new T(function(){return B(unCStr("BelowTimeout"));}),_iP=new T(function(){return B(unCStr("AndObs"));}),_iQ=new T(function(){return B(unCStr("OrObs"));}),_iR=new T(function(){return B(unCStr("NotObs"));}),_iS=function(_iT,_iU){var _iV=new T(function(){var _iW=E(_iT),_iX=new T(function(){var _iY=new T(function(){var _iZ=new T(function(){var _j0=new T(function(){var _j1=new T(function(){var _j2=new T(function(){if(_iW>10){return new T0(2);}else{var _j3=new T(function(){var _j4=new T(function(){var _j5=function(_j6){return new F(function(){return A3(_gh,_i4,_4m,function(_j7){return new F(function(){return A1(_iU,new T2(6,_j6,_j7));});});});};return B(A3(_gh,_i4,_4m,_j5));});return B(_fq(function(_j8){var _j9=E(_j8);return (_j9._==3)?(!B(_4q(_j9.a,_iL)))?new T0(2):E(_j4):new T0(2);}));}),_ja=function(_jb){return E(_j3);};return new T1(1,function(_jc){return new F(function(){return A2(_e7,_jc,_ja);});});}});if(_iW>10){return B(_3K(_4W,_j2));}else{var _jd=new T(function(){var _je=new T(function(){var _jf=function(_jg){return new F(function(){return A3(_gs,_gV,_4m,function(_jh){return new F(function(){return A1(_iU,new T2(5,_jg,_jh));});});});};return B(A3(_gh,_hH,_4m,_jf));});return B(_fq(function(_ji){var _jj=E(_ji);return (_jj._==3)?(!B(_4q(_jj.a,_iM)))?new T0(2):E(_je):new T0(2);}));}),_jk=function(_jl){return E(_jd);};return B(_3K(new T1(1,function(_jm){return new F(function(){return A2(_e7,_jm,_jk);});}),_j2));}});if(_iW>10){return B(_3K(_4W,_j1));}else{var _jn=new T(function(){var _jo=new T(function(){var _jp=function(_jq){var _jr=function(_js){return new F(function(){return A3(_gs,_gV,_4m,function(_jt){return new F(function(){return A1(_iU,new T3(4,_jq,_js,_jt));});});});};return new F(function(){return A3(_gs,_gV,_4m,_jr);});};return B(A3(_gh,_hH,_4m,_jp));});return B(_fq(function(_ju){var _jv=E(_ju);return (_jv._==3)?(!B(_4q(_jv.a,_iN)))?new T0(2):E(_jo):new T0(2);}));}),_jw=function(_jx){return E(_jn);};return B(_3K(new T1(1,function(_jy){return new F(function(){return A2(_e7,_jy,_jw);});}),_j1));}});if(_iW>10){return B(_3K(_4W,_j0));}else{var _jz=new T(function(){var _jA=new T(function(){return B(A3(_gh,_iS,_4m,function(_jB){return new F(function(){return A1(_iU,new T1(3,_jB));});}));});return B(_fq(function(_jC){var _jD=E(_jC);return (_jD._==3)?(!B(_4q(_jD.a,_iR)))?new T0(2):E(_jA):new T0(2);}));}),_jE=function(_jF){return E(_jz);};return B(_3K(new T1(1,function(_jG){return new F(function(){return A2(_e7,_jG,_jE);});}),_j0));}});if(_iW>10){return B(_3K(_4W,_iZ));}else{var _jH=new T(function(){var _jI=new T(function(){var _jJ=function(_jK){return new F(function(){return A3(_gh,_iS,_4m,function(_jL){return new F(function(){return A1(_iU,new T2(2,_jK,_jL));});});});};return B(A3(_gh,_iS,_4m,_jJ));});return B(_fq(function(_jM){var _jN=E(_jM);return (_jN._==3)?(!B(_4q(_jN.a,_iQ)))?new T0(2):E(_jI):new T0(2);}));}),_jO=function(_jP){return E(_jH);};return B(_3K(new T1(1,function(_jQ){return new F(function(){return A2(_e7,_jQ,_jO);});}),_iZ));}});if(_iW>10){return B(_3K(_4W,_iY));}else{var _jR=new T(function(){var _jS=new T(function(){var _jT=function(_jU){return new F(function(){return A3(_gh,_iS,_4m,function(_jV){return new F(function(){return A1(_iU,new T2(1,_jU,_jV));});});});};return B(A3(_gh,_iS,_4m,_jT));});return B(_fq(function(_jW){var _jX=E(_jW);return (_jX._==3)?(!B(_4q(_jX.a,_iP)))?new T0(2):E(_jS):new T0(2);}));}),_jY=function(_jZ){return E(_jR);};return B(_3K(new T1(1,function(_k0){return new F(function(){return A2(_e7,_k0,_jY);});}),_iY));}});if(_iW>10){return B(_3K(_4W,_iX));}else{var _k1=new T(function(){var _k2=new T(function(){return B(A3(_gs,_gV,_4m,function(_k3){return new F(function(){return A1(_iU,new T1(0,_k3));});}));});return B(_fq(function(_k4){var _k5=E(_k4);return (_k5._==3)?(!B(_4q(_k5.a,_iO)))?new T0(2):E(_k2):new T0(2);}));}),_k6=function(_k7){return E(_k1);};return B(_3K(new T1(1,function(_k8){return new F(function(){return A2(_e7,_k8,_k6);});}),_iX));}});return new F(function(){return _3K(B(_ix(_iw,_iT,_iU)),_iV);});},_k9=__Z,_ka=new T(function(){return B(unCStr("RedeemCC"));}),_kb=new T(function(){return B(unCStr("Pay"));}),_kc=new T(function(){return B(unCStr("Both"));}),_kd=new T(function(){return B(unCStr("Choice"));}),_ke=new T(function(){return B(unCStr("CommitCash"));}),_kf=new T(function(){return B(unCStr("When"));}),_kg=function(_kh,_ki){var _kj=new T(function(){var _kk=new T(function(){return B(A1(_ki,_k9));});return B(_fq(function(_kl){var _km=E(_kl);return (_km._==3)?(!B(_4q(_km.a,_1m)))?new T0(2):E(_kk):new T0(2);}));}),_kn=function(_ko){return E(_kj);},_kp=new T(function(){var _kq=E(_kh),_kr=new T(function(){var _ks=new T(function(){var _kt=new T(function(){var _ku=new T(function(){var _kv=new T(function(){if(_kq>10){return new T0(2);}else{var _kw=new T(function(){var _kx=new T(function(){var _ky=function(_kz){var _kA=function(_kB){var _kC=function(_kD){return new F(function(){return A3(_gh,_kg,_4m,function(_kE){return new F(function(){return A1(_ki,new T4(6,_kz,_kB,_kD,_kE));});});});};return new F(function(){return A3(_gh,_kg,_4m,_kC);});};return new F(function(){return A3(_gs,_gV,_4m,_kA);});};return B(A3(_gh,_iS,_4m,_ky));});return B(_fq(function(_kF){var _kG=E(_kF);return (_kG._==3)?(!B(_4q(_kG.a,_kf)))?new T0(2):E(_kx):new T0(2);}));}),_kH=function(_kI){return E(_kw);};return new T1(1,function(_kJ){return new F(function(){return A2(_e7,_kJ,_kH);});});}});if(_kq>10){return B(_3K(_4W,_kv));}else{var _kK=new T(function(){var _kL=new T(function(){var _kM=function(_kN){var _kO=function(_kP){var _kQ=function(_kR){var _kS=function(_kT){var _kU=function(_kV){return new F(function(){return A3(_gh,_kg,_4m,function(_kW){return new F(function(){return A1(_ki,new T6(5,_kN,_kP,_kR,_kT,_kV,_kW));});});});};return new F(function(){return A3(_gs,_gV,_4m,_kU);});};return new F(function(){return A3(_gs,_gV,_4m,_kS);});};return new F(function(){return A3(_gs,_gV,_4m,_kQ);});};return new F(function(){return A3(_gs,_gV,_4m,_kO);});};return B(A3(_gh,_hd,_4m,_kM));});return B(_fq(function(_kX){var _kY=E(_kX);return (_kY._==3)?(!B(_4q(_kY.a,_ke)))?new T0(2):E(_kL):new T0(2);}));}),_kZ=function(_l0){return E(_kK);};return B(_3K(new T1(1,function(_l1){return new F(function(){return A2(_e7,_l1,_kZ);});}),_kv));}});if(_kq>10){return B(_3K(_4W,_ku));}else{var _l2=new T(function(){var _l3=new T(function(){var _l4=function(_l5){var _l6=function(_l7){return new F(function(){return A3(_gh,_kg,_4m,function(_l8){return new F(function(){return A1(_ki,new T3(4,_l5,_l7,_l8));});});});};return new F(function(){return A3(_gh,_kg,_4m,_l6);});};return B(A3(_gh,_iS,_4m,_l4));});return B(_fq(function(_l9){var _la=E(_l9);return (_la._==3)?(!B(_4q(_la.a,_kd)))?new T0(2):E(_l3):new T0(2);}));}),_lb=function(_lc){return E(_l2);};return B(_3K(new T1(1,function(_ld){return new F(function(){return A2(_e7,_ld,_lb);});}),_ku));}});if(_kq>10){return B(_3K(_4W,_kt));}else{var _le=new T(function(){var _lf=new T(function(){var _lg=function(_lh){return new F(function(){return A3(_gh,_kg,_4m,function(_li){return new F(function(){return A1(_ki,new T2(3,_lh,_li));});});});};return B(A3(_gh,_kg,_4m,_lg));});return B(_fq(function(_lj){var _lk=E(_lj);return (_lk._==3)?(!B(_4q(_lk.a,_kc)))?new T0(2):E(_lf):new T0(2);}));}),_ll=function(_lm){return E(_le);};return B(_3K(new T1(1,function(_ln){return new F(function(){return A2(_e7,_ln,_ll);});}),_kt));}});if(_kq>10){return B(_3K(_4W,_ks));}else{var _lo=new T(function(){var _lp=new T(function(){var _lq=function(_lr){var _ls=function(_lt){var _lu=function(_lv){var _lw=function(_lx){var _ly=function(_lz){return new F(function(){return A3(_gh,_kg,_4m,function(_lA){return new F(function(){return A1(_ki,new T6(2,_lr,_lt,_lv,_lx,_lz,_lA));});});});};return new F(function(){return A3(_gs,_gV,_4m,_ly);});};return new F(function(){return A3(_gs,_gV,_4m,_lw);});};return new F(function(){return A3(_gs,_gV,_4m,_lu);});};return new F(function(){return A3(_gs,_gV,_4m,_ls);});};return B(A3(_gh,_hs,_4m,_lq));});return B(_fq(function(_lB){var _lC=E(_lB);return (_lC._==3)?(!B(_4q(_lC.a,_kb)))?new T0(2):E(_lp):new T0(2);}));}),_lD=function(_lE){return E(_lo);};return B(_3K(new T1(1,function(_lF){return new F(function(){return A2(_e7,_lF,_lD);});}),_ks));}});if(_kq>10){return B(_3K(_4W,_kr));}else{var _lG=new T(function(){var _lH=new T(function(){var _lI=function(_lJ){return new F(function(){return A3(_gh,_kg,_4m,function(_lK){return new F(function(){return A1(_ki,new T2(1,_lJ,_lK));});});});};return B(A3(_gh,_hd,_4m,_lI));});return B(_fq(function(_lL){var _lM=E(_lL);return (_lM._==3)?(!B(_4q(_lM.a,_ka)))?new T0(2):E(_lH):new T0(2);}));}),_lN=function(_lO){return E(_lG);};return B(_3K(new T1(1,function(_lP){return new F(function(){return A2(_e7,_lP,_lN);});}),_kr));}});return new F(function(){return _3K(new T1(1,function(_lQ){return new F(function(){return A2(_e7,_lQ,_kn);});}),_kp);});},_lR=function(_lS){var _lT=function(_lU){return E(new T2(3,_lS,_4W));};return new T1(1,function(_lV){return new F(function(){return A2(_e7,_lV,_lT);});});},_lW=new T(function(){return B(A3(_gh,_kg,_fX,_lR));}),_lX=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_lY=function(_lZ){while(1){var _m0=B((function(_m1){var _m2=E(_m1);if(!_m2._){return __Z;}else{var _m3=_m2.b,_m4=E(_m2.a);if(!E(_m4.b)._){return new T2(1,_m4.a,new T(function(){return B(_lY(_m3));}));}else{_lZ=_m3;return __continue;}}})(_lZ));if(_m0!=__continue){return _m0;}}},_m5=function(_){var _m6=__app0(E(_lX)),_m7=B(_lY(B(_3A(_lW,new T(function(){var _m8=String(_m6);return fromJSStr(_m8);})))));if(!_m7._){return E(_2d);}else{if(!E(_m7.b)._){return new F(function(){return _27(_24,B(_1t(0,_m7.a,_21)),_);});}else{return E(_23);}}},_m9="(function (b) { return (b.inputList.length); })",_ma="(function (b, x) { return (b.inputList[x]); })",_mb=function(_mc,_md,_){var _me=eval(E(_ma)),_mf=__app2(E(_me),_mc,_md);return new T1(0,_mf);},_mg=function(_mh,_mi,_mj,_){var _mk=E(_mj);if(!_mk._){return _21;}else{var _ml=B(_mb(_mh,E(_mk.a),_)),_mm=B(_mg(_mh,_,_mk.b,_));return new T2(1,_ml,_mm);}},_mn=function(_mo,_mp){if(_mo<=_mp){var _mq=function(_mr){return new T2(1,_mr,new T(function(){if(_mr!=_mp){return B(_mq(_mr+1|0));}else{return __Z;}}));};return new F(function(){return _mq(_mo);});}else{return __Z;}},_ms=function(_mt,_){var _mu=eval(E(_m9)),_mv=__app1(E(_mu),_mt),_mw=Number(_mv),_mx=jsTrunc(_mw);return new F(function(){return _mg(_mt,_,new T(function(){return B(_mn(0,_mx-1|0));}),_);});},_my="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_mz="(function (x) { return x.name; })",_mA=new T(function(){return B(unCStr("\""));}),_mB=function(_mC){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_2(_mC,_mA));}))));});},_mD=function(_mE,_mF,_){var _mG=E(_mF);if(!_mG._){return new F(function(){return _mB(_mE);});}else{var _mH=E(_mG.a),_mI=E(_mz),_mJ=eval(_mI),_mK=__app1(E(_mJ),E(_mH.a)),_mL=String(_mK);if(!B(_4q(fromJSStr(_mL),_mE))){var _mM=function(_mN,_mO,_){while(1){var _mP=E(_mO);if(!_mP._){return new F(function(){return _mB(_mN);});}else{var _mQ=E(_mP.a),_mR=eval(_mI),_mS=__app1(E(_mR),E(_mQ.a)),_mT=String(_mS);if(!B(_4q(fromJSStr(_mT),_mN))){_mO=_mP.b;continue;}else{return _mQ;}}}};return new F(function(){return _mM(_mE,_mG.b,_);});}else{return _mH;}}},_mU=function(_mV,_mW,_mX,_){var _mY=B(_ms(_mW,_)),_mZ=B(_mD(_mV,_mY,_)),_n0=eval(E(_my)),_n1=__app2(E(_n0),E(E(_mX).a),E(E(_mZ).a));return new F(function(){return _25(_);});},_n2=function(_n3){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_2(_n3,_mA));}))));});},_n4=function(_n5,_n6,_){var _n7=E(_n6);if(!_n7._){return new F(function(){return _n2(_n5);});}else{var _n8=E(_n7.a),_n9=E(_mz),_na=eval(_n9),_nb=__app1(E(_na),E(_n8.a)),_nc=String(_nb);if(!B(_4q(fromJSStr(_nc),_n5))){var _nd=function(_ne,_nf,_){while(1){var _ng=E(_nf);if(!_ng._){return new F(function(){return _n2(_ne);});}else{var _nh=E(_ng.a),_ni=eval(_n9),_nj=__app1(E(_ni),E(_nh.a)),_nk=String(_nj);if(!B(_4q(fromJSStr(_nk),_ne))){_nf=_ng.b;continue;}else{return _nh;}}}};return new F(function(){return _nd(_n5,_n7.b,_);});}else{return _n8;}}},_nl="(function (b) { return (b.fieldRow.length); })",_nm="(function (b, x) { return (b.fieldRow[x]); })",_nn=function(_no,_np,_){var _nq=eval(E(_nm)),_nr=__app2(E(_nq),_no,_np);return new T1(0,_nr);},_ns=function(_nt,_nu,_nv,_){var _nw=E(_nv);if(!_nw._){return _21;}else{var _nx=B(_nn(_nt,E(_nw.a),_)),_ny=B(_ns(_nt,_,_nw.b,_));return new T2(1,_nx,_ny);}},_nz=function(_nA,_){var _nB=eval(E(_nl)),_nC=__app1(E(_nB),_nA),_nD=Number(_nC),_nE=jsTrunc(_nD);return new F(function(){return _ns(_nA,_,new T(function(){return B(_mn(0,_nE-1|0));}),_);});},_nF=function(_nG,_){var _nH=E(_nG);if(!_nH._){return _21;}else{var _nI=B(_nz(E(E(_nH.a).a),_)),_nJ=B(_nF(_nH.b,_));return new T2(1,_nI,_nJ);}},_nK=function(_nL){var _nM=E(_nL);if(!_nM._){return __Z;}else{return new F(function(){return _2(_nM.a,new T(function(){return B(_nK(_nM.b));},1));});}},_nN=function(_nO,_nP,_){var _nQ=B(_ms(_nP,_)),_nR=B(_nF(_nQ,_));return new F(function(){return _n4(_nO,B(_nK(_nR)),_);});},_nS="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_nT=function(_nU,_nV,_nW,_){var _nX=B(_ms(_nV,_)),_nY=B(_mD(_nU,_nX,_)),_nZ=eval(E(_nS)),_o0=__app2(E(_nZ),E(E(_nW).a),E(E(_nY).a));return new F(function(){return _25(_);});},_o1=new T(function(){return B(unCStr("contract_redeemcc"));}),_o2=new T(function(){return B(unCStr("contract_pay"));}),_o3=new T(function(){return B(unCStr("contract_both"));}),_o4=new T(function(){return B(unCStr("contract_choice"));}),_o5=new T(function(){return B(unCStr("contract_commitcash"));}),_o6=new T(function(){return B(unCStr("contract_when"));}),_o7="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_o8=function(_o9,_){var _oa=eval(E(_o7)),_ob=__app1(E(_oa),toJSStr(E(_o9)));return new T1(0,_ob);},_oc=new T(function(){return B(unCStr("contract2"));}),_od=new T(function(){return B(unCStr("contract1"));}),_oe=new T(function(){return B(unCStr("expiration"));}),_of=new T(function(){return B(unCStr("payee_id"));}),_og=new T(function(){return B(unCStr("payer_id"));}),_oh=new T(function(){return B(unCStr("pay_id"));}),_oi=new T(function(){return B(unCStr("contract_null"));}),_oj=new T(function(){return B(unCStr("observation"));}),_ok=new T(function(){return B(unCStr("timeout"));}),_ol=new T(function(){return B(unCStr("contract"));}),_om=new T(function(){return B(unCStr("end_expiration"));}),_on=new T(function(){return B(unCStr("start_expiration"));}),_oo=new T(function(){return B(unCStr("ammount"));}),_op=new T(function(){return B(unCStr("person_id"));}),_oq=new T(function(){return B(unCStr("ccommit_id"));}),_or=function(_os,_ot,_ou,_){var _ov=B(_ms(_ot,_)),_ow=B(_mD(_os,_ov,_)),_ox=eval(E(_nS)),_oy=__app2(E(_ox),E(E(_ou).a),E(E(_ow).a));return new F(function(){return _25(_);});},_oz=new T(function(){return B(unCStr("observation_personchosethis"));}),_oA=new T(function(){return B(unCStr("observation_personchosesomething"));}),_oB=new T(function(){return B(unCStr("observation_value_ge"));}),_oC=new T(function(){return B(unCStr("observation_trueobs"));}),_oD=new T(function(){return B(unCStr("observation_falseobs"));}),_oE=new T(function(){return B(unCStr("observation_belowtimeout"));}),_oF=new T(function(){return B(unCStr("observation_andobs"));}),_oG=new T(function(){return B(unCStr("observation_orobs"));}),_oH=new T(function(){return B(unCStr("observation_notobs"));}),_oI=new T(function(){return B(unCStr("value2"));}),_oJ=new T(function(){return B(unCStr("value1"));}),_oK=new T(function(){return B(unCStr("person"));}),_oL=new T(function(){return B(unCStr("choice_id"));}),_oM=new T(function(){return B(unCStr("choice_value"));}),_oN=new T(function(){return B(unCStr("observation2"));}),_oO=new T(function(){return B(unCStr("observation1"));}),_oP=new T(function(){return B(unCStr("block_number"));}),_oQ=new T(function(){return B(unCStr("value_available_money"));}),_oR=new T(function(){return B(unCStr("value_add_money"));}),_oS=new T(function(){return B(unCStr("value_const_money"));}),_oT=new T(function(){return B(unCStr("money"));}),_oU=new T(function(){return B(unCStr("commit_id"));}),_oV="(function (b, s) { return (b.setText(s)); })",_oW=function(_oX,_){var _oY=E(_oX);switch(_oY._){case 0:var _oZ=B(_o8(_oQ,_)),_p0=E(_oZ),_p1=B(_nN(_oU,E(_p0.a),_)),_p2=eval(E(_oV)),_p3=__app2(E(_p2),E(E(_p1).a),toJSStr(B(_c(0,E(_oY.a),_21))));return _p0;case 1:var _p4=B(_oW(_oY.a,_)),_p5=B(_oW(_oY.b,_)),_p6=B(_o8(_oR,_)),_p7=E(_p6),_p8=E(_p7.a),_p9=B(_or(_oJ,_p8,_p4,_)),_pa=B(_or(_oI,_p8,_p5,_));return _p7;default:var _pb=B(_o8(_oS,_)),_pc=E(_pb),_pd=B(_nN(_oT,E(_pc.a),_)),_pe=eval(E(_oV)),_pf=__app2(E(_pe),E(E(_pd).a),toJSStr(B(_c(0,E(_oY.a),_21))));return _pc;}},_pg=function(_ph,_){var _pi=E(_ph);switch(_pi._){case 0:var _pj=B(_o8(_oE,_)),_pk=E(_pj),_pl=B(_nN(_oP,E(_pk.a),_)),_pm=eval(E(_oV)),_pn=__app2(E(_pm),E(E(_pl).a),toJSStr(B(_c(0,E(_pi.a),_21))));return _pk;case 1:var _po=B(_pg(_pi.a,_)),_pp=B(_pg(_pi.b,_)),_pq=B(_o8(_oF,_)),_pr=E(_pq),_ps=E(_pr.a),_pt=B(_nT(_oO,_ps,_po,_)),_pu=B(_nT(_oN,_ps,_pp,_));return _pr;case 2:var _pv=B(_pg(_pi.a,_)),_pw=B(_pg(_pi.b,_)),_px=B(_o8(_oG,_)),_py=E(_px),_pz=E(_py.a),_pA=B(_nT(_oO,_pz,_pv,_)),_pB=B(_nT(_oN,_pz,_pw,_));return _py;case 3:var _pC=B(_pg(_pi.a,_)),_pD=B(_o8(_oH,_)),_pE=E(_pD),_pF=B(_nT(_oj,E(_pE.a),_pC,_));return _pE;case 4:var _pG=B(_o8(_oz,_)),_pH=E(_pG),_pI=E(_pH.a),_pJ=B(_nN(_oL,_pI,_)),_pK=eval(E(_oV)),_pL=__app2(E(_pK),E(E(_pJ).a),toJSStr(B(_c(0,E(_pi.a),_21)))),_pM=B(_nN(_oK,_pI,_)),_pN=__app2(E(_pK),E(E(_pM).a),toJSStr(B(_c(0,E(_pi.b),_21)))),_pO=B(_nN(_oM,_pI,_)),_pP=__app2(E(_pK),E(E(_pO).a),toJSStr(B(_c(0,E(_pi.c),_21))));return _pH;case 5:var _pQ=B(_o8(_oA,_)),_pR=E(_pQ),_pS=E(_pR.a),_pT=B(_nN(_oL,_pS,_)),_pU=eval(E(_oV)),_pV=__app2(E(_pU),E(E(_pT).a),toJSStr(B(_c(0,E(_pi.a),_21)))),_pW=B(_nN(_oK,_pS,_)),_pX=__app2(E(_pU),E(E(_pW).a),toJSStr(B(_c(0,E(_pi.b),_21))));return _pR;case 6:var _pY=B(_oW(_pi.a,_)),_pZ=B(_oW(_pi.b,_)),_q0=B(_o8(_oB,_)),_q1=E(_q0),_q2=E(_q1.a),_q3=B(_or(_oJ,_q2,_pY,_)),_q4=B(_or(_oI,_q2,_pZ,_));return _q1;case 7:return new F(function(){return _o8(_oC,_);});break;default:return new F(function(){return _o8(_oD,_);});}},_q5=function(_q6,_){var _q7=E(_q6);switch(_q7._){case 0:return new F(function(){return _o8(_oi,_);});break;case 1:var _q8=B(_q5(_q7.b,_)),_q9=B(_o8(_o1,_)),_qa=E(_q9),_qb=E(_qa.a),_qc=B(_nN(_oq,_qb,_)),_qd=eval(E(_oV)),_qe=__app2(E(_qd),E(E(_qc).a),toJSStr(B(_c(0,E(_q7.a),_21)))),_qf=B(_mU(_ol,_qb,_q8,_));return _qa;case 2:var _qg=B(_q5(_q7.f,_)),_qh=B(_o8(_o2,_)),_qi=E(_qh),_qj=E(_qi.a),_qk=B(_nN(_oh,_qj,_)),_ql=eval(E(_oV)),_qm=__app2(E(_ql),E(E(_qk).a),toJSStr(B(_c(0,E(_q7.a),_21)))),_qn=B(_nN(_og,_qj,_)),_qo=__app2(E(_ql),E(E(_qn).a),toJSStr(B(_c(0,E(_q7.b),_21)))),_qp=B(_nN(_of,_qj,_)),_qq=__app2(E(_ql),E(E(_qp).a),toJSStr(B(_c(0,E(_q7.c),_21)))),_qr=B(_nN(_oo,_qj,_)),_qs=__app2(E(_ql),E(E(_qr).a),toJSStr(B(_c(0,E(_q7.d),_21)))),_qt=B(_nN(_oe,_qj,_)),_qu=__app2(E(_ql),E(E(_qt).a),toJSStr(B(_c(0,E(_q7.e),_21)))),_qv=B(_mU(_ol,_qj,_qg,_));return _qi;case 3:var _qw=B(_q5(_q7.a,_)),_qx=B(_q5(_q7.b,_)),_qy=B(_o8(_o3,_)),_qz=E(_qy),_qA=E(_qz.a),_qB=B(_mU(_od,_qA,_qw,_)),_qC=B(_mU(_oc,_qA,_qx,_));return _qz;case 4:var _qD=B(_pg(_q7.a,_)),_qE=B(_q5(_q7.b,_)),_qF=B(_q5(_q7.c,_)),_qG=B(_o8(_o4,_)),_qH=E(_qG),_qI=E(_qH.a),_qJ=B(_nT(_oj,_qI,_qD,_)),_qK=B(_mU(_od,_qI,_qE,_)),_qL=B(_mU(_oc,_qI,_qF,_));return _qH;case 5:var _qM=B(_q5(_q7.f,_)),_qN=B(_o8(_o5,_)),_qO=E(_qN),_qP=E(_qO.a),_qQ=B(_nN(_oq,_qP,_)),_qR=eval(E(_oV)),_qS=__app2(E(_qR),E(E(_qQ).a),toJSStr(B(_c(0,E(_q7.a),_21)))),_qT=B(_nN(_op,_qP,_)),_qU=__app2(E(_qR),E(E(_qT).a),toJSStr(B(_c(0,E(_q7.b),_21)))),_qV=B(_nN(_oo,_qP,_)),_qW=__app2(E(_qR),E(E(_qV).a),toJSStr(B(_c(0,E(_q7.c),_21)))),_qX=B(_nN(_on,_qP,_)),_qY=__app2(E(_qR),E(E(_qX).a),toJSStr(B(_c(0,E(_q7.d),_21)))),_qZ=B(_nN(_om,_qP,_)),_r0=__app2(E(_qR),E(E(_qZ).a),toJSStr(B(_c(0,E(_q7.e),_21)))),_r1=B(_mU(_ol,_qP,_qM,_));return _qO;default:var _r2=B(_pg(_q7.a,_)),_r3=B(_q5(_q7.c,_)),_r4=B(_q5(_q7.d,_)),_r5=B(_o8(_o6,_)),_r6=E(_r5),_r7=E(_r6.a),_r8=B(_nN(_ok,_r7,_)),_r9=eval(E(_oV)),_ra=__app2(E(_r9),E(E(_r8).a),toJSStr(B(_c(0,E(_q7.b),_21)))),_rb=B(_nT(_oj,_r7,_r2,_)),_rc=B(_mU(_od,_r7,_r3,_)),_rd=B(_mU(_oc,_r7,_r4,_));return _r6;}},_re=new T(function(){return B(unCStr("base_contract"));}),_rf=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_rg=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_rh=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_ri=function(_rj,_){var _rk=__app0(E(_rh)),_rl=__app0(E(_rg)),_rm=B(_lY(B(_3A(_lW,_rj))));if(!_rm._){return E(_2d);}else{if(!E(_rm.b)._){var _rn=B(_q5(_rm.a,_)),_ro=B(_mU(_re,_rl,_rn,_)),_rp=__app0(E(_rf));return _0;}else{return E(_23);}}},_rq="(function (t) {return document.getElementById(t).value})",_rr=function(_){var _rs=eval(E(_rq)),_rt=__app1(E(_rs),toJSStr(E(_24)));return new F(function(){return _ri(new T(function(){var _ru=String(_rt);return fromJSStr(_ru);}),_);});},_rv=new T0(1),_rw=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_rx=function(_ry){return new F(function(){return err(_rw);});},_rz=new T(function(){return B(_rx(_));}),_rA=function(_rB,_rC,_rD){var _rE=E(_rD);if(!_rE._){var _rF=_rE.a,_rG=E(_rC);if(!_rG._){var _rH=_rG.a,_rI=_rG.b;if(_rH<=(imul(3,_rF)|0)){return new T4(0,(1+_rH|0)+_rF|0,E(_rB),E(_rG),E(_rE));}else{var _rJ=E(_rG.c);if(!_rJ._){var _rK=_rJ.a,_rL=E(_rG.d);if(!_rL._){var _rM=_rL.a,_rN=_rL.b,_rO=_rL.c;if(_rM>=(imul(2,_rK)|0)){var _rP=function(_rQ){var _rR=E(_rL.d);return (_rR._==0)?new T4(0,(1+_rH|0)+_rF|0,E(_rN),E(new T4(0,(1+_rK|0)+_rQ|0,E(_rI),E(_rJ),E(_rO))),E(new T4(0,(1+_rF|0)+_rR.a|0,E(_rB),E(_rR),E(_rE)))):new T4(0,(1+_rH|0)+_rF|0,E(_rN),E(new T4(0,(1+_rK|0)+_rQ|0,E(_rI),E(_rJ),E(_rO))),E(new T4(0,1+_rF|0,E(_rB),E(_rv),E(_rE))));},_rS=E(_rO);if(!_rS._){return new F(function(){return _rP(_rS.a);});}else{return new F(function(){return _rP(0);});}}else{return new T4(0,(1+_rH|0)+_rF|0,E(_rI),E(_rJ),E(new T4(0,(1+_rF|0)+_rM|0,E(_rB),E(_rL),E(_rE))));}}else{return E(_rz);}}else{return E(_rz);}}}else{return new T4(0,1+_rF|0,E(_rB),E(_rv),E(_rE));}}else{var _rT=E(_rC);if(!_rT._){var _rU=_rT.a,_rV=_rT.b,_rW=_rT.d,_rX=E(_rT.c);if(!_rX._){var _rY=_rX.a,_rZ=E(_rW);if(!_rZ._){var _s0=_rZ.a,_s1=_rZ.b,_s2=_rZ.c;if(_s0>=(imul(2,_rY)|0)){var _s3=function(_s4){var _s5=E(_rZ.d);return (_s5._==0)?new T4(0,1+_rU|0,E(_s1),E(new T4(0,(1+_rY|0)+_s4|0,E(_rV),E(_rX),E(_s2))),E(new T4(0,1+_s5.a|0,E(_rB),E(_s5),E(_rv)))):new T4(0,1+_rU|0,E(_s1),E(new T4(0,(1+_rY|0)+_s4|0,E(_rV),E(_rX),E(_s2))),E(new T4(0,1,E(_rB),E(_rv),E(_rv))));},_s6=E(_s2);if(!_s6._){return new F(function(){return _s3(_s6.a);});}else{return new F(function(){return _s3(0);});}}else{return new T4(0,1+_rU|0,E(_rV),E(_rX),E(new T4(0,1+_s0|0,E(_rB),E(_rZ),E(_rv))));}}else{return new T4(0,3,E(_rV),E(_rX),E(new T4(0,1,E(_rB),E(_rv),E(_rv))));}}else{var _s7=E(_rW);return (_s7._==0)?new T4(0,3,E(_s7.b),E(new T4(0,1,E(_rV),E(_rv),E(_rv))),E(new T4(0,1,E(_rB),E(_rv),E(_rv)))):new T4(0,2,E(_rB),E(_rT),E(_rv));}}else{return new T4(0,1,E(_rB),E(_rv),E(_rv));}}},_s8=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_s9=function(_sa){return new F(function(){return err(_s8);});},_sb=new T(function(){return B(_s9(_));}),_sc=function(_sd,_se,_sf){var _sg=E(_se);if(!_sg._){var _sh=_sg.a,_si=E(_sf);if(!_si._){var _sj=_si.a,_sk=_si.b;if(_sj<=(imul(3,_sh)|0)){return new T4(0,(1+_sh|0)+_sj|0,E(_sd),E(_sg),E(_si));}else{var _sl=E(_si.c);if(!_sl._){var _sm=_sl.a,_sn=_sl.b,_so=_sl.c,_sp=E(_si.d);if(!_sp._){var _sq=_sp.a;if(_sm>=(imul(2,_sq)|0)){var _sr=function(_ss){var _st=E(_sd),_su=E(_sl.d);return (_su._==0)?new T4(0,(1+_sh|0)+_sj|0,E(_sn),E(new T4(0,(1+_sh|0)+_ss|0,E(_st),E(_sg),E(_so))),E(new T4(0,(1+_sq|0)+_su.a|0,E(_sk),E(_su),E(_sp)))):new T4(0,(1+_sh|0)+_sj|0,E(_sn),E(new T4(0,(1+_sh|0)+_ss|0,E(_st),E(_sg),E(_so))),E(new T4(0,1+_sq|0,E(_sk),E(_rv),E(_sp))));},_sv=E(_so);if(!_sv._){return new F(function(){return _sr(_sv.a);});}else{return new F(function(){return _sr(0);});}}else{return new T4(0,(1+_sh|0)+_sj|0,E(_sk),E(new T4(0,(1+_sh|0)+_sm|0,E(_sd),E(_sg),E(_sl))),E(_sp));}}else{return E(_sb);}}else{return E(_sb);}}}else{return new T4(0,1+_sh|0,E(_sd),E(_sg),E(_rv));}}else{var _sw=E(_sf);if(!_sw._){var _sx=_sw.a,_sy=_sw.b,_sz=_sw.d,_sA=E(_sw.c);if(!_sA._){var _sB=_sA.a,_sC=_sA.b,_sD=_sA.c,_sE=E(_sz);if(!_sE._){var _sF=_sE.a;if(_sB>=(imul(2,_sF)|0)){var _sG=function(_sH){var _sI=E(_sd),_sJ=E(_sA.d);return (_sJ._==0)?new T4(0,1+_sx|0,E(_sC),E(new T4(0,1+_sH|0,E(_sI),E(_rv),E(_sD))),E(new T4(0,(1+_sF|0)+_sJ.a|0,E(_sy),E(_sJ),E(_sE)))):new T4(0,1+_sx|0,E(_sC),E(new T4(0,1+_sH|0,E(_sI),E(_rv),E(_sD))),E(new T4(0,1+_sF|0,E(_sy),E(_rv),E(_sE))));},_sK=E(_sD);if(!_sK._){return new F(function(){return _sG(_sK.a);});}else{return new F(function(){return _sG(0);});}}else{return new T4(0,1+_sx|0,E(_sy),E(new T4(0,1+_sB|0,E(_sd),E(_rv),E(_sA))),E(_sE));}}else{return new T4(0,3,E(_sC),E(new T4(0,1,E(_sd),E(_rv),E(_rv))),E(new T4(0,1,E(_sy),E(_rv),E(_rv))));}}else{var _sL=E(_sz);return (_sL._==0)?new T4(0,3,E(_sy),E(new T4(0,1,E(_sd),E(_rv),E(_rv))),E(_sL)):new T4(0,2,E(_sd),E(_rv),E(_sw));}}else{return new T4(0,1,E(_sd),E(_rv),E(_rv));}}},_sM=function(_sN,_sO,_sP,_sQ,_sR){var _sS=E(_sR);if(!_sS._){var _sT=_sS.c,_sU=_sS.d,_sV=E(_sS.b),_sW=E(_sN),_sX=E(_sV.a);if(_sW>=_sX){if(_sW!=_sX){return new F(function(){return _sc(_sV,_sT,B(_sM(_sW,_sO,_sP,_sQ,_sU)));});}else{var _sY=E(_sO),_sZ=E(_sV.b);if(_sY>=_sZ){if(_sY!=_sZ){return new F(function(){return _sc(_sV,_sT,B(_sM(_sW,_sY,_sP,_sQ,_sU)));});}else{var _t0=E(_sP),_t1=E(_sV.c);if(_t0>=_t1){if(_t0!=_t1){return new F(function(){return _sc(_sV,_sT,B(_sM(_sW,_sY,_t0,_sQ,_sU)));});}else{var _t2=E(_sQ),_t3=E(_sV.d);if(_t2>=_t3){if(_t2!=_t3){return new F(function(){return _sc(_sV,_sT,B(_sM(_sW,_sY,_t0,_t2,_sU)));});}else{return new T4(0,_sS.a,E(new T4(0,_sW,_sY,_t0,_t2)),E(_sT),E(_sU));}}else{return new F(function(){return _rA(_sV,B(_sM(_sW,_sY,_t0,_t2,_sT)),_sU);});}}}else{return new F(function(){return _rA(_sV,B(_sM(_sW,_sY,_t0,_sQ,_sT)),_sU);});}}}else{return new F(function(){return _rA(_sV,B(_sM(_sW,_sY,_sP,_sQ,_sT)),_sU);});}}}else{return new F(function(){return _rA(_sV,B(_sM(_sW,_sO,_sP,_sQ,_sT)),_sU);});}}else{return new T4(0,1,E(new T4(0,_sN,_sO,_sP,_sQ)),E(_rv),E(_rv));}},_t4=function(_t5,_t6){while(1){var _t7=E(_t6);if(!_t7._){return E(_t5);}else{var _t8=E(_t7.a),_t9=B(_sM(_t8.a,_t8.b,_t8.c,_t8.d,_t5));_t5=_t9;_t6=_t7.b;continue;}}},_ta=function(_tb,_tc,_td,_te,_tf,_tg){return new F(function(){return _t4(B(_sM(_tc,_td,_te,_tf,_tb)),_tg);});},_th=function(_ti){return new T4(0,1,E(_ti),E(_rv),E(_rv));},_tj=function(_tk,_tl){var _tm=E(_tl);if(!_tm._){return new F(function(){return _sc(_tm.b,_tm.c,B(_tj(_tk,_tm.d)));});}else{return new F(function(){return _th(_tk);});}},_tn=function(_to,_tp){var _tq=E(_tp);if(!_tq._){return new F(function(){return _rA(_tq.b,B(_tn(_to,_tq.c)),_tq.d);});}else{return new F(function(){return _th(_to);});}},_tr=function(_ts,_tt,_tu,_tv,_tw){return new F(function(){return _sc(_tu,_tv,B(_tj(_ts,_tw)));});},_tx=function(_ty,_tz,_tA,_tB,_tC){return new F(function(){return _rA(_tA,B(_tn(_ty,_tB)),_tC);});},_tD=function(_tE,_tF,_tG,_tH,_tI,_tJ){var _tK=E(_tF);if(!_tK._){var _tL=_tK.a,_tM=_tK.b,_tN=_tK.c,_tO=_tK.d;if((imul(3,_tL)|0)>=_tG){if((imul(3,_tG)|0)>=_tL){return new T4(0,(_tL+_tG|0)+1|0,E(_tE),E(_tK),E(new T4(0,_tG,E(_tH),E(_tI),E(_tJ))));}else{return new F(function(){return _sc(_tM,_tN,B(_tD(_tE,_tO,_tG,_tH,_tI,_tJ)));});}}else{return new F(function(){return _rA(_tH,B(_tP(_tE,_tL,_tM,_tN,_tO,_tI)),_tJ);});}}else{return new F(function(){return _tx(_tE,_tG,_tH,_tI,_tJ);});}},_tP=function(_tQ,_tR,_tS,_tT,_tU,_tV){var _tW=E(_tV);if(!_tW._){var _tX=_tW.a,_tY=_tW.b,_tZ=_tW.c,_u0=_tW.d;if((imul(3,_tR)|0)>=_tX){if((imul(3,_tX)|0)>=_tR){return new T4(0,(_tR+_tX|0)+1|0,E(_tQ),E(new T4(0,_tR,E(_tS),E(_tT),E(_tU))),E(_tW));}else{return new F(function(){return _sc(_tS,_tT,B(_tD(_tQ,_tU,_tX,_tY,_tZ,_u0)));});}}else{return new F(function(){return _rA(_tY,B(_tP(_tQ,_tR,_tS,_tT,_tU,_tZ)),_u0);});}}else{return new F(function(){return _tr(_tQ,_tR,_tS,_tT,_tU);});}},_u1=function(_u2,_u3,_u4){var _u5=E(_u3);if(!_u5._){var _u6=_u5.a,_u7=_u5.b,_u8=_u5.c,_u9=_u5.d,_ua=E(_u4);if(!_ua._){var _ub=_ua.a,_uc=_ua.b,_ud=_ua.c,_ue=_ua.d;if((imul(3,_u6)|0)>=_ub){if((imul(3,_ub)|0)>=_u6){return new T4(0,(_u6+_ub|0)+1|0,E(_u2),E(_u5),E(_ua));}else{return new F(function(){return _sc(_u7,_u8,B(_tD(_u2,_u9,_ub,_uc,_ud,_ue)));});}}else{return new F(function(){return _rA(_uc,B(_tP(_u2,_u6,_u7,_u8,_u9,_ud)),_ue);});}}else{return new F(function(){return _tr(_u2,_u6,_u7,_u8,_u9);});}}else{return new F(function(){return _tn(_u2,_u4);});}},_uf=function(_ug,_uh){var _ui=E(_uh);if(!_ui._){return new T3(0,_rv,_21,_21);}else{var _uj=_ui.a,_uk=E(_ug);if(_uk==1){var _ul=E(_ui.b);if(!_ul._){return new T3(0,new T(function(){return new T4(0,1,E(_uj),E(_rv),E(_rv));}),_21,_21);}else{var _um=E(_uj),_un=E(_um.a),_uo=E(_ul.a),_up=E(_uo.a);if(_un>=_up){if(_un!=_up){return new T3(0,new T4(0,1,E(_um),E(_rv),E(_rv)),_21,_ul);}else{var _uq=E(_um.b),_ur=E(_uo.b);if(_uq>=_ur){if(_uq!=_ur){return new T3(0,new T4(0,1,E(_um),E(_rv),E(_rv)),_21,_ul);}else{var _us=E(_um.c),_ut=E(_uo.c);return (_us>=_ut)?(_us!=_ut)?new T3(0,new T4(0,1,E(_um),E(_rv),E(_rv)),_21,_ul):(E(_um.d)<E(_uo.d))?new T3(0,new T4(0,1,E(_um),E(_rv),E(_rv)),_ul,_21):new T3(0,new T4(0,1,E(_um),E(_rv),E(_rv)),_21,_ul):new T3(0,new T4(0,1,E(_um),E(_rv),E(_rv)),_ul,_21);}}else{return new T3(0,new T4(0,1,E(_um),E(_rv),E(_rv)),_ul,_21);}}}else{return new T3(0,new T4(0,1,E(_um),E(_rv),E(_rv)),_ul,_21);}}}else{var _uu=B(_uf(_uk>>1,_ui)),_uv=_uu.a,_uw=_uu.c,_ux=E(_uu.b);if(!_ux._){return new T3(0,_uv,_21,_uw);}else{var _uy=_ux.a,_uz=E(_ux.b);if(!_uz._){return new T3(0,new T(function(){return B(_tj(_uy,_uv));}),_21,_uw);}else{var _uA=E(_uy),_uB=E(_uA.a),_uC=E(_uz.a),_uD=E(_uC.a);if(_uB>=_uD){if(_uB!=_uD){return new T3(0,_uv,_21,_ux);}else{var _uE=E(_uA.b),_uF=E(_uC.b);if(_uE>=_uF){if(_uE!=_uF){return new T3(0,_uv,_21,_ux);}else{var _uG=E(_uA.c),_uH=E(_uC.c);if(_uG>=_uH){if(_uG!=_uH){return new T3(0,_uv,_21,_ux);}else{if(E(_uA.d)<E(_uC.d)){var _uI=B(_uf(_uk>>1,_uz));return new T3(0,new T(function(){return B(_u1(_uA,_uv,_uI.a));}),_uI.b,_uI.c);}else{return new T3(0,_uv,_21,_ux);}}}else{var _uJ=B(_uf(_uk>>1,_uz));return new T3(0,new T(function(){return B(_u1(_uA,_uv,_uJ.a));}),_uJ.b,_uJ.c);}}}else{var _uK=B(_uf(_uk>>1,_uz));return new T3(0,new T(function(){return B(_u1(_uA,_uv,_uK.a));}),_uK.b,_uK.c);}}}else{var _uL=B(_uf(_uk>>1,_uz));return new T3(0,new T(function(){return B(_u1(_uA,_uv,_uL.a));}),_uL.b,_uL.c);}}}}}},_uM=function(_uN,_uO,_uP){var _uQ=E(_uP);if(!_uQ._){return E(_uO);}else{var _uR=_uQ.a,_uS=E(_uQ.b);if(!_uS._){return new F(function(){return _tj(_uR,_uO);});}else{var _uT=E(_uR),_uU=_uT.b,_uV=_uT.c,_uW=_uT.d,_uX=E(_uT.a),_uY=E(_uS.a),_uZ=E(_uY.a),_v0=function(_v1){var _v2=B(_uf(_uN,_uS)),_v3=_v2.a,_v4=E(_v2.c);if(!_v4._){return new F(function(){return _uM(_uN<<1,B(_u1(_uT,_uO,_v3)),_v2.b);});}else{return new F(function(){return _t4(B(_u1(_uT,_uO,_v3)),_v4);});}};if(_uX>=_uZ){if(_uX!=_uZ){return new F(function(){return _ta(_uO,_uX,_uU,_uV,_uW,_uS);});}else{var _v5=E(_uU),_v6=E(_uY.b);if(_v5>=_v6){if(_v5!=_v6){return new F(function(){return _ta(_uO,_uX,_v5,_uV,_uW,_uS);});}else{var _v7=E(_uV),_v8=E(_uY.c);if(_v7>=_v8){if(_v7!=_v8){return new F(function(){return _ta(_uO,_uX,_v5,_v7,_uW,_uS);});}else{var _v9=E(_uW);if(_v9<E(_uY.d)){return new F(function(){return _v0(_);});}else{return new F(function(){return _ta(_uO,_uX,_v5,_v7,_v9,_uS);});}}}else{return new F(function(){return _v0(_);});}}}else{return new F(function(){return _v0(_);});}}}else{return new F(function(){return _v0(_);});}}}},_va=function(_vb){var _vc=E(_vb);if(!_vc._){return new T0(1);}else{var _vd=_vc.a,_ve=E(_vc.b);if(!_ve._){return new T4(0,1,E(_vd),E(_rv),E(_rv));}else{var _vf=_ve.b,_vg=E(_vd),_vh=E(_vg.a),_vi=E(_ve.a),_vj=_vi.b,_vk=_vi.c,_vl=_vi.d,_vm=E(_vi.a);if(_vh>=_vm){if(_vh!=_vm){return new F(function(){return _ta(new T4(0,1,E(_vg),E(_rv),E(_rv)),_vm,_vj,_vk,_vl,_vf);});}else{var _vn=E(_vg.b),_vo=E(_vj);if(_vn>=_vo){if(_vn!=_vo){return new F(function(){return _ta(new T4(0,1,E(_vg),E(_rv),E(_rv)),_vm,_vo,_vk,_vl,_vf);});}else{var _vp=E(_vg.c),_vq=E(_vk);if(_vp>=_vq){if(_vp!=_vq){return new F(function(){return _ta(new T4(0,1,E(_vg),E(_rv),E(_rv)),_vm,_vo,_vq,_vl,_vf);});}else{var _vr=E(_vl);if(E(_vg.d)<_vr){return new F(function(){return _uM(1,new T4(0,1,E(_vg),E(_rv),E(_rv)),_ve);});}else{return new F(function(){return _ta(new T4(0,1,E(_vg),E(_rv),E(_rv)),_vm,_vo,_vq,_vr,_vf);});}}}else{return new F(function(){return _uM(1,new T4(0,1,E(_vg),E(_rv),E(_rv)),_ve);});}}}else{return new F(function(){return _uM(1,new T4(0,1,E(_vg),E(_rv),E(_rv)),_ve);});}}}else{return new F(function(){return _uM(1,new T4(0,1,E(_vg),E(_rv),E(_rv)),_ve);});}}}},_vs=function(_vt,_vu,_vv,_vw,_vx){var _vy=E(_vt);if(_vy==1){var _vz=E(_vx);if(!_vz._){return new T3(0,new T4(0,1,E(new T3(0,_vu,_vv,_vw)),E(_rv),E(_rv)),_21,_21);}else{var _vA=E(_vu),_vB=E(_vz.a),_vC=E(_vB.a);if(_vA>=_vC){if(_vA!=_vC){return new T3(0,new T4(0,1,E(new T3(0,_vA,_vv,_vw)),E(_rv),E(_rv)),_21,_vz);}else{var _vD=E(_vB.b);return (_vv>=_vD)?(_vv!=_vD)?new T3(0,new T4(0,1,E(new T3(0,_vA,_vv,_vw)),E(_rv),E(_rv)),_21,_vz):(_vw<E(_vB.c))?new T3(0,new T4(0,1,E(new T3(0,_vA,_vv,_vw)),E(_rv),E(_rv)),_vz,_21):new T3(0,new T4(0,1,E(new T3(0,_vA,_vv,_vw)),E(_rv),E(_rv)),_21,_vz):new T3(0,new T4(0,1,E(new T3(0,_vA,_vv,_vw)),E(_rv),E(_rv)),_vz,_21);}}else{return new T3(0,new T4(0,1,E(new T3(0,_vA,_vv,_vw)),E(_rv),E(_rv)),_vz,_21);}}}else{var _vE=B(_vs(_vy>>1,_vu,_vv,_vw,_vx)),_vF=_vE.a,_vG=_vE.c,_vH=E(_vE.b);if(!_vH._){return new T3(0,_vF,_21,_vG);}else{var _vI=_vH.a,_vJ=E(_vH.b);if(!_vJ._){return new T3(0,new T(function(){return B(_tj(_vI,_vF));}),_21,_vG);}else{var _vK=_vJ.b,_vL=E(_vI),_vM=E(_vL.a),_vN=E(_vJ.a),_vO=_vN.b,_vP=_vN.c,_vQ=E(_vN.a);if(_vM>=_vQ){if(_vM!=_vQ){return new T3(0,_vF,_21,_vH);}else{var _vR=E(_vL.b),_vS=E(_vO);if(_vR>=_vS){if(_vR!=_vS){return new T3(0,_vF,_21,_vH);}else{var _vT=E(_vP);if(E(_vL.c)<_vT){var _vU=B(_vs(_vy>>1,_vQ,_vS,_vT,_vK));return new T3(0,new T(function(){return B(_u1(_vL,_vF,_vU.a));}),_vU.b,_vU.c);}else{return new T3(0,_vF,_21,_vH);}}}else{var _vV=B(_vW(_vy>>1,_vQ,_vS,_vP,_vK));return new T3(0,new T(function(){return B(_u1(_vL,_vF,_vV.a));}),_vV.b,_vV.c);}}}else{var _vX=B(_vY(_vy>>1,_vQ,_vO,_vP,_vK));return new T3(0,new T(function(){return B(_u1(_vL,_vF,_vX.a));}),_vX.b,_vX.c);}}}}},_vW=function(_vZ,_w0,_w1,_w2,_w3){var _w4=E(_vZ);if(_w4==1){var _w5=E(_w3);if(!_w5._){return new T3(0,new T4(0,1,E(new T3(0,_w0,_w1,_w2)),E(_rv),E(_rv)),_21,_21);}else{var _w6=E(_w0),_w7=E(_w5.a),_w8=E(_w7.a);if(_w6>=_w8){if(_w6!=_w8){return new T3(0,new T4(0,1,E(new T3(0,_w6,_w1,_w2)),E(_rv),E(_rv)),_21,_w5);}else{var _w9=E(_w7.b);if(_w1>=_w9){if(_w1!=_w9){return new T3(0,new T4(0,1,E(new T3(0,_w6,_w1,_w2)),E(_rv),E(_rv)),_21,_w5);}else{var _wa=E(_w2);return (_wa<E(_w7.c))?new T3(0,new T4(0,1,E(new T3(0,_w6,_w1,_wa)),E(_rv),E(_rv)),_w5,_21):new T3(0,new T4(0,1,E(new T3(0,_w6,_w1,_wa)),E(_rv),E(_rv)),_21,_w5);}}else{return new T3(0,new T4(0,1,E(new T3(0,_w6,_w1,_w2)),E(_rv),E(_rv)),_w5,_21);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_w6,_w1,_w2)),E(_rv),E(_rv)),_w5,_21);}}}else{var _wb=B(_vW(_w4>>1,_w0,_w1,_w2,_w3)),_wc=_wb.a,_wd=_wb.c,_we=E(_wb.b);if(!_we._){return new T3(0,_wc,_21,_wd);}else{var _wf=_we.a,_wg=E(_we.b);if(!_wg._){return new T3(0,new T(function(){return B(_tj(_wf,_wc));}),_21,_wd);}else{var _wh=_wg.b,_wi=E(_wf),_wj=E(_wi.a),_wk=E(_wg.a),_wl=_wk.b,_wm=_wk.c,_wn=E(_wk.a);if(_wj>=_wn){if(_wj!=_wn){return new T3(0,_wc,_21,_we);}else{var _wo=E(_wi.b),_wp=E(_wl);if(_wo>=_wp){if(_wo!=_wp){return new T3(0,_wc,_21,_we);}else{var _wq=E(_wm);if(E(_wi.c)<_wq){var _wr=B(_vs(_w4>>1,_wn,_wp,_wq,_wh));return new T3(0,new T(function(){return B(_u1(_wi,_wc,_wr.a));}),_wr.b,_wr.c);}else{return new T3(0,_wc,_21,_we);}}}else{var _ws=B(_vW(_w4>>1,_wn,_wp,_wm,_wh));return new T3(0,new T(function(){return B(_u1(_wi,_wc,_ws.a));}),_ws.b,_ws.c);}}}else{var _wt=B(_vY(_w4>>1,_wn,_wl,_wm,_wh));return new T3(0,new T(function(){return B(_u1(_wi,_wc,_wt.a));}),_wt.b,_wt.c);}}}}},_vY=function(_wu,_wv,_ww,_wx,_wy){var _wz=E(_wu);if(_wz==1){var _wA=E(_wy);if(!_wA._){return new T3(0,new T4(0,1,E(new T3(0,_wv,_ww,_wx)),E(_rv),E(_rv)),_21,_21);}else{var _wB=E(_wv),_wC=E(_wA.a),_wD=E(_wC.a);if(_wB>=_wD){if(_wB!=_wD){return new T3(0,new T4(0,1,E(new T3(0,_wB,_ww,_wx)),E(_rv),E(_rv)),_21,_wA);}else{var _wE=E(_ww),_wF=E(_wC.b);if(_wE>=_wF){if(_wE!=_wF){return new T3(0,new T4(0,1,E(new T3(0,_wB,_wE,_wx)),E(_rv),E(_rv)),_21,_wA);}else{var _wG=E(_wx);return (_wG<E(_wC.c))?new T3(0,new T4(0,1,E(new T3(0,_wB,_wE,_wG)),E(_rv),E(_rv)),_wA,_21):new T3(0,new T4(0,1,E(new T3(0,_wB,_wE,_wG)),E(_rv),E(_rv)),_21,_wA);}}else{return new T3(0,new T4(0,1,E(new T3(0,_wB,_wE,_wx)),E(_rv),E(_rv)),_wA,_21);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_wB,_ww,_wx)),E(_rv),E(_rv)),_wA,_21);}}}else{var _wH=B(_vY(_wz>>1,_wv,_ww,_wx,_wy)),_wI=_wH.a,_wJ=_wH.c,_wK=E(_wH.b);if(!_wK._){return new T3(0,_wI,_21,_wJ);}else{var _wL=_wK.a,_wM=E(_wK.b);if(!_wM._){return new T3(0,new T(function(){return B(_tj(_wL,_wI));}),_21,_wJ);}else{var _wN=_wM.b,_wO=E(_wL),_wP=E(_wO.a),_wQ=E(_wM.a),_wR=_wQ.b,_wS=_wQ.c,_wT=E(_wQ.a);if(_wP>=_wT){if(_wP!=_wT){return new T3(0,_wI,_21,_wK);}else{var _wU=E(_wO.b),_wV=E(_wR);if(_wU>=_wV){if(_wU!=_wV){return new T3(0,_wI,_21,_wK);}else{var _wW=E(_wS);if(E(_wO.c)<_wW){var _wX=B(_vs(_wz>>1,_wT,_wV,_wW,_wN));return new T3(0,new T(function(){return B(_u1(_wO,_wI,_wX.a));}),_wX.b,_wX.c);}else{return new T3(0,_wI,_21,_wK);}}}else{var _wY=B(_vW(_wz>>1,_wT,_wV,_wS,_wN));return new T3(0,new T(function(){return B(_u1(_wO,_wI,_wY.a));}),_wY.b,_wY.c);}}}else{var _wZ=B(_vY(_wz>>1,_wT,_wR,_wS,_wN));return new T3(0,new T(function(){return B(_u1(_wO,_wI,_wZ.a));}),_wZ.b,_wZ.c);}}}}},_x0=function(_x1,_x2,_x3,_x4,_x5){var _x6=E(_x5);if(!_x6._){var _x7=_x6.c,_x8=_x6.d,_x9=E(_x6.b),_xa=E(_x9.a);if(_x1>=_xa){if(_x1!=_xa){return new F(function(){return _sc(_x9,_x7,B(_x0(_x1,_,_x3,_x4,_x8)));});}else{var _xb=E(_x9.b);if(_x3>=_xb){if(_x3!=_xb){return new F(function(){return _sc(_x9,_x7,B(_x0(_x1,_,_x3,_x4,_x8)));});}else{var _xc=E(_x9.c);if(_x4>=_xc){if(_x4!=_xc){return new F(function(){return _sc(_x9,_x7,B(_x0(_x1,_,_x3,_x4,_x8)));});}else{return new T4(0,_x6.a,E(new T3(0,_x1,_x3,_x4)),E(_x7),E(_x8));}}else{return new F(function(){return _rA(_x9,B(_x0(_x1,_,_x3,_x4,_x7)),_x8);});}}}else{return new F(function(){return _rA(_x9,B(_x0(_x1,_,_x3,_x4,_x7)),_x8);});}}}else{return new F(function(){return _rA(_x9,B(_x0(_x1,_,_x3,_x4,_x7)),_x8);});}}else{return new T4(0,1,E(new T3(0,_x1,_x3,_x4)),E(_rv),E(_rv));}},_xd=function(_xe,_xf,_xg,_xh,_xi){var _xj=E(_xi);if(!_xj._){var _xk=_xj.c,_xl=_xj.d,_xm=E(_xj.b),_xn=E(_xm.a);if(_xe>=_xn){if(_xe!=_xn){return new F(function(){return _sc(_xm,_xk,B(_xd(_xe,_,_xg,_xh,_xl)));});}else{var _xo=E(_xm.b);if(_xg>=_xo){if(_xg!=_xo){return new F(function(){return _sc(_xm,_xk,B(_xd(_xe,_,_xg,_xh,_xl)));});}else{var _xp=E(_xh),_xq=E(_xm.c);if(_xp>=_xq){if(_xp!=_xq){return new F(function(){return _sc(_xm,_xk,B(_x0(_xe,_,_xg,_xp,_xl)));});}else{return new T4(0,_xj.a,E(new T3(0,_xe,_xg,_xp)),E(_xk),E(_xl));}}else{return new F(function(){return _rA(_xm,B(_x0(_xe,_,_xg,_xp,_xk)),_xl);});}}}else{return new F(function(){return _rA(_xm,B(_xd(_xe,_,_xg,_xh,_xk)),_xl);});}}}else{return new F(function(){return _rA(_xm,B(_xd(_xe,_,_xg,_xh,_xk)),_xl);});}}else{return new T4(0,1,E(new T3(0,_xe,_xg,_xh)),E(_rv),E(_rv));}},_xr=function(_xs,_xt,_xu,_xv,_xw){var _xx=E(_xw);if(!_xx._){var _xy=_xx.c,_xz=_xx.d,_xA=E(_xx.b),_xB=E(_xA.a);if(_xs>=_xB){if(_xs!=_xB){return new F(function(){return _sc(_xA,_xy,B(_xr(_xs,_,_xu,_xv,_xz)));});}else{var _xC=E(_xu),_xD=E(_xA.b);if(_xC>=_xD){if(_xC!=_xD){return new F(function(){return _sc(_xA,_xy,B(_xd(_xs,_,_xC,_xv,_xz)));});}else{var _xE=E(_xv),_xF=E(_xA.c);if(_xE>=_xF){if(_xE!=_xF){return new F(function(){return _sc(_xA,_xy,B(_x0(_xs,_,_xC,_xE,_xz)));});}else{return new T4(0,_xx.a,E(new T3(0,_xs,_xC,_xE)),E(_xy),E(_xz));}}else{return new F(function(){return _rA(_xA,B(_x0(_xs,_,_xC,_xE,_xy)),_xz);});}}}else{return new F(function(){return _rA(_xA,B(_xd(_xs,_,_xC,_xv,_xy)),_xz);});}}}else{return new F(function(){return _rA(_xA,B(_xr(_xs,_,_xu,_xv,_xy)),_xz);});}}else{return new T4(0,1,E(new T3(0,_xs,_xu,_xv)),E(_rv),E(_rv));}},_xG=function(_xH,_xI,_xJ,_xK){var _xL=E(_xK);if(!_xL._){var _xM=_xL.c,_xN=_xL.d,_xO=E(_xL.b),_xP=E(_xH),_xQ=E(_xO.a);if(_xP>=_xQ){if(_xP!=_xQ){return new F(function(){return _sc(_xO,_xM,B(_xr(_xP,_,_xI,_xJ,_xN)));});}else{var _xR=E(_xI),_xS=E(_xO.b);if(_xR>=_xS){if(_xR!=_xS){return new F(function(){return _sc(_xO,_xM,B(_xd(_xP,_,_xR,_xJ,_xN)));});}else{var _xT=E(_xJ),_xU=E(_xO.c);if(_xT>=_xU){if(_xT!=_xU){return new F(function(){return _sc(_xO,_xM,B(_x0(_xP,_,_xR,_xT,_xN)));});}else{return new T4(0,_xL.a,E(new T3(0,_xP,_xR,_xT)),E(_xM),E(_xN));}}else{return new F(function(){return _rA(_xO,B(_x0(_xP,_,_xR,_xT,_xM)),_xN);});}}}else{return new F(function(){return _rA(_xO,B(_xd(_xP,_,_xR,_xJ,_xM)),_xN);});}}}else{return new F(function(){return _rA(_xO,B(_xr(_xP,_,_xI,_xJ,_xM)),_xN);});}}else{return new T4(0,1,E(new T3(0,_xH,_xI,_xJ)),E(_rv),E(_rv));}},_xV=function(_xW,_xX){while(1){var _xY=E(_xX);if(!_xY._){return E(_xW);}else{var _xZ=E(_xY.a),_y0=B(_xG(_xZ.a,_xZ.b,_xZ.c,_xW));_xW=_y0;_xX=_xY.b;continue;}}},_y1=function(_y2,_y3,_y4,_y5,_y6){return new F(function(){return _xV(B(_xG(_y3,_y4,_y5,_y2)),_y6);});},_y7=function(_y8,_y9,_ya){var _yb=E(_y9);return new F(function(){return _xV(B(_xG(_yb.a,_yb.b,_yb.c,_y8)),_ya);});},_yc=function(_yd,_ye,_yf){var _yg=E(_yf);if(!_yg._){return E(_ye);}else{var _yh=_yg.a,_yi=E(_yg.b);if(!_yi._){return new F(function(){return _tj(_yh,_ye);});}else{var _yj=E(_yh),_yk=_yj.b,_yl=_yj.c,_ym=E(_yj.a),_yn=E(_yi.a),_yo=_yn.b,_yp=_yn.c,_yq=E(_yn.a),_yr=function(_ys){var _yt=B(_vY(_yd,_yq,_yo,_yp,_yi.b)),_yu=_yt.a,_yv=E(_yt.c);if(!_yv._){return new F(function(){return _yc(_yd<<1,B(_u1(_yj,_ye,_yu)),_yt.b);});}else{return new F(function(){return _y7(B(_u1(_yj,_ye,_yu)),_yv.a,_yv.b);});}};if(_ym>=_yq){if(_ym!=_yq){return new F(function(){return _y1(_ye,_ym,_yk,_yl,_yi);});}else{var _yw=E(_yk),_yx=E(_yo);if(_yw>=_yx){if(_yw!=_yx){return new F(function(){return _y1(_ye,_ym,_yw,_yl,_yi);});}else{var _yy=E(_yl);if(_yy<E(_yp)){return new F(function(){return _yr(_);});}else{return new F(function(){return _y1(_ye,_ym,_yw,_yy,_yi);});}}}else{return new F(function(){return _yr(_);});}}}else{return new F(function(){return _yr(_);});}}}},_yz=function(_yA,_yB,_yC,_yD,_yE,_yF){var _yG=E(_yF);if(!_yG._){return new F(function(){return _tj(new T3(0,_yC,_yD,_yE),_yB);});}else{var _yH=E(_yC),_yI=E(_yG.a),_yJ=_yI.b,_yK=_yI.c,_yL=E(_yI.a),_yM=function(_yN){var _yO=B(_vY(_yA,_yL,_yJ,_yK,_yG.b)),_yP=_yO.a,_yQ=E(_yO.c);if(!_yQ._){return new F(function(){return _yc(_yA<<1,B(_u1(new T3(0,_yH,_yD,_yE),_yB,_yP)),_yO.b);});}else{return new F(function(){return _y7(B(_u1(new T3(0,_yH,_yD,_yE),_yB,_yP)),_yQ.a,_yQ.b);});}};if(_yH>=_yL){if(_yH!=_yL){return new F(function(){return _y1(_yB,_yH,_yD,_yE,_yG);});}else{var _yR=E(_yJ);if(_yD>=_yR){if(_yD!=_yR){return new F(function(){return _y1(_yB,_yH,_yD,_yE,_yG);});}else{var _yS=E(_yE);if(_yS<E(_yK)){return new F(function(){return _yM(_);});}else{return new F(function(){return _y1(_yB,_yH,_yD,_yS,_yG);});}}}else{return new F(function(){return _yM(_);});}}}else{return new F(function(){return _yM(_);});}}},_yT=function(_yU,_yV,_yW,_yX,_yY,_yZ){var _z0=E(_yZ);if(!_z0._){return new F(function(){return _tj(new T3(0,_yW,_yX,_yY),_yV);});}else{var _z1=E(_yW),_z2=E(_z0.a),_z3=_z2.b,_z4=_z2.c,_z5=E(_z2.a),_z6=function(_z7){var _z8=B(_vY(_yU,_z5,_z3,_z4,_z0.b)),_z9=_z8.a,_za=E(_z8.c);if(!_za._){return new F(function(){return _yc(_yU<<1,B(_u1(new T3(0,_z1,_yX,_yY),_yV,_z9)),_z8.b);});}else{return new F(function(){return _y7(B(_u1(new T3(0,_z1,_yX,_yY),_yV,_z9)),_za.a,_za.b);});}};if(_z1>=_z5){if(_z1!=_z5){return new F(function(){return _y1(_yV,_z1,_yX,_yY,_z0);});}else{var _zb=E(_z3);if(_yX>=_zb){if(_yX!=_zb){return new F(function(){return _y1(_yV,_z1,_yX,_yY,_z0);});}else{if(_yY<E(_z4)){return new F(function(){return _z6(_);});}else{return new F(function(){return _y1(_yV,_z1,_yX,_yY,_z0);});}}}else{return new F(function(){return _z6(_);});}}}else{return new F(function(){return _z6(_);});}}},_zc=function(_zd,_ze,_zf,_zg,_zh,_zi){var _zj=E(_zi);if(!_zj._){return new F(function(){return _tj(new T3(0,_zf,_zg,_zh),_ze);});}else{var _zk=E(_zf),_zl=E(_zj.a),_zm=_zl.b,_zn=_zl.c,_zo=E(_zl.a),_zp=function(_zq){var _zr=B(_vY(_zd,_zo,_zm,_zn,_zj.b)),_zs=_zr.a,_zt=E(_zr.c);if(!_zt._){return new F(function(){return _yc(_zd<<1,B(_u1(new T3(0,_zk,_zg,_zh),_ze,_zs)),_zr.b);});}else{return new F(function(){return _y7(B(_u1(new T3(0,_zk,_zg,_zh),_ze,_zs)),_zt.a,_zt.b);});}};if(_zk>=_zo){if(_zk!=_zo){return new F(function(){return _y1(_ze,_zk,_zg,_zh,_zj);});}else{var _zu=E(_zg),_zv=E(_zm);if(_zu>=_zv){if(_zu!=_zv){return new F(function(){return _y1(_ze,_zk,_zu,_zh,_zj);});}else{var _zw=E(_zh);if(_zw<E(_zn)){return new F(function(){return _zp(_);});}else{return new F(function(){return _y1(_ze,_zk,_zu,_zw,_zj);});}}}else{return new F(function(){return _zp(_);});}}}else{return new F(function(){return _zp(_);});}}},_zx=function(_zy){var _zz=E(_zy);if(!_zz._){return new T0(1);}else{var _zA=_zz.a,_zB=E(_zz.b);if(!_zB._){return new T4(0,1,E(_zA),E(_rv),E(_rv));}else{var _zC=_zB.b,_zD=E(_zA),_zE=E(_zD.a),_zF=E(_zB.a),_zG=_zF.b,_zH=_zF.c,_zI=E(_zF.a);if(_zE>=_zI){if(_zE!=_zI){return new F(function(){return _y1(new T4(0,1,E(_zD),E(_rv),E(_rv)),_zI,_zG,_zH,_zC);});}else{var _zJ=E(_zD.b),_zK=E(_zG);if(_zJ>=_zK){if(_zJ!=_zK){return new F(function(){return _y1(new T4(0,1,E(_zD),E(_rv),E(_rv)),_zI,_zK,_zH,_zC);});}else{var _zL=E(_zH);if(E(_zD.c)<_zL){return new F(function(){return _yT(1,new T4(0,1,E(_zD),E(_rv),E(_rv)),_zI,_zK,_zL,_zC);});}else{return new F(function(){return _y1(new T4(0,1,E(_zD),E(_rv),E(_rv)),_zI,_zK,_zL,_zC);});}}}else{return new F(function(){return _yz(1,new T4(0,1,E(_zD),E(_rv),E(_rv)),_zI,_zK,_zH,_zC);});}}}else{return new F(function(){return _zc(1,new T4(0,1,E(_zD),E(_rv),E(_rv)),_zI,_zG,_zH,_zC);});}}}},_zM=new T0(1),_zN=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_zO=function(_zP){return new F(function(){return err(_zN);});},_zQ=new T(function(){return B(_zO(_));}),_zR=function(_zS,_zT,_zU,_zV){var _zW=E(_zU);if(!_zW._){var _zX=_zW.a,_zY=E(_zV);if(!_zY._){var _zZ=_zY.a,_A0=_zY.b,_A1=_zY.c;if(_zZ<=(imul(3,_zX)|0)){return new T5(0,(1+_zX|0)+_zZ|0,E(_zS),_zT,E(_zW),E(_zY));}else{var _A2=E(_zY.d);if(!_A2._){var _A3=_A2.a,_A4=_A2.b,_A5=_A2.c,_A6=_A2.d,_A7=E(_zY.e);if(!_A7._){var _A8=_A7.a;if(_A3>=(imul(2,_A8)|0)){var _A9=function(_Aa){var _Ab=E(_zS),_Ac=E(_A2.e);return (_Ac._==0)?new T5(0,(1+_zX|0)+_zZ|0,E(_A4),_A5,E(new T5(0,(1+_zX|0)+_Aa|0,E(_Ab),_zT,E(_zW),E(_A6))),E(new T5(0,(1+_A8|0)+_Ac.a|0,E(_A0),_A1,E(_Ac),E(_A7)))):new T5(0,(1+_zX|0)+_zZ|0,E(_A4),_A5,E(new T5(0,(1+_zX|0)+_Aa|0,E(_Ab),_zT,E(_zW),E(_A6))),E(new T5(0,1+_A8|0,E(_A0),_A1,E(_zM),E(_A7))));},_Ad=E(_A6);if(!_Ad._){return new F(function(){return _A9(_Ad.a);});}else{return new F(function(){return _A9(0);});}}else{return new T5(0,(1+_zX|0)+_zZ|0,E(_A0),_A1,E(new T5(0,(1+_zX|0)+_A3|0,E(_zS),_zT,E(_zW),E(_A2))),E(_A7));}}else{return E(_zQ);}}else{return E(_zQ);}}}else{return new T5(0,1+_zX|0,E(_zS),_zT,E(_zW),E(_zM));}}else{var _Ae=E(_zV);if(!_Ae._){var _Af=_Ae.a,_Ag=_Ae.b,_Ah=_Ae.c,_Ai=_Ae.e,_Aj=E(_Ae.d);if(!_Aj._){var _Ak=_Aj.a,_Al=_Aj.b,_Am=_Aj.c,_An=_Aj.d,_Ao=E(_Ai);if(!_Ao._){var _Ap=_Ao.a;if(_Ak>=(imul(2,_Ap)|0)){var _Aq=function(_Ar){var _As=E(_zS),_At=E(_Aj.e);return (_At._==0)?new T5(0,1+_Af|0,E(_Al),_Am,E(new T5(0,1+_Ar|0,E(_As),_zT,E(_zM),E(_An))),E(new T5(0,(1+_Ap|0)+_At.a|0,E(_Ag),_Ah,E(_At),E(_Ao)))):new T5(0,1+_Af|0,E(_Al),_Am,E(new T5(0,1+_Ar|0,E(_As),_zT,E(_zM),E(_An))),E(new T5(0,1+_Ap|0,E(_Ag),_Ah,E(_zM),E(_Ao))));},_Au=E(_An);if(!_Au._){return new F(function(){return _Aq(_Au.a);});}else{return new F(function(){return _Aq(0);});}}else{return new T5(0,1+_Af|0,E(_Ag),_Ah,E(new T5(0,1+_Ak|0,E(_zS),_zT,E(_zM),E(_Aj))),E(_Ao));}}else{return new T5(0,3,E(_Al),_Am,E(new T5(0,1,E(_zS),_zT,E(_zM),E(_zM))),E(new T5(0,1,E(_Ag),_Ah,E(_zM),E(_zM))));}}else{var _Av=E(_Ai);return (_Av._==0)?new T5(0,3,E(_Ag),_Ah,E(new T5(0,1,E(_zS),_zT,E(_zM),E(_zM))),E(_Av)):new T5(0,2,E(_zS),_zT,E(_zM),E(_Ae));}}else{return new T5(0,1,E(_zS),_zT,E(_zM),E(_zM));}}},_Aw=function(_Ax,_Ay){return new T5(0,1,E(_Ax),_Ay,E(_zM),E(_zM));},_Az=function(_AA,_AB,_AC){var _AD=E(_AC);if(!_AD._){return new F(function(){return _zR(_AD.b,_AD.c,_AD.d,B(_Az(_AA,_AB,_AD.e)));});}else{return new F(function(){return _Aw(_AA,_AB);});}},_AE=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_AF=function(_AG){return new F(function(){return err(_AE);});},_AH=new T(function(){return B(_AF(_));}),_AI=function(_AJ,_AK,_AL,_AM){var _AN=E(_AM);if(!_AN._){var _AO=_AN.a,_AP=E(_AL);if(!_AP._){var _AQ=_AP.a,_AR=_AP.b,_AS=_AP.c;if(_AQ<=(imul(3,_AO)|0)){return new T5(0,(1+_AQ|0)+_AO|0,E(_AJ),_AK,E(_AP),E(_AN));}else{var _AT=E(_AP.d);if(!_AT._){var _AU=_AT.a,_AV=E(_AP.e);if(!_AV._){var _AW=_AV.a,_AX=_AV.b,_AY=_AV.c,_AZ=_AV.d;if(_AW>=(imul(2,_AU)|0)){var _B0=function(_B1){var _B2=E(_AV.e);return (_B2._==0)?new T5(0,(1+_AQ|0)+_AO|0,E(_AX),_AY,E(new T5(0,(1+_AU|0)+_B1|0,E(_AR),_AS,E(_AT),E(_AZ))),E(new T5(0,(1+_AO|0)+_B2.a|0,E(_AJ),_AK,E(_B2),E(_AN)))):new T5(0,(1+_AQ|0)+_AO|0,E(_AX),_AY,E(new T5(0,(1+_AU|0)+_B1|0,E(_AR),_AS,E(_AT),E(_AZ))),E(new T5(0,1+_AO|0,E(_AJ),_AK,E(_zM),E(_AN))));},_B3=E(_AZ);if(!_B3._){return new F(function(){return _B0(_B3.a);});}else{return new F(function(){return _B0(0);});}}else{return new T5(0,(1+_AQ|0)+_AO|0,E(_AR),_AS,E(_AT),E(new T5(0,(1+_AO|0)+_AW|0,E(_AJ),_AK,E(_AV),E(_AN))));}}else{return E(_AH);}}else{return E(_AH);}}}else{return new T5(0,1+_AO|0,E(_AJ),_AK,E(_zM),E(_AN));}}else{var _B4=E(_AL);if(!_B4._){var _B5=_B4.a,_B6=_B4.b,_B7=_B4.c,_B8=_B4.e,_B9=E(_B4.d);if(!_B9._){var _Ba=_B9.a,_Bb=E(_B8);if(!_Bb._){var _Bc=_Bb.a,_Bd=_Bb.b,_Be=_Bb.c,_Bf=_Bb.d;if(_Bc>=(imul(2,_Ba)|0)){var _Bg=function(_Bh){var _Bi=E(_Bb.e);return (_Bi._==0)?new T5(0,1+_B5|0,E(_Bd),_Be,E(new T5(0,(1+_Ba|0)+_Bh|0,E(_B6),_B7,E(_B9),E(_Bf))),E(new T5(0,1+_Bi.a|0,E(_AJ),_AK,E(_Bi),E(_zM)))):new T5(0,1+_B5|0,E(_Bd),_Be,E(new T5(0,(1+_Ba|0)+_Bh|0,E(_B6),_B7,E(_B9),E(_Bf))),E(new T5(0,1,E(_AJ),_AK,E(_zM),E(_zM))));},_Bj=E(_Bf);if(!_Bj._){return new F(function(){return _Bg(_Bj.a);});}else{return new F(function(){return _Bg(0);});}}else{return new T5(0,1+_B5|0,E(_B6),_B7,E(_B9),E(new T5(0,1+_Bc|0,E(_AJ),_AK,E(_Bb),E(_zM))));}}else{return new T5(0,3,E(_B6),_B7,E(_B9),E(new T5(0,1,E(_AJ),_AK,E(_zM),E(_zM))));}}else{var _Bk=E(_B8);return (_Bk._==0)?new T5(0,3,E(_Bk.b),_Bk.c,E(new T5(0,1,E(_B6),_B7,E(_zM),E(_zM))),E(new T5(0,1,E(_AJ),_AK,E(_zM),E(_zM)))):new T5(0,2,E(_AJ),_AK,E(_B4),E(_zM));}}else{return new T5(0,1,E(_AJ),_AK,E(_zM),E(_zM));}}},_Bl=function(_Bm,_Bn,_Bo){var _Bp=E(_Bo);if(!_Bp._){return new F(function(){return _AI(_Bp.b,_Bp.c,B(_Bl(_Bm,_Bn,_Bp.d)),_Bp.e);});}else{return new F(function(){return _Aw(_Bm,_Bn);});}},_Bq=function(_Br,_Bs,_Bt,_Bu,_Bv,_Bw,_Bx){return new F(function(){return _AI(_Bu,_Bv,B(_Bl(_Br,_Bs,_Bw)),_Bx);});},_By=function(_Bz,_BA,_BB,_BC,_BD,_BE,_BF,_BG){var _BH=E(_BB);if(!_BH._){var _BI=_BH.a,_BJ=_BH.b,_BK=_BH.c,_BL=_BH.d,_BM=_BH.e;if((imul(3,_BI)|0)>=_BC){if((imul(3,_BC)|0)>=_BI){return new T5(0,(_BI+_BC|0)+1|0,E(_Bz),_BA,E(_BH),E(new T5(0,_BC,E(_BD),_BE,E(_BF),E(_BG))));}else{return new F(function(){return _zR(_BJ,_BK,_BL,B(_By(_Bz,_BA,_BM,_BC,_BD,_BE,_BF,_BG)));});}}else{return new F(function(){return _AI(_BD,_BE,B(_BN(_Bz,_BA,_BI,_BJ,_BK,_BL,_BM,_BF)),_BG);});}}else{return new F(function(){return _Bq(_Bz,_BA,_BC,_BD,_BE,_BF,_BG);});}},_BN=function(_BO,_BP,_BQ,_BR,_BS,_BT,_BU,_BV){var _BW=E(_BV);if(!_BW._){var _BX=_BW.a,_BY=_BW.b,_BZ=_BW.c,_C0=_BW.d,_C1=_BW.e;if((imul(3,_BQ)|0)>=_BX){if((imul(3,_BX)|0)>=_BQ){return new T5(0,(_BQ+_BX|0)+1|0,E(_BO),_BP,E(new T5(0,_BQ,E(_BR),_BS,E(_BT),E(_BU))),E(_BW));}else{return new F(function(){return _zR(_BR,_BS,_BT,B(_By(_BO,_BP,_BU,_BX,_BY,_BZ,_C0,_C1)));});}}else{return new F(function(){return _AI(_BY,_BZ,B(_BN(_BO,_BP,_BQ,_BR,_BS,_BT,_BU,_C0)),_C1);});}}else{return new F(function(){return _Az(_BO,_BP,new T5(0,_BQ,E(_BR),_BS,E(_BT),E(_BU)));});}},_C2=function(_C3,_C4,_C5,_C6){var _C7=E(_C5);if(!_C7._){var _C8=_C7.a,_C9=_C7.b,_Ca=_C7.c,_Cb=_C7.d,_Cc=_C7.e,_Cd=E(_C6);if(!_Cd._){var _Ce=_Cd.a,_Cf=_Cd.b,_Cg=_Cd.c,_Ch=_Cd.d,_Ci=_Cd.e;if((imul(3,_C8)|0)>=_Ce){if((imul(3,_Ce)|0)>=_C8){return new T5(0,(_C8+_Ce|0)+1|0,E(_C3),_C4,E(_C7),E(_Cd));}else{return new F(function(){return _zR(_C9,_Ca,_Cb,B(_By(_C3,_C4,_Cc,_Ce,_Cf,_Cg,_Ch,_Ci)));});}}else{return new F(function(){return _AI(_Cf,_Cg,B(_BN(_C3,_C4,_C8,_C9,_Ca,_Cb,_Cc,_Ch)),_Ci);});}}else{return new F(function(){return _Az(_C3,_C4,_C7);});}}else{return new F(function(){return _Bl(_C3,_C4,_C6);});}},_Cj=function(_Ck,_Cl,_Cm,_Cn,_Co){var _Cp=E(_Ck);if(_Cp==1){var _Cq=E(_Co);if(!_Cq._){return new T3(0,new T5(0,1,E(new T2(0,_Cl,_Cm)),_Cn,E(_zM),E(_zM)),_21,_21);}else{var _Cr=E(E(_Cq.a).a),_Cs=E(_Cl),_Ct=E(_Cr.a);return (_Cs>=_Ct)?(_Cs!=_Ct)?new T3(0,new T5(0,1,E(new T2(0,_Cs,_Cm)),_Cn,E(_zM),E(_zM)),_21,_Cq):(_Cm<E(_Cr.b))?new T3(0,new T5(0,1,E(new T2(0,_Cs,_Cm)),_Cn,E(_zM),E(_zM)),_Cq,_21):new T3(0,new T5(0,1,E(new T2(0,_Cs,_Cm)),_Cn,E(_zM),E(_zM)),_21,_Cq):new T3(0,new T5(0,1,E(new T2(0,_Cs,_Cm)),_Cn,E(_zM),E(_zM)),_Cq,_21);}}else{var _Cu=B(_Cj(_Cp>>1,_Cl,_Cm,_Cn,_Co)),_Cv=_Cu.a,_Cw=_Cu.c,_Cx=E(_Cu.b);if(!_Cx._){return new T3(0,_Cv,_21,_Cw);}else{var _Cy=E(_Cx.a),_Cz=_Cy.a,_CA=_Cy.b,_CB=E(_Cx.b);if(!_CB._){return new T3(0,new T(function(){return B(_Az(_Cz,_CA,_Cv));}),_21,_Cw);}else{var _CC=_CB.b,_CD=E(_CB.a),_CE=_CD.b,_CF=E(_Cz),_CG=E(_CD.a),_CH=_CG.b,_CI=E(_CF.a),_CJ=E(_CG.a);if(_CI>=_CJ){if(_CI!=_CJ){return new T3(0,_Cv,_21,_Cx);}else{var _CK=E(_CH);if(E(_CF.b)<_CK){var _CL=B(_Cj(_Cp>>1,_CJ,_CK,_CE,_CC));return new T3(0,new T(function(){return B(_C2(_CF,_CA,_Cv,_CL.a));}),_CL.b,_CL.c);}else{return new T3(0,_Cv,_21,_Cx);}}}else{var _CM=B(_CN(_Cp>>1,_CJ,_CH,_CE,_CC));return new T3(0,new T(function(){return B(_C2(_CF,_CA,_Cv,_CM.a));}),_CM.b,_CM.c);}}}}},_CN=function(_CO,_CP,_CQ,_CR,_CS){var _CT=E(_CO);if(_CT==1){var _CU=E(_CS);if(!_CU._){return new T3(0,new T5(0,1,E(new T2(0,_CP,_CQ)),_CR,E(_zM),E(_zM)),_21,_21);}else{var _CV=E(E(_CU.a).a),_CW=E(_CP),_CX=E(_CV.a);if(_CW>=_CX){if(_CW!=_CX){return new T3(0,new T5(0,1,E(new T2(0,_CW,_CQ)),_CR,E(_zM),E(_zM)),_21,_CU);}else{var _CY=E(_CQ);return (_CY<E(_CV.b))?new T3(0,new T5(0,1,E(new T2(0,_CW,_CY)),_CR,E(_zM),E(_zM)),_CU,_21):new T3(0,new T5(0,1,E(new T2(0,_CW,_CY)),_CR,E(_zM),E(_zM)),_21,_CU);}}else{return new T3(0,new T5(0,1,E(new T2(0,_CW,_CQ)),_CR,E(_zM),E(_zM)),_CU,_21);}}}else{var _CZ=B(_CN(_CT>>1,_CP,_CQ,_CR,_CS)),_D0=_CZ.a,_D1=_CZ.c,_D2=E(_CZ.b);if(!_D2._){return new T3(0,_D0,_21,_D1);}else{var _D3=E(_D2.a),_D4=_D3.a,_D5=_D3.b,_D6=E(_D2.b);if(!_D6._){return new T3(0,new T(function(){return B(_Az(_D4,_D5,_D0));}),_21,_D1);}else{var _D7=_D6.b,_D8=E(_D6.a),_D9=_D8.b,_Da=E(_D4),_Db=E(_D8.a),_Dc=_Db.b,_Dd=E(_Da.a),_De=E(_Db.a);if(_Dd>=_De){if(_Dd!=_De){return new T3(0,_D0,_21,_D2);}else{var _Df=E(_Dc);if(E(_Da.b)<_Df){var _Dg=B(_Cj(_CT>>1,_De,_Df,_D9,_D7));return new T3(0,new T(function(){return B(_C2(_Da,_D5,_D0,_Dg.a));}),_Dg.b,_Dg.c);}else{return new T3(0,_D0,_21,_D2);}}}else{var _Dh=B(_CN(_CT>>1,_De,_Dc,_D9,_D7));return new T3(0,new T(function(){return B(_C2(_Da,_D5,_D0,_Dh.a));}),_Dh.b,_Dh.c);}}}}},_Di=function(_Dj,_Dk,_Dl,_Dm,_Dn){var _Do=E(_Dn);if(!_Do._){var _Dp=_Do.c,_Dq=_Do.d,_Dr=_Do.e,_Ds=E(_Do.b),_Dt=E(_Ds.a);if(_Dj>=_Dt){if(_Dj!=_Dt){return new F(function(){return _zR(_Ds,_Dp,_Dq,B(_Di(_Dj,_,_Dl,_Dm,_Dr)));});}else{var _Du=E(_Ds.b);if(_Dl>=_Du){if(_Dl!=_Du){return new F(function(){return _zR(_Ds,_Dp,_Dq,B(_Di(_Dj,_,_Dl,_Dm,_Dr)));});}else{return new T5(0,_Do.a,E(new T2(0,_Dj,_Dl)),_Dm,E(_Dq),E(_Dr));}}else{return new F(function(){return _AI(_Ds,_Dp,B(_Di(_Dj,_,_Dl,_Dm,_Dq)),_Dr);});}}}else{return new F(function(){return _AI(_Ds,_Dp,B(_Di(_Dj,_,_Dl,_Dm,_Dq)),_Dr);});}}else{return new T5(0,1,E(new T2(0,_Dj,_Dl)),_Dm,E(_zM),E(_zM));}},_Dv=function(_Dw,_Dx,_Dy,_Dz,_DA){var _DB=E(_DA);if(!_DB._){var _DC=_DB.c,_DD=_DB.d,_DE=_DB.e,_DF=E(_DB.b),_DG=E(_DF.a);if(_Dw>=_DG){if(_Dw!=_DG){return new F(function(){return _zR(_DF,_DC,_DD,B(_Dv(_Dw,_,_Dy,_Dz,_DE)));});}else{var _DH=E(_Dy),_DI=E(_DF.b);if(_DH>=_DI){if(_DH!=_DI){return new F(function(){return _zR(_DF,_DC,_DD,B(_Di(_Dw,_,_DH,_Dz,_DE)));});}else{return new T5(0,_DB.a,E(new T2(0,_Dw,_DH)),_Dz,E(_DD),E(_DE));}}else{return new F(function(){return _AI(_DF,_DC,B(_Di(_Dw,_,_DH,_Dz,_DD)),_DE);});}}}else{return new F(function(){return _AI(_DF,_DC,B(_Dv(_Dw,_,_Dy,_Dz,_DD)),_DE);});}}else{return new T5(0,1,E(new T2(0,_Dw,_Dy)),_Dz,E(_zM),E(_zM));}},_DJ=function(_DK,_DL,_DM,_DN){var _DO=E(_DN);if(!_DO._){var _DP=_DO.c,_DQ=_DO.d,_DR=_DO.e,_DS=E(_DO.b),_DT=E(_DK),_DU=E(_DS.a);if(_DT>=_DU){if(_DT!=_DU){return new F(function(){return _zR(_DS,_DP,_DQ,B(_Dv(_DT,_,_DL,_DM,_DR)));});}else{var _DV=E(_DL),_DW=E(_DS.b);if(_DV>=_DW){if(_DV!=_DW){return new F(function(){return _zR(_DS,_DP,_DQ,B(_Di(_DT,_,_DV,_DM,_DR)));});}else{return new T5(0,_DO.a,E(new T2(0,_DT,_DV)),_DM,E(_DQ),E(_DR));}}else{return new F(function(){return _AI(_DS,_DP,B(_Di(_DT,_,_DV,_DM,_DQ)),_DR);});}}}else{return new F(function(){return _AI(_DS,_DP,B(_Dv(_DT,_,_DL,_DM,_DQ)),_DR);});}}else{return new T5(0,1,E(new T2(0,_DK,_DL)),_DM,E(_zM),E(_zM));}},_DX=function(_DY,_DZ){while(1){var _E0=E(_DZ);if(!_E0._){return E(_DY);}else{var _E1=E(_E0.a),_E2=E(_E1.a),_E3=B(_DJ(_E2.a,_E2.b,_E1.b,_DY));_DY=_E3;_DZ=_E0.b;continue;}}},_E4=function(_E5,_E6,_E7,_E8,_E9){return new F(function(){return _DX(B(_DJ(_E6,_E7,_E8,_E5)),_E9);});},_Ea=function(_Eb,_Ec,_Ed){var _Ee=E(_Ec),_Ef=E(_Ee.a);return new F(function(){return _DX(B(_DJ(_Ef.a,_Ef.b,_Ee.b,_Eb)),_Ed);});},_Eg=function(_Eh,_Ei,_Ej){var _Ek=E(_Ej);if(!_Ek._){return E(_Ei);}else{var _El=E(_Ek.a),_Em=_El.a,_En=_El.b,_Eo=E(_Ek.b);if(!_Eo._){return new F(function(){return _Az(_Em,_En,_Ei);});}else{var _Ep=E(_Eo.a),_Eq=E(_Em),_Er=_Eq.b,_Es=E(_Ep.a),_Et=_Es.b,_Eu=E(_Eq.a),_Ev=E(_Es.a),_Ew=function(_Ex){var _Ey=B(_CN(_Eh,_Ev,_Et,_Ep.b,_Eo.b)),_Ez=_Ey.a,_EA=E(_Ey.c);if(!_EA._){return new F(function(){return _Eg(_Eh<<1,B(_C2(_Eq,_En,_Ei,_Ez)),_Ey.b);});}else{return new F(function(){return _Ea(B(_C2(_Eq,_En,_Ei,_Ez)),_EA.a,_EA.b);});}};if(_Eu>=_Ev){if(_Eu!=_Ev){return new F(function(){return _E4(_Ei,_Eu,_Er,_En,_Eo);});}else{var _EB=E(_Er);if(_EB<E(_Et)){return new F(function(){return _Ew(_);});}else{return new F(function(){return _E4(_Ei,_Eu,_EB,_En,_Eo);});}}}else{return new F(function(){return _Ew(_);});}}}},_EC=function(_ED,_EE,_EF,_EG,_EH,_EI){var _EJ=E(_EI);if(!_EJ._){return new F(function(){return _Az(new T2(0,_EF,_EG),_EH,_EE);});}else{var _EK=E(_EJ.a),_EL=E(_EK.a),_EM=_EL.b,_EN=E(_EF),_EO=E(_EL.a),_EP=function(_EQ){var _ER=B(_CN(_ED,_EO,_EM,_EK.b,_EJ.b)),_ES=_ER.a,_ET=E(_ER.c);if(!_ET._){return new F(function(){return _Eg(_ED<<1,B(_C2(new T2(0,_EN,_EG),_EH,_EE,_ES)),_ER.b);});}else{return new F(function(){return _Ea(B(_C2(new T2(0,_EN,_EG),_EH,_EE,_ES)),_ET.a,_ET.b);});}};if(_EN>=_EO){if(_EN!=_EO){return new F(function(){return _E4(_EE,_EN,_EG,_EH,_EJ);});}else{if(_EG<E(_EM)){return new F(function(){return _EP(_);});}else{return new F(function(){return _E4(_EE,_EN,_EG,_EH,_EJ);});}}}else{return new F(function(){return _EP(_);});}}},_EU=function(_EV,_EW,_EX,_EY,_EZ,_F0){var _F1=E(_F0);if(!_F1._){return new F(function(){return _Az(new T2(0,_EX,_EY),_EZ,_EW);});}else{var _F2=E(_F1.a),_F3=E(_F2.a),_F4=_F3.b,_F5=E(_EX),_F6=E(_F3.a),_F7=function(_F8){var _F9=B(_CN(_EV,_F6,_F4,_F2.b,_F1.b)),_Fa=_F9.a,_Fb=E(_F9.c);if(!_Fb._){return new F(function(){return _Eg(_EV<<1,B(_C2(new T2(0,_F5,_EY),_EZ,_EW,_Fa)),_F9.b);});}else{return new F(function(){return _Ea(B(_C2(new T2(0,_F5,_EY),_EZ,_EW,_Fa)),_Fb.a,_Fb.b);});}};if(_F5>=_F6){if(_F5!=_F6){return new F(function(){return _E4(_EW,_F5,_EY,_EZ,_F1);});}else{var _Fc=E(_EY);if(_Fc<E(_F4)){return new F(function(){return _F7(_);});}else{return new F(function(){return _E4(_EW,_F5,_Fc,_EZ,_F1);});}}}else{return new F(function(){return _F7(_);});}}},_Fd=function(_Fe){var _Ff=E(_Fe);if(!_Ff._){return new T0(1);}else{var _Fg=E(_Ff.a),_Fh=_Fg.a,_Fi=_Fg.b,_Fj=E(_Ff.b);if(!_Fj._){return new T5(0,1,E(_Fh),_Fi,E(_zM),E(_zM));}else{var _Fk=_Fj.b,_Fl=E(_Fj.a),_Fm=_Fl.b,_Fn=E(_Fh),_Fo=E(_Fl.a),_Fp=_Fo.b,_Fq=E(_Fn.a),_Fr=E(_Fo.a);if(_Fq>=_Fr){if(_Fq!=_Fr){return new F(function(){return _E4(new T5(0,1,E(_Fn),_Fi,E(_zM),E(_zM)),_Fr,_Fp,_Fm,_Fk);});}else{var _Fs=E(_Fp);if(E(_Fn.b)<_Fs){return new F(function(){return _EC(1,new T5(0,1,E(_Fn),_Fi,E(_zM),E(_zM)),_Fr,_Fs,_Fm,_Fk);});}else{return new F(function(){return _E4(new T5(0,1,E(_Fn),_Fi,E(_zM),E(_zM)),_Fr,_Fs,_Fm,_Fk);});}}}else{return new F(function(){return _EU(1,new T5(0,1,E(_Fn),_Fi,E(_zM),E(_zM)),_Fr,_Fp,_Fm,_Fk);});}}}},_Ft=function(_Fu,_Fv,_Fw,_Fx,_Fy){var _Fz=E(_Fu);if(_Fz==1){var _FA=E(_Fy);if(!_FA._){return new T3(0,new T5(0,1,E(new T2(0,_Fv,_Fw)),_Fx,E(_zM),E(_zM)),_21,_21);}else{var _FB=E(E(_FA.a).a),_FC=E(_Fv),_FD=E(_FB.a);return (_FC>=_FD)?(_FC!=_FD)?new T3(0,new T5(0,1,E(new T2(0,_FC,_Fw)),_Fx,E(_zM),E(_zM)),_21,_FA):(_Fw<E(_FB.b))?new T3(0,new T5(0,1,E(new T2(0,_FC,_Fw)),_Fx,E(_zM),E(_zM)),_FA,_21):new T3(0,new T5(0,1,E(new T2(0,_FC,_Fw)),_Fx,E(_zM),E(_zM)),_21,_FA):new T3(0,new T5(0,1,E(new T2(0,_FC,_Fw)),_Fx,E(_zM),E(_zM)),_FA,_21);}}else{var _FE=B(_Ft(_Fz>>1,_Fv,_Fw,_Fx,_Fy)),_FF=_FE.a,_FG=_FE.c,_FH=E(_FE.b);if(!_FH._){return new T3(0,_FF,_21,_FG);}else{var _FI=E(_FH.a),_FJ=_FI.a,_FK=_FI.b,_FL=E(_FH.b);if(!_FL._){return new T3(0,new T(function(){return B(_Az(_FJ,_FK,_FF));}),_21,_FG);}else{var _FM=_FL.b,_FN=E(_FL.a),_FO=_FN.b,_FP=E(_FJ),_FQ=E(_FN.a),_FR=_FQ.b,_FS=E(_FP.a),_FT=E(_FQ.a);if(_FS>=_FT){if(_FS!=_FT){return new T3(0,_FF,_21,_FH);}else{var _FU=E(_FR);if(E(_FP.b)<_FU){var _FV=B(_Ft(_Fz>>1,_FT,_FU,_FO,_FM));return new T3(0,new T(function(){return B(_C2(_FP,_FK,_FF,_FV.a));}),_FV.b,_FV.c);}else{return new T3(0,_FF,_21,_FH);}}}else{var _FW=B(_FX(_Fz>>1,_FT,_FR,_FO,_FM));return new T3(0,new T(function(){return B(_C2(_FP,_FK,_FF,_FW.a));}),_FW.b,_FW.c);}}}}},_FX=function(_FY,_FZ,_G0,_G1,_G2){var _G3=E(_FY);if(_G3==1){var _G4=E(_G2);if(!_G4._){return new T3(0,new T5(0,1,E(new T2(0,_FZ,_G0)),_G1,E(_zM),E(_zM)),_21,_21);}else{var _G5=E(E(_G4.a).a),_G6=E(_FZ),_G7=E(_G5.a);if(_G6>=_G7){if(_G6!=_G7){return new T3(0,new T5(0,1,E(new T2(0,_G6,_G0)),_G1,E(_zM),E(_zM)),_21,_G4);}else{var _G8=E(_G0);return (_G8<E(_G5.b))?new T3(0,new T5(0,1,E(new T2(0,_G6,_G8)),_G1,E(_zM),E(_zM)),_G4,_21):new T3(0,new T5(0,1,E(new T2(0,_G6,_G8)),_G1,E(_zM),E(_zM)),_21,_G4);}}else{return new T3(0,new T5(0,1,E(new T2(0,_G6,_G0)),_G1,E(_zM),E(_zM)),_G4,_21);}}}else{var _G9=B(_FX(_G3>>1,_FZ,_G0,_G1,_G2)),_Ga=_G9.a,_Gb=_G9.c,_Gc=E(_G9.b);if(!_Gc._){return new T3(0,_Ga,_21,_Gb);}else{var _Gd=E(_Gc.a),_Ge=_Gd.a,_Gf=_Gd.b,_Gg=E(_Gc.b);if(!_Gg._){return new T3(0,new T(function(){return B(_Az(_Ge,_Gf,_Ga));}),_21,_Gb);}else{var _Gh=_Gg.b,_Gi=E(_Gg.a),_Gj=_Gi.b,_Gk=E(_Ge),_Gl=E(_Gi.a),_Gm=_Gl.b,_Gn=E(_Gk.a),_Go=E(_Gl.a);if(_Gn>=_Go){if(_Gn!=_Go){return new T3(0,_Ga,_21,_Gc);}else{var _Gp=E(_Gm);if(E(_Gk.b)<_Gp){var _Gq=B(_Ft(_G3>>1,_Go,_Gp,_Gj,_Gh));return new T3(0,new T(function(){return B(_C2(_Gk,_Gf,_Ga,_Gq.a));}),_Gq.b,_Gq.c);}else{return new T3(0,_Ga,_21,_Gc);}}}else{var _Gr=B(_FX(_G3>>1,_Go,_Gm,_Gj,_Gh));return new T3(0,new T(function(){return B(_C2(_Gk,_Gf,_Ga,_Gr.a));}),_Gr.b,_Gr.c);}}}}},_Gs=function(_Gt,_Gu,_Gv,_Gw,_Gx){var _Gy=E(_Gx);if(!_Gy._){var _Gz=_Gy.c,_GA=_Gy.d,_GB=_Gy.e,_GC=E(_Gy.b),_GD=E(_GC.a);if(_Gt>=_GD){if(_Gt!=_GD){return new F(function(){return _zR(_GC,_Gz,_GA,B(_Gs(_Gt,_,_Gv,_Gw,_GB)));});}else{var _GE=E(_GC.b);if(_Gv>=_GE){if(_Gv!=_GE){return new F(function(){return _zR(_GC,_Gz,_GA,B(_Gs(_Gt,_,_Gv,_Gw,_GB)));});}else{return new T5(0,_Gy.a,E(new T2(0,_Gt,_Gv)),_Gw,E(_GA),E(_GB));}}else{return new F(function(){return _AI(_GC,_Gz,B(_Gs(_Gt,_,_Gv,_Gw,_GA)),_GB);});}}}else{return new F(function(){return _AI(_GC,_Gz,B(_Gs(_Gt,_,_Gv,_Gw,_GA)),_GB);});}}else{return new T5(0,1,E(new T2(0,_Gt,_Gv)),_Gw,E(_zM),E(_zM));}},_GF=function(_GG,_GH,_GI,_GJ,_GK){var _GL=E(_GK);if(!_GL._){var _GM=_GL.c,_GN=_GL.d,_GO=_GL.e,_GP=E(_GL.b),_GQ=E(_GP.a);if(_GG>=_GQ){if(_GG!=_GQ){return new F(function(){return _zR(_GP,_GM,_GN,B(_GF(_GG,_,_GI,_GJ,_GO)));});}else{var _GR=E(_GI),_GS=E(_GP.b);if(_GR>=_GS){if(_GR!=_GS){return new F(function(){return _zR(_GP,_GM,_GN,B(_Gs(_GG,_,_GR,_GJ,_GO)));});}else{return new T5(0,_GL.a,E(new T2(0,_GG,_GR)),_GJ,E(_GN),E(_GO));}}else{return new F(function(){return _AI(_GP,_GM,B(_Gs(_GG,_,_GR,_GJ,_GN)),_GO);});}}}else{return new F(function(){return _AI(_GP,_GM,B(_GF(_GG,_,_GI,_GJ,_GN)),_GO);});}}else{return new T5(0,1,E(new T2(0,_GG,_GI)),_GJ,E(_zM),E(_zM));}},_GT=function(_GU,_GV,_GW,_GX){var _GY=E(_GX);if(!_GY._){var _GZ=_GY.c,_H0=_GY.d,_H1=_GY.e,_H2=E(_GY.b),_H3=E(_GU),_H4=E(_H2.a);if(_H3>=_H4){if(_H3!=_H4){return new F(function(){return _zR(_H2,_GZ,_H0,B(_GF(_H3,_,_GV,_GW,_H1)));});}else{var _H5=E(_GV),_H6=E(_H2.b);if(_H5>=_H6){if(_H5!=_H6){return new F(function(){return _zR(_H2,_GZ,_H0,B(_Gs(_H3,_,_H5,_GW,_H1)));});}else{return new T5(0,_GY.a,E(new T2(0,_H3,_H5)),_GW,E(_H0),E(_H1));}}else{return new F(function(){return _AI(_H2,_GZ,B(_Gs(_H3,_,_H5,_GW,_H0)),_H1);});}}}else{return new F(function(){return _AI(_H2,_GZ,B(_GF(_H3,_,_GV,_GW,_H0)),_H1);});}}else{return new T5(0,1,E(new T2(0,_GU,_GV)),_GW,E(_zM),E(_zM));}},_H7=function(_H8,_H9){while(1){var _Ha=E(_H9);if(!_Ha._){return E(_H8);}else{var _Hb=E(_Ha.a),_Hc=E(_Hb.a),_Hd=B(_GT(_Hc.a,_Hc.b,_Hb.b,_H8));_H8=_Hd;_H9=_Ha.b;continue;}}},_He=function(_Hf,_Hg,_Hh,_Hi,_Hj){return new F(function(){return _H7(B(_GT(_Hg,_Hh,_Hi,_Hf)),_Hj);});},_Hk=function(_Hl,_Hm,_Hn){var _Ho=E(_Hm),_Hp=E(_Ho.a);return new F(function(){return _H7(B(_GT(_Hp.a,_Hp.b,_Ho.b,_Hl)),_Hn);});},_Hq=function(_Hr,_Hs,_Ht){var _Hu=E(_Ht);if(!_Hu._){return E(_Hs);}else{var _Hv=E(_Hu.a),_Hw=_Hv.a,_Hx=_Hv.b,_Hy=E(_Hu.b);if(!_Hy._){return new F(function(){return _Az(_Hw,_Hx,_Hs);});}else{var _Hz=E(_Hy.a),_HA=E(_Hw),_HB=_HA.b,_HC=E(_Hz.a),_HD=_HC.b,_HE=E(_HA.a),_HF=E(_HC.a),_HG=function(_HH){var _HI=B(_FX(_Hr,_HF,_HD,_Hz.b,_Hy.b)),_HJ=_HI.a,_HK=E(_HI.c);if(!_HK._){return new F(function(){return _Hq(_Hr<<1,B(_C2(_HA,_Hx,_Hs,_HJ)),_HI.b);});}else{return new F(function(){return _Hk(B(_C2(_HA,_Hx,_Hs,_HJ)),_HK.a,_HK.b);});}};if(_HE>=_HF){if(_HE!=_HF){return new F(function(){return _He(_Hs,_HE,_HB,_Hx,_Hy);});}else{var _HL=E(_HB);if(_HL<E(_HD)){return new F(function(){return _HG(_);});}else{return new F(function(){return _He(_Hs,_HE,_HL,_Hx,_Hy);});}}}else{return new F(function(){return _HG(_);});}}}},_HM=function(_HN,_HO,_HP,_HQ,_HR,_HS){var _HT=E(_HS);if(!_HT._){return new F(function(){return _Az(new T2(0,_HP,_HQ),_HR,_HO);});}else{var _HU=E(_HT.a),_HV=E(_HU.a),_HW=_HV.b,_HX=E(_HP),_HY=E(_HV.a),_HZ=function(_I0){var _I1=B(_FX(_HN,_HY,_HW,_HU.b,_HT.b)),_I2=_I1.a,_I3=E(_I1.c);if(!_I3._){return new F(function(){return _Hq(_HN<<1,B(_C2(new T2(0,_HX,_HQ),_HR,_HO,_I2)),_I1.b);});}else{return new F(function(){return _Hk(B(_C2(new T2(0,_HX,_HQ),_HR,_HO,_I2)),_I3.a,_I3.b);});}};if(_HX>=_HY){if(_HX!=_HY){return new F(function(){return _He(_HO,_HX,_HQ,_HR,_HT);});}else{var _I4=E(_HQ);if(_I4<E(_HW)){return new F(function(){return _HZ(_);});}else{return new F(function(){return _He(_HO,_HX,_I4,_HR,_HT);});}}}else{return new F(function(){return _HZ(_);});}}},_I5=function(_I6,_I7,_I8,_I9,_Ia,_Ib){var _Ic=E(_Ib);if(!_Ic._){return new F(function(){return _Az(new T2(0,_I8,_I9),_Ia,_I7);});}else{var _Id=E(_Ic.a),_Ie=E(_Id.a),_If=_Ie.b,_Ig=E(_I8),_Ih=E(_Ie.a),_Ii=function(_Ij){var _Ik=B(_FX(_I6,_Ih,_If,_Id.b,_Ic.b)),_Il=_Ik.a,_Im=E(_Ik.c);if(!_Im._){return new F(function(){return _Hq(_I6<<1,B(_C2(new T2(0,_Ig,_I9),_Ia,_I7,_Il)),_Ik.b);});}else{return new F(function(){return _Hk(B(_C2(new T2(0,_Ig,_I9),_Ia,_I7,_Il)),_Im.a,_Im.b);});}};if(_Ig>=_Ih){if(_Ig!=_Ih){return new F(function(){return _He(_I7,_Ig,_I9,_Ia,_Ic);});}else{if(_I9<E(_If)){return new F(function(){return _Ii(_);});}else{return new F(function(){return _He(_I7,_Ig,_I9,_Ia,_Ic);});}}}else{return new F(function(){return _Ii(_);});}}},_In=function(_Io){var _Ip=E(_Io);if(!_Ip._){return new T0(1);}else{var _Iq=E(_Ip.a),_Ir=_Iq.a,_Is=_Iq.b,_It=E(_Ip.b);if(!_It._){return new T5(0,1,E(_Ir),_Is,E(_zM),E(_zM));}else{var _Iu=_It.b,_Iv=E(_It.a),_Iw=_Iv.b,_Ix=E(_Ir),_Iy=E(_Iv.a),_Iz=_Iy.b,_IA=E(_Ix.a),_IB=E(_Iy.a);if(_IA>=_IB){if(_IA!=_IB){return new F(function(){return _He(new T5(0,1,E(_Ix),_Is,E(_zM),E(_zM)),_IB,_Iz,_Iw,_Iu);});}else{var _IC=E(_Iz);if(E(_Ix.b)<_IC){return new F(function(){return _I5(1,new T5(0,1,E(_Ix),_Is,E(_zM),E(_zM)),_IB,_IC,_Iw,_Iu);});}else{return new F(function(){return _He(new T5(0,1,E(_Ix),_Is,E(_zM),E(_zM)),_IB,_IC,_Iw,_Iu);});}}}else{return new F(function(){return _HM(1,new T5(0,1,E(_Ix),_Is,E(_zM),E(_zM)),_IB,_Iz,_Iw,_Iu);});}}}},_ID=function(_IE,_IF){while(1){var _IG=B((function(_IH,_II){var _IJ=E(_II);if(!_IJ._){_IE=new T2(1,new T2(0,_IJ.b,_IJ.c),new T(function(){return B(_ID(_IH,_IJ.e));}));_IF=_IJ.d;return __continue;}else{return E(_IH);}})(_IE,_IF));if(_IG!=__continue){return _IG;}}},_IK=function(_IL,_IM,_IN){return new F(function(){return A1(_IL,new T2(1,_2G,new T(function(){return B(A1(_IM,_IN));})));});},_IO=new T(function(){return B(unCStr("CC "));}),_IP=function(_IQ,_IR,_IS,_IT,_IU,_IV){var _IW=function(_IX){var _IY=new T(function(){var _IZ=new T(function(){return B(_c(11,E(_IT),new T2(1,_v,new T(function(){return B(_c(11,E(_IU),_IX));}))));});return B(_c(11,E(_IS),new T2(1,_v,_IZ)));});return new F(function(){return _n(11,_IR,new T2(1,_v,_IY));});};if(_IQ<11){return new F(function(){return _2(_IO,new T(function(){return B(_IW(_IV));},1));});}else{var _J0=new T(function(){return B(_2(_IO,new T(function(){return B(_IW(new T2(1,_a,_IV)));},1)));});return new T2(1,_b,_J0);}},_J1=function(_J2,_J3){var _J4=E(_J2);return new F(function(){return _IP(0,_J4.a,_J4.b,_J4.c,_J4.d,_J3);});},_J5=new T(function(){return B(unCStr("RC "));}),_J6=function(_J7,_J8,_J9,_Ja,_Jb){var _Jc=function(_Jd){var _Je=new T(function(){var _Jf=new T(function(){return B(_c(11,E(_J9),new T2(1,_v,new T(function(){return B(_c(11,E(_Ja),_Jd));}))));});return B(_n(11,_J8,new T2(1,_v,_Jf)));},1);return new F(function(){return _2(_J5,_Je);});};if(_J7<11){return new F(function(){return _Jc(_Jb);});}else{return new T2(1,_b,new T(function(){return B(_Jc(new T2(1,_a,_Jb)));}));}},_Jg=function(_Jh,_Ji){var _Jj=E(_Jh);return new F(function(){return _J6(0,_Jj.a,_Jj.b,_Jj.c,_Ji);});},_Jk=new T(function(){return B(unCStr(": empty list"));}),_Jl=new T(function(){return B(unCStr("Prelude."));}),_Jm=function(_Jn){return new F(function(){return err(B(_2(_Jl,new T(function(){return B(_2(_Jn,_Jk));},1))));});},_Jo=new T(function(){return B(unCStr("foldr1"));}),_Jp=new T(function(){return B(_Jm(_Jo));}),_Jq=function(_Jr,_Js){var _Jt=E(_Js);if(!_Jt._){return E(_Jp);}else{var _Ju=_Jt.a,_Jv=E(_Jt.b);if(!_Jv._){return E(_Ju);}else{return new F(function(){return A2(_Jr,_Ju,new T(function(){return B(_Jq(_Jr,_Jv));}));});}}},_Jw=function(_Jx,_Jy,_Jz){var _JA=new T(function(){var _JB=function(_JC){var _JD=E(_Jx),_JE=new T(function(){return B(A3(_Jq,_IK,new T2(1,function(_JF){return new F(function(){return _1h(0,_JD.a,_JF);});},new T2(1,function(_JG){return new F(function(){return _c(0,E(_JD.b),_JG);});},_21)),new T2(1,_a,_JC)));});return new T2(1,_b,_JE);};return B(A3(_Jq,_IK,new T2(1,_JB,new T2(1,function(_JH){return new F(function(){return _c(0,E(_Jy),_JH);});},_21)),new T2(1,_a,_Jz)));});return new T2(0,_b,_JA);},_JI=function(_JJ,_JK){var _JL=E(_JJ),_JM=B(_Jw(_JL.a,_JL.b,_JK));return new T2(1,_JM.a,_JM.b);},_JN=function(_JO,_JP){return new F(function(){return _2J(_JI,_JO,_JP);});},_JQ=function(_JR,_JS,_JT){var _JU=new T(function(){var _JV=function(_JW){var _JX=E(_JR),_JY=new T(function(){return B(A3(_Jq,_IK,new T2(1,function(_JZ){return new F(function(){return _h(0,_JX.a,_JZ);});},new T2(1,function(_K0){return new F(function(){return _c(0,E(_JX.b),_K0);});},_21)),new T2(1,_a,_JW)));});return new T2(1,_b,_JY);};return B(A3(_Jq,_IK,new T2(1,_JV,new T2(1,function(_K1){return new F(function(){return _c(0,E(_JS),_K1);});},_21)),new T2(1,_a,_JT)));});return new T2(0,_b,_JU);},_K2=function(_K3,_K4){var _K5=E(_K3),_K6=B(_JQ(_K5.a,_K5.b,_K4));return new T2(1,_K6.a,_K6.b);},_K7=function(_K8,_K9){return new F(function(){return _2J(_K2,_K8,_K9);});},_Ka=new T2(1,_a,_21),_Kb=function(_Kc,_Kd){while(1){var _Ke=B((function(_Kf,_Kg){var _Kh=E(_Kg);if(!_Kh._){_Kc=new T2(1,_Kh.b,new T(function(){return B(_Kb(_Kf,_Kh.d));}));_Kd=_Kh.c;return __continue;}else{return E(_Kf);}})(_Kc,_Kd));if(_Ke!=__continue){return _Ke;}}},_Ki=function(_Kj,_Kk,_Kl,_Km){var _Kn=new T(function(){var _Ko=new T(function(){return B(_ID(_21,_Km));}),_Kp=new T(function(){return B(_ID(_21,_Kl));}),_Kq=new T(function(){return B(_Kb(_21,_Kk));}),_Kr=new T(function(){return B(_Kb(_21,_Kj));});return B(A3(_Jq,_IK,new T2(1,function(_Ks){return new F(function(){return _2J(_J1,_Kr,_Ks);});},new T2(1,function(_Kt){return new F(function(){return _2J(_Jg,_Kq,_Kt);});},new T2(1,function(_Ku){return new F(function(){return _JN(_Kp,_Ku);});},new T2(1,function(_Kv){return new F(function(){return _K7(_Ko,_Kv);});},_21)))),_Ka));});return new T2(0,_b,_Kn);},_Kw=new T(function(){return B(err(_22));}),_Kx=new T(function(){return B(err(_2c));}),_Ky=function(_Kz){return new F(function(){return _gs(_gV,_Kz);});},_KA=new T(function(){return B(unCStr("["));}),_KB=function(_KC,_KD){var _KE=function(_KF,_KG){var _KH=new T(function(){return B(A1(_KG,_21));}),_KI=new T(function(){var _KJ=function(_KK){return new F(function(){return _KE(_8C,function(_KL){return new F(function(){return A1(_KG,new T2(1,_KK,_KL));});});});};return B(A2(_KC,_fX,_KJ));}),_KM=new T(function(){return B(_fq(function(_KN){var _KO=E(_KN);if(_KO._==2){var _KP=E(_KO.a);if(!_KP._){return new T0(2);}else{var _KQ=_KP.b;switch(E(_KP.a)){case 44:return (E(_KQ)._==0)?(!E(_KF))?new T0(2):E(_KI):new T0(2);case 93:return (E(_KQ)._==0)?E(_KH):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_KR=function(_KS){return E(_KM);};return new T1(1,function(_KT){return new F(function(){return A2(_e7,_KT,_KR);});});},_KU=function(_KV,_KW){return new F(function(){return _KX(_KW);});},_KX=function(_KY){var _KZ=new T(function(){var _L0=new T(function(){var _L1=new T(function(){var _L2=function(_L3){return new F(function(){return _KE(_8C,function(_L4){return new F(function(){return A1(_KY,new T2(1,_L3,_L4));});});});};return B(A2(_KC,_fX,_L2));});return B(_3K(B(_KE(_8B,_KY)),_L1));});return B(_fq(function(_L5){var _L6=E(_L5);return (_L6._==2)?(!B(_4q(_L6.a,_KA)))?new T0(2):E(_L0):new T0(2);}));}),_L7=function(_L8){return E(_KZ);};return new F(function(){return _3K(new T1(1,function(_L9){return new F(function(){return A2(_e7,_L9,_L7);});}),new T(function(){return new T1(1,B(_fY(_KU,_KY)));}));});};return new F(function(){return _KX(_KD);});},_La=function(_Lb,_Lc){return new F(function(){return _KB(_Ky,_Lc);});},_Ld=new T(function(){return B(_KB(_Ky,_4X));}),_Le=function(_Kz){return new F(function(){return _3A(_Ld,_Kz);});},_Lf=function(_Lg){var _Lh=new T(function(){return B(A3(_gs,_gV,_Lg,_4X));});return function(_Li){return new F(function(){return _3A(_Lh,_Li);});};},_Lj=new T4(0,_Lf,_Le,_Ky,_La),_Lk=function(_Ll){return new F(function(){return _gh(_hH,_Ll);});},_Lm=function(_Ln,_Lo){return new F(function(){return _KB(_Lk,_Lo);});},_Lp=new T(function(){return B(_KB(_Lk,_4X));}),_Lq=function(_Ll){return new F(function(){return _3A(_Lp,_Ll);});},_Lr=function(_Ls){var _Lt=new T(function(){return B(A3(_gh,_hH,_Ls,_4X));});return function(_Li){return new F(function(){return _3A(_Lt,_Li);});};},_Lu=new T4(0,_Lr,_Lq,_Lk,_Lm),_Lv=new T(function(){return B(unCStr(","));}),_Lw=function(_Lx){return E(E(_Lx).c);},_Ly=function(_Lz,_LA,_LB){var _LC=new T(function(){return B(_Lw(_LA));}),_LD=new T(function(){return B(A2(_Lw,_Lz,_LB));}),_LE=function(_LF){var _LG=function(_LH){var _LI=new T(function(){var _LJ=new T(function(){return B(A2(_LC,_LB,function(_LK){return new F(function(){return A1(_LF,new T2(0,_LH,_LK));});}));});return B(_fq(function(_LL){var _LM=E(_LL);return (_LM._==2)?(!B(_4q(_LM.a,_Lv)))?new T0(2):E(_LJ):new T0(2);}));}),_LN=function(_LO){return E(_LI);};return new T1(1,function(_LP){return new F(function(){return A2(_e7,_LP,_LN);});});};return new F(function(){return A1(_LD,_LG);});};return E(_LE);},_LQ=function(_LR,_LS,_LT){var _LU=function(_Kz){return new F(function(){return _Ly(_LR,_LS,_Kz);});},_LV=function(_LW,_LX){return new F(function(){return _LY(_LX);});},_LY=function(_LZ){return new F(function(){return _3K(new T1(1,B(_fY(_LU,_LZ))),new T(function(){return new T1(1,B(_fY(_LV,_LZ)));}));});};return new F(function(){return _LY(_LT);});},_M0=function(_M1,_M2){return new F(function(){return _LQ(_Lu,_Lj,_M2);});},_M3=new T(function(){return B(_KB(_M0,_4X));}),_M4=function(_Ll){return new F(function(){return _3A(_M3,_Ll);});},_M5=new T(function(){return B(_LQ(_Lu,_Lj,_4X));}),_M6=function(_Ll){return new F(function(){return _3A(_M5,_Ll);});},_M7=function(_M8,_Ll){return new F(function(){return _M6(_Ll);});},_M9=function(_Ma,_Mb){return new F(function(){return _KB(_M0,_Mb);});},_Mc=new T4(0,_M7,_M4,_M0,_M9),_Md=function(_Me,_Mf){return new F(function(){return _LQ(_Mc,_Lj,_Mf);});},_Mg=function(_Mh,_Mi){return new F(function(){return _KB(_Md,_Mi);});},_Mj=new T(function(){return B(_KB(_Mg,_4X));}),_Mk=function(_Ml){return new F(function(){return _3A(_Mj,_Ml);});},_Mm=function(_Mn){return new F(function(){return _KB(_Mg,_Mn);});},_Mo=function(_Mp,_Mq){return new F(function(){return _Mm(_Mq);});},_Mr=new T(function(){return B(_KB(_Md,_4X));}),_Ms=function(_Ml){return new F(function(){return _3A(_Mr,_Ml);});},_Mt=function(_Mu,_Ml){return new F(function(){return _Ms(_Ml);});},_Mv=new T4(0,_Mt,_Mk,_Mg,_Mo),_Mw=function(_Ll){return new F(function(){return _gh(_hs,_Ll);});},_Mx=function(_My,_Mz){return new F(function(){return _KB(_Mw,_Mz);});},_MA=new T(function(){return B(_KB(_Mw,_4X));}),_MB=function(_Ll){return new F(function(){return _3A(_MA,_Ll);});},_MC=function(_MD){var _ME=new T(function(){return B(A3(_gh,_hs,_MD,_4X));});return function(_Li){return new F(function(){return _3A(_ME,_Li);});};},_MF=new T4(0,_MC,_MB,_Mw,_Mx),_MG=function(_MH,_MI){return new F(function(){return _LQ(_MF,_Lj,_MI);});},_MJ=new T(function(){return B(_KB(_MG,_4X));}),_MK=function(_Ll){return new F(function(){return _3A(_MJ,_Ll);});},_ML=new T(function(){return B(_LQ(_MF,_Lj,_4X));}),_MM=function(_Ll){return new F(function(){return _3A(_ML,_Ll);});},_MN=function(_MO,_Ll){return new F(function(){return _MM(_Ll);});},_MP=function(_MQ,_MR){return new F(function(){return _KB(_MG,_MR);});},_MS=new T4(0,_MN,_MK,_MG,_MP),_MT=function(_MU,_MV){return new F(function(){return _LQ(_MS,_Lj,_MV);});},_MW=function(_MX,_MY){return new F(function(){return _KB(_MT,_MY);});},_MZ=new T(function(){return B(_KB(_MW,_4X));}),_N0=function(_Ml){return new F(function(){return _3A(_MZ,_Ml);});},_N1=function(_N2){return new F(function(){return _KB(_MW,_N2);});},_N3=function(_N4,_N5){return new F(function(){return _N1(_N5);});},_N6=new T(function(){return B(_KB(_MT,_4X));}),_N7=function(_Ml){return new F(function(){return _3A(_N6,_Ml);});},_N8=function(_N9,_Ml){return new F(function(){return _N7(_Ml);});},_Na=new T4(0,_N8,_N0,_MW,_N3),_Nb=new T(function(){return B(unCStr("RC"));}),_Nc=function(_Nd,_Ne){if(_Nd>10){return new T0(2);}else{var _Nf=new T(function(){var _Ng=new T(function(){var _Nh=function(_Ni){var _Nj=function(_Nk){return new F(function(){return A3(_gs,_gV,_4m,function(_Nl){return new F(function(){return A1(_Ne,new T3(0,_Ni,_Nk,_Nl));});});});};return new F(function(){return A3(_gs,_gV,_4m,_Nj);});};return B(A3(_gh,_hd,_4m,_Nh));});return B(_fq(function(_Nm){var _Nn=E(_Nm);return (_Nn._==3)?(!B(_4q(_Nn.a,_Nb)))?new T0(2):E(_Ng):new T0(2);}));}),_No=function(_Np){return E(_Nf);};return new T1(1,function(_Nq){return new F(function(){return A2(_e7,_Nq,_No);});});}},_Nr=function(_Ns,_Nt){return new F(function(){return _Nc(E(_Ns),_Nt);});},_Nu=function(_Ll){return new F(function(){return _gh(_Nr,_Ll);});},_Nv=function(_Nw,_Nx){return new F(function(){return _KB(_Nu,_Nx);});},_Ny=new T(function(){return B(_KB(_Nv,_4X));}),_Nz=function(_Ml){return new F(function(){return _3A(_Ny,_Ml);});},_NA=new T(function(){return B(_KB(_Nu,_4X));}),_NB=function(_Ml){return new F(function(){return _3A(_NA,_Ml);});},_NC=function(_ND,_Ml){return new F(function(){return _NB(_Ml);});},_NE=function(_NF,_NG){return new F(function(){return _KB(_Nv,_NG);});},_NH=new T4(0,_NC,_Nz,_Nv,_NE),_NI=new T(function(){return B(unCStr("CC"));}),_NJ=function(_NK,_NL){if(_NK>10){return new T0(2);}else{var _NM=new T(function(){var _NN=new T(function(){var _NO=function(_NP){var _NQ=function(_NR){var _NS=function(_NT){return new F(function(){return A3(_gs,_gV,_4m,function(_NU){return new F(function(){return A1(_NL,new T4(0,_NP,_NR,_NT,_NU));});});});};return new F(function(){return A3(_gs,_gV,_4m,_NS);});};return new F(function(){return A3(_gs,_gV,_4m,_NQ);});};return B(A3(_gh,_hd,_4m,_NO));});return B(_fq(function(_NV){var _NW=E(_NV);return (_NW._==3)?(!B(_4q(_NW.a,_NI)))?new T0(2):E(_NN):new T0(2);}));}),_NX=function(_NY){return E(_NM);};return new T1(1,function(_NZ){return new F(function(){return A2(_e7,_NZ,_NX);});});}},_O0=function(_O1,_O2){return new F(function(){return _NJ(E(_O1),_O2);});},_O3=function(_Ll){return new F(function(){return _gh(_O0,_Ll);});},_O4=function(_O5,_O6){return new F(function(){return _KB(_O3,_O6);});},_O7=new T(function(){return B(_KB(_O4,_4X));}),_O8=function(_Ml){return new F(function(){return _3A(_O7,_Ml);});},_O9=new T(function(){return B(_KB(_O3,_4X));}),_Oa=function(_Ml){return new F(function(){return _3A(_O9,_Ml);});},_Ob=function(_Oc,_Ml){return new F(function(){return _Oa(_Ml);});},_Od=function(_Oe,_Of){return new F(function(){return _KB(_O4,_Of);});},_Og=new T4(0,_Ob,_O8,_O4,_Od),_Oh=function(_Oi,_Oj,_Ok,_Ol,_Om){var _On=new T(function(){return B(_Ly(_Oi,_Oj,_Om));}),_Oo=new T(function(){return B(_Lw(_Ol));}),_Op=function(_Oq){var _Or=function(_Os){var _Ot=E(_Os),_Ou=new T(function(){var _Ov=new T(function(){var _Ow=function(_Ox){var _Oy=new T(function(){var _Oz=new T(function(){return B(A2(_Oo,_Om,function(_OA){return new F(function(){return A1(_Oq,new T4(0,_Ot.a,_Ot.b,_Ox,_OA));});}));});return B(_fq(function(_OB){var _OC=E(_OB);return (_OC._==2)?(!B(_4q(_OC.a,_Lv)))?new T0(2):E(_Oz):new T0(2);}));}),_OD=function(_OE){return E(_Oy);};return new T1(1,function(_OF){return new F(function(){return A2(_e7,_OF,_OD);});});};return B(A3(_Lw,_Ok,_Om,_Ow));});return B(_fq(function(_OG){var _OH=E(_OG);return (_OH._==2)?(!B(_4q(_OH.a,_Lv)))?new T0(2):E(_Ov):new T0(2);}));}),_OI=function(_OJ){return E(_Ou);};return new T1(1,function(_OK){return new F(function(){return A2(_e7,_OK,_OI);});});};return new F(function(){return A1(_On,_Or);});};return E(_Op);},_OL=function(_OM,_ON,_OO,_OP,_OQ){var _OR=function(_Kz){return new F(function(){return _Oh(_OM,_ON,_OO,_OP,_Kz);});},_OS=function(_OT,_OU){return new F(function(){return _OV(_OU);});},_OV=function(_OW){return new F(function(){return _3K(new T1(1,B(_fY(_OR,_OW))),new T(function(){return new T1(1,B(_fY(_OS,_OW)));}));});};return new F(function(){return _OV(_OQ);});},_OX=new T(function(){return B(_OL(_Og,_NH,_Na,_Mv,_lR));}),_OY=new T(function(){return B(unCStr("contractInput"));}),_OZ=function(_P0,_P1,_P2,_){var _P3=E(_OY),_P4=eval(E(_rq)),_P5=__app1(E(_P4),toJSStr(_P3)),_P6=B(_lY(B(_3A(_OX,new T(function(){var _P7=String(_P5);return fromJSStr(_P7);})))));if(!_P6._){return E(_Kx);}else{if(!E(_P6.b)._){var _P8=E(_P6.a),_P9=B(_Ki(new T(function(){return B(_va(_P8.a));},1),new T(function(){return B(_zx(_P8.b));},1),new T(function(){return B(_In(_P8.c));},1),new T(function(){return B(_DJ(_P2,_P0,_P1,B(_Fd(_P8.d))));},1)));return new F(function(){return _27(_P3,new T2(1,_P9.a,_P9.b),_);});}else{return E(_Kw);}}},_Pa=function(_Pb,_Pc,_Pd,_){var _Pe=E(_OY),_Pf=eval(E(_rq)),_Pg=__app1(E(_Pf),toJSStr(_Pe)),_Ph=B(_lY(B(_3A(_OX,new T(function(){var _Pi=String(_Pg);return fromJSStr(_Pi);})))));if(!_Ph._){return E(_Kx);}else{if(!E(_Ph.b)._){var _Pj=E(_Ph.a),_Pk=B(_Ki(new T(function(){return B(_va(_Pj.a));},1),new T(function(){return B(_zx(_Pj.b));},1),new T(function(){return B(_GT(_Pd,_Pb,_Pc,B(_In(_Pj.c))));},1),new T(function(){return B(_Fd(_Pj.d));},1)));return new F(function(){return _27(_Pe,new T2(1,_Pk.a,_Pk.b),_);});}else{return E(_Kw);}}},_Pl=new T(function(){return B(unCStr("contractOutput"));}),_Pm=new T(function(){return B(unCStr("([], [], [], [])"));}),_Pn=new T(function(){return B(unCStr("([], [])"));}),_Po=new T(function(){return B(unCStr("contractState"));}),_Pp=new T(function(){return B(_c(0,0,_21));}),_Pq=new T(function(){return B(unCStr("currBlock"));}),_Pr=function(_){var _Ps=__app0(E(_rh)),_Pt=B(_27(_24,_21,_)),_Pu=B(_27(_Pq,_Pp,_)),_Pv=B(_27(_Po,_Pn,_)),_Pw=B(_27(_OY,_Pm,_));return new F(function(){return _27(_Pl,_21,_);});},_Px=function(_Py,_Pz,_PA,_PB,_){var _PC=E(_OY),_PD=eval(E(_rq)),_PE=__app1(E(_PD),toJSStr(_PC)),_PF=B(_lY(B(_3A(_OX,new T(function(){var _PG=String(_PE);return fromJSStr(_PG);})))));if(!_PF._){return E(_Kx);}else{if(!E(_PF.b)._){var _PH=E(_PF.a),_PI=B(_Ki(new T(function(){return B(_sM(_PA,_Py,_Pz,_PB,B(_va(_PH.a))));},1),new T(function(){return B(_zx(_PH.b));},1),new T(function(){return B(_In(_PH.c));},1),new T(function(){return B(_Fd(_PH.d));},1)));return new F(function(){return _27(_PC,new T2(1,_PI.a,_PI.b),_);});}else{return E(_Kw);}}},_PJ=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_PK=new T(function(){return B(unCStr("NotRedeemed "));}),_PL=function(_PM,_PN,_PO){var _PP=E(_PN);if(!_PP._){var _PQ=function(_PR){return new F(function(){return _c(11,E(_PP.a),new T2(1,_v,new T(function(){return B(_c(11,E(_PP.b),_PR));})));});};if(E(_PM)<11){return new F(function(){return _2(_PK,new T(function(){return B(_PQ(_PO));},1));});}else{var _PS=new T(function(){return B(_2(_PK,new T(function(){return B(_PQ(new T2(1,_a,_PO)));},1)));});return new T2(1,_b,_PS);}}else{return new F(function(){return _2(_PJ,_PO);});}},_PT=0,_PU=function(_PV,_PW,_PX){var _PY=new T(function(){var _PZ=function(_Q0){var _Q1=E(_PW),_Q2=new T(function(){return B(A3(_Jq,_IK,new T2(1,function(_Q3){return new F(function(){return _c(0,E(_Q1.a),_Q3);});},new T2(1,function(_Ml){return new F(function(){return _PL(_PT,_Q1.b,_Ml);});},_21)),new T2(1,_a,_Q0)));});return new T2(1,_b,_Q2);};return B(A3(_Jq,_IK,new T2(1,function(_Q4){return new F(function(){return _n(0,_PV,_Q4);});},new T2(1,_PZ,_21)),new T2(1,_a,_PX)));});return new T2(0,_b,_PY);},_Q5=function(_Q6,_Q7){var _Q8=E(_Q6),_Q9=B(_PU(_Q8.a,_Q8.b,_Q7));return new T2(1,_Q9.a,_Q9.b);},_Qa=function(_Qb,_Qc){return new F(function(){return _2J(_Q5,_Qb,_Qc);});},_Qd=function(_Qe,_Qf,_Qg,_Qh){var _Qi=E(_Qe);if(_Qi==1){var _Qj=E(_Qh);if(!_Qj._){return new T3(0,new T(function(){var _Qk=E(_Qf);return new T5(0,1,E(_Qk),_Qg,E(_zM),E(_zM));}),_21,_21);}else{var _Ql=E(_Qf);return (_Ql<E(E(_Qj.a).a))?new T3(0,new T5(0,1,E(_Ql),_Qg,E(_zM),E(_zM)),_Qj,_21):new T3(0,new T5(0,1,E(_Ql),_Qg,E(_zM),E(_zM)),_21,_Qj);}}else{var _Qm=B(_Qd(_Qi>>1,_Qf,_Qg,_Qh)),_Qn=_Qm.a,_Qo=_Qm.c,_Qp=E(_Qm.b);if(!_Qp._){return new T3(0,_Qn,_21,_Qo);}else{var _Qq=E(_Qp.a),_Qr=_Qq.a,_Qs=_Qq.b,_Qt=E(_Qp.b);if(!_Qt._){return new T3(0,new T(function(){return B(_Az(_Qr,_Qs,_Qn));}),_21,_Qo);}else{var _Qu=E(_Qt.a),_Qv=E(_Qr),_Qw=E(_Qu.a);if(_Qv<_Qw){var _Qx=B(_Qd(_Qi>>1,_Qw,_Qu.b,_Qt.b));return new T3(0,new T(function(){return B(_C2(_Qv,_Qs,_Qn,_Qx.a));}),_Qx.b,_Qx.c);}else{return new T3(0,_Qn,_21,_Qp);}}}}},_Qy=function(_Qz,_QA,_QB){var _QC=E(_QB);if(!_QC._){var _QD=_QC.c,_QE=_QC.d,_QF=_QC.e,_QG=E(_QC.b);if(_Qz>=_QG){if(_Qz!=_QG){return new F(function(){return _zR(_QG,_QD,_QE,B(_Qy(_Qz,_QA,_QF)));});}else{return new T5(0,_QC.a,E(_Qz),_QA,E(_QE),E(_QF));}}else{return new F(function(){return _AI(_QG,_QD,B(_Qy(_Qz,_QA,_QE)),_QF);});}}else{return new T5(0,1,E(_Qz),_QA,E(_zM),E(_zM));}},_QH=function(_QI,_QJ){while(1){var _QK=E(_QJ);if(!_QK._){return E(_QI);}else{var _QL=E(_QK.a),_QM=B(_Qy(E(_QL.a),_QL.b,_QI));_QI=_QM;_QJ=_QK.b;continue;}}},_QN=function(_QO,_QP,_QQ,_QR){return new F(function(){return _QH(B(_Qy(E(_QP),_QQ,_QO)),_QR);});},_QS=function(_QT,_QU,_QV){var _QW=E(_QU);return new F(function(){return _QH(B(_Qy(E(_QW.a),_QW.b,_QT)),_QV);});},_QX=function(_QY,_QZ,_R0){while(1){var _R1=E(_R0);if(!_R1._){return E(_QZ);}else{var _R2=E(_R1.a),_R3=_R2.a,_R4=_R2.b,_R5=E(_R1.b);if(!_R5._){return new F(function(){return _Az(_R3,_R4,_QZ);});}else{var _R6=E(_R5.a),_R7=E(_R3),_R8=E(_R6.a);if(_R7<_R8){var _R9=B(_Qd(_QY,_R8,_R6.b,_R5.b)),_Ra=_R9.a,_Rb=E(_R9.c);if(!_Rb._){var _Rc=_QY<<1,_Rd=B(_C2(_R7,_R4,_QZ,_Ra));_QY=_Rc;_QZ=_Rd;_R0=_R9.b;continue;}else{return new F(function(){return _QS(B(_C2(_R7,_R4,_QZ,_Ra)),_Rb.a,_Rb.b);});}}else{return new F(function(){return _QN(_QZ,_R7,_R4,_R5);});}}}}},_Re=function(_Rf,_Rg,_Rh,_Ri,_Rj){var _Rk=E(_Rj);if(!_Rk._){return new F(function(){return _Az(_Rh,_Ri,_Rg);});}else{var _Rl=E(_Rk.a),_Rm=E(_Rh),_Rn=E(_Rl.a);if(_Rm<_Rn){var _Ro=B(_Qd(_Rf,_Rn,_Rl.b,_Rk.b)),_Rp=_Ro.a,_Rq=E(_Ro.c);if(!_Rq._){return new F(function(){return _QX(_Rf<<1,B(_C2(_Rm,_Ri,_Rg,_Rp)),_Ro.b);});}else{return new F(function(){return _QS(B(_C2(_Rm,_Ri,_Rg,_Rp)),_Rq.a,_Rq.b);});}}else{return new F(function(){return _QN(_Rg,_Rm,_Ri,_Rk);});}}},_Rr=function(_Rs){var _Rt=E(_Rs);if(!_Rt._){return new T0(1);}else{var _Ru=E(_Rt.a),_Rv=_Ru.a,_Rw=_Ru.b,_Rx=E(_Rt.b);if(!_Rx._){var _Ry=E(_Rv);return new T5(0,1,E(_Ry),_Rw,E(_zM),E(_zM));}else{var _Rz=_Rx.b,_RA=E(_Rx.a),_RB=_RA.b,_RC=E(_Rv),_RD=E(_RA.a);if(_RC<_RD){return new F(function(){return _Re(1,new T5(0,1,E(_RC),_Rw,E(_zM),E(_zM)),_RD,_RB,_Rz);});}else{return new F(function(){return _QN(new T5(0,1,E(_RC),_Rw,E(_zM),E(_zM)),_RD,_RB,_Rz);});}}}},_RE=new T(function(){return B(unCStr("ChoiceMade "));}),_RF=new T(function(){return B(unCStr("DuplicateRedeem "));}),_RG=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_RH=new T(function(){return B(unCStr("CommitRedeemed "));}),_RI=new T(function(){return B(unCStr("SuccessfulCommit "));}),_RJ=new T(function(){return B(unCStr("FailedPay "));}),_RK=new T(function(){return B(unCStr("ExpiredPay "));}),_RL=new T(function(){return B(unCStr("SuccessfulPay "));}),_RM=function(_RN,_RO,_RP){var _RQ=E(_RO);switch(_RQ._){case 0:var _RR=function(_RS){var _RT=new T(function(){var _RU=new T(function(){return B(_c(11,E(_RQ.c),new T2(1,_v,new T(function(){return B(_c(11,E(_RQ.d),_RS));}))));});return B(_c(11,E(_RQ.b),new T2(1,_v,_RU)));});return new F(function(){return _1h(11,_RQ.a,new T2(1,_v,_RT));});};if(_RN<11){return new F(function(){return _2(_RL,new T(function(){return B(_RR(_RP));},1));});}else{var _RV=new T(function(){return B(_2(_RL,new T(function(){return B(_RR(new T2(1,_a,_RP)));},1)));});return new T2(1,_b,_RV);}break;case 1:var _RW=function(_RX){var _RY=new T(function(){var _RZ=new T(function(){return B(_c(11,E(_RQ.c),new T2(1,_v,new T(function(){return B(_c(11,E(_RQ.d),_RX));}))));});return B(_c(11,E(_RQ.b),new T2(1,_v,_RZ)));});return new F(function(){return _1h(11,_RQ.a,new T2(1,_v,_RY));});};if(_RN<11){return new F(function(){return _2(_RK,new T(function(){return B(_RW(_RP));},1));});}else{var _S0=new T(function(){return B(_2(_RK,new T(function(){return B(_RW(new T2(1,_a,_RP)));},1)));});return new T2(1,_b,_S0);}break;case 2:var _S1=function(_S2){var _S3=new T(function(){var _S4=new T(function(){return B(_c(11,E(_RQ.c),new T2(1,_v,new T(function(){return B(_c(11,E(_RQ.d),_S2));}))));});return B(_c(11,E(_RQ.b),new T2(1,_v,_S4)));});return new F(function(){return _1h(11,_RQ.a,new T2(1,_v,_S3));});};if(_RN<11){return new F(function(){return _2(_RJ,new T(function(){return B(_S1(_RP));},1));});}else{var _S5=new T(function(){return B(_2(_RJ,new T(function(){return B(_S1(new T2(1,_a,_RP)));},1)));});return new T2(1,_b,_S5);}break;case 3:var _S6=function(_S7){var _S8=new T(function(){var _S9=new T(function(){return B(_c(11,E(_RQ.b),new T2(1,_v,new T(function(){return B(_c(11,E(_RQ.c),_S7));}))));});return B(_n(11,_RQ.a,new T2(1,_v,_S9)));},1);return new F(function(){return _2(_RI,_S8);});};if(_RN<11){return new F(function(){return _S6(_RP);});}else{return new T2(1,_b,new T(function(){return B(_S6(new T2(1,_a,_RP)));}));}break;case 4:var _Sa=function(_Sb){var _Sc=new T(function(){var _Sd=new T(function(){return B(_c(11,E(_RQ.b),new T2(1,_v,new T(function(){return B(_c(11,E(_RQ.c),_Sb));}))));});return B(_n(11,_RQ.a,new T2(1,_v,_Sd)));},1);return new F(function(){return _2(_RH,_Sc);});};if(_RN<11){return new F(function(){return _Sa(_RP);});}else{return new T2(1,_b,new T(function(){return B(_Sa(new T2(1,_a,_RP)));}));}break;case 5:var _Se=function(_Sf){var _Sg=new T(function(){var _Sh=new T(function(){return B(_c(11,E(_RQ.b),new T2(1,_v,new T(function(){return B(_c(11,E(_RQ.c),_Sf));}))));});return B(_n(11,_RQ.a,new T2(1,_v,_Sh)));},1);return new F(function(){return _2(_RG,_Sg);});};if(_RN<11){return new F(function(){return _Se(_RP);});}else{return new T2(1,_b,new T(function(){return B(_Se(new T2(1,_a,_RP)));}));}break;case 6:var _Si=function(_Sj){return new F(function(){return _n(11,_RQ.a,new T2(1,_v,new T(function(){return B(_c(11,E(_RQ.b),_Sj));})));});};if(_RN<11){return new F(function(){return _2(_RF,new T(function(){return B(_Si(_RP));},1));});}else{var _Sk=new T(function(){return B(_2(_RF,new T(function(){return B(_Si(new T2(1,_a,_RP)));},1)));});return new T2(1,_b,_Sk);}break;default:var _Sl=function(_Sm){var _Sn=new T(function(){var _So=new T(function(){return B(_c(11,E(_RQ.b),new T2(1,_v,new T(function(){return B(_c(11,E(_RQ.c),_Sm));}))));});return B(_h(11,_RQ.a,new T2(1,_v,_So)));},1);return new F(function(){return _2(_RE,_Sn);});};if(_RN<11){return new F(function(){return _Sl(_RP);});}else{return new T2(1,_b,new T(function(){return B(_Sl(new T2(1,_a,_RP)));}));}}},_Sp=function(_Sq,_Sr){return E(_Sq)==E(_Sr);},_Ss=function(_St,_Su){var _Sv=E(_St);switch(_Sv._){case 0:var _Sw=E(_Su);if(!_Sw._){if(E(_Sv.a)!=E(_Sw.a)){return false;}else{if(E(_Sv.b)!=E(_Sw.b)){return false;}else{if(E(_Sv.c)!=E(_Sw.c)){return false;}else{return new F(function(){return _Sp(_Sv.d,_Sw.d);});}}}}else{return false;}break;case 1:var _Sx=E(_Su);if(_Sx._==1){if(E(_Sv.a)!=E(_Sx.a)){return false;}else{if(E(_Sv.b)!=E(_Sx.b)){return false;}else{if(E(_Sv.c)!=E(_Sx.c)){return false;}else{return new F(function(){return _Sp(_Sv.d,_Sx.d);});}}}}else{return false;}break;case 2:var _Sy=E(_Su);if(_Sy._==2){if(E(_Sv.a)!=E(_Sy.a)){return false;}else{if(E(_Sv.b)!=E(_Sy.b)){return false;}else{if(E(_Sv.c)!=E(_Sy.c)){return false;}else{return new F(function(){return _Sp(_Sv.d,_Sy.d);});}}}}else{return false;}break;case 3:var _Sz=E(_Su);if(_Sz._==3){if(E(_Sv.a)!=E(_Sz.a)){return false;}else{if(E(_Sv.b)!=E(_Sz.b)){return false;}else{return new F(function(){return _Sp(_Sv.c,_Sz.c);});}}}else{return false;}break;case 4:var _SA=E(_Su);if(_SA._==4){if(E(_Sv.a)!=E(_SA.a)){return false;}else{if(E(_Sv.b)!=E(_SA.b)){return false;}else{return new F(function(){return _Sp(_Sv.c,_SA.c);});}}}else{return false;}break;case 5:var _SB=E(_Su);if(_SB._==5){if(E(_Sv.a)!=E(_SB.a)){return false;}else{if(E(_Sv.b)!=E(_SB.b)){return false;}else{return new F(function(){return _Sp(_Sv.c,_SB.c);});}}}else{return false;}break;case 6:var _SC=E(_Su);if(_SC._==6){if(E(_Sv.a)!=E(_SC.a)){return false;}else{return new F(function(){return _Sp(_Sv.b,_SC.b);});}}else{return false;}break;default:var _SD=E(_Su);if(_SD._==7){if(E(_Sv.a)!=E(_SD.a)){return false;}else{if(E(_Sv.b)!=E(_SD.b)){return false;}else{return new F(function(){return _Sp(_Sv.c,_SD.c);});}}}else{return false;}}},_SE=function(_SF,_SG){return (!B(_Ss(_SF,_SG)))?true:false;},_SH=new T2(0,_Ss,_SE),_SI=function(_SJ,_SK){while(1){var _SL=E(_SJ);switch(_SL._){case 0:var _SM=E(_SK);if(!_SM._){return new F(function(){return _Sp(_SL.a,_SM.a);});}else{return false;}break;case 1:var _SN=E(_SK);if(_SN._==1){if(!B(_SI(_SL.a,_SN.a))){return false;}else{_SJ=_SL.b;_SK=_SN.b;continue;}}else{return false;}break;default:var _SO=E(_SK);if(_SO._==2){return new F(function(){return _Sp(_SL.a,_SO.a);});}else{return false;}}}},_SP=function(_SQ,_SR){while(1){var _SS=E(_SQ);switch(_SS._){case 0:var _ST=E(_SR);if(!_ST._){return new F(function(){return _Sp(_SS.a,_ST.a);});}else{return false;}break;case 1:var _SU=E(_SR);if(_SU._==1){if(!B(_SP(_SS.a,_SU.a))){return false;}else{_SQ=_SS.b;_SR=_SU.b;continue;}}else{return false;}break;case 2:var _SV=E(_SR);if(_SV._==2){if(!B(_SP(_SS.a,_SV.a))){return false;}else{_SQ=_SS.b;_SR=_SV.b;continue;}}else{return false;}break;case 3:var _SW=E(_SR);if(_SW._==3){_SQ=_SS.a;_SR=_SW.a;continue;}else{return false;}break;case 4:var _SX=E(_SR);if(_SX._==4){if(E(_SS.a)!=E(_SX.a)){return false;}else{if(E(_SS.b)!=E(_SX.b)){return false;}else{return new F(function(){return _Sp(_SS.c,_SX.c);});}}}else{return false;}break;case 5:var _SY=E(_SR);if(_SY._==5){if(E(_SS.a)!=E(_SY.a)){return false;}else{return new F(function(){return _Sp(_SS.b,_SY.b);});}}else{return false;}break;case 6:var _SZ=E(_SR);if(_SZ._==6){if(!B(_SI(_SS.a,_SZ.a))){return false;}else{return new F(function(){return _SI(_SS.b,_SZ.b);});}}else{return false;}break;case 7:return (E(_SR)._==7)?true:false;default:return (E(_SR)._==8)?true:false;}}},_T0=function(_T1,_T2){while(1){var _T3=E(_T1);switch(_T3._){case 0:return (E(_T2)._==0)?true:false;case 1:var _T4=E(_T2);if(_T4._==1){if(E(_T3.a)!=E(_T4.a)){return false;}else{_T1=_T3.b;_T2=_T4.b;continue;}}else{return false;}break;case 2:var _T5=E(_T2);if(_T5._==2){if(E(_T3.a)!=E(_T5.a)){return false;}else{if(E(_T3.b)!=E(_T5.b)){return false;}else{if(E(_T3.c)!=E(_T5.c)){return false;}else{if(E(_T3.d)!=E(_T5.d)){return false;}else{if(E(_T3.e)!=E(_T5.e)){return false;}else{_T1=_T3.f;_T2=_T5.f;continue;}}}}}}else{return false;}break;case 3:var _T6=E(_T2);if(_T6._==3){if(!B(_T0(_T3.a,_T6.a))){return false;}else{_T1=_T3.b;_T2=_T6.b;continue;}}else{return false;}break;case 4:var _T7=E(_T2);if(_T7._==4){if(!B(_SP(_T3.a,_T7.a))){return false;}else{if(!B(_T0(_T3.b,_T7.b))){return false;}else{_T1=_T3.c;_T2=_T7.c;continue;}}}else{return false;}break;case 5:var _T8=E(_T2);if(_T8._==5){if(E(_T3.a)!=E(_T8.a)){return false;}else{if(E(_T3.b)!=E(_T8.b)){return false;}else{if(E(_T3.c)!=E(_T8.c)){return false;}else{if(E(_T3.d)!=E(_T8.d)){return false;}else{if(E(_T3.e)!=E(_T8.e)){return false;}else{_T1=_T3.f;_T2=_T8.f;continue;}}}}}}else{return false;}break;default:var _T9=E(_T2);if(_T9._==6){if(!B(_SP(_T3.a,_T9.a))){return false;}else{if(E(_T3.b)!=E(_T9.b)){return false;}else{if(!B(_T0(_T3.c,_T9.c))){return false;}else{_T1=_T3.d;_T2=_T9.d;continue;}}}}else{return false;}}}},_Ta=function(_Tb,_Tc,_Td,_Te){if(_Tb!=_Td){return false;}else{return new F(function(){return _Sp(_Tc,_Te);});}},_Tf=function(_Tg,_Th){var _Ti=E(_Tg),_Tj=E(_Th);return new F(function(){return _Ta(E(_Ti.a),_Ti.b,E(_Tj.a),_Tj.b);});},_Tk=function(_Tl,_Tm,_Tn,_To){return (_Tl!=_Tn)?true:(E(_Tm)!=E(_To))?true:false;},_Tp=function(_Tq,_Tr){var _Ts=E(_Tq),_Tt=E(_Tr);return new F(function(){return _Tk(E(_Ts.a),_Ts.b,E(_Tt.a),_Tt.b);});},_Tu=new T2(0,_Tf,_Tp),_Tv=function(_Tw,_Tx){return E(_Tw)!=E(_Tx);},_Ty=new T2(0,_Sp,_Tv),_Tz=function(_TA,_TB,_TC,_TD,_TE,_TF){return (!B(A3(_8r,_TA,_TC,_TE)))?true:(!B(A3(_8r,_TB,_TD,_TF)))?true:false;},_TG=function(_TH,_TI,_TJ,_TK){var _TL=E(_TJ),_TM=E(_TK);return new F(function(){return _Tz(_TH,_TI,_TL.a,_TL.b,_TM.a,_TM.b);});},_TN=function(_TO,_TP,_TQ,_TR,_TS,_TT){if(!B(A3(_8r,_TO,_TQ,_TS))){return false;}else{return new F(function(){return A3(_8r,_TP,_TR,_TT);});}},_TU=function(_TV,_TW,_TX,_TY){var _TZ=E(_TX),_U0=E(_TY);return new F(function(){return _TN(_TV,_TW,_TZ.a,_TZ.b,_U0.a,_U0.b);});},_U1=function(_U2,_U3){return new T2(0,function(_U4,_U5){return new F(function(){return _TU(_U2,_U3,_U4,_U5);});},function(_U4,_U5){return new F(function(){return _TG(_U2,_U3,_U4,_U5);});});},_U6=function(_U7,_U8,_U9){while(1){var _Ua=E(_U8);if(!_Ua._){return (E(_U9)._==0)?true:false;}else{var _Ub=E(_U9);if(!_Ub._){return false;}else{if(!B(A3(_8r,_U7,_Ua.a,_Ub.a))){return false;}else{_U8=_Ua.b;_U9=_Ub.b;continue;}}}}},_Uc=function(_Ud,_Ue){var _Uf=new T(function(){return B(_U1(_Ud,_Ue));}),_Ug=function(_Uh,_Ui){var _Uj=function(_Uk){var _Ul=function(_Um){if(_Uk!=_Um){return false;}else{return new F(function(){return _U6(_Uf,B(_ID(_21,_Uh)),B(_ID(_21,_Ui)));});}},_Un=E(_Ui);if(!_Un._){return new F(function(){return _Ul(_Un.a);});}else{return new F(function(){return _Ul(0);});}},_Uo=E(_Uh);if(!_Uo._){return new F(function(){return _Uj(_Uo.a);});}else{return new F(function(){return _Uj(0);});}};return E(_Ug);},_Up=new T(function(){return B(_Uc(_Tu,_Ty));}),_Uq=new T2(0,_Sp,_Tv),_Ur=function(_Us,_Ut){var _Uu=E(_Us);if(!_Uu._){var _Uv=E(_Ut);if(!_Uv._){if(E(_Uu.a)!=E(_Uv.a)){return false;}else{return new F(function(){return _Sp(_Uu.b,_Uv.b);});}}else{return false;}}else{return (E(_Ut)._==0)?false:true;}},_Uw=function(_Ux,_Uy,_Uz,_UA){if(_Ux!=_Uz){return false;}else{return new F(function(){return _Ur(_Uy,_UA);});}},_UB=function(_UC,_UD){var _UE=E(_UC),_UF=E(_UD);return new F(function(){return _Uw(E(_UE.a),_UE.b,E(_UF.a),_UF.b);});},_UG=function(_UH,_UI,_UJ,_UK){if(_UH!=_UJ){return true;}else{var _UL=E(_UI);if(!_UL._){var _UM=E(_UK);return (_UM._==0)?(E(_UL.a)!=E(_UM.a))?true:(E(_UL.b)!=E(_UM.b))?true:false:true;}else{return (E(_UK)._==0)?true:false;}}},_UN=function(_UO,_UP){var _UQ=E(_UO),_UR=E(_UP);return new F(function(){return _UG(E(_UQ.a),_UQ.b,E(_UR.a),_UR.b);});},_US=new T2(0,_UB,_UN),_UT=new T(function(){return B(_Uc(_Uq,_US));}),_UU=function(_UV,_UW){var _UX=E(_UV),_UY=E(_UW);return (_UX>_UY)?E(_UX):E(_UY);},_UZ=function(_V0,_V1){var _V2=E(_V0),_V3=E(_V1);return (_V2>_V3)?E(_V3):E(_V2);},_V4=function(_V5,_V6){return (_V5>=_V6)?(_V5!=_V6)?2:1:0;},_V7=function(_V8,_V9){return new F(function(){return _V4(E(_V8),E(_V9));});},_Va=function(_Vb,_Vc){return E(_Vb)>=E(_Vc);},_Vd=function(_Ve,_Vf){return E(_Ve)>E(_Vf);},_Vg=function(_Vh,_Vi){return E(_Vh)<=E(_Vi);},_Vj=function(_Vk,_Vl){return E(_Vk)<E(_Vl);},_Vm={_:0,a:_Uq,b:_V7,c:_Vj,d:_Vg,e:_Vd,f:_Va,g:_UU,h:_UZ},_Vn=function(_Vo,_Vp,_Vq,_Vr,_Vs){while(1){var _Vt=E(_Vs);if(!_Vt._){var _Vu=_Vt.c,_Vv=_Vt.d,_Vw=E(_Vt.b),_Vx=E(_Vw.a);if(_Vo>=_Vx){if(_Vo!=_Vx){_Vp=_;_Vs=_Vv;continue;}else{var _Vy=E(_Vw.b);if(_Vq>=_Vy){if(_Vq!=_Vy){_Vp=_;_Vs=_Vv;continue;}else{var _Vz=E(_Vw.c);if(_Vr>=_Vz){if(_Vr!=_Vz){_Vp=_;_Vs=_Vv;continue;}else{return true;}}else{_Vp=_;_Vs=_Vu;continue;}}}else{_Vp=_;_Vs=_Vu;continue;}}}else{_Vp=_;_Vs=_Vu;continue;}}else{return false;}}},_VA=function(_VB,_VC,_VD,_VE,_VF){while(1){var _VG=E(_VF);if(!_VG._){var _VH=_VG.c,_VI=_VG.d,_VJ=E(_VG.b),_VK=E(_VJ.a);if(_VB>=_VK){if(_VB!=_VK){_VC=_;_VF=_VI;continue;}else{var _VL=E(_VJ.b);if(_VD>=_VL){if(_VD!=_VL){_VC=_;_VF=_VI;continue;}else{var _VM=E(_VE),_VN=E(_VJ.c);if(_VM>=_VN){if(_VM!=_VN){return new F(function(){return _Vn(_VB,_,_VD,_VM,_VI);});}else{return true;}}else{return new F(function(){return _Vn(_VB,_,_VD,_VM,_VH);});}}}else{_VC=_;_VF=_VH;continue;}}}else{_VC=_;_VF=_VH;continue;}}else{return false;}}},_VO=function(_VP,_VQ,_VR,_VS,_VT){while(1){var _VU=E(_VT);if(!_VU._){var _VV=_VU.c,_VW=_VU.d,_VX=E(_VU.b),_VY=E(_VX.a);if(_VP>=_VY){if(_VP!=_VY){_VQ=_;_VT=_VW;continue;}else{var _VZ=E(_VR),_W0=E(_VX.b);if(_VZ>=_W0){if(_VZ!=_W0){return new F(function(){return _VA(_VP,_,_VZ,_VS,_VW);});}else{var _W1=E(_VS),_W2=E(_VX.c);if(_W1>=_W2){if(_W1!=_W2){return new F(function(){return _Vn(_VP,_,_VZ,_W1,_VW);});}else{return true;}}else{return new F(function(){return _Vn(_VP,_,_VZ,_W1,_VV);});}}}else{return new F(function(){return _VA(_VP,_,_VZ,_VS,_VV);});}}}else{_VQ=_;_VT=_VV;continue;}}else{return false;}}},_W3=function(_W4,_W5,_W6,_W7){var _W8=E(_W7);if(!_W8._){var _W9=_W8.c,_Wa=_W8.d,_Wb=E(_W8.b),_Wc=E(_W4),_Wd=E(_Wb.a);if(_Wc>=_Wd){if(_Wc!=_Wd){return new F(function(){return _VO(_Wc,_,_W5,_W6,_Wa);});}else{var _We=E(_W5),_Wf=E(_Wb.b);if(_We>=_Wf){if(_We!=_Wf){return new F(function(){return _VA(_Wc,_,_We,_W6,_Wa);});}else{var _Wg=E(_W6),_Wh=E(_Wb.c);if(_Wg>=_Wh){if(_Wg!=_Wh){return new F(function(){return _Vn(_Wc,_,_We,_Wg,_Wa);});}else{return true;}}else{return new F(function(){return _Vn(_Wc,_,_We,_Wg,_W9);});}}}else{return new F(function(){return _VA(_Wc,_,_We,_W6,_W9);});}}}else{return new F(function(){return _VO(_Wc,_,_W5,_W6,_W9);});}}else{return false;}},_Wi=function(_Wj,_Wk,_Wl,_Wm,_Wn){var _Wo=E(_Wn);if(!_Wo._){if(E(_Wo.b)>E(_Wk)){return false;}else{return new F(function(){return _W3(_Wl,_Wm,_Wo.a,E(_Wj).b);});}}else{return false;}},_Wp=function(_Wq,_Wr,_Ws,_Wt,_Wu){var _Wv=E(_Wu);if(!_Wv._){var _Ww=new T(function(){var _Wx=B(_Wp(_Wv.a,_Wv.b,_Wv.c,_Wv.d,_Wv.e));return new T2(0,_Wx.a,_Wx.b);});return new T2(0,new T(function(){return E(E(_Ww).a);}),new T(function(){return B(_AI(_Wr,_Ws,_Wt,E(_Ww).b));}));}else{return new T2(0,new T2(0,_Wr,_Ws),_Wt);}},_Wy=function(_Wz,_WA,_WB,_WC,_WD){var _WE=E(_WC);if(!_WE._){var _WF=new T(function(){var _WG=B(_Wy(_WE.a,_WE.b,_WE.c,_WE.d,_WE.e));return new T2(0,_WG.a,_WG.b);});return new T2(0,new T(function(){return E(E(_WF).a);}),new T(function(){return B(_zR(_WA,_WB,E(_WF).b,_WD));}));}else{return new T2(0,new T2(0,_WA,_WB),_WD);}},_WH=function(_WI,_WJ){var _WK=E(_WI);if(!_WK._){var _WL=_WK.a,_WM=E(_WJ);if(!_WM._){var _WN=_WM.a;if(_WL<=_WN){var _WO=B(_Wy(_WN,_WM.b,_WM.c,_WM.d,_WM.e)),_WP=E(_WO.a);return new F(function(){return _AI(_WP.a,_WP.b,_WK,_WO.b);});}else{var _WQ=B(_Wp(_WL,_WK.b,_WK.c,_WK.d,_WK.e)),_WR=E(_WQ.a);return new F(function(){return _zR(_WR.a,_WR.b,_WQ.b,_WM);});}}else{return E(_WK);}}else{return E(_WJ);}},_WS=function(_WT,_WU,_WV,_WW,_WX,_WY){var _WZ=E(_WT);if(!_WZ._){var _X0=_WZ.a,_X1=_WZ.b,_X2=_WZ.c,_X3=_WZ.d,_X4=_WZ.e;if((imul(3,_X0)|0)>=_WU){if((imul(3,_WU)|0)>=_X0){return new F(function(){return _WH(_WZ,new T5(0,_WU,E(_WV),_WW,E(_WX),E(_WY)));});}else{return new F(function(){return _zR(_X1,_X2,_X3,B(_WS(_X4,_WU,_WV,_WW,_WX,_WY)));});}}else{return new F(function(){return _AI(_WV,_WW,B(_X5(_X0,_X1,_X2,_X3,_X4,_WX)),_WY);});}}else{return new T5(0,_WU,E(_WV),_WW,E(_WX),E(_WY));}},_X5=function(_X6,_X7,_X8,_X9,_Xa,_Xb){var _Xc=E(_Xb);if(!_Xc._){var _Xd=_Xc.a,_Xe=_Xc.b,_Xf=_Xc.c,_Xg=_Xc.d,_Xh=_Xc.e;if((imul(3,_X6)|0)>=_Xd){if((imul(3,_Xd)|0)>=_X6){return new F(function(){return _WH(new T5(0,_X6,E(_X7),_X8,E(_X9),E(_Xa)),_Xc);});}else{return new F(function(){return _zR(_X7,_X8,_X9,B(_WS(_Xa,_Xd,_Xe,_Xf,_Xg,_Xh)));});}}else{return new F(function(){return _AI(_Xe,_Xf,B(_X5(_X6,_X7,_X8,_X9,_Xa,_Xg)),_Xh);});}}else{return new T5(0,_X6,E(_X7),_X8,E(_X9),E(_Xa));}},_Xi=function(_Xj,_Xk){var _Xl=E(_Xj);if(!_Xl._){var _Xm=_Xl.a,_Xn=_Xl.b,_Xo=_Xl.c,_Xp=_Xl.d,_Xq=_Xl.e,_Xr=E(_Xk);if(!_Xr._){var _Xs=_Xr.a,_Xt=_Xr.b,_Xu=_Xr.c,_Xv=_Xr.d,_Xw=_Xr.e;if((imul(3,_Xm)|0)>=_Xs){if((imul(3,_Xs)|0)>=_Xm){return new F(function(){return _WH(_Xl,_Xr);});}else{return new F(function(){return _zR(_Xn,_Xo,_Xp,B(_WS(_Xq,_Xs,_Xt,_Xu,_Xv,_Xw)));});}}else{return new F(function(){return _AI(_Xt,_Xu,B(_X5(_Xm,_Xn,_Xo,_Xp,_Xq,_Xv)),_Xw);});}}else{return E(_Xl);}}else{return E(_Xk);}},_Xx=function(_Xy,_Xz){var _XA=E(_Xz);if(!_XA._){var _XB=_XA.b,_XC=_XA.c,_XD=B(_Xx(_Xy,_XA.d)),_XE=_XD.a,_XF=_XD.b,_XG=B(_Xx(_Xy,_XA.e)),_XH=_XG.a,_XI=_XG.b;return (!B(A2(_Xy,_XB,_XC)))?new T2(0,B(_Xi(_XE,_XH)),B(_C2(_XB,_XC,_XF,_XI))):new T2(0,B(_C2(_XB,_XC,_XE,_XH)),B(_Xi(_XF,_XI)));}else{return new T2(0,_zM,_zM);}},_XJ=__Z,_XK=function(_XL,_XM){while(1){var _XN=B((function(_XO,_XP){var _XQ=E(_XP);if(!_XQ._){var _XR=_XQ.e,_XS=new T(function(){var _XT=E(_XQ.c),_XU=E(_XT.b);if(!_XU._){return new T2(1,new T3(5,_XQ.b,_XT.a,_XU.a),new T(function(){return B(_XK(_XO,_XR));}));}else{return B(_XK(_XO,_XR));}},1);_XL=_XS;_XM=_XQ.d;return __continue;}else{return E(_XO);}})(_XL,_XM));if(_XN!=__continue){return _XN;}}},_XV=function(_XW,_XX){var _XY=E(_XX);return (_XY._==0)?new T5(0,_XY.a,E(_XY.b),new T(function(){return B(A1(_XW,_XY.c));}),E(B(_XV(_XW,_XY.d))),E(B(_XV(_XW,_XY.e)))):new T0(1);},_XZ=new T0(1),_Y0=function(_Y1){var _Y2=E(_Y1),_Y3=E(_Y2.b);return new T2(0,_Y2.a,_XZ);},_Y4=function(_Y5){return E(E(_Y5).b);},_Y6=function(_Y7,_Y8,_Y9){var _Ya=E(_Y8);if(!_Ya._){return E(_Y9);}else{var _Yb=function(_Yc,_Yd){while(1){var _Ye=E(_Yd);if(!_Ye._){var _Yf=_Ye.b,_Yg=_Ye.e;switch(B(A3(_Y4,_Y7,_Yc,_Yf))){case 0:return new F(function(){return _C2(_Yf,_Ye.c,B(_Yb(_Yc,_Ye.d)),_Yg);});break;case 1:return E(_Yg);default:_Yd=_Yg;continue;}}else{return new T0(1);}}};return new F(function(){return _Yb(_Ya.a,_Y9);});}},_Yh=function(_Yi,_Yj,_Yk){var _Yl=E(_Yj);if(!_Yl._){return E(_Yk);}else{var _Ym=function(_Yn,_Yo){while(1){var _Yp=E(_Yo);if(!_Yp._){var _Yq=_Yp.b,_Yr=_Yp.d;switch(B(A3(_Y4,_Yi,_Yq,_Yn))){case 0:return new F(function(){return _C2(_Yq,_Yp.c,_Yr,B(_Ym(_Yn,_Yp.e)));});break;case 1:return E(_Yr);default:_Yo=_Yr;continue;}}else{return new T0(1);}}};return new F(function(){return _Ym(_Yl.a,_Yk);});}},_Ys=function(_Yt,_Yu,_Yv,_Yw){var _Yx=E(_Yu),_Yy=E(_Yw);if(!_Yy._){var _Yz=_Yy.b,_YA=_Yy.c,_YB=_Yy.d,_YC=_Yy.e;switch(B(A3(_Y4,_Yt,_Yx,_Yz))){case 0:return new F(function(){return _AI(_Yz,_YA,B(_Ys(_Yt,_Yx,_Yv,_YB)),_YC);});break;case 1:return E(_Yy);default:return new F(function(){return _zR(_Yz,_YA,_YB,B(_Ys(_Yt,_Yx,_Yv,_YC)));});}}else{return new T5(0,1,E(_Yx),_Yv,E(_zM),E(_zM));}},_YD=function(_YE,_YF,_YG,_YH){return new F(function(){return _Ys(_YE,_YF,_YG,_YH);});},_YI=function(_YJ){return E(E(_YJ).d);},_YK=function(_YL){return E(E(_YL).f);},_YM=function(_YN,_YO,_YP,_YQ){var _YR=E(_YO);if(!_YR._){var _YS=E(_YP);if(!_YS._){return E(_YQ);}else{var _YT=function(_YU,_YV){while(1){var _YW=E(_YV);if(!_YW._){if(!B(A3(_YK,_YN,_YW.b,_YU))){return E(_YW);}else{_YV=_YW.d;continue;}}else{return new T0(1);}}};return new F(function(){return _YT(_YS.a,_YQ);});}}else{var _YX=_YR.a,_YY=E(_YP);if(!_YY._){var _YZ=function(_Z0,_Z1){while(1){var _Z2=E(_Z1);if(!_Z2._){if(!B(A3(_YI,_YN,_Z2.b,_Z0))){return E(_Z2);}else{_Z1=_Z2.e;continue;}}else{return new T0(1);}}};return new F(function(){return _YZ(_YX,_YQ);});}else{var _Z3=function(_Z4,_Z5,_Z6){while(1){var _Z7=E(_Z6);if(!_Z7._){var _Z8=_Z7.b;if(!B(A3(_YI,_YN,_Z8,_Z4))){if(!B(A3(_YK,_YN,_Z8,_Z5))){return E(_Z7);}else{_Z6=_Z7.d;continue;}}else{_Z6=_Z7.e;continue;}}else{return new T0(1);}}};return new F(function(){return _Z3(_YX,_YY.a,_YQ);});}}},_Z9=function(_Za,_Zb,_Zc,_Zd,_Ze){var _Zf=E(_Ze);if(!_Zf._){var _Zg=_Zf.b,_Zh=_Zf.c,_Zi=_Zf.d,_Zj=_Zf.e,_Zk=E(_Zd);if(!_Zk._){var _Zl=_Zk.b,_Zm=function(_Zn){var _Zo=new T1(1,E(_Zl));return new F(function(){return _C2(_Zl,_Zk.c,B(_Z9(_Za,_Zb,_Zo,_Zk.d,B(_YM(_Za,_Zb,_Zo,_Zf)))),B(_Z9(_Za,_Zo,_Zc,_Zk.e,B(_YM(_Za,_Zo,_Zc,_Zf)))));});};if(!E(_Zi)._){return new F(function(){return _Zm(_);});}else{if(!E(_Zj)._){return new F(function(){return _Zm(_);});}else{return new F(function(){return _YD(_Za,_Zg,_Zh,_Zk);});}}}else{return new F(function(){return _C2(_Zg,_Zh,B(_Y6(_Za,_Zb,_Zi)),B(_Yh(_Za,_Zc,_Zj)));});}}else{return E(_Zd);}},_Zp=function(_Zq,_Zr,_Zs,_Zt,_Zu,_Zv,_Zw,_Zx,_Zy,_Zz,_ZA,_ZB,_ZC){var _ZD=function(_ZE){var _ZF=new T1(1,E(_Zu));return new F(function(){return _C2(_Zu,_Zv,B(_Z9(_Zq,_Zr,_ZF,_Zw,B(_YM(_Zq,_Zr,_ZF,new T5(0,_Zy,E(_Zz),_ZA,E(_ZB),E(_ZC)))))),B(_Z9(_Zq,_ZF,_Zs,_Zx,B(_YM(_Zq,_ZF,_Zs,new T5(0,_Zy,E(_Zz),_ZA,E(_ZB),E(_ZC)))))));});};if(!E(_ZB)._){return new F(function(){return _ZD(_);});}else{if(!E(_ZC)._){return new F(function(){return _ZD(_);});}else{return new F(function(){return _YD(_Zq,_Zz,_ZA,new T5(0,_Zt,E(_Zu),_Zv,E(_Zw),E(_Zx)));});}}},_ZG=function(_ZH,_ZI,_ZJ){var _ZK=new T(function(){var _ZL=new T(function(){return E(E(_ZJ).b);}),_ZM=B(_Xx(function(_ZN,_ZO){var _ZP=E(_ZO);return new F(function(){return _Wi(_ZH,_ZL,_ZN,_ZP.a,_ZP.b);});},_ZI));return new T2(0,_ZM.a,_ZM.b);}),_ZQ=new T(function(){return E(E(_ZK).a);});return new T2(0,new T(function(){var _ZR=B(_XV(_Y0,_ZQ));if(!_ZR._){var _ZS=E(E(_ZK).b);if(!_ZS._){return B(_Zp(_Vm,_XJ,_XJ,_ZR.a,_ZR.b,_ZR.c,_ZR.d,_ZR.e,_ZS.a,_ZS.b,_ZS.c,_ZS.d,_ZS.e));}else{return E(_ZR);}}else{return E(E(_ZK).b);}}),new T(function(){return B(_XK(_21,_ZQ));}));},_ZT=function(_ZU,_ZV,_ZW,_ZX){while(1){var _ZY=E(_ZX);if(!_ZY._){var _ZZ=_ZY.d,_100=_ZY.e,_101=E(_ZY.b),_102=E(_101.a);if(_ZU>=_102){if(_ZU!=_102){_ZV=_;_ZX=_100;continue;}else{var _103=E(_101.b);if(_ZW>=_103){if(_ZW!=_103){_ZV=_;_ZX=_100;continue;}else{return true;}}else{_ZV=_;_ZX=_ZZ;continue;}}}else{_ZV=_;_ZX=_ZZ;continue;}}else{return false;}}},_104=function(_105,_106,_107,_108){while(1){var _109=E(_108);if(!_109._){var _10a=_109.d,_10b=_109.e,_10c=E(_109.b),_10d=E(_10c.a);if(_105>=_10d){if(_105!=_10d){_106=_;_108=_10b;continue;}else{var _10e=E(_107),_10f=E(_10c.b);if(_10e>=_10f){if(_10e!=_10f){return new F(function(){return _ZT(_105,_,_10e,_10b);});}else{return true;}}else{return new F(function(){return _ZT(_105,_,_10e,_10a);});}}}else{_106=_;_108=_10a;continue;}}else{return false;}}},_10g=function(_10h,_10i,_10j,_10k,_10l){var _10m=E(_10l);if(!_10m._){var _10n=_10m.c,_10o=_10m.d,_10p=_10m.e,_10q=E(_10m.b),_10r=E(_10q.a);if(_10h>=_10r){if(_10h!=_10r){return new F(function(){return _zR(_10q,_10n,_10o,B(_10g(_10h,_,_10j,_10k,_10p)));});}else{var _10s=E(_10q.b);if(_10j>=_10s){if(_10j!=_10s){return new F(function(){return _zR(_10q,_10n,_10o,B(_10g(_10h,_,_10j,_10k,_10p)));});}else{return new T5(0,_10m.a,E(new T2(0,_10h,_10j)),_10k,E(_10o),E(_10p));}}else{return new F(function(){return _AI(_10q,_10n,B(_10g(_10h,_,_10j,_10k,_10o)),_10p);});}}}else{return new F(function(){return _AI(_10q,_10n,B(_10g(_10h,_,_10j,_10k,_10o)),_10p);});}}else{return new T5(0,1,E(new T2(0,_10h,_10j)),_10k,E(_zM),E(_zM));}},_10t=function(_10u,_10v,_10w,_10x,_10y){var _10z=E(_10y);if(!_10z._){var _10A=_10z.c,_10B=_10z.d,_10C=_10z.e,_10D=E(_10z.b),_10E=E(_10D.a);if(_10u>=_10E){if(_10u!=_10E){return new F(function(){return _zR(_10D,_10A,_10B,B(_10t(_10u,_,_10w,_10x,_10C)));});}else{var _10F=E(_10w),_10G=E(_10D.b);if(_10F>=_10G){if(_10F!=_10G){return new F(function(){return _zR(_10D,_10A,_10B,B(_10g(_10u,_,_10F,_10x,_10C)));});}else{return new T5(0,_10z.a,E(new T2(0,_10u,_10F)),_10x,E(_10B),E(_10C));}}else{return new F(function(){return _AI(_10D,_10A,B(_10g(_10u,_,_10F,_10x,_10B)),_10C);});}}}else{return new F(function(){return _AI(_10D,_10A,B(_10t(_10u,_,_10w,_10x,_10B)),_10C);});}}else{return new T5(0,1,E(new T2(0,_10u,_10w)),_10x,E(_zM),E(_zM));}},_10H=function(_10I,_10J,_10K,_10L){var _10M=E(_10L);if(!_10M._){var _10N=_10M.c,_10O=_10M.d,_10P=_10M.e,_10Q=E(_10M.b),_10R=E(_10I),_10S=E(_10Q.a);if(_10R>=_10S){if(_10R!=_10S){return new F(function(){return _zR(_10Q,_10N,_10O,B(_10t(_10R,_,_10J,_10K,_10P)));});}else{var _10T=E(_10J),_10U=E(_10Q.b);if(_10T>=_10U){if(_10T!=_10U){return new F(function(){return _zR(_10Q,_10N,_10O,B(_10g(_10R,_,_10T,_10K,_10P)));});}else{return new T5(0,_10M.a,E(new T2(0,_10R,_10T)),_10K,E(_10O),E(_10P));}}else{return new F(function(){return _AI(_10Q,_10N,B(_10g(_10R,_,_10T,_10K,_10O)),_10P);});}}}else{return new F(function(){return _AI(_10Q,_10N,B(_10t(_10R,_,_10J,_10K,_10O)),_10P);});}}else{return new T5(0,1,E(new T2(0,_10I,_10J)),_10K,E(_zM),E(_zM));}},_10V=function(_10W,_10X,_10Y){while(1){var _10Z=B((function(_110,_111,_112){var _113=E(_112);if(!_113._){var _114=_113.c,_115=_113.e,_116=E(_113.b),_117=_116.a,_118=_116.b,_119=B(_10V(_110,_111,_113.d)),_11a=_119.a,_11b=_119.b,_11c=function(_11d){return new F(function(){return _10V(new T(function(){return B(_10H(_117,_118,_114,_11a));}),new T2(1,new T3(7,_117,_118,_114),_11b),_115);});},_11e=E(_11a);if(!_11e._){var _11f=_11e.d,_11g=_11e.e,_11h=E(_11e.b),_11i=E(_117),_11j=E(_11h.a);if(_11i>=_11j){if(_11i!=_11j){if(!B(_104(_11i,_,_118,_11g))){return new F(function(){return _11c(_);});}else{_10W=_11e;_10X=_11b;_10Y=_115;return __continue;}}else{var _11k=E(_118),_11l=E(_11h.b);if(_11k>=_11l){if(_11k!=_11l){if(!B(_ZT(_11i,_,_11k,_11g))){return new F(function(){return _11c(_);});}else{_10W=_11e;_10X=_11b;_10Y=_115;return __continue;}}else{_10W=_11e;_10X=_11b;_10Y=_115;return __continue;}}else{if(!B(_ZT(_11i,_,_11k,_11f))){return new F(function(){return _11c(_);});}else{_10W=_11e;_10X=_11b;_10Y=_115;return __continue;}}}}else{if(!B(_104(_11i,_,_118,_11f))){return new F(function(){return _11c(_);});}else{_10W=_11e;_10X=_11b;_10Y=_115;return __continue;}}}else{return new F(function(){return _11c(_);});}}else{return new T2(0,_110,_111);}})(_10W,_10X,_10Y));if(_10Z!=__continue){return _10Z;}}},_11m=0,_11n=function(_11o,_11p,_11q,_11r){while(1){var _11s=E(_11r);if(!_11s._){var _11t=_11s.d,_11u=_11s.e,_11v=E(_11s.b),_11w=E(_11v.a);if(_11o>=_11w){if(_11o!=_11w){_11p=_;_11r=_11u;continue;}else{var _11x=E(_11v.b);if(_11q>=_11x){if(_11q!=_11x){_11p=_;_11r=_11u;continue;}else{return new T1(1,_11s.c);}}else{_11p=_;_11r=_11t;continue;}}}else{_11p=_;_11r=_11t;continue;}}else{return __Z;}}},_11y=function(_11z,_11A,_11B,_11C){while(1){var _11D=E(_11C);if(!_11D._){var _11E=_11D.d,_11F=_11D.e,_11G=E(_11D.b),_11H=E(_11G.a);if(_11z>=_11H){if(_11z!=_11H){_11A=_;_11C=_11F;continue;}else{var _11I=E(_11B),_11J=E(_11G.b);if(_11I>=_11J){if(_11I!=_11J){return new F(function(){return _11n(_11z,_,_11I,_11F);});}else{return new T1(1,_11D.c);}}else{return new F(function(){return _11n(_11z,_,_11I,_11E);});}}}else{_11A=_;_11C=_11E;continue;}}else{return __Z;}}},_11K=function(_11L,_11M,_11N,_11O,_11P){while(1){var _11Q=E(_11P);if(!_11Q._){var _11R=_11Q.c,_11S=_11Q.d,_11T=E(_11Q.b),_11U=E(_11L),_11V=E(_11T.a);if(_11U>=_11V){if(_11U!=_11V){_11L=_11U;_11P=_11S;continue;}else{var _11W=E(_11M),_11X=E(_11T.b);if(_11W>=_11X){if(_11W!=_11X){_11L=_11U;_11M=_11W;_11P=_11S;continue;}else{var _11Y=E(_11N),_11Z=E(_11T.c);if(_11Y>=_11Z){if(_11Y!=_11Z){_11L=_11U;_11M=_11W;_11N=_11Y;_11P=_11S;continue;}else{var _120=E(_11T.d);if(_11O>=_120){if(_11O!=_120){_11L=_11U;_11M=_11W;_11N=_11Y;_11P=_11S;continue;}else{return true;}}else{_11L=_11U;_11M=_11W;_11N=_11Y;_11P=_11R;continue;}}}else{_11L=_11U;_11M=_11W;_11N=_11Y;_11P=_11R;continue;}}}else{_11L=_11U;_11M=_11W;_11P=_11R;continue;}}}else{_11L=_11U;_11P=_11R;continue;}}else{return false;}}},_121=function(_122,_123){return E(_122)+E(_123)|0;},_124=function(_125,_126,_127){var _128=function(_129,_12a){while(1){var _12b=B((function(_12c,_12d){var _12e=E(_12d);if(!_12e._){var _12f=new T(function(){return B(_128(_12c,_12e.e));}),_12g=function(_12h){var _12i=E(_12e.c),_12j=E(_12i.b);if(!_12j._){if(E(_12i.a)!=E(_126)){return new F(function(){return A1(_12f,_12h);});}else{if(E(_12j.b)>E(_127)){return new F(function(){return A1(_12f,new T(function(){return B(_121(_12h,_12j.a));}));});}else{return new F(function(){return A1(_12f,_12h);});}}}else{return new F(function(){return A1(_12f,_12h);});}};_129=_12g;_12a=_12e.d;return __continue;}else{return E(_12c);}})(_129,_12a));if(_12b!=__continue){return _12b;}}};return new F(function(){return A3(_128,_5K,_125,_11m);});},_12k=function(_12l,_12m){while(1){var _12n=E(_12m);if(!_12n._){var _12o=E(_12n.b);if(_12l>=_12o){if(_12l!=_12o){_12m=_12n.e;continue;}else{return new T1(1,_12n.c);}}else{_12m=_12n.d;continue;}}else{return __Z;}}},_12p=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_12q=new T(function(){return B(err(_12p));}),_12r=function(_12s,_12t){var _12u=E(_12t);if(!_12u._){return E(_12q);}else{var _12v=_12u.b,_12w=E(_12u.a),_12x=_12w.a,_12y=E(_12w.b),_12z=_12y.a,_12A=E(_12y.b);if(!_12A._){var _12B=_12A.b,_12C=E(_12A.a);return (_12s>_12C)?(_12C>=_12s)?E(_12v):new T2(1,new T2(0,_12x,new T2(0,_12z,new T2(0,_11m,_12B))),new T(function(){return B(_12r(_12s-_12C|0,_12v));})):new T2(1,new T2(0,_12x,new T2(0,_12z,new T2(0,_12C-_12s|0,_12B))),_21);}else{return E(_12v);}}},_12D=function(_12E,_12F){var _12G=E(_12F);if(!_12G._){return E(_12q);}else{var _12H=_12G.b,_12I=E(_12G.a),_12J=_12I.a,_12K=E(_12I.b),_12L=_12K.a,_12M=E(_12K.b);if(!_12M._){var _12N=_12M.b,_12O=E(_12E),_12P=E(_12M.a);return (_12O>_12P)?(_12P>=_12O)?E(_12H):new T2(1,new T2(0,_12J,new T2(0,_12L,new T2(0,_11m,_12N))),new T(function(){return B(_12r(_12O-_12P|0,_12H));})):new T2(1,new T2(0,_12J,new T2(0,_12L,new T2(0,_12P-_12O|0,_12N))),_21);}else{return E(_12H);}}},_12Q=function(_12R,_12S){var _12T=E(_12S);if(!_12T._){var _12U=_12T.b,_12V=_12T.c,_12W=_12T.d,_12X=_12T.e;if(!B(A2(_12R,_12U,_12V))){return new F(function(){return _Xi(B(_12Q(_12R,_12W)),B(_12Q(_12R,_12X)));});}else{return new F(function(){return _C2(_12U,_12V,B(_12Q(_12R,_12W)),B(_12Q(_12R,_12X)));});}}else{return new T0(1);}},_12Y=function(_12Z,_130){var _131=E(_12Z);if(!_131._){var _132=E(_130);if(!_132._){return new F(function(){return _V7(_131.b,_132.b);});}else{return 0;}}else{return (E(_130)._==0)?2:1;}},_133=function(_134,_135){return new F(function(){return _12Y(E(E(_134).b).b,E(E(_135).b).b);});},_136=new T2(1,_21,_21),_137=function(_138,_139){var _13a=function(_13b,_13c){var _13d=E(_13b);if(!_13d._){return E(_13c);}else{var _13e=_13d.a,_13f=E(_13c);if(!_13f._){return E(_13d);}else{var _13g=_13f.a;return (B(A2(_138,_13e,_13g))==2)?new T2(1,_13g,new T(function(){return B(_13a(_13d,_13f.b));})):new T2(1,_13e,new T(function(){return B(_13a(_13d.b,_13f));}));}}},_13h=function(_13i){var _13j=E(_13i);if(!_13j._){return __Z;}else{var _13k=E(_13j.b);return (_13k._==0)?E(_13j):new T2(1,new T(function(){return B(_13a(_13j.a,_13k.a));}),new T(function(){return B(_13h(_13k.b));}));}},_13l=new T(function(){return B(_13m(B(_13h(_21))));}),_13m=function(_13n){while(1){var _13o=E(_13n);if(!_13o._){return E(_13l);}else{if(!E(_13o.b)._){return E(_13o.a);}else{_13n=B(_13h(_13o));continue;}}}},_13p=new T(function(){return B(_13q(_21));}),_13r=function(_13s,_13t,_13u){while(1){var _13v=B((function(_13w,_13x,_13y){var _13z=E(_13y);if(!_13z._){return new T2(1,new T2(1,_13w,_13x),_13p);}else{var _13A=_13z.a;if(B(A2(_138,_13w,_13A))==2){var _13B=new T2(1,_13w,_13x);_13s=_13A;_13t=_13B;_13u=_13z.b;return __continue;}else{return new T2(1,new T2(1,_13w,_13x),new T(function(){return B(_13q(_13z));}));}}})(_13s,_13t,_13u));if(_13v!=__continue){return _13v;}}},_13C=function(_13D,_13E,_13F){while(1){var _13G=B((function(_13H,_13I,_13J){var _13K=E(_13J);if(!_13K._){return new T2(1,new T(function(){return B(A1(_13I,new T2(1,_13H,_21)));}),_13p);}else{var _13L=_13K.a,_13M=_13K.b;switch(B(A2(_138,_13H,_13L))){case 0:_13D=_13L;_13E=function(_13N){return new F(function(){return A1(_13I,new T2(1,_13H,_13N));});};_13F=_13M;return __continue;case 1:_13D=_13L;_13E=function(_13O){return new F(function(){return A1(_13I,new T2(1,_13H,_13O));});};_13F=_13M;return __continue;default:return new T2(1,new T(function(){return B(A1(_13I,new T2(1,_13H,_21)));}),new T(function(){return B(_13q(_13K));}));}}})(_13D,_13E,_13F));if(_13G!=__continue){return _13G;}}},_13q=function(_13P){var _13Q=E(_13P);if(!_13Q._){return E(_136);}else{var _13R=_13Q.a,_13S=E(_13Q.b);if(!_13S._){return new T2(1,_13Q,_21);}else{var _13T=_13S.a,_13U=_13S.b;if(B(A2(_138,_13R,_13T))==2){return new F(function(){return _13r(_13T,new T2(1,_13R,_21),_13U);});}else{return new F(function(){return _13C(_13T,function(_13V){return new T2(1,_13R,_13V);},_13U);});}}}};return new F(function(){return _13m(B(_13q(_139)));});},_13W=function(_13X,_13Y,_13Z){var _140=B(_Rr(B(_12D(_13Y,B(_137(_133,B(_ID(_21,B(_12Q(function(_141,_142){return new F(function(){return A1(_13X,_142);});},_13Z))))))))));if(!_140._){var _143=E(_13Z);if(!_143._){return new F(function(){return _Zp(_Vm,_XJ,_XJ,_140.a,_140.b,_140.c,_140.d,_140.e,_143.a,_143.b,_143.c,_143.d,_143.e);});}else{return E(_140);}}else{return E(_13Z);}},_144=function(_145,_146,_147,_148){while(1){var _149=E(_148);if(!_149._){var _14a=_149.d,_14b=_149.e,_14c=E(_149.b),_14d=E(_14c.a);if(_145>=_14d){if(_145!=_14d){_146=_;_148=_14b;continue;}else{var _14e=E(_14c.b);if(_147>=_14e){if(_147!=_14e){_146=_;_148=_14b;continue;}else{return new T1(1,_149.c);}}else{_146=_;_148=_14a;continue;}}}else{_146=_;_148=_14a;continue;}}else{return __Z;}}},_14f=function(_14g,_14h,_14i,_14j){while(1){var _14k=E(_14j);if(!_14k._){var _14l=_14k.d,_14m=_14k.e,_14n=E(_14k.b),_14o=E(_14n.a);if(_14g>=_14o){if(_14g!=_14o){_14h=_;_14j=_14m;continue;}else{var _14p=E(_14i),_14q=E(_14n.b);if(_14p>=_14q){if(_14p!=_14q){return new F(function(){return _144(_14g,_,_14p,_14m);});}else{return new T1(1,_14k.c);}}else{return new F(function(){return _144(_14g,_,_14p,_14l);});}}}else{_14h=_;_14j=_14l;continue;}}else{return __Z;}}},_14r=function(_14s,_14t,_14u){var _14v=E(_14u);if(!_14v._){var _14w=_14v.d,_14x=_14v.e,_14y=E(_14v.b),_14z=E(_14s),_14A=E(_14y.a);if(_14z>=_14A){if(_14z!=_14A){return new F(function(){return _104(_14z,_,_14t,_14x);});}else{var _14B=E(_14t),_14C=E(_14y.b);if(_14B>=_14C){if(_14B!=_14C){return new F(function(){return _ZT(_14z,_,_14B,_14x);});}else{return true;}}else{return new F(function(){return _ZT(_14z,_,_14B,_14w);});}}}else{return new F(function(){return _104(_14z,_,_14t,_14w);});}}else{return false;}},_14D=function(_14E,_14F){var _14G=E(_14F);switch(_14G._){case 0:var _14H=B(_12k(E(_14G.a),_14E));if(!_14H._){return E(_11m);}else{var _14I=E(E(_14H.a).b);return (_14I._==0)?E(_14I.a):E(_11m);}break;case 1:return B(_14D(_14E,_14G.a))+B(_14D(_14E,_14G.b))|0;default:return E(_14G.a);}},_14J=function(_14K,_14L,_14M){while(1){var _14N=E(_14L);switch(_14N._){case 0:return (E(_14N.a)>E(E(_14M).b))?true:false;case 1:if(!B(_14J(_14K,_14N.a,_14M))){return false;}else{_14L=_14N.b;continue;}break;case 2:if(!B(_14J(_14K,_14N.a,_14M))){_14L=_14N.b;continue;}else{return true;}break;case 3:return (!B(_14J(_14K,_14N.a,_14M)))?true:false;case 4:var _14O=_14N.b,_14P=_14N.c,_14Q=E(E(_14K).b);if(!_14Q._){var _14R=_14Q.d,_14S=_14Q.e,_14T=E(_14Q.b),_14U=E(_14N.a),_14V=E(_14T.a);if(_14U>=_14V){if(_14U!=_14V){var _14W=B(_14f(_14U,_,_14O,_14S));if(!_14W._){return false;}else{return new F(function(){return _Sp(_14W.a,_14P);});}}else{var _14X=E(_14O),_14Y=E(_14T.b);if(_14X>=_14Y){if(_14X!=_14Y){var _14Z=B(_144(_14U,_,_14X,_14S));if(!_14Z._){return false;}else{return new F(function(){return _Sp(_14Z.a,_14P);});}}else{return new F(function(){return _Sp(_14Q.c,_14P);});}}else{var _150=B(_144(_14U,_,_14X,_14R));if(!_150._){return false;}else{return new F(function(){return _Sp(_150.a,_14P);});}}}}else{var _151=B(_14f(_14U,_,_14O,_14R));if(!_151._){return false;}else{return new F(function(){return _Sp(_151.a,_14P);});}}}else{return false;}break;case 5:return new F(function(){return _14r(_14N.a,_14N.b,E(_14K).b);});break;case 6:var _152=E(_14K).a;return B(_14D(_152,_14N.a))>=B(_14D(_152,_14N.b));case 7:return true;default:return false;}}},_153=function(_154,_155,_156,_157){var _158=E(_156);switch(_158._){case 0:return new T3(0,_155,_k9,_21);case 1:var _159=_158.b,_15a=E(_155),_15b=_15a.a,_15c=E(_158.a),_15d=B(_12k(_15c,_15b));if(!_15d._){return new T3(0,_15a,_158,_21);}else{var _15e=E(_15d.a),_15f=_15e.a,_15g=E(_15e.b);if(!_15g._){var _15h=_15g.a;return (!B(_VO(_15c,_,_15f,_15h,E(_154).b)))?new T3(0,_15a,_158,_21):new T3(0,new T2(0,new T(function(){return B(_Qy(_15c,new T2(0,_15f,_XZ),_15b));}),_15a.b),_159,new T2(1,new T3(4,_15c,_15f,_15h),_21));}else{return new T3(0,_15a,_159,new T2(1,new T2(6,_15c,_15f),_21));}}break;case 2:var _15i=_158.a,_15j=_158.b,_15k=_158.c,_15l=_158.d,_15m=_158.f,_15n=E(E(_157).b);if(E(_158.e)>_15n){var _15o=function(_15p){var _15q=E(_15l);if(E(_15p)!=_15q){return new T3(0,_155,_158,_21);}else{var _15r=E(_155),_15s=_15r.a;if(B(_124(_15s,_15j,_15n))<_15q){return new T3(0,_15r,_15m,new T2(1,new T4(2,_15i,_15j,_15k,_15q),_21));}else{var _15t=new T(function(){return B(_13W(function(_15u){var _15v=E(_15u),_15w=E(_15v.b);return (_15w._==0)?(E(_15v.a)!=E(_15j))?false:(E(_15w.b)>_15n)?true:false:false;},_15q,_15s));});return new T3(0,new T2(0,_15t,_15r.b),_15m,new T2(1,new T4(0,_15i,_15j,_15k,_15q),_21));}}},_15x=E(E(_154).c);if(!_15x._){var _15y=_15x.d,_15z=_15x.e,_15A=E(_15x.b),_15B=E(_15i),_15C=E(_15A.a);if(_15B>=_15C){if(_15B!=_15C){var _15D=B(_11y(_15B,_,_15k,_15z));if(!_15D._){return new T3(0,_155,_158,_21);}else{return new F(function(){return _15o(_15D.a);});}}else{var _15E=E(_15k),_15F=E(_15A.b);if(_15E>=_15F){if(_15E!=_15F){var _15G=B(_11n(_15B,_,_15E,_15z));if(!_15G._){return new T3(0,_155,_158,_21);}else{return new F(function(){return _15o(_15G.a);});}}else{return new F(function(){return _15o(_15x.c);});}}else{var _15H=B(_11n(_15B,_,_15E,_15y));if(!_15H._){return new T3(0,_155,_158,_21);}else{return new F(function(){return _15o(_15H.a);});}}}}else{var _15I=B(_11y(_15B,_,_15k,_15y));if(!_15I._){return new T3(0,_155,_158,_21);}else{return new F(function(){return _15o(_15I.a);});}}}else{return new T3(0,_155,_158,_21);}}else{return new T3(0,_155,_15m,new T2(1,new T4(1,_15i,_15j,_15k,_15l),_21));}break;case 3:var _15J=new T(function(){var _15K=B(_153(_154,_155,_158.a,_157));return new T3(0,_15K.a,_15K.b,_15K.c);}),_15L=new T(function(){var _15M=B(_153(_154,new T(function(){return E(E(_15J).a);}),_158.b,_157));return new T3(0,_15M.a,_15M.b,_15M.c);}),_15N=new T(function(){return B(_2(E(_15J).c,new T(function(){return E(E(_15L).c);},1)));}),_15O=new T(function(){var _15P=E(_15J).b,_15Q=E(_15L).b,_15R=function(_15S){var _15T=E(_15Q);switch(_15T._){case 0:return E(_15P);case 1:return new T2(3,_15P,_15T);case 2:return new T2(3,_15P,_15T);case 3:return new T2(3,_15P,_15T);case 4:return new T2(3,_15P,_15T);case 5:return new T2(3,_15P,_15T);default:return new T2(3,_15P,_15T);}};switch(E(_15P)._){case 0:return E(_15Q);break;case 1:return B(_15R(_));break;case 2:return B(_15R(_));break;case 3:return B(_15R(_));break;case 4:return B(_15R(_));break;case 5:return B(_15R(_));break;default:return B(_15R(_));}});return new T3(0,new T(function(){return E(E(_15L).a);}),_15O,_15N);case 4:return (!B(_14J(_155,_158.a,_157)))?new T3(0,_155,_158.c,_21):new T3(0,_155,_158.b,_21);case 5:var _15U=_158.a,_15V=_158.b,_15W=_158.c,_15X=_158.f,_15Y=E(_158.e),_15Z=E(E(_157).b),_160=_15Y<=_15Z,_161=new T(function(){return E(_158.d)<=_15Z;}),_162=new T(function(){return B(_Qy(E(_15U),new T2(0,_15V,new T(function(){if(!E(_160)){if(!E(_161)){return new T2(0,_15W,_15Y);}else{return new T0(1);}}else{return new T0(1);}})),E(_155).a));});return (!E(_160))?(!E(_161))?(!B(_11K(_15U,_15V,_15W,_15Y,E(_154).a)))?new T3(0,_155,_158,_21):new T3(0,new T(function(){return new T2(0,_162,E(_155).b);}),_15X,new T2(1,new T3(3,_15U,_15V,_15W),_21)):new T3(0,new T(function(){return new T2(0,_162,E(_155).b);}),_15X,new T2(1,new T3(3,_15U,_15V,_11m),new T2(1,new T3(4,_15U,_15V,_11m),_21))):new T3(0,new T(function(){return new T2(0,_162,E(_155).b);}),_15X,new T2(1,new T3(3,_15U,_15V,_11m),new T2(1,new T3(4,_15U,_15V,_11m),_21)));default:var _163=E(_157);return (E(_158.b)>E(_163.b))?(!B(_14J(_155,_158.a,_163)))?new T3(0,_155,_158,_21):new T3(0,_155,_158.c,_21):new T3(0,_155,_158.d,_21);}},_164=function(_165,_166,_167,_168){var _169=new T(function(){var _16a=B(_ZG(_165,new T(function(){return E(E(_166).a);},1),_168));return new T2(0,_16a.a,_16a.b);}),_16b=new T(function(){var _16c=B(_10V(new T(function(){return E(E(_166).b);}),_21,E(_165).d));return new T2(0,_16c.a,_16c.b);}),_16d=new T(function(){var _16e=new T(function(){var _16f=E(_166);return new T2(0,new T(function(){return E(E(_169).a);}),new T(function(){return E(E(_16b).a);}));}),_16g=B(_153(_165,_16e,_167,_168));return new T3(0,_16g.a,_16g.b,_16g.c);}),_16h=new T(function(){var _16i=new T(function(){return B(_2(E(_169).b,new T(function(){return E(E(_16d).c);},1)));},1);return B(_2(E(_16b).b,_16i));});return new T3(0,new T(function(){return E(E(_16d).a);}),new T(function(){return E(E(_16d).b);}),_16h);},_16j=function(_16k,_16l,_16m,_16n,_16o,_16p){var _16q=new T2(0,_16l,_16m),_16r=B(_164(_16k,_16q,_16n,_16o)),_16s=_16r.b,_16t=_16r.c,_16u=E(_16r.a),_16v=_16u.a,_16w=_16u.b,_16x=function(_16y){return new F(function(){return _16j(_16k,_16v,_16w,_16s,_16o,new T(function(){return B(_2(_16t,_16p));}));});};if(!B(A2(_UT,_16v,_16l))){return new F(function(){return _16x(_);});}else{if(!B(A2(_Up,_16w,_16m))){return new F(function(){return _16x(_);});}else{if(!B(_T0(_16s,_16n))){return new F(function(){return _16x(_);});}else{if(!B(_U6(_SH,_16t,_21))){return new F(function(){return _16x(_);});}else{return new T3(0,_16q,_16n,_16p);}}}}},_16z=new T(function(){return B(err(_22));}),_16A=new T(function(){return B(err(_2c));}),_16B=new T(function(){return B(A3(_gs,_gV,_fX,_lR));}),_16C=new T(function(){return B(err(_22));}),_16D=new T(function(){return B(err(_2c));}),_16E=function(_Ll){return new F(function(){return _gh(_hd,_Ll);});},_16F=function(_16G,_16H){return new F(function(){return _KB(_16E,_16H);});},_16I=new T(function(){return B(_KB(_16E,_4X));}),_16J=function(_Ll){return new F(function(){return _3A(_16I,_Ll);});},_16K=function(_16L){var _16M=new T(function(){return B(A3(_gh,_hd,_16L,_4X));});return function(_Li){return new F(function(){return _3A(_16M,_Li);});};},_16N=new T4(0,_16K,_16J,_16E,_16F),_16O=new T(function(){return B(unCStr("NotRedeemed"));}),_16P=function(_16Q,_16R){var _16S=new T(function(){var _16T=new T(function(){return B(A1(_16R,_XZ));});return B(_fq(function(_16U){var _16V=E(_16U);return (_16V._==3)?(!B(_4q(_16V.a,_PJ)))?new T0(2):E(_16T):new T0(2);}));}),_16W=function(_16X){return E(_16S);},_16Y=new T(function(){if(E(_16Q)>10){return new T0(2);}else{var _16Z=new T(function(){var _170=new T(function(){var _171=function(_172){return new F(function(){return A3(_gs,_gV,_4m,function(_173){return new F(function(){return A1(_16R,new T2(0,_172,_173));});});});};return B(A3(_gs,_gV,_4m,_171));});return B(_fq(function(_174){var _175=E(_174);return (_175._==3)?(!B(_4q(_175.a,_16O)))?new T0(2):E(_170):new T0(2);}));}),_176=function(_177){return E(_16Z);};return new T1(1,function(_178){return new F(function(){return A2(_e7,_178,_176);});});}});return new F(function(){return _3K(new T1(1,function(_179){return new F(function(){return A2(_e7,_179,_16W);});}),_16Y);});},_17a=function(_Ll){return new F(function(){return _gh(_16P,_Ll);});},_17b=function(_17c,_17d){return new F(function(){return _KB(_17a,_17d);});},_17e=new T(function(){return B(_KB(_17a,_4X));}),_17f=function(_Ll){return new F(function(){return _3A(_17e,_Ll);});},_17g=function(_17h){var _17i=new T(function(){return B(A3(_gh,_16P,_17h,_4X));});return function(_Li){return new F(function(){return _3A(_17i,_Li);});};},_17j=new T4(0,_17g,_17f,_17a,_17b),_17k=function(_17l,_17m){return new F(function(){return _LQ(_Lj,_17j,_17m);});},_17n=new T(function(){return B(_KB(_17k,_4X));}),_17o=function(_Ll){return new F(function(){return _3A(_17n,_Ll);});},_17p=new T(function(){return B(_LQ(_Lj,_17j,_4X));}),_17q=function(_Ll){return new F(function(){return _3A(_17p,_Ll);});},_17r=function(_17s,_Ll){return new F(function(){return _17q(_Ll);});},_17t=function(_17u,_17v){return new F(function(){return _KB(_17k,_17v);});},_17w=new T4(0,_17r,_17o,_17k,_17t),_17x=function(_17y,_17z){return new F(function(){return _LQ(_16N,_17w,_17z);});},_17A=function(_17B,_17C){return new F(function(){return _KB(_17x,_17C);});},_17D=new T(function(){return B(_KB(_17A,_4X));}),_17E=function(_Ml){return new F(function(){return _3A(_17D,_Ml);});},_17F=function(_17G){return new F(function(){return _KB(_17A,_17G);});},_17H=function(_17I,_17J){return new F(function(){return _17F(_17J);});},_17K=new T(function(){return B(_KB(_17x,_4X));}),_17L=function(_Ml){return new F(function(){return _3A(_17K,_Ml);});},_17M=function(_17N,_Ml){return new F(function(){return _17L(_Ml);});},_17O=new T4(0,_17M,_17E,_17A,_17H),_17P=new T(function(){return B(_LQ(_17O,_Mv,_lR));}),_17Q=new T(function(){return B(unAppCStr("[]",_21));}),_17R=42,_17S=new T2(1,_2H,_21),_17T=function(_17U){var _17V=E(_17U);if(!_17V._){return E(_17S);}else{var _17W=new T(function(){return B(_RM(0,_17V.a,new T(function(){return B(_17T(_17V.b));})));});return new T2(1,_2G,_17W);}},_17X=function(_){var _17Y=E(_OY),_17Z=eval(E(_rq)),_180=_17Z,_181=__app1(E(_180),toJSStr(_17Y)),_182=E(_Po),_183=__app1(E(_180),toJSStr(_182)),_184=__app0(E(_lX)),_185=E(_Pq),_186=__app1(E(_180),toJSStr(_185)),_187=new T(function(){var _188=B(_lY(B(_3A(_16B,new T(function(){var _189=String(_186);return fromJSStr(_189);})))));if(!_188._){return E(_16A);}else{if(!E(_188.b)._){return E(_188.a);}else{return E(_16z);}}}),_18a=B(_lY(B(_3A(_17P,new T(function(){var _18b=String(_183);return fromJSStr(_18b);})))));if(!_18a._){return E(_16D);}else{if(!E(_18a.b)._){var _18c=E(_18a.a),_18d=new T(function(){var _18e=B(_lY(B(_3A(_lW,new T(function(){var _18f=String(_184);return fromJSStr(_18f);})))));if(!_18e._){return E(_2d);}else{if(!E(_18e.b)._){return E(_18e.a);}else{return E(_23);}}}),_18g=new T(function(){var _18h=B(_lY(B(_3A(_OX,new T(function(){var _18i=String(_181);return fromJSStr(_18i);})))));if(!_18h._){return E(_Kx);}else{if(!E(_18h.b)._){var _18j=E(_18h.a);return new T4(0,new T(function(){return B(_va(_18j.a));}),new T(function(){return B(_zx(_18j.b));}),new T(function(){return B(_In(_18j.c));}),new T(function(){return B(_Fd(_18j.d));}));}else{return E(_Kw);}}}),_18k=B(_16j(_18g,new T(function(){return B(_Rr(_18c.a));}),new T(function(){return B(_Fd(_18c.b));}),_18d,new T2(0,_17R,_187),_21)),_18l=function(_,_18m){var _18n=B(_27(_24,B(_1t(0,_18k.b,_21)),_)),_18o=E(_18k.a),_18p=new T(function(){var _18q=new T(function(){return B(_ID(_21,_18o.b));}),_18r=new T(function(){return B(_ID(_21,_18o.a));});return B(A3(_Jq,_IK,new T2(1,function(_18s){return new F(function(){return _Qa(_18r,_18s);});},new T2(1,function(_18t){return new F(function(){return _K7(_18q,_18t);});},_21)),_Ka));}),_18u=B(_27(_182,new T2(1,_b,_18p),_)),_18v=B(_27(_17Y,_Pm,_)),_18w=B(_27(_185,B(_c(0,E(_187)+1|0,_21)),_)),_18x=__app1(E(_180),toJSStr(E(_24)));return new F(function(){return _ri(new T(function(){var _18y=String(_18x);return fromJSStr(_18y);}),_);});},_18z=E(_18k.c);if(!_18z._){var _18A=B(_27(_Pl,_17Q,_));return new F(function(){return _18l(_,_18A);});}else{var _18B=new T(function(){return B(_RM(0,_18z.a,new T(function(){return B(_17T(_18z.b));})));}),_18C=B(_27(_Pl,new T2(1,_2I,_18B),_));return new F(function(){return _18l(_,_18C);});}}else{return E(_16C);}}},_18D=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18E=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18F=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18G=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18H=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18I=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18J=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18K=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18L=function(_){return new F(function(){return __jsNull();});},_18M=function(_18N){var _18O=B(A1(_18N,_));return E(_18O);},_18P=new T(function(){return B(_18M(_18L));}),_18Q=new T(function(){return E(_18P);}),_18R=function(_18S,_18T,_18U,_){var _18V=E(_OY),_18W=eval(E(_rq)),_18X=__app1(E(_18W),toJSStr(_18V)),_18Y=B(_lY(B(_3A(_OX,new T(function(){var _18Z=String(_18X);return fromJSStr(_18Z);})))));if(!_18Y._){return E(_Kx);}else{if(!E(_18Y.b)._){var _190=E(_18Y.a),_191=B(_Ki(new T(function(){return B(_va(_190.a));},1),new T(function(){return B(_xG(_18U,_18S,_18T,B(_zx(_190.b))));},1),new T(function(){return B(_In(_190.c));},1),new T(function(){return B(_Fd(_190.d));},1)));return new F(function(){return _27(_18V,new T2(1,_191.a,_191.b),_);});}else{return E(_Kw);}}},_192=function(_){var _193=eval(E(_rq)),_194=__app1(E(_193),toJSStr(E(_24))),_195=B(_ri(new T(function(){var _196=String(_194);return fromJSStr(_196);}),_)),_197=__createJSFunc(0,function(_){var _198=B(_Pr(_));return _18Q;}),_199=__app2(E(_18F),"clear_workspace",_197),_19a=__createJSFunc(0,function(_){var _19b=B(_m5(_));return _18Q;}),_19c=__app2(E(_18E),"b2c",_19a),_19d=__createJSFunc(0,function(_){var _19e=B(_rr(_));return _18Q;}),_19f=__app2(E(_18D),"c2b",_19d),_19g=function(_19h){var _19i=new T(function(){var _19j=Number(E(_19h));return jsTrunc(_19j);}),_19k=function(_19l){var _19m=new T(function(){var _19n=Number(E(_19l));return jsTrunc(_19n);}),_19o=function(_19p){var _19q=new T(function(){var _19r=Number(E(_19p));return jsTrunc(_19r);}),_19s=function(_19t,_){var _19u=B(_Px(_19i,_19m,_19q,new T(function(){var _19v=Number(E(_19t));return jsTrunc(_19v);}),_));return _18Q;};return E(_19s);};return E(_19o);};return E(_19k);},_19w=__createJSFunc(5,E(_19g)),_19x=__app2(E(_18K),"commit",_19w),_19y=function(_19z){var _19A=new T(function(){var _19B=Number(E(_19z));return jsTrunc(_19B);}),_19C=function(_19D){var _19E=new T(function(){var _19F=Number(E(_19D));return jsTrunc(_19F);}),_19G=function(_19H,_){var _19I=B(_18R(_19A,_19E,new T(function(){var _19J=Number(E(_19H));return jsTrunc(_19J);}),_));return _18Q;};return E(_19G);};return E(_19C);},_19K=__createJSFunc(4,E(_19y)),_19L=__app2(E(_18J),"redeem",_19K),_19M=function(_19N){var _19O=new T(function(){var _19P=Number(E(_19N));return jsTrunc(_19P);}),_19Q=function(_19R){var _19S=new T(function(){var _19T=Number(E(_19R));return jsTrunc(_19T);}),_19U=function(_19V,_){var _19W=B(_Pa(_19O,_19S,new T(function(){var _19X=Number(E(_19V));return jsTrunc(_19X);}),_));return _18Q;};return E(_19U);};return E(_19Q);},_19Y=__createJSFunc(4,E(_19M)),_19Z=__app2(E(_18I),"claim",_19Y),_1a0=function(_1a1){var _1a2=new T(function(){var _1a3=Number(E(_1a1));return jsTrunc(_1a3);}),_1a4=function(_1a5){var _1a6=new T(function(){var _1a7=Number(E(_1a5));return jsTrunc(_1a7);}),_1a8=function(_1a9,_){var _1aa=B(_OZ(_1a2,_1a6,new T(function(){var _1ab=Number(E(_1a9));return jsTrunc(_1ab);}),_));return _18Q;};return E(_1a8);};return E(_1a4);},_1ac=__createJSFunc(4,E(_1a0)),_1ad=__app2(E(_18H),"choose",_1ac),_1ae=__createJSFunc(0,function(_){var _1af=B(_17X(_));return _18Q;}),_1ag=__app2(E(_18G),"execute",_1ae);return _0;},_1ah=function(_){return new F(function(){return _192(_);});};
var hasteMain = function() {B(A(_1ah, [0]));};window.onload = hasteMain;