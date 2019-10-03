"use strict";
var __haste_prog_id = '8a2484f295568448b084314eec7682dfbb5fb6263814377a0efea7d28bee7672';
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

var _0=new T0(1),_1=__Z,_2=function(_3,_4){var _5=E(_3);if(!_5._){var _6=_5.a,_7=E(_4);if(!_7._){var _8=_7.a;return (_6!=_8)?(_6>_8)?2:0:1;}else{var _9=I_compareInt(_7.a,_6);return (_9<=0)?(_9>=0)?1:2:0;}}else{var _a=_5.a,_b=E(_4);if(!_b._){var _c=I_compareInt(_a,_b.a);return (_c>=0)?(_c<=0)?1:2:0;}else{var _d=I_compare(_a,_b.a);return (_d>=0)?(_d<=0)?1:2:0;}}},_e=function(_f,_g){var _h=E(_f);if(!_h._){var _i=_h.a,_j=E(_g);return (_j._==0)?_i>=_j.a:I_compareInt(_j.a,_i)<=0;}else{var _k=_h.a,_l=E(_g);return (_l._==0)?I_compareInt(_k,_l.a)>=0:I_compare(_k,_l.a)>=0;}},_m=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_n=function(_o){return new F(function(){return err(_m);});},_p=new T(function(){return B(_n(_));}),_q=function(_r,_s,_t,_u){var _v=E(_t);if(!_v._){var _w=_v.a,_x=E(_u);if(!_x._){var _y=_x.a,_z=_x.b,_A=_x.c;if(_y<=(imul(3,_w)|0)){return new T5(0,(1+_w|0)+_y|0,E(_r),_s,E(_v),E(_x));}else{var _B=E(_x.d);if(!_B._){var _C=_B.a,_D=_B.b,_E=_B.c,_F=_B.d,_G=E(_x.e);if(!_G._){var _H=_G.a;if(_C>=(imul(2,_H)|0)){var _I=function(_J){var _K=E(_r),_L=E(_B.e);return (_L._==0)?new T5(0,(1+_w|0)+_y|0,E(_D),_E,E(new T5(0,(1+_w|0)+_J|0,E(_K),_s,E(_v),E(_F))),E(new T5(0,(1+_H|0)+_L.a|0,E(_z),_A,E(_L),E(_G)))):new T5(0,(1+_w|0)+_y|0,E(_D),_E,E(new T5(0,(1+_w|0)+_J|0,E(_K),_s,E(_v),E(_F))),E(new T5(0,1+_H|0,E(_z),_A,E(_0),E(_G))));},_M=E(_F);if(!_M._){return new F(function(){return _I(_M.a);});}else{return new F(function(){return _I(0);});}}else{return new T5(0,(1+_w|0)+_y|0,E(_z),_A,E(new T5(0,(1+_w|0)+_C|0,E(_r),_s,E(_v),E(_B))),E(_G));}}else{return E(_p);}}else{return E(_p);}}}else{return new T5(0,1+_w|0,E(_r),_s,E(_v),E(_0));}}else{var _N=E(_u);if(!_N._){var _O=_N.a,_P=_N.b,_Q=_N.c,_R=_N.e,_S=E(_N.d);if(!_S._){var _T=_S.a,_U=_S.b,_V=_S.c,_W=_S.d,_X=E(_R);if(!_X._){var _Y=_X.a;if(_T>=(imul(2,_Y)|0)){var _Z=function(_10){var _11=E(_r),_12=E(_S.e);return (_12._==0)?new T5(0,1+_O|0,E(_U),_V,E(new T5(0,1+_10|0,E(_11),_s,E(_0),E(_W))),E(new T5(0,(1+_Y|0)+_12.a|0,E(_P),_Q,E(_12),E(_X)))):new T5(0,1+_O|0,E(_U),_V,E(new T5(0,1+_10|0,E(_11),_s,E(_0),E(_W))),E(new T5(0,1+_Y|0,E(_P),_Q,E(_0),E(_X))));},_13=E(_W);if(!_13._){return new F(function(){return _Z(_13.a);});}else{return new F(function(){return _Z(0);});}}else{return new T5(0,1+_O|0,E(_P),_Q,E(new T5(0,1+_T|0,E(_r),_s,E(_0),E(_S))),E(_X));}}else{return new T5(0,3,E(_U),_V,E(new T5(0,1,E(_r),_s,E(_0),E(_0))),E(new T5(0,1,E(_P),_Q,E(_0),E(_0))));}}else{var _14=E(_R);return (_14._==0)?new T5(0,3,E(_P),_Q,E(new T5(0,1,E(_r),_s,E(_0),E(_0))),E(_14)):new T5(0,2,E(_r),_s,E(_0),E(_N));}}else{return new T5(0,1,E(_r),_s,E(_0),E(_0));}}},_15=function(_16,_17){return new T5(0,1,E(_16),_17,E(_0),E(_0));},_18=function(_19,_1a,_1b){var _1c=E(_1b);if(!_1c._){return new F(function(){return _q(_1c.b,_1c.c,_1c.d,B(_18(_19,_1a,_1c.e)));});}else{return new F(function(){return _15(_19,_1a);});}},_1d=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_1e=function(_1f){return new F(function(){return err(_1d);});},_1g=new T(function(){return B(_1e(_));}),_1h=function(_1i,_1j,_1k,_1l){var _1m=E(_1l);if(!_1m._){var _1n=_1m.a,_1o=E(_1k);if(!_1o._){var _1p=_1o.a,_1q=_1o.b,_1r=_1o.c;if(_1p<=(imul(3,_1n)|0)){return new T5(0,(1+_1p|0)+_1n|0,E(_1i),_1j,E(_1o),E(_1m));}else{var _1s=E(_1o.d);if(!_1s._){var _1t=_1s.a,_1u=E(_1o.e);if(!_1u._){var _1v=_1u.a,_1w=_1u.b,_1x=_1u.c,_1y=_1u.d;if(_1v>=(imul(2,_1t)|0)){var _1z=function(_1A){var _1B=E(_1u.e);return (_1B._==0)?new T5(0,(1+_1p|0)+_1n|0,E(_1w),_1x,E(new T5(0,(1+_1t|0)+_1A|0,E(_1q),_1r,E(_1s),E(_1y))),E(new T5(0,(1+_1n|0)+_1B.a|0,E(_1i),_1j,E(_1B),E(_1m)))):new T5(0,(1+_1p|0)+_1n|0,E(_1w),_1x,E(new T5(0,(1+_1t|0)+_1A|0,E(_1q),_1r,E(_1s),E(_1y))),E(new T5(0,1+_1n|0,E(_1i),_1j,E(_0),E(_1m))));},_1C=E(_1y);if(!_1C._){return new F(function(){return _1z(_1C.a);});}else{return new F(function(){return _1z(0);});}}else{return new T5(0,(1+_1p|0)+_1n|0,E(_1q),_1r,E(_1s),E(new T5(0,(1+_1n|0)+_1v|0,E(_1i),_1j,E(_1u),E(_1m))));}}else{return E(_1g);}}else{return E(_1g);}}}else{return new T5(0,1+_1n|0,E(_1i),_1j,E(_0),E(_1m));}}else{var _1D=E(_1k);if(!_1D._){var _1E=_1D.a,_1F=_1D.b,_1G=_1D.c,_1H=_1D.e,_1I=E(_1D.d);if(!_1I._){var _1J=_1I.a,_1K=E(_1H);if(!_1K._){var _1L=_1K.a,_1M=_1K.b,_1N=_1K.c,_1O=_1K.d;if(_1L>=(imul(2,_1J)|0)){var _1P=function(_1Q){var _1R=E(_1K.e);return (_1R._==0)?new T5(0,1+_1E|0,E(_1M),_1N,E(new T5(0,(1+_1J|0)+_1Q|0,E(_1F),_1G,E(_1I),E(_1O))),E(new T5(0,1+_1R.a|0,E(_1i),_1j,E(_1R),E(_0)))):new T5(0,1+_1E|0,E(_1M),_1N,E(new T5(0,(1+_1J|0)+_1Q|0,E(_1F),_1G,E(_1I),E(_1O))),E(new T5(0,1,E(_1i),_1j,E(_0),E(_0))));},_1S=E(_1O);if(!_1S._){return new F(function(){return _1P(_1S.a);});}else{return new F(function(){return _1P(0);});}}else{return new T5(0,1+_1E|0,E(_1F),_1G,E(_1I),E(new T5(0,1+_1L|0,E(_1i),_1j,E(_1K),E(_0))));}}else{return new T5(0,3,E(_1F),_1G,E(_1I),E(new T5(0,1,E(_1i),_1j,E(_0),E(_0))));}}else{var _1T=E(_1H);return (_1T._==0)?new T5(0,3,E(_1T.b),_1T.c,E(new T5(0,1,E(_1F),_1G,E(_0),E(_0))),E(new T5(0,1,E(_1i),_1j,E(_0),E(_0)))):new T5(0,2,E(_1i),_1j,E(_1D),E(_0));}}else{return new T5(0,1,E(_1i),_1j,E(_0),E(_0));}}},_1U=function(_1V,_1W,_1X){var _1Y=E(_1X);if(!_1Y._){return new F(function(){return _1h(_1Y.b,_1Y.c,B(_1U(_1V,_1W,_1Y.d)),_1Y.e);});}else{return new F(function(){return _15(_1V,_1W);});}},_1Z=function(_20,_21,_22,_23,_24,_25,_26){return new F(function(){return _1h(_23,_24,B(_1U(_20,_21,_25)),_26);});},_27=function(_28,_29,_2a,_2b,_2c,_2d,_2e,_2f){var _2g=E(_2a);if(!_2g._){var _2h=_2g.a,_2i=_2g.b,_2j=_2g.c,_2k=_2g.d,_2l=_2g.e;if((imul(3,_2h)|0)>=_2b){if((imul(3,_2b)|0)>=_2h){return new T5(0,(_2h+_2b|0)+1|0,E(_28),_29,E(_2g),E(new T5(0,_2b,E(_2c),_2d,E(_2e),E(_2f))));}else{return new F(function(){return _q(_2i,_2j,_2k,B(_27(_28,_29,_2l,_2b,_2c,_2d,_2e,_2f)));});}}else{return new F(function(){return _1h(_2c,_2d,B(_2m(_28,_29,_2h,_2i,_2j,_2k,_2l,_2e)),_2f);});}}else{return new F(function(){return _1Z(_28,_29,_2b,_2c,_2d,_2e,_2f);});}},_2m=function(_2n,_2o,_2p,_2q,_2r,_2s,_2t,_2u){var _2v=E(_2u);if(!_2v._){var _2w=_2v.a,_2x=_2v.b,_2y=_2v.c,_2z=_2v.d,_2A=_2v.e;if((imul(3,_2p)|0)>=_2w){if((imul(3,_2w)|0)>=_2p){return new T5(0,(_2p+_2w|0)+1|0,E(_2n),_2o,E(new T5(0,_2p,E(_2q),_2r,E(_2s),E(_2t))),E(_2v));}else{return new F(function(){return _q(_2q,_2r,_2s,B(_27(_2n,_2o,_2t,_2w,_2x,_2y,_2z,_2A)));});}}else{return new F(function(){return _1h(_2x,_2y,B(_2m(_2n,_2o,_2p,_2q,_2r,_2s,_2t,_2z)),_2A);});}}else{return new F(function(){return _18(_2n,_2o,new T5(0,_2p,E(_2q),_2r,E(_2s),E(_2t)));});}},_2B=function(_2C,_2D,_2E,_2F){var _2G=E(_2E);if(!_2G._){var _2H=_2G.a,_2I=_2G.b,_2J=_2G.c,_2K=_2G.d,_2L=_2G.e,_2M=E(_2F);if(!_2M._){var _2N=_2M.a,_2O=_2M.b,_2P=_2M.c,_2Q=_2M.d,_2R=_2M.e;if((imul(3,_2H)|0)>=_2N){if((imul(3,_2N)|0)>=_2H){return new T5(0,(_2H+_2N|0)+1|0,E(_2C),_2D,E(_2G),E(_2M));}else{return new F(function(){return _q(_2I,_2J,_2K,B(_27(_2C,_2D,_2L,_2N,_2O,_2P,_2Q,_2R)));});}}else{return new F(function(){return _1h(_2O,_2P,B(_2m(_2C,_2D,_2H,_2I,_2J,_2K,_2L,_2Q)),_2R);});}}else{return new F(function(){return _18(_2C,_2D,_2G);});}}else{return new F(function(){return _1U(_2C,_2D,_2F);});}},_2S=function(_2T,_2U,_2V,_2W,_2X){var _2Y=E(_2T);if(_2Y==1){var _2Z=E(_2X);if(!_2Z._){return new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_1,_1);}else{var _30=E(E(_2Z.a).a);switch(B(_2(_2U,_30.a))){case 0:return new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_2Z,_1);case 1:return (!B(_e(_2V,_30.b)))?new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_2Z,_1):new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_1,_2Z);default:return new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_1,_2Z);}}}else{var _31=B(_2S(_2Y>>1,_2U,_2V,_2W,_2X)),_32=_31.a,_33=_31.c,_34=E(_31.b);if(!_34._){return new T3(0,_32,_1,_33);}else{var _35=E(_34.a),_36=_35.a,_37=_35.b,_38=E(_34.b);if(!_38._){return new T3(0,new T(function(){return B(_18(_36,_37,_32));}),_1,_33);}else{var _39=_38.b,_3a=E(_38.a),_3b=_3a.b,_3c=E(_36),_3d=E(_3a.a),_3e=_3d.a,_3f=_3d.b;switch(B(_2(_3c.a,_3e))){case 0:var _3g=B(_2S(_2Y>>1,_3e,_3f,_3b,_39));return new T3(0,new T(function(){return B(_2B(_3c,_37,_32,_3g.a));}),_3g.b,_3g.c);case 1:if(!B(_e(_3c.b,_3f))){var _3h=B(_2S(_2Y>>1,_3e,_3f,_3b,_39));return new T3(0,new T(function(){return B(_2B(_3c,_37,_32,_3h.a));}),_3h.b,_3h.c);}else{return new T3(0,_32,_1,_34);}break;default:return new T3(0,_32,_1,_34);}}}}},_3i=function(_3j,_3k,_3l,_3m){var _3n=E(_3m);if(!_3n._){var _3o=_3n.c,_3p=_3n.d,_3q=_3n.e,_3r=E(_3n.b);switch(B(_2(_3j,_3r.a))){case 0:return new F(function(){return _1h(_3r,_3o,B(_3i(_3j,_3k,_3l,_3p)),_3q);});break;case 1:switch(B(_2(_3k,_3r.b))){case 0:return new F(function(){return _1h(_3r,_3o,B(_3i(_3j,_3k,_3l,_3p)),_3q);});break;case 1:return new T5(0,_3n.a,E(new T2(0,_3j,_3k)),_3l,E(_3p),E(_3q));default:return new F(function(){return _q(_3r,_3o,_3p,B(_3i(_3j,_3k,_3l,_3q)));});}break;default:return new F(function(){return _q(_3r,_3o,_3p,B(_3i(_3j,_3k,_3l,_3q)));});}}else{return new T5(0,1,E(new T2(0,_3j,_3k)),_3l,E(_0),E(_0));}},_3s=function(_3t,_3u){while(1){var _3v=E(_3u);if(!_3v._){return E(_3t);}else{var _3w=E(_3v.a),_3x=E(_3w.a),_3y=B(_3i(_3x.a,_3x.b,_3w.b,_3t));_3t=_3y;_3u=_3v.b;continue;}}},_3z=function(_3A,_3B,_3C,_3D,_3E){return new F(function(){return _3s(B(_3i(_3B,_3C,_3D,_3A)),_3E);});},_3F=function(_3G,_3H,_3I){var _3J=E(_3H),_3K=E(_3J.a);return new F(function(){return _3s(B(_3i(_3K.a,_3K.b,_3J.b,_3G)),_3I);});},_3L=function(_3M,_3N,_3O){var _3P=E(_3O);if(!_3P._){return E(_3N);}else{var _3Q=E(_3P.a),_3R=_3Q.a,_3S=_3Q.b,_3T=E(_3P.b);if(!_3T._){return new F(function(){return _18(_3R,_3S,_3N);});}else{var _3U=E(_3T.a),_3V=E(_3R),_3W=_3V.a,_3X=_3V.b,_3Y=E(_3U.a),_3Z=_3Y.a,_40=_3Y.b,_41=function(_42){var _43=B(_2S(_3M,_3Z,_40,_3U.b,_3T.b)),_44=_43.a,_45=E(_43.c);if(!_45._){return new F(function(){return _3L(_3M<<1,B(_2B(_3V,_3S,_3N,_44)),_43.b);});}else{return new F(function(){return _3F(B(_2B(_3V,_3S,_3N,_44)),_45.a,_45.b);});}};switch(B(_2(_3W,_3Z))){case 0:return new F(function(){return _41(_);});break;case 1:if(!B(_e(_3X,_40))){return new F(function(){return _41(_);});}else{return new F(function(){return _3z(_3N,_3W,_3X,_3S,_3T);});}break;default:return new F(function(){return _3z(_3N,_3W,_3X,_3S,_3T);});}}}},_46=function(_47,_48,_49,_4a,_4b,_4c){var _4d=E(_4c);if(!_4d._){return new F(function(){return _18(new T2(0,_49,_4a),_4b,_48);});}else{var _4e=E(_4d.a),_4f=E(_4e.a),_4g=_4f.a,_4h=_4f.b,_4i=function(_4j){var _4k=B(_2S(_47,_4g,_4h,_4e.b,_4d.b)),_4l=_4k.a,_4m=E(_4k.c);if(!_4m._){return new F(function(){return _3L(_47<<1,B(_2B(new T2(0,_49,_4a),_4b,_48,_4l)),_4k.b);});}else{return new F(function(){return _3F(B(_2B(new T2(0,_49,_4a),_4b,_48,_4l)),_4m.a,_4m.b);});}};switch(B(_2(_49,_4g))){case 0:return new F(function(){return _4i(_);});break;case 1:if(!B(_e(_4a,_4h))){return new F(function(){return _4i(_);});}else{return new F(function(){return _3z(_48,_49,_4a,_4b,_4d);});}break;default:return new F(function(){return _3z(_48,_49,_4a,_4b,_4d);});}}},_4n=function(_4o){var _4p=E(_4o);if(!_4p._){return new T0(1);}else{var _4q=E(_4p.a),_4r=_4q.a,_4s=_4q.b,_4t=E(_4p.b);if(!_4t._){return new T5(0,1,E(_4r),_4s,E(_0),E(_0));}else{var _4u=_4t.b,_4v=E(_4t.a),_4w=_4v.b,_4x=E(_4r),_4y=E(_4v.a),_4z=_4y.a,_4A=_4y.b;switch(B(_2(_4x.a,_4z))){case 0:return new F(function(){return _46(1,new T5(0,1,E(_4x),_4s,E(_0),E(_0)),_4z,_4A,_4w,_4u);});break;case 1:if(!B(_e(_4x.b,_4A))){return new F(function(){return _46(1,new T5(0,1,E(_4x),_4s,E(_0),E(_0)),_4z,_4A,_4w,_4u);});}else{return new F(function(){return _3z(new T5(0,1,E(_4x),_4s,E(_0),E(_0)),_4z,_4A,_4w,_4u);});}break;default:return new F(function(){return _3z(new T5(0,1,E(_4x),_4s,E(_0),E(_0)),_4z,_4A,_4w,_4u);});}}}},_4B=new T0(1),_4C=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_4D=function(_4E){return new F(function(){return err(_4C);});},_4F=new T(function(){return B(_4D(_));}),_4G=function(_4H,_4I,_4J){var _4K=E(_4I);if(!_4K._){var _4L=_4K.a,_4M=E(_4J);if(!_4M._){var _4N=_4M.a,_4O=_4M.b;if(_4N<=(imul(3,_4L)|0)){return new T4(0,(1+_4L|0)+_4N|0,E(_4H),E(_4K),E(_4M));}else{var _4P=E(_4M.c);if(!_4P._){var _4Q=_4P.a,_4R=_4P.b,_4S=_4P.c,_4T=E(_4M.d);if(!_4T._){var _4U=_4T.a;if(_4Q>=(imul(2,_4U)|0)){var _4V=function(_4W){var _4X=E(_4H),_4Y=E(_4P.d);return (_4Y._==0)?new T4(0,(1+_4L|0)+_4N|0,E(_4R),E(new T4(0,(1+_4L|0)+_4W|0,E(_4X),E(_4K),E(_4S))),E(new T4(0,(1+_4U|0)+_4Y.a|0,E(_4O),E(_4Y),E(_4T)))):new T4(0,(1+_4L|0)+_4N|0,E(_4R),E(new T4(0,(1+_4L|0)+_4W|0,E(_4X),E(_4K),E(_4S))),E(new T4(0,1+_4U|0,E(_4O),E(_4B),E(_4T))));},_4Z=E(_4S);if(!_4Z._){return new F(function(){return _4V(_4Z.a);});}else{return new F(function(){return _4V(0);});}}else{return new T4(0,(1+_4L|0)+_4N|0,E(_4O),E(new T4(0,(1+_4L|0)+_4Q|0,E(_4H),E(_4K),E(_4P))),E(_4T));}}else{return E(_4F);}}else{return E(_4F);}}}else{return new T4(0,1+_4L|0,E(_4H),E(_4K),E(_4B));}}else{var _50=E(_4J);if(!_50._){var _51=_50.a,_52=_50.b,_53=_50.d,_54=E(_50.c);if(!_54._){var _55=_54.a,_56=_54.b,_57=_54.c,_58=E(_53);if(!_58._){var _59=_58.a;if(_55>=(imul(2,_59)|0)){var _5a=function(_5b){var _5c=E(_4H),_5d=E(_54.d);return (_5d._==0)?new T4(0,1+_51|0,E(_56),E(new T4(0,1+_5b|0,E(_5c),E(_4B),E(_57))),E(new T4(0,(1+_59|0)+_5d.a|0,E(_52),E(_5d),E(_58)))):new T4(0,1+_51|0,E(_56),E(new T4(0,1+_5b|0,E(_5c),E(_4B),E(_57))),E(new T4(0,1+_59|0,E(_52),E(_4B),E(_58))));},_5e=E(_57);if(!_5e._){return new F(function(){return _5a(_5e.a);});}else{return new F(function(){return _5a(0);});}}else{return new T4(0,1+_51|0,E(_52),E(new T4(0,1+_55|0,E(_4H),E(_4B),E(_54))),E(_58));}}else{return new T4(0,3,E(_56),E(new T4(0,1,E(_4H),E(_4B),E(_4B))),E(new T4(0,1,E(_52),E(_4B),E(_4B))));}}else{var _5f=E(_53);return (_5f._==0)?new T4(0,3,E(_52),E(new T4(0,1,E(_4H),E(_4B),E(_4B))),E(_5f)):new T4(0,2,E(_4H),E(_4B),E(_50));}}else{return new T4(0,1,E(_4H),E(_4B),E(_4B));}}},_5g=function(_5h){return new T4(0,1,E(_5h),E(_4B),E(_4B));},_5i=function(_5j,_5k){var _5l=E(_5k);if(!_5l._){return new F(function(){return _4G(_5l.b,_5l.c,B(_5i(_5j,_5l.d)));});}else{return new F(function(){return _5g(_5j);});}},_5m=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_5n=function(_5o){return new F(function(){return err(_5m);});},_5p=new T(function(){return B(_5n(_));}),_5q=function(_5r,_5s,_5t){var _5u=E(_5t);if(!_5u._){var _5v=_5u.a,_5w=E(_5s);if(!_5w._){var _5x=_5w.a,_5y=_5w.b;if(_5x<=(imul(3,_5v)|0)){return new T4(0,(1+_5x|0)+_5v|0,E(_5r),E(_5w),E(_5u));}else{var _5z=E(_5w.c);if(!_5z._){var _5A=_5z.a,_5B=E(_5w.d);if(!_5B._){var _5C=_5B.a,_5D=_5B.b,_5E=_5B.c;if(_5C>=(imul(2,_5A)|0)){var _5F=function(_5G){var _5H=E(_5B.d);return (_5H._==0)?new T4(0,(1+_5x|0)+_5v|0,E(_5D),E(new T4(0,(1+_5A|0)+_5G|0,E(_5y),E(_5z),E(_5E))),E(new T4(0,(1+_5v|0)+_5H.a|0,E(_5r),E(_5H),E(_5u)))):new T4(0,(1+_5x|0)+_5v|0,E(_5D),E(new T4(0,(1+_5A|0)+_5G|0,E(_5y),E(_5z),E(_5E))),E(new T4(0,1+_5v|0,E(_5r),E(_4B),E(_5u))));},_5I=E(_5E);if(!_5I._){return new F(function(){return _5F(_5I.a);});}else{return new F(function(){return _5F(0);});}}else{return new T4(0,(1+_5x|0)+_5v|0,E(_5y),E(_5z),E(new T4(0,(1+_5v|0)+_5C|0,E(_5r),E(_5B),E(_5u))));}}else{return E(_5p);}}else{return E(_5p);}}}else{return new T4(0,1+_5v|0,E(_5r),E(_4B),E(_5u));}}else{var _5J=E(_5s);if(!_5J._){var _5K=_5J.a,_5L=_5J.b,_5M=_5J.d,_5N=E(_5J.c);if(!_5N._){var _5O=_5N.a,_5P=E(_5M);if(!_5P._){var _5Q=_5P.a,_5R=_5P.b,_5S=_5P.c;if(_5Q>=(imul(2,_5O)|0)){var _5T=function(_5U){var _5V=E(_5P.d);return (_5V._==0)?new T4(0,1+_5K|0,E(_5R),E(new T4(0,(1+_5O|0)+_5U|0,E(_5L),E(_5N),E(_5S))),E(new T4(0,1+_5V.a|0,E(_5r),E(_5V),E(_4B)))):new T4(0,1+_5K|0,E(_5R),E(new T4(0,(1+_5O|0)+_5U|0,E(_5L),E(_5N),E(_5S))),E(new T4(0,1,E(_5r),E(_4B),E(_4B))));},_5W=E(_5S);if(!_5W._){return new F(function(){return _5T(_5W.a);});}else{return new F(function(){return _5T(0);});}}else{return new T4(0,1+_5K|0,E(_5L),E(_5N),E(new T4(0,1+_5Q|0,E(_5r),E(_5P),E(_4B))));}}else{return new T4(0,3,E(_5L),E(_5N),E(new T4(0,1,E(_5r),E(_4B),E(_4B))));}}else{var _5X=E(_5M);return (_5X._==0)?new T4(0,3,E(_5X.b),E(new T4(0,1,E(_5L),E(_4B),E(_4B))),E(new T4(0,1,E(_5r),E(_4B),E(_4B)))):new T4(0,2,E(_5r),E(_5J),E(_4B));}}else{return new T4(0,1,E(_5r),E(_4B),E(_4B));}}},_5Y=function(_5Z,_60){var _61=E(_60);if(!_61._){return new F(function(){return _5q(_61.b,B(_5Y(_5Z,_61.c)),_61.d);});}else{return new F(function(){return _5g(_5Z);});}},_62=function(_63,_64,_65,_66,_67){return new F(function(){return _4G(_65,_66,B(_5i(_63,_67)));});},_68=function(_69,_6a,_6b,_6c,_6d){return new F(function(){return _5q(_6b,B(_5Y(_69,_6c)),_6d);});},_6e=function(_6f,_6g,_6h,_6i,_6j,_6k){var _6l=E(_6g);if(!_6l._){var _6m=_6l.a,_6n=_6l.b,_6o=_6l.c,_6p=_6l.d;if((imul(3,_6m)|0)>=_6h){if((imul(3,_6h)|0)>=_6m){return new T4(0,(_6m+_6h|0)+1|0,E(_6f),E(_6l),E(new T4(0,_6h,E(_6i),E(_6j),E(_6k))));}else{return new F(function(){return _4G(_6n,_6o,B(_6e(_6f,_6p,_6h,_6i,_6j,_6k)));});}}else{return new F(function(){return _5q(_6i,B(_6q(_6f,_6m,_6n,_6o,_6p,_6j)),_6k);});}}else{return new F(function(){return _68(_6f,_6h,_6i,_6j,_6k);});}},_6q=function(_6r,_6s,_6t,_6u,_6v,_6w){var _6x=E(_6w);if(!_6x._){var _6y=_6x.a,_6z=_6x.b,_6A=_6x.c,_6B=_6x.d;if((imul(3,_6s)|0)>=_6y){if((imul(3,_6y)|0)>=_6s){return new T4(0,(_6s+_6y|0)+1|0,E(_6r),E(new T4(0,_6s,E(_6t),E(_6u),E(_6v))),E(_6x));}else{return new F(function(){return _4G(_6t,_6u,B(_6e(_6r,_6v,_6y,_6z,_6A,_6B)));});}}else{return new F(function(){return _5q(_6z,B(_6q(_6r,_6s,_6t,_6u,_6v,_6A)),_6B);});}}else{return new F(function(){return _62(_6r,_6s,_6t,_6u,_6v);});}},_6C=function(_6D,_6E,_6F){var _6G=E(_6E);if(!_6G._){var _6H=_6G.a,_6I=_6G.b,_6J=_6G.c,_6K=_6G.d,_6L=E(_6F);if(!_6L._){var _6M=_6L.a,_6N=_6L.b,_6O=_6L.c,_6P=_6L.d;if((imul(3,_6H)|0)>=_6M){if((imul(3,_6M)|0)>=_6H){return new T4(0,(_6H+_6M|0)+1|0,E(_6D),E(_6G),E(_6L));}else{return new F(function(){return _4G(_6I,_6J,B(_6e(_6D,_6K,_6M,_6N,_6O,_6P)));});}}else{return new F(function(){return _5q(_6N,B(_6q(_6D,_6H,_6I,_6J,_6K,_6O)),_6P);});}}else{return new F(function(){return _62(_6D,_6H,_6I,_6J,_6K);});}}else{return new F(function(){return _5Y(_6D,_6F);});}},_6Q=function(_6R,_6S,_6T,_6U,_6V){var _6W=E(_6R);if(_6W==1){var _6X=E(_6V);if(!_6X._){return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_1,_1);}else{var _6Y=E(_6X.a);switch(B(_2(_6S,_6Y.a))){case 0:return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_6X,_1);case 1:switch(B(_2(_6T,_6Y.b))){case 0:return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_6X,_1);case 1:return (!B(_e(_6U,_6Y.c)))?new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_6X,_1):new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_1,_6X);default:return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_1,_6X);}break;default:return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_1,_6X);}}}else{var _6Z=B(_6Q(_6W>>1,_6S,_6T,_6U,_6V)),_70=_6Z.a,_71=_6Z.c,_72=E(_6Z.b);if(!_72._){return new T3(0,_70,_1,_71);}else{var _73=_72.a,_74=E(_72.b);if(!_74._){return new T3(0,new T(function(){return B(_5i(_73,_70));}),_1,_71);}else{var _75=_74.b,_76=E(_73),_77=E(_74.a),_78=_77.a,_79=_77.b,_7a=_77.c;switch(B(_2(_76.a,_78))){case 0:var _7b=B(_6Q(_6W>>1,_78,_79,_7a,_75));return new T3(0,new T(function(){return B(_6C(_76,_70,_7b.a));}),_7b.b,_7b.c);case 1:switch(B(_2(_76.b,_79))){case 0:var _7c=B(_6Q(_6W>>1,_78,_79,_7a,_75));return new T3(0,new T(function(){return B(_6C(_76,_70,_7c.a));}),_7c.b,_7c.c);case 1:if(!B(_e(_76.c,_7a))){var _7d=B(_6Q(_6W>>1,_78,_79,_7a,_75));return new T3(0,new T(function(){return B(_6C(_76,_70,_7d.a));}),_7d.b,_7d.c);}else{return new T3(0,_70,_1,_72);}break;default:return new T3(0,_70,_1,_72);}break;default:return new T3(0,_70,_1,_72);}}}}},_7e=function(_7f,_7g,_7h,_7i){var _7j=E(_7i);if(!_7j._){var _7k=_7j.c,_7l=_7j.d,_7m=E(_7j.b);switch(B(_2(_7f,_7m.a))){case 0:return new F(function(){return _5q(_7m,B(_7e(_7f,_7g,_7h,_7k)),_7l);});break;case 1:switch(B(_2(_7g,_7m.b))){case 0:return new F(function(){return _5q(_7m,B(_7e(_7f,_7g,_7h,_7k)),_7l);});break;case 1:switch(B(_2(_7h,_7m.c))){case 0:return new F(function(){return _5q(_7m,B(_7e(_7f,_7g,_7h,_7k)),_7l);});break;case 1:return new T4(0,_7j.a,E(new T3(0,_7f,_7g,_7h)),E(_7k),E(_7l));default:return new F(function(){return _4G(_7m,_7k,B(_7e(_7f,_7g,_7h,_7l)));});}break;default:return new F(function(){return _4G(_7m,_7k,B(_7e(_7f,_7g,_7h,_7l)));});}break;default:return new F(function(){return _4G(_7m,_7k,B(_7e(_7f,_7g,_7h,_7l)));});}}else{return new T4(0,1,E(new T3(0,_7f,_7g,_7h)),E(_4B),E(_4B));}},_7n=function(_7o,_7p){while(1){var _7q=E(_7p);if(!_7q._){return E(_7o);}else{var _7r=E(_7q.a),_7s=B(_7e(_7r.a,_7r.b,_7r.c,_7o));_7o=_7s;_7p=_7q.b;continue;}}},_7t=function(_7u,_7v,_7w,_7x,_7y){return new F(function(){return _7n(B(_7e(_7v,_7w,_7x,_7u)),_7y);});},_7z=function(_7A,_7B,_7C){var _7D=E(_7B);return new F(function(){return _7n(B(_7e(_7D.a,_7D.b,_7D.c,_7A)),_7C);});},_7E=function(_7F,_7G,_7H){var _7I=E(_7H);if(!_7I._){return E(_7G);}else{var _7J=_7I.a,_7K=E(_7I.b);if(!_7K._){return new F(function(){return _5i(_7J,_7G);});}else{var _7L=E(_7J),_7M=_7L.a,_7N=_7L.b,_7O=_7L.c,_7P=E(_7K.a),_7Q=_7P.a,_7R=_7P.b,_7S=_7P.c,_7T=function(_7U){var _7V=B(_6Q(_7F,_7Q,_7R,_7S,_7K.b)),_7W=_7V.a,_7X=E(_7V.c);if(!_7X._){return new F(function(){return _7E(_7F<<1,B(_6C(_7L,_7G,_7W)),_7V.b);});}else{return new F(function(){return _7z(B(_6C(_7L,_7G,_7W)),_7X.a,_7X.b);});}};switch(B(_2(_7M,_7Q))){case 0:return new F(function(){return _7T(_);});break;case 1:switch(B(_2(_7N,_7R))){case 0:return new F(function(){return _7T(_);});break;case 1:if(!B(_e(_7O,_7S))){return new F(function(){return _7T(_);});}else{return new F(function(){return _7t(_7G,_7M,_7N,_7O,_7K);});}break;default:return new F(function(){return _7t(_7G,_7M,_7N,_7O,_7K);});}break;default:return new F(function(){return _7t(_7G,_7M,_7N,_7O,_7K);});}}}},_7Y=function(_7Z,_80,_81,_82,_83,_84){var _85=E(_84);if(!_85._){return new F(function(){return _5i(new T3(0,_81,_82,_83),_80);});}else{var _86=E(_85.a),_87=_86.a,_88=_86.b,_89=_86.c,_8a=function(_8b){var _8c=B(_6Q(_7Z,_87,_88,_89,_85.b)),_8d=_8c.a,_8e=E(_8c.c);if(!_8e._){return new F(function(){return _7E(_7Z<<1,B(_6C(new T3(0,_81,_82,_83),_80,_8d)),_8c.b);});}else{return new F(function(){return _7z(B(_6C(new T3(0,_81,_82,_83),_80,_8d)),_8e.a,_8e.b);});}};switch(B(_2(_81,_87))){case 0:return new F(function(){return _8a(_);});break;case 1:switch(B(_2(_82,_88))){case 0:return new F(function(){return _8a(_);});break;case 1:if(!B(_e(_83,_89))){return new F(function(){return _8a(_);});}else{return new F(function(){return _7t(_80,_81,_82,_83,_85);});}break;default:return new F(function(){return _7t(_80,_81,_82,_83,_85);});}break;default:return new F(function(){return _7t(_80,_81,_82,_83,_85);});}}},_8f=function(_8g){var _8h=E(_8g);if(!_8h._){return new T0(1);}else{var _8i=_8h.a,_8j=E(_8h.b);if(!_8j._){return new T4(0,1,E(_8i),E(_4B),E(_4B));}else{var _8k=_8j.b,_8l=E(_8i),_8m=E(_8j.a),_8n=_8m.a,_8o=_8m.b,_8p=_8m.c;switch(B(_2(_8l.a,_8n))){case 0:return new F(function(){return _7Y(1,new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});break;case 1:switch(B(_2(_8l.b,_8o))){case 0:return new F(function(){return _7Y(1,new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});break;case 1:if(!B(_e(_8l.c,_8p))){return new F(function(){return _7Y(1,new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});}else{return new F(function(){return _7t(new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});}break;default:return new F(function(){return _7t(new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});}break;default:return new F(function(){return _7t(new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});}}}},_8q=function(_8r,_8s,_8t,_8u,_8v){var _8w=E(_8r);if(_8w==1){var _8x=E(_8v);if(!_8x._){return new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_1,_1);}else{var _8y=E(E(_8x.a).a);switch(B(_2(_8s,_8y.a))){case 0:return new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_8x,_1);case 1:return (!B(_e(_8t,_8y.b)))?new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_8x,_1):new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_1,_8x);default:return new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_1,_8x);}}}else{var _8z=B(_8q(_8w>>1,_8s,_8t,_8u,_8v)),_8A=_8z.a,_8B=_8z.c,_8C=E(_8z.b);if(!_8C._){return new T3(0,_8A,_1,_8B);}else{var _8D=E(_8C.a),_8E=_8D.a,_8F=_8D.b,_8G=E(_8C.b);if(!_8G._){return new T3(0,new T(function(){return B(_18(_8E,_8F,_8A));}),_1,_8B);}else{var _8H=_8G.b,_8I=E(_8G.a),_8J=_8I.b,_8K=E(_8E),_8L=E(_8I.a),_8M=_8L.a,_8N=_8L.b;switch(B(_2(_8K.a,_8M))){case 0:var _8O=B(_8q(_8w>>1,_8M,_8N,_8J,_8H));return new T3(0,new T(function(){return B(_2B(_8K,_8F,_8A,_8O.a));}),_8O.b,_8O.c);case 1:if(!B(_e(_8K.b,_8N))){var _8P=B(_8q(_8w>>1,_8M,_8N,_8J,_8H));return new T3(0,new T(function(){return B(_2B(_8K,_8F,_8A,_8P.a));}),_8P.b,_8P.c);}else{return new T3(0,_8A,_1,_8C);}break;default:return new T3(0,_8A,_1,_8C);}}}}},_8Q=function(_8R,_8S,_8T,_8U){var _8V=E(_8U);if(!_8V._){var _8W=_8V.c,_8X=_8V.d,_8Y=_8V.e,_8Z=E(_8V.b);switch(B(_2(_8R,_8Z.a))){case 0:return new F(function(){return _1h(_8Z,_8W,B(_8Q(_8R,_8S,_8T,_8X)),_8Y);});break;case 1:switch(B(_2(_8S,_8Z.b))){case 0:return new F(function(){return _1h(_8Z,_8W,B(_8Q(_8R,_8S,_8T,_8X)),_8Y);});break;case 1:return new T5(0,_8V.a,E(new T2(0,_8R,_8S)),_8T,E(_8X),E(_8Y));default:return new F(function(){return _q(_8Z,_8W,_8X,B(_8Q(_8R,_8S,_8T,_8Y)));});}break;default:return new F(function(){return _q(_8Z,_8W,_8X,B(_8Q(_8R,_8S,_8T,_8Y)));});}}else{return new T5(0,1,E(new T2(0,_8R,_8S)),_8T,E(_0),E(_0));}},_90=function(_91,_92){while(1){var _93=E(_92);if(!_93._){return E(_91);}else{var _94=E(_93.a),_95=E(_94.a),_96=B(_8Q(_95.a,_95.b,_94.b,_91));_91=_96;_92=_93.b;continue;}}},_97=function(_98,_99,_9a,_9b,_9c){return new F(function(){return _90(B(_8Q(_99,_9a,_9b,_98)),_9c);});},_9d=function(_9e,_9f,_9g){var _9h=E(_9f),_9i=E(_9h.a);return new F(function(){return _90(B(_8Q(_9i.a,_9i.b,_9h.b,_9e)),_9g);});},_9j=function(_9k,_9l,_9m){var _9n=E(_9m);if(!_9n._){return E(_9l);}else{var _9o=E(_9n.a),_9p=_9o.a,_9q=_9o.b,_9r=E(_9n.b);if(!_9r._){return new F(function(){return _18(_9p,_9q,_9l);});}else{var _9s=E(_9r.a),_9t=E(_9p),_9u=_9t.a,_9v=_9t.b,_9w=E(_9s.a),_9x=_9w.a,_9y=_9w.b,_9z=function(_9A){var _9B=B(_8q(_9k,_9x,_9y,_9s.b,_9r.b)),_9C=_9B.a,_9D=E(_9B.c);if(!_9D._){return new F(function(){return _9j(_9k<<1,B(_2B(_9t,_9q,_9l,_9C)),_9B.b);});}else{return new F(function(){return _9d(B(_2B(_9t,_9q,_9l,_9C)),_9D.a,_9D.b);});}};switch(B(_2(_9u,_9x))){case 0:return new F(function(){return _9z(_);});break;case 1:if(!B(_e(_9v,_9y))){return new F(function(){return _9z(_);});}else{return new F(function(){return _97(_9l,_9u,_9v,_9q,_9r);});}break;default:return new F(function(){return _97(_9l,_9u,_9v,_9q,_9r);});}}}},_9E=function(_9F,_9G,_9H,_9I,_9J,_9K){var _9L=E(_9K);if(!_9L._){return new F(function(){return _18(new T2(0,_9H,_9I),_9J,_9G);});}else{var _9M=E(_9L.a),_9N=E(_9M.a),_9O=_9N.a,_9P=_9N.b,_9Q=function(_9R){var _9S=B(_8q(_9F,_9O,_9P,_9M.b,_9L.b)),_9T=_9S.a,_9U=E(_9S.c);if(!_9U._){return new F(function(){return _9j(_9F<<1,B(_2B(new T2(0,_9H,_9I),_9J,_9G,_9T)),_9S.b);});}else{return new F(function(){return _9d(B(_2B(new T2(0,_9H,_9I),_9J,_9G,_9T)),_9U.a,_9U.b);});}};switch(B(_2(_9H,_9O))){case 0:return new F(function(){return _9Q(_);});break;case 1:if(!B(_e(_9I,_9P))){return new F(function(){return _9Q(_);});}else{return new F(function(){return _97(_9G,_9H,_9I,_9J,_9L);});}break;default:return new F(function(){return _97(_9G,_9H,_9I,_9J,_9L);});}}},_9V=function(_9W){var _9X=E(_9W);if(!_9X._){return new T0(1);}else{var _9Y=E(_9X.a),_9Z=_9Y.a,_a0=_9Y.b,_a1=E(_9X.b);if(!_a1._){return new T5(0,1,E(_9Z),_a0,E(_0),E(_0));}else{var _a2=_a1.b,_a3=E(_a1.a),_a4=_a3.b,_a5=E(_9Z),_a6=E(_a3.a),_a7=_a6.a,_a8=_a6.b;switch(B(_2(_a5.a,_a7))){case 0:return new F(function(){return _9E(1,new T5(0,1,E(_a5),_a0,E(_0),E(_0)),_a7,_a8,_a4,_a2);});break;case 1:if(!B(_e(_a5.b,_a8))){return new F(function(){return _9E(1,new T5(0,1,E(_a5),_a0,E(_0),E(_0)),_a7,_a8,_a4,_a2);});}else{return new F(function(){return _97(new T5(0,1,E(_a5),_a0,E(_0),E(_0)),_a7,_a8,_a4,_a2);});}break;default:return new F(function(){return _97(new T5(0,1,E(_a5),_a0,E(_0),E(_0)),_a7,_a8,_a4,_a2);});}}}},_a9=function(_aa,_ab,_ac,_ad,_ae,_af){var _ag=E(_aa);if(_ag==1){var _ah=E(_af);if(!_ah._){return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_1);}else{var _ai=E(_ah.a);switch(B(_2(_ab,_ai.a))){case 0:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_ah,_1);case 1:switch(B(_2(_ac,_ai.b))){case 0:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_ah,_1);case 1:switch(B(_2(_ad,_ai.c))){case 0:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_ah,_1);case 1:return (!B(_e(_ae,_ai.d)))?new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_ah,_1):new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_ah);default:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_ah);}break;default:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_ah);}break;default:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_ah);}}}else{var _aj=B(_a9(_ag>>1,_ab,_ac,_ad,_ae,_af)),_ak=_aj.a,_al=_aj.c,_am=E(_aj.b);if(!_am._){return new T3(0,_ak,_1,_al);}else{var _an=_am.a,_ao=E(_am.b);if(!_ao._){return new T3(0,new T(function(){return B(_5i(_an,_ak));}),_1,_al);}else{var _ap=_ao.b,_aq=E(_an),_ar=E(_ao.a),_as=_ar.a,_at=_ar.b,_au=_ar.c,_av=_ar.d;switch(B(_2(_aq.a,_as))){case 0:var _aw=B(_a9(_ag>>1,_as,_at,_au,_av,_ap));return new T3(0,new T(function(){return B(_6C(_aq,_ak,_aw.a));}),_aw.b,_aw.c);case 1:switch(B(_2(_aq.b,_at))){case 0:var _ax=B(_a9(_ag>>1,_as,_at,_au,_av,_ap));return new T3(0,new T(function(){return B(_6C(_aq,_ak,_ax.a));}),_ax.b,_ax.c);case 1:switch(B(_2(_aq.c,_au))){case 0:var _ay=B(_a9(_ag>>1,_as,_at,_au,_av,_ap));return new T3(0,new T(function(){return B(_6C(_aq,_ak,_ay.a));}),_ay.b,_ay.c);case 1:if(!B(_e(_aq.d,_av))){var _az=B(_a9(_ag>>1,_as,_at,_au,_av,_ap));return new T3(0,new T(function(){return B(_6C(_aq,_ak,_az.a));}),_az.b,_az.c);}else{return new T3(0,_ak,_1,_am);}break;default:return new T3(0,_ak,_1,_am);}break;default:return new T3(0,_ak,_1,_am);}break;default:return new T3(0,_ak,_1,_am);}}}}},_aA=function(_aB,_aC,_aD,_aE,_aF){var _aG=E(_aF);if(!_aG._){var _aH=_aG.c,_aI=_aG.d,_aJ=E(_aG.b);switch(B(_2(_aB,_aJ.a))){case 0:return new F(function(){return _5q(_aJ,B(_aA(_aB,_aC,_aD,_aE,_aH)),_aI);});break;case 1:switch(B(_2(_aC,_aJ.b))){case 0:return new F(function(){return _5q(_aJ,B(_aA(_aB,_aC,_aD,_aE,_aH)),_aI);});break;case 1:switch(B(_2(_aD,_aJ.c))){case 0:return new F(function(){return _5q(_aJ,B(_aA(_aB,_aC,_aD,_aE,_aH)),_aI);});break;case 1:switch(B(_2(_aE,_aJ.d))){case 0:return new F(function(){return _5q(_aJ,B(_aA(_aB,_aC,_aD,_aE,_aH)),_aI);});break;case 1:return new T4(0,_aG.a,E(new T4(0,_aB,_aC,_aD,_aE)),E(_aH),E(_aI));default:return new F(function(){return _4G(_aJ,_aH,B(_aA(_aB,_aC,_aD,_aE,_aI)));});}break;default:return new F(function(){return _4G(_aJ,_aH,B(_aA(_aB,_aC,_aD,_aE,_aI)));});}break;default:return new F(function(){return _4G(_aJ,_aH,B(_aA(_aB,_aC,_aD,_aE,_aI)));});}break;default:return new F(function(){return _4G(_aJ,_aH,B(_aA(_aB,_aC,_aD,_aE,_aI)));});}}else{return new T4(0,1,E(new T4(0,_aB,_aC,_aD,_aE)),E(_4B),E(_4B));}},_aK=function(_aL,_aM){while(1){var _aN=E(_aM);if(!_aN._){return E(_aL);}else{var _aO=E(_aN.a),_aP=B(_aA(_aO.a,_aO.b,_aO.c,_aO.d,_aL));_aL=_aP;_aM=_aN.b;continue;}}},_aQ=function(_aR,_aS,_aT,_aU,_aV,_aW){return new F(function(){return _aK(B(_aA(_aS,_aT,_aU,_aV,_aR)),_aW);});},_aX=function(_aY,_aZ,_b0){var _b1=E(_aZ);return new F(function(){return _aK(B(_aA(_b1.a,_b1.b,_b1.c,_b1.d,_aY)),_b0);});},_b2=function(_b3,_b4,_b5){var _b6=E(_b5);if(!_b6._){return E(_b4);}else{var _b7=_b6.a,_b8=E(_b6.b);if(!_b8._){return new F(function(){return _5i(_b7,_b4);});}else{var _b9=E(_b7),_ba=_b9.a,_bb=_b9.b,_bc=_b9.c,_bd=_b9.d,_be=E(_b8.a),_bf=_be.a,_bg=_be.b,_bh=_be.c,_bi=_be.d,_bj=function(_bk){var _bl=B(_a9(_b3,_bf,_bg,_bh,_bi,_b8.b)),_bm=_bl.a,_bn=E(_bl.c);if(!_bn._){return new F(function(){return _b2(_b3<<1,B(_6C(_b9,_b4,_bm)),_bl.b);});}else{return new F(function(){return _aX(B(_6C(_b9,_b4,_bm)),_bn.a,_bn.b);});}};switch(B(_2(_ba,_bf))){case 0:return new F(function(){return _bj(_);});break;case 1:switch(B(_2(_bb,_bg))){case 0:return new F(function(){return _bj(_);});break;case 1:switch(B(_2(_bc,_bh))){case 0:return new F(function(){return _bj(_);});break;case 1:if(!B(_e(_bd,_bi))){return new F(function(){return _bj(_);});}else{return new F(function(){return _aQ(_b4,_ba,_bb,_bc,_bd,_b8);});}break;default:return new F(function(){return _aQ(_b4,_ba,_bb,_bc,_bd,_b8);});}break;default:return new F(function(){return _aQ(_b4,_ba,_bb,_bc,_bd,_b8);});}break;default:return new F(function(){return _aQ(_b4,_ba,_bb,_bc,_bd,_b8);});}}}},_bo=function(_bp,_bq,_br,_bs,_bt,_bu,_bv){var _bw=E(_bv);if(!_bw._){return new F(function(){return _5i(new T4(0,_br,_bs,_bt,_bu),_bq);});}else{var _bx=E(_bw.a),_by=_bx.a,_bz=_bx.b,_bA=_bx.c,_bB=_bx.d,_bC=function(_bD){var _bE=B(_a9(_bp,_by,_bz,_bA,_bB,_bw.b)),_bF=_bE.a,_bG=E(_bE.c);if(!_bG._){return new F(function(){return _b2(_bp<<1,B(_6C(new T4(0,_br,_bs,_bt,_bu),_bq,_bF)),_bE.b);});}else{return new F(function(){return _aX(B(_6C(new T4(0,_br,_bs,_bt,_bu),_bq,_bF)),_bG.a,_bG.b);});}};switch(B(_2(_br,_by))){case 0:return new F(function(){return _bC(_);});break;case 1:switch(B(_2(_bs,_bz))){case 0:return new F(function(){return _bC(_);});break;case 1:switch(B(_2(_bt,_bA))){case 0:return new F(function(){return _bC(_);});break;case 1:if(!B(_e(_bu,_bB))){return new F(function(){return _bC(_);});}else{return new F(function(){return _aQ(_bq,_br,_bs,_bt,_bu,_bw);});}break;default:return new F(function(){return _aQ(_bq,_br,_bs,_bt,_bu,_bw);});}break;default:return new F(function(){return _aQ(_bq,_br,_bs,_bt,_bu,_bw);});}break;default:return new F(function(){return _aQ(_bq,_br,_bs,_bt,_bu,_bw);});}}},_bH=function(_bI){var _bJ=E(_bI);if(!_bJ._){return new T0(1);}else{var _bK=_bJ.a,_bL=E(_bJ.b);if(!_bL._){return new T4(0,1,E(_bK),E(_4B),E(_4B));}else{var _bM=_bL.b,_bN=E(_bK),_bO=E(_bL.a),_bP=_bO.a,_bQ=_bO.b,_bR=_bO.c,_bS=_bO.d;switch(B(_2(_bN.a,_bP))){case 0:return new F(function(){return _bo(1,new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});break;case 1:switch(B(_2(_bN.b,_bQ))){case 0:return new F(function(){return _bo(1,new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});break;case 1:switch(B(_2(_bN.c,_bR))){case 0:return new F(function(){return _bo(1,new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});break;case 1:if(!B(_e(_bN.d,_bS))){return new F(function(){return _bo(1,new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}else{return new F(function(){return _aQ(new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}break;default:return new F(function(){return _aQ(new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}break;default:return new F(function(){return _aQ(new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}break;default:return new F(function(){return _aQ(new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}}}},_bT=0,_bU=function(_bV){var _bW=E(_bV);if(!_bW._){return E(_bW.a);}else{return new F(function(){return I_toInt(_bW.a);});}},_bX=function(_bY){return new F(function(){return _bU(_bY);});},_bZ=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_c0=new T(function(){return B(err(_bZ));}),_c1=function(_c2,_c3){while(1){var _c4=B((function(_c5,_c6){var _c7=E(_c6);if(!_c7._){_c2=new T2(1,new T2(0,_c7.b,_c7.c),new T(function(){return B(_c1(_c5,_c7.e));}));_c3=_c7.d;return __continue;}else{return E(_c5);}})(_c2,_c3));if(_c4!=__continue){return _c4;}}},_c8=44,_c9=function(_ca,_cb,_cc){return new F(function(){return A1(_ca,new T2(1,_c8,new T(function(){return B(A1(_cb,_cc));})));});},_cd=new T(function(){return B(unCStr("CC "));}),_ce=function(_cf,_cg){var _ch=E(_cf);return (_ch._==0)?E(_cg):new T2(1,_ch.a,new T(function(){return B(_ce(_ch.b,_cg));}));},_ci=function(_cj){while(1){var _ck=E(_cj);if(!_ck._){_cj=new T1(1,I_fromInt(_ck.a));continue;}else{return new F(function(){return I_toString(_ck.a);});}}},_cl=function(_cm,_cn){return new F(function(){return _ce(fromJSStr(B(_ci(_cm))),_cn);});},_co=function(_cp,_cq){var _cr=E(_cp);if(!_cr._){var _cs=_cr.a,_ct=E(_cq);return (_ct._==0)?_cs<_ct.a:I_compareInt(_ct.a,_cs)>0;}else{var _cu=_cr.a,_cv=E(_cq);return (_cv._==0)?I_compareInt(_cu,_cv.a)<0:I_compare(_cu,_cv.a)<0;}},_cw=41,_cx=40,_cy=new T1(0,0),_cz=function(_cA,_cB,_cC){if(_cA<=6){return new F(function(){return _cl(_cB,_cC);});}else{if(!B(_co(_cB,_cy))){return new F(function(){return _cl(_cB,_cC);});}else{return new T2(1,_cx,new T(function(){return B(_ce(fromJSStr(B(_ci(_cB))),new T2(1,_cw,_cC)));}));}}},_cD=new T(function(){return B(unCStr("IdentCC "));}),_cE=function(_cF,_cG,_cH){if(_cF<11){return new F(function(){return _ce(_cD,new T(function(){return B(_cz(11,_cG,_cH));},1));});}else{var _cI=new T(function(){return B(_ce(_cD,new T(function(){return B(_cz(11,_cG,new T2(1,_cw,_cH)));},1)));});return new T2(1,_cx,_cI);}},_cJ=32,_cK=function(_cL,_cM,_cN,_cO,_cP,_cQ){var _cR=function(_cS){var _cT=new T(function(){var _cU=new T(function(){return B(_cz(11,_cO,new T2(1,_cJ,new T(function(){return B(_cz(11,_cP,_cS));}))));});return B(_cz(11,_cN,new T2(1,_cJ,_cU)));});return new F(function(){return _cE(11,_cM,new T2(1,_cJ,_cT));});};if(_cL<11){return new F(function(){return _ce(_cd,new T(function(){return B(_cR(_cQ));},1));});}else{var _cV=new T(function(){return B(_ce(_cd,new T(function(){return B(_cR(new T2(1,_cw,_cQ)));},1)));});return new T2(1,_cx,_cV);}},_cW=function(_cX,_cY){var _cZ=E(_cX);return new F(function(){return _cK(0,_cZ.a,_cZ.b,_cZ.c,_cZ.d,_cY);});},_d0=new T(function(){return B(unCStr("RC "));}),_d1=function(_d2,_d3,_d4,_d5,_d6){var _d7=function(_d8){var _d9=new T(function(){var _da=new T(function(){return B(_cz(11,_d4,new T2(1,_cJ,new T(function(){return B(_cz(11,_d5,_d8));}))));});return B(_cE(11,_d3,new T2(1,_cJ,_da)));},1);return new F(function(){return _ce(_d0,_d9);});};if(_d2<11){return new F(function(){return _d7(_d6);});}else{return new T2(1,_cx,new T(function(){return B(_d7(new T2(1,_cw,_d6)));}));}},_db=function(_dc,_dd){var _de=E(_dc);return new F(function(){return _d1(0,_de.a,_de.b,_de.c,_dd);});},_df=new T(function(){return B(unCStr("IdentPay "));}),_dg=function(_dh,_di,_dj){if(_dh<11){return new F(function(){return _ce(_df,new T(function(){return B(_cz(11,_di,_dj));},1));});}else{var _dk=new T(function(){return B(_ce(_df,new T(function(){return B(_cz(11,_di,new T2(1,_cw,_dj)));},1)));});return new T2(1,_cx,_dk);}},_dl=new T(function(){return B(unCStr(": empty list"));}),_dm=new T(function(){return B(unCStr("Prelude."));}),_dn=function(_do){return new F(function(){return err(B(_ce(_dm,new T(function(){return B(_ce(_do,_dl));},1))));});},_dp=new T(function(){return B(unCStr("foldr1"));}),_dq=new T(function(){return B(_dn(_dp));}),_dr=function(_ds,_dt){var _du=E(_dt);if(!_du._){return E(_dq);}else{var _dv=_du.a,_dw=E(_du.b);if(!_dw._){return E(_dv);}else{return new F(function(){return A2(_ds,_dv,new T(function(){return B(_dr(_ds,_dw));}));});}}},_dx=function(_dy,_dz,_dA){var _dB=new T(function(){var _dC=function(_dD){var _dE=E(_dy),_dF=new T(function(){return B(A3(_dr,_c9,new T2(1,function(_dG){return new F(function(){return _dg(0,_dE.a,_dG);});},new T2(1,function(_dH){return new F(function(){return _cz(0,_dE.b,_dH);});},_1)),new T2(1,_cw,_dD)));});return new T2(1,_cx,_dF);};return B(A3(_dr,_c9,new T2(1,_dC,new T2(1,function(_dI){return new F(function(){return _cz(0,_dz,_dI);});},_1)),new T2(1,_cw,_dA)));});return new T2(0,_cx,_dB);},_dJ=function(_dK,_dL){var _dM=E(_dK),_dN=B(_dx(_dM.a,_dM.b,_dL));return new T2(1,_dN.a,_dN.b);},_dO=93,_dP=91,_dQ=function(_dR,_dS,_dT){var _dU=E(_dS);if(!_dU._){return new F(function(){return unAppCStr("[]",_dT);});}else{var _dV=new T(function(){var _dW=new T(function(){var _dX=function(_dY){var _dZ=E(_dY);if(!_dZ._){return E(new T2(1,_dO,_dT));}else{var _e0=new T(function(){return B(A2(_dR,_dZ.a,new T(function(){return B(_dX(_dZ.b));})));});return new T2(1,_c8,_e0);}};return B(_dX(_dU.b));});return B(A2(_dR,_dU.a,_dW));});return new T2(1,_dP,_dV);}},_e1=function(_e2,_e3){return new F(function(){return _dQ(_dJ,_e2,_e3);});},_e4=new T(function(){return B(unCStr("IdentChoice "));}),_e5=function(_e6,_e7,_e8){if(_e6<11){return new F(function(){return _ce(_e4,new T(function(){return B(_cz(11,_e7,_e8));},1));});}else{var _e9=new T(function(){return B(_ce(_e4,new T(function(){return B(_cz(11,_e7,new T2(1,_cw,_e8)));},1)));});return new T2(1,_cx,_e9);}},_ea=function(_eb,_ec,_ed){var _ee=new T(function(){var _ef=function(_eg){var _eh=E(_eb),_ei=new T(function(){return B(A3(_dr,_c9,new T2(1,function(_ej){return new F(function(){return _e5(0,_eh.a,_ej);});},new T2(1,function(_ek){return new F(function(){return _cz(0,_eh.b,_ek);});},_1)),new T2(1,_cw,_eg)));});return new T2(1,_cx,_ei);};return B(A3(_dr,_c9,new T2(1,_ef,new T2(1,function(_el){return new F(function(){return _cz(0,_ec,_el);});},_1)),new T2(1,_cw,_ed)));});return new T2(0,_cx,_ee);},_em=function(_en,_eo){var _ep=E(_en),_eq=B(_ea(_ep.a,_ep.b,_eo));return new T2(1,_eq.a,_eq.b);},_er=function(_es,_et){return new F(function(){return _dQ(_em,_es,_et);});},_eu=new T2(1,_cw,_1),_ev=function(_ew,_ex){while(1){var _ey=B((function(_ez,_eA){var _eB=E(_eA);if(!_eB._){_ew=new T2(1,_eB.b,new T(function(){return B(_ev(_ez,_eB.d));}));_ex=_eB.c;return __continue;}else{return E(_ez);}})(_ew,_ex));if(_ey!=__continue){return _ey;}}},_eC=function(_eD,_eE,_eF,_eG){var _eH=new T(function(){var _eI=new T(function(){return B(_c1(_1,_eG));}),_eJ=new T(function(){return B(_c1(_1,_eF));}),_eK=new T(function(){return B(_ev(_1,_eE));}),_eL=new T(function(){return B(_ev(_1,_eD));});return B(A3(_dr,_c9,new T2(1,function(_eM){return new F(function(){return _dQ(_cW,_eL,_eM);});},new T2(1,function(_eN){return new F(function(){return _dQ(_db,_eK,_eN);});},new T2(1,function(_eO){return new F(function(){return _e1(_eJ,_eO);});},new T2(1,function(_eP){return new F(function(){return _er(_eI,_eP);});},_1)))),_eu));});return new T2(0,_cx,_eH);},_eQ=new T(function(){return B(err(_bZ));}),_eR=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_eS=new T(function(){return B(err(_eR));}),_eT=new T0(2),_eU=function(_eV){return new T2(3,_eV,_eT);},_eW=new T(function(){return B(unCStr("base"));}),_eX=new T(function(){return B(unCStr("Control.Exception.Base"));}),_eY=new T(function(){return B(unCStr("PatternMatchFail"));}),_eZ=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_eW,_eX,_eY),_f0=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_eZ,_1,_1),_f1=function(_f2){return E(_f0);},_f3=function(_f4){return E(E(_f4).a);},_f5=function(_f6,_f7,_f8){var _f9=B(A1(_f6,_)),_fa=B(A1(_f7,_)),_fb=hs_eqWord64(_f9.a,_fa.a);if(!_fb){return __Z;}else{var _fc=hs_eqWord64(_f9.b,_fa.b);return (!_fc)?__Z:new T1(1,_f8);}},_fd=function(_fe){var _ff=E(_fe);return new F(function(){return _f5(B(_f3(_ff.a)),_f1,_ff.b);});},_fg=function(_fh){return E(E(_fh).a);},_fi=function(_fj){return new T2(0,_fk,_fj);},_fl=function(_fm,_fn){return new F(function(){return _ce(E(_fm).a,_fn);});},_fo=function(_fp,_fq){return new F(function(){return _dQ(_fl,_fp,_fq);});},_fr=function(_fs,_ft,_fu){return new F(function(){return _ce(E(_ft).a,_fu);});},_fv=new T3(0,_fr,_fg,_fo),_fk=new T(function(){return new T5(0,_f1,_fv,_fi,_fd,_fg);}),_fw=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_fx=function(_fy){return E(E(_fy).c);},_fz=function(_fA,_fB){return new F(function(){return die(new T(function(){return B(A2(_fx,_fB,_fA));}));});},_fC=function(_fD,_fE){return new F(function(){return _fz(_fD,_fE);});},_fF=function(_fG,_fH){var _fI=E(_fH);if(!_fI._){return new T2(0,_1,_1);}else{var _fJ=_fI.a;if(!B(A1(_fG,_fJ))){return new T2(0,_1,_fI);}else{var _fK=new T(function(){var _fL=B(_fF(_fG,_fI.b));return new T2(0,_fL.a,_fL.b);});return new T2(0,new T2(1,_fJ,new T(function(){return E(E(_fK).a);})),new T(function(){return E(E(_fK).b);}));}}},_fM=32,_fN=new T(function(){return B(unCStr("\n"));}),_fO=function(_fP){return (E(_fP)==124)?false:true;},_fQ=function(_fR,_fS){var _fT=B(_fF(_fO,B(unCStr(_fR)))),_fU=_fT.a,_fV=function(_fW,_fX){var _fY=new T(function(){var _fZ=new T(function(){return B(_ce(_fS,new T(function(){return B(_ce(_fX,_fN));},1)));});return B(unAppCStr(": ",_fZ));},1);return new F(function(){return _ce(_fW,_fY);});},_g0=E(_fT.b);if(!_g0._){return new F(function(){return _fV(_fU,_1);});}else{if(E(_g0.a)==124){return new F(function(){return _fV(_fU,new T2(1,_fM,_g0.b));});}else{return new F(function(){return _fV(_fU,_1);});}}},_g1=function(_g2){return new F(function(){return _fC(new T1(0,new T(function(){return B(_fQ(_g2,_fw));})),_fk);});},_g3=new T(function(){return B(_g1("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_g4=function(_g5,_g6){while(1){var _g7=B((function(_g8,_g9){var _ga=E(_g8);switch(_ga._){case 0:var _gb=E(_g9);if(!_gb._){return __Z;}else{_g5=B(A1(_ga.a,_gb.a));_g6=_gb.b;return __continue;}break;case 1:var _gc=B(A1(_ga.a,_g9)),_gd=_g9;_g5=_gc;_g6=_gd;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_ga.a,_g9),new T(function(){return B(_g4(_ga.b,_g9));}));default:return E(_ga.a);}})(_g5,_g6));if(_g7!=__continue){return _g7;}}},_ge=function(_gf,_gg){var _gh=function(_gi){var _gj=E(_gg);if(_gj._==3){return new T2(3,_gj.a,new T(function(){return B(_ge(_gf,_gj.b));}));}else{var _gk=E(_gf);if(_gk._==2){return E(_gj);}else{var _gl=E(_gj);if(_gl._==2){return E(_gk);}else{var _gm=function(_gn){var _go=E(_gl);if(_go._==4){var _gp=function(_gq){return new T1(4,new T(function(){return B(_ce(B(_g4(_gk,_gq)),_go.a));}));};return new T1(1,_gp);}else{var _gr=E(_gk);if(_gr._==1){var _gs=_gr.a,_gt=E(_go);if(!_gt._){return new T1(1,function(_gu){return new F(function(){return _ge(B(A1(_gs,_gu)),_gt);});});}else{var _gv=function(_gw){return new F(function(){return _ge(B(A1(_gs,_gw)),new T(function(){return B(A1(_gt.a,_gw));}));});};return new T1(1,_gv);}}else{var _gx=E(_go);if(!_gx._){return E(_g3);}else{var _gy=function(_gz){return new F(function(){return _ge(_gr,new T(function(){return B(A1(_gx.a,_gz));}));});};return new T1(1,_gy);}}}},_gA=E(_gk);switch(_gA._){case 1:var _gB=E(_gl);if(_gB._==4){var _gC=function(_gD){return new T1(4,new T(function(){return B(_ce(B(_g4(B(A1(_gA.a,_gD)),_gD)),_gB.a));}));};return new T1(1,_gC);}else{return new F(function(){return _gm(_);});}break;case 4:var _gE=_gA.a,_gF=E(_gl);switch(_gF._){case 0:var _gG=function(_gH){var _gI=new T(function(){return B(_ce(_gE,new T(function(){return B(_g4(_gF,_gH));},1)));});return new T1(4,_gI);};return new T1(1,_gG);case 1:var _gJ=function(_gK){var _gL=new T(function(){return B(_ce(_gE,new T(function(){return B(_g4(B(A1(_gF.a,_gK)),_gK));},1)));});return new T1(4,_gL);};return new T1(1,_gJ);default:return new T1(4,new T(function(){return B(_ce(_gE,_gF.a));}));}break;default:return new F(function(){return _gm(_);});}}}}},_gM=E(_gf);switch(_gM._){case 0:var _gN=E(_gg);if(!_gN._){var _gO=function(_gP){return new F(function(){return _ge(B(A1(_gM.a,_gP)),new T(function(){return B(A1(_gN.a,_gP));}));});};return new T1(0,_gO);}else{return new F(function(){return _gh(_);});}break;case 3:return new T2(3,_gM.a,new T(function(){return B(_ge(_gM.b,_gg));}));default:return new F(function(){return _gh(_);});}},_gQ=new T(function(){return B(unCStr("("));}),_gR=new T(function(){return B(unCStr(")"));}),_gS=function(_gT,_gU){while(1){var _gV=E(_gT);if(!_gV._){return (E(_gU)._==0)?true:false;}else{var _gW=E(_gU);if(!_gW._){return false;}else{if(E(_gV.a)!=E(_gW.a)){return false;}else{_gT=_gV.b;_gU=_gW.b;continue;}}}}},_gX=function(_gY,_gZ){return E(_gY)!=E(_gZ);},_h0=function(_h1,_h2){return E(_h1)==E(_h2);},_h3=new T2(0,_h0,_gX),_h4=function(_h5,_h6){while(1){var _h7=E(_h5);if(!_h7._){return (E(_h6)._==0)?true:false;}else{var _h8=E(_h6);if(!_h8._){return false;}else{if(E(_h7.a)!=E(_h8.a)){return false;}else{_h5=_h7.b;_h6=_h8.b;continue;}}}}},_h9=function(_ha,_hb){return (!B(_h4(_ha,_hb)))?true:false;},_hc=new T2(0,_h4,_h9),_hd=function(_he,_hf){var _hg=E(_he);switch(_hg._){case 0:return new T1(0,function(_hh){return new F(function(){return _hd(B(A1(_hg.a,_hh)),_hf);});});case 1:return new T1(1,function(_hi){return new F(function(){return _hd(B(A1(_hg.a,_hi)),_hf);});});case 2:return new T0(2);case 3:return new F(function(){return _ge(B(A1(_hf,_hg.a)),new T(function(){return B(_hd(_hg.b,_hf));}));});break;default:var _hj=function(_hk){var _hl=E(_hk);if(!_hl._){return __Z;}else{var _hm=E(_hl.a);return new F(function(){return _ce(B(_g4(B(A1(_hf,_hm.a)),_hm.b)),new T(function(){return B(_hj(_hl.b));},1));});}},_hn=B(_hj(_hg.a));return (_hn._==0)?new T0(2):new T1(4,_hn);}},_ho=function(_hp,_hq){var _hr=E(_hp);if(!_hr){return new F(function(){return A1(_hq,_bT);});}else{var _hs=new T(function(){return B(_ho(_hr-1|0,_hq));});return new T1(0,function(_ht){return E(_hs);});}},_hu=function(_hv,_hw,_hx){var _hy=new T(function(){return B(A1(_hv,_eU));}),_hz=function(_hA,_hB,_hC,_hD){while(1){var _hE=B((function(_hF,_hG,_hH,_hI){var _hJ=E(_hF);switch(_hJ._){case 0:var _hK=E(_hG);if(!_hK._){return new F(function(){return A1(_hw,_hI);});}else{var _hL=_hH+1|0,_hM=_hI;_hA=B(A1(_hJ.a,_hK.a));_hB=_hK.b;_hC=_hL;_hD=_hM;return __continue;}break;case 1:var _hN=B(A1(_hJ.a,_hG)),_hO=_hG,_hL=_hH,_hM=_hI;_hA=_hN;_hB=_hO;_hC=_hL;_hD=_hM;return __continue;case 2:return new F(function(){return A1(_hw,_hI);});break;case 3:var _hP=new T(function(){return B(_hd(_hJ,_hI));});return new F(function(){return _ho(_hH,function(_hQ){return E(_hP);});});break;default:return new F(function(){return _hd(_hJ,_hI);});}})(_hA,_hB,_hC,_hD));if(_hE!=__continue){return _hE;}}};return function(_hR){return new F(function(){return _hz(_hy,_hR,0,_hx);});};},_hS=function(_hT){return new F(function(){return A1(_hT,_1);});},_hU=function(_hV,_hW){var _hX=function(_hY){var _hZ=E(_hY);if(!_hZ._){return E(_hS);}else{var _i0=_hZ.a;if(!B(A1(_hV,_i0))){return E(_hS);}else{var _i1=new T(function(){return B(_hX(_hZ.b));}),_i2=function(_i3){var _i4=new T(function(){return B(A1(_i1,function(_i5){return new F(function(){return A1(_i3,new T2(1,_i0,_i5));});}));});return new T1(0,function(_i6){return E(_i4);});};return E(_i2);}}};return function(_i7){return new F(function(){return A2(_hX,_i7,_hW);});};},_i8=new T0(6),_i9=function(_ia){return E(_ia);},_ib=new T(function(){return B(unCStr("valDig: Bad base"));}),_ic=new T(function(){return B(err(_ib));}),_id=function(_ie,_if){var _ig=function(_ih,_ii){var _ij=E(_ih);if(!_ij._){var _ik=new T(function(){return B(A1(_ii,_1));});return function(_il){return new F(function(){return A1(_il,_ik);});};}else{var _im=E(_ij.a),_in=function(_io){var _ip=new T(function(){return B(_ig(_ij.b,function(_iq){return new F(function(){return A1(_ii,new T2(1,_io,_iq));});}));}),_ir=function(_is){var _it=new T(function(){return B(A1(_ip,_is));});return new T1(0,function(_iu){return E(_it);});};return E(_ir);};switch(E(_ie)){case 8:if(48>_im){var _iv=new T(function(){return B(A1(_ii,_1));});return function(_iw){return new F(function(){return A1(_iw,_iv);});};}else{if(_im>55){var _ix=new T(function(){return B(A1(_ii,_1));});return function(_iy){return new F(function(){return A1(_iy,_ix);});};}else{return new F(function(){return _in(_im-48|0);});}}break;case 10:if(48>_im){var _iz=new T(function(){return B(A1(_ii,_1));});return function(_iA){return new F(function(){return A1(_iA,_iz);});};}else{if(_im>57){var _iB=new T(function(){return B(A1(_ii,_1));});return function(_iC){return new F(function(){return A1(_iC,_iB);});};}else{return new F(function(){return _in(_im-48|0);});}}break;case 16:if(48>_im){if(97>_im){if(65>_im){var _iD=new T(function(){return B(A1(_ii,_1));});return function(_iE){return new F(function(){return A1(_iE,_iD);});};}else{if(_im>70){var _iF=new T(function(){return B(A1(_ii,_1));});return function(_iG){return new F(function(){return A1(_iG,_iF);});};}else{return new F(function(){return _in((_im-65|0)+10|0);});}}}else{if(_im>102){if(65>_im){var _iH=new T(function(){return B(A1(_ii,_1));});return function(_iI){return new F(function(){return A1(_iI,_iH);});};}else{if(_im>70){var _iJ=new T(function(){return B(A1(_ii,_1));});return function(_iK){return new F(function(){return A1(_iK,_iJ);});};}else{return new F(function(){return _in((_im-65|0)+10|0);});}}}else{return new F(function(){return _in((_im-97|0)+10|0);});}}}else{if(_im>57){if(97>_im){if(65>_im){var _iL=new T(function(){return B(A1(_ii,_1));});return function(_iM){return new F(function(){return A1(_iM,_iL);});};}else{if(_im>70){var _iN=new T(function(){return B(A1(_ii,_1));});return function(_iO){return new F(function(){return A1(_iO,_iN);});};}else{return new F(function(){return _in((_im-65|0)+10|0);});}}}else{if(_im>102){if(65>_im){var _iP=new T(function(){return B(A1(_ii,_1));});return function(_iQ){return new F(function(){return A1(_iQ,_iP);});};}else{if(_im>70){var _iR=new T(function(){return B(A1(_ii,_1));});return function(_iS){return new F(function(){return A1(_iS,_iR);});};}else{return new F(function(){return _in((_im-65|0)+10|0);});}}}else{return new F(function(){return _in((_im-97|0)+10|0);});}}}else{return new F(function(){return _in(_im-48|0);});}}break;default:return E(_ic);}}},_iT=function(_iU){var _iV=E(_iU);if(!_iV._){return new T0(2);}else{return new F(function(){return A1(_if,_iV);});}};return function(_iW){return new F(function(){return A3(_ig,_iW,_i9,_iT);});};},_iX=16,_iY=8,_iZ=function(_j0){var _j1=function(_j2){return new F(function(){return A1(_j0,new T1(5,new T2(0,_iY,_j2)));});},_j3=function(_j4){return new F(function(){return A1(_j0,new T1(5,new T2(0,_iX,_j4)));});},_j5=function(_j6){switch(E(_j6)){case 79:return new T1(1,B(_id(_iY,_j1)));case 88:return new T1(1,B(_id(_iX,_j3)));case 111:return new T1(1,B(_id(_iY,_j1)));case 120:return new T1(1,B(_id(_iX,_j3)));default:return new T0(2);}};return function(_j7){return (E(_j7)==48)?E(new T1(0,_j5)):new T0(2);};},_j8=function(_j9){return new T1(0,B(_iZ(_j9)));},_ja=__Z,_jb=function(_jc){return new F(function(){return A1(_jc,_ja);});},_jd=function(_je){return new F(function(){return A1(_je,_ja);});},_jf=10,_jg=new T1(0,1),_jh=new T1(0,2147483647),_ji=function(_jj,_jk){while(1){var _jl=E(_jj);if(!_jl._){var _jm=_jl.a,_jn=E(_jk);if(!_jn._){var _jo=_jn.a,_jp=addC(_jm,_jo);if(!E(_jp.b)){return new T1(0,_jp.a);}else{_jj=new T1(1,I_fromInt(_jm));_jk=new T1(1,I_fromInt(_jo));continue;}}else{_jj=new T1(1,I_fromInt(_jm));_jk=_jn;continue;}}else{var _jq=E(_jk);if(!_jq._){_jj=_jl;_jk=new T1(1,I_fromInt(_jq.a));continue;}else{return new T1(1,I_add(_jl.a,_jq.a));}}}},_jr=new T(function(){return B(_ji(_jh,_jg));}),_js=function(_jt){var _ju=E(_jt);if(!_ju._){var _jv=E(_ju.a);return (_jv==( -2147483648))?E(_jr):new T1(0, -_jv);}else{return new T1(1,I_negate(_ju.a));}},_jw=new T1(0,10),_jx=function(_jy,_jz){while(1){var _jA=E(_jy);if(!_jA._){return E(_jz);}else{var _jB=_jz+1|0;_jy=_jA.b;_jz=_jB;continue;}}},_jC=function(_jD,_jE){var _jF=E(_jE);return (_jF._==0)?__Z:new T2(1,new T(function(){return B(A1(_jD,_jF.a));}),new T(function(){return B(_jC(_jD,_jF.b));}));},_jG=function(_jH){return new T1(0,_jH);},_jI=function(_jJ){return new F(function(){return _jG(E(_jJ));});},_jK=new T(function(){return B(unCStr("this should not happen"));}),_jL=new T(function(){return B(err(_jK));}),_jM=function(_jN,_jO){while(1){var _jP=E(_jN);if(!_jP._){var _jQ=_jP.a,_jR=E(_jO);if(!_jR._){var _jS=_jR.a;if(!(imul(_jQ,_jS)|0)){return new T1(0,imul(_jQ,_jS)|0);}else{_jN=new T1(1,I_fromInt(_jQ));_jO=new T1(1,I_fromInt(_jS));continue;}}else{_jN=new T1(1,I_fromInt(_jQ));_jO=_jR;continue;}}else{var _jT=E(_jO);if(!_jT._){_jN=_jP;_jO=new T1(1,I_fromInt(_jT.a));continue;}else{return new T1(1,I_mul(_jP.a,_jT.a));}}}},_jU=function(_jV,_jW){var _jX=E(_jW);if(!_jX._){return __Z;}else{var _jY=E(_jX.b);return (_jY._==0)?E(_jL):new T2(1,B(_ji(B(_jM(_jX.a,_jV)),_jY.a)),new T(function(){return B(_jU(_jV,_jY.b));}));}},_jZ=new T1(0,0),_k0=function(_k1,_k2,_k3){while(1){var _k4=B((function(_k5,_k6,_k7){var _k8=E(_k7);if(!_k8._){return E(_jZ);}else{if(!E(_k8.b)._){return E(_k8.a);}else{var _k9=E(_k6);if(_k9<=40){var _ka=function(_kb,_kc){while(1){var _kd=E(_kc);if(!_kd._){return E(_kb);}else{var _ke=B(_ji(B(_jM(_kb,_k5)),_kd.a));_kb=_ke;_kc=_kd.b;continue;}}};return new F(function(){return _ka(_jZ,_k8);});}else{var _kf=B(_jM(_k5,_k5));if(!(_k9%2)){var _kg=B(_jU(_k5,_k8));_k1=_kf;_k2=quot(_k9+1|0,2);_k3=_kg;return __continue;}else{var _kg=B(_jU(_k5,new T2(1,_jZ,_k8)));_k1=_kf;_k2=quot(_k9+1|0,2);_k3=_kg;return __continue;}}}}})(_k1,_k2,_k3));if(_k4!=__continue){return _k4;}}},_kh=function(_ki,_kj){return new F(function(){return _k0(_ki,new T(function(){return B(_jx(_kj,0));},1),B(_jC(_jI,_kj)));});},_kk=function(_kl){var _km=new T(function(){var _kn=new T(function(){var _ko=function(_kp){return new F(function(){return A1(_kl,new T1(1,new T(function(){return B(_kh(_jw,_kp));})));});};return new T1(1,B(_id(_jf,_ko)));}),_kq=function(_kr){if(E(_kr)==43){var _ks=function(_kt){return new F(function(){return A1(_kl,new T1(1,new T(function(){return B(_kh(_jw,_kt));})));});};return new T1(1,B(_id(_jf,_ks)));}else{return new T0(2);}},_ku=function(_kv){if(E(_kv)==45){var _kw=function(_kx){return new F(function(){return A1(_kl,new T1(1,new T(function(){return B(_js(B(_kh(_jw,_kx))));})));});};return new T1(1,B(_id(_jf,_kw)));}else{return new T0(2);}};return B(_ge(B(_ge(new T1(0,_ku),new T1(0,_kq))),_kn));});return new F(function(){return _ge(new T1(0,function(_ky){return (E(_ky)==101)?E(_km):new T0(2);}),new T1(0,function(_kz){return (E(_kz)==69)?E(_km):new T0(2);}));});},_kA=function(_kB){var _kC=function(_kD){return new F(function(){return A1(_kB,new T1(1,_kD));});};return function(_kE){return (E(_kE)==46)?new T1(1,B(_id(_jf,_kC))):new T0(2);};},_kF=function(_kG){return new T1(0,B(_kA(_kG)));},_kH=function(_kI){var _kJ=function(_kK){var _kL=function(_kM){return new T1(1,B(_hu(_kk,_jb,function(_kN){return new F(function(){return A1(_kI,new T1(5,new T3(1,_kK,_kM,_kN)));});})));};return new T1(1,B(_hu(_kF,_jd,_kL)));};return new F(function(){return _id(_jf,_kJ);});},_kO=function(_kP){return new T1(1,B(_kH(_kP)));},_kQ=function(_kR){return E(E(_kR).a);},_kS=function(_kT,_kU,_kV){while(1){var _kW=E(_kV);if(!_kW._){return false;}else{if(!B(A3(_kQ,_kT,_kU,_kW.a))){_kV=_kW.b;continue;}else{return true;}}}},_kX=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_kY=function(_kZ){return new F(function(){return _kS(_h3,_kZ,_kX);});},_l0=false,_l1=true,_l2=function(_l3){var _l4=new T(function(){return B(A1(_l3,_iY));}),_l5=new T(function(){return B(A1(_l3,_iX));});return function(_l6){switch(E(_l6)){case 79:return E(_l4);case 88:return E(_l5);case 111:return E(_l4);case 120:return E(_l5);default:return new T0(2);}};},_l7=function(_l8){return new T1(0,B(_l2(_l8)));},_l9=function(_la){return new F(function(){return A1(_la,_jf);});},_lb=function(_lc,_ld){var _le=jsShowI(_lc);return new F(function(){return _ce(fromJSStr(_le),_ld);});},_lf=function(_lg,_lh,_li){if(_lh>=0){return new F(function(){return _lb(_lh,_li);});}else{if(_lg<=6){return new F(function(){return _lb(_lh,_li);});}else{return new T2(1,_cx,new T(function(){var _lj=jsShowI(_lh);return B(_ce(fromJSStr(_lj),new T2(1,_cw,_li)));}));}}},_lk=function(_ll){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_lf(9,_ll,_1));}))));});},_lm=function(_ln,_lo){var _lp=E(_ln);if(!_lp._){var _lq=_lp.a,_lr=E(_lo);return (_lr._==0)?_lq<=_lr.a:I_compareInt(_lr.a,_lq)>=0;}else{var _ls=_lp.a,_lt=E(_lo);return (_lt._==0)?I_compareInt(_ls,_lt.a)<=0:I_compare(_ls,_lt.a)<=0;}},_lu=function(_lv){return new T0(2);},_lw=function(_lx){var _ly=E(_lx);if(!_ly._){return E(_lu);}else{var _lz=_ly.a,_lA=E(_ly.b);if(!_lA._){return E(_lz);}else{var _lB=new T(function(){return B(_lw(_lA));}),_lC=function(_lD){return new F(function(){return _ge(B(A1(_lz,_lD)),new T(function(){return B(A1(_lB,_lD));}));});};return E(_lC);}}},_lE=function(_lF,_lG){var _lH=function(_lI,_lJ,_lK){var _lL=E(_lI);if(!_lL._){return new F(function(){return A1(_lK,_lF);});}else{var _lM=E(_lJ);if(!_lM._){return new T0(2);}else{if(E(_lL.a)!=E(_lM.a)){return new T0(2);}else{var _lN=new T(function(){return B(_lH(_lL.b,_lM.b,_lK));});return new T1(0,function(_lO){return E(_lN);});}}}};return function(_lP){return new F(function(){return _lH(_lF,_lP,_lG);});};},_lQ=new T(function(){return B(unCStr("SO"));}),_lR=14,_lS=function(_lT){var _lU=new T(function(){return B(A1(_lT,_lR));});return new T1(1,B(_lE(_lQ,function(_lV){return E(_lU);})));},_lW=new T(function(){return B(unCStr("SOH"));}),_lX=1,_lY=function(_lZ){var _m0=new T(function(){return B(A1(_lZ,_lX));});return new T1(1,B(_lE(_lW,function(_m1){return E(_m0);})));},_m2=function(_m3){return new T1(1,B(_hu(_lY,_lS,_m3)));},_m4=new T(function(){return B(unCStr("NUL"));}),_m5=0,_m6=function(_m7){var _m8=new T(function(){return B(A1(_m7,_m5));});return new T1(1,B(_lE(_m4,function(_m9){return E(_m8);})));},_ma=new T(function(){return B(unCStr("STX"));}),_mb=2,_mc=function(_md){var _me=new T(function(){return B(A1(_md,_mb));});return new T1(1,B(_lE(_ma,function(_mf){return E(_me);})));},_mg=new T(function(){return B(unCStr("ETX"));}),_mh=3,_mi=function(_mj){var _mk=new T(function(){return B(A1(_mj,_mh));});return new T1(1,B(_lE(_mg,function(_ml){return E(_mk);})));},_mm=new T(function(){return B(unCStr("EOT"));}),_mn=4,_mo=function(_mp){var _mq=new T(function(){return B(A1(_mp,_mn));});return new T1(1,B(_lE(_mm,function(_mr){return E(_mq);})));},_ms=new T(function(){return B(unCStr("ENQ"));}),_mt=5,_mu=function(_mv){var _mw=new T(function(){return B(A1(_mv,_mt));});return new T1(1,B(_lE(_ms,function(_mx){return E(_mw);})));},_my=new T(function(){return B(unCStr("ACK"));}),_mz=6,_mA=function(_mB){var _mC=new T(function(){return B(A1(_mB,_mz));});return new T1(1,B(_lE(_my,function(_mD){return E(_mC);})));},_mE=new T(function(){return B(unCStr("BEL"));}),_mF=7,_mG=function(_mH){var _mI=new T(function(){return B(A1(_mH,_mF));});return new T1(1,B(_lE(_mE,function(_mJ){return E(_mI);})));},_mK=new T(function(){return B(unCStr("BS"));}),_mL=8,_mM=function(_mN){var _mO=new T(function(){return B(A1(_mN,_mL));});return new T1(1,B(_lE(_mK,function(_mP){return E(_mO);})));},_mQ=new T(function(){return B(unCStr("HT"));}),_mR=9,_mS=function(_mT){var _mU=new T(function(){return B(A1(_mT,_mR));});return new T1(1,B(_lE(_mQ,function(_mV){return E(_mU);})));},_mW=new T(function(){return B(unCStr("LF"));}),_mX=10,_mY=function(_mZ){var _n0=new T(function(){return B(A1(_mZ,_mX));});return new T1(1,B(_lE(_mW,function(_n1){return E(_n0);})));},_n2=new T(function(){return B(unCStr("VT"));}),_n3=11,_n4=function(_n5){var _n6=new T(function(){return B(A1(_n5,_n3));});return new T1(1,B(_lE(_n2,function(_n7){return E(_n6);})));},_n8=new T(function(){return B(unCStr("FF"));}),_n9=12,_na=function(_nb){var _nc=new T(function(){return B(A1(_nb,_n9));});return new T1(1,B(_lE(_n8,function(_nd){return E(_nc);})));},_ne=new T(function(){return B(unCStr("CR"));}),_nf=13,_ng=function(_nh){var _ni=new T(function(){return B(A1(_nh,_nf));});return new T1(1,B(_lE(_ne,function(_nj){return E(_ni);})));},_nk=new T(function(){return B(unCStr("SI"));}),_nl=15,_nm=function(_nn){var _no=new T(function(){return B(A1(_nn,_nl));});return new T1(1,B(_lE(_nk,function(_np){return E(_no);})));},_nq=new T(function(){return B(unCStr("DLE"));}),_nr=16,_ns=function(_nt){var _nu=new T(function(){return B(A1(_nt,_nr));});return new T1(1,B(_lE(_nq,function(_nv){return E(_nu);})));},_nw=new T(function(){return B(unCStr("DC1"));}),_nx=17,_ny=function(_nz){var _nA=new T(function(){return B(A1(_nz,_nx));});return new T1(1,B(_lE(_nw,function(_nB){return E(_nA);})));},_nC=new T(function(){return B(unCStr("DC2"));}),_nD=18,_nE=function(_nF){var _nG=new T(function(){return B(A1(_nF,_nD));});return new T1(1,B(_lE(_nC,function(_nH){return E(_nG);})));},_nI=new T(function(){return B(unCStr("DC3"));}),_nJ=19,_nK=function(_nL){var _nM=new T(function(){return B(A1(_nL,_nJ));});return new T1(1,B(_lE(_nI,function(_nN){return E(_nM);})));},_nO=new T(function(){return B(unCStr("DC4"));}),_nP=20,_nQ=function(_nR){var _nS=new T(function(){return B(A1(_nR,_nP));});return new T1(1,B(_lE(_nO,function(_nT){return E(_nS);})));},_nU=new T(function(){return B(unCStr("NAK"));}),_nV=21,_nW=function(_nX){var _nY=new T(function(){return B(A1(_nX,_nV));});return new T1(1,B(_lE(_nU,function(_nZ){return E(_nY);})));},_o0=new T(function(){return B(unCStr("SYN"));}),_o1=22,_o2=function(_o3){var _o4=new T(function(){return B(A1(_o3,_o1));});return new T1(1,B(_lE(_o0,function(_o5){return E(_o4);})));},_o6=new T(function(){return B(unCStr("ETB"));}),_o7=23,_o8=function(_o9){var _oa=new T(function(){return B(A1(_o9,_o7));});return new T1(1,B(_lE(_o6,function(_ob){return E(_oa);})));},_oc=new T(function(){return B(unCStr("CAN"));}),_od=24,_oe=function(_of){var _og=new T(function(){return B(A1(_of,_od));});return new T1(1,B(_lE(_oc,function(_oh){return E(_og);})));},_oi=new T(function(){return B(unCStr("EM"));}),_oj=25,_ok=function(_ol){var _om=new T(function(){return B(A1(_ol,_oj));});return new T1(1,B(_lE(_oi,function(_on){return E(_om);})));},_oo=new T(function(){return B(unCStr("SUB"));}),_op=26,_oq=function(_or){var _os=new T(function(){return B(A1(_or,_op));});return new T1(1,B(_lE(_oo,function(_ot){return E(_os);})));},_ou=new T(function(){return B(unCStr("ESC"));}),_ov=27,_ow=function(_ox){var _oy=new T(function(){return B(A1(_ox,_ov));});return new T1(1,B(_lE(_ou,function(_oz){return E(_oy);})));},_oA=new T(function(){return B(unCStr("FS"));}),_oB=28,_oC=function(_oD){var _oE=new T(function(){return B(A1(_oD,_oB));});return new T1(1,B(_lE(_oA,function(_oF){return E(_oE);})));},_oG=new T(function(){return B(unCStr("GS"));}),_oH=29,_oI=function(_oJ){var _oK=new T(function(){return B(A1(_oJ,_oH));});return new T1(1,B(_lE(_oG,function(_oL){return E(_oK);})));},_oM=new T(function(){return B(unCStr("RS"));}),_oN=30,_oO=function(_oP){var _oQ=new T(function(){return B(A1(_oP,_oN));});return new T1(1,B(_lE(_oM,function(_oR){return E(_oQ);})));},_oS=new T(function(){return B(unCStr("US"));}),_oT=31,_oU=function(_oV){var _oW=new T(function(){return B(A1(_oV,_oT));});return new T1(1,B(_lE(_oS,function(_oX){return E(_oW);})));},_oY=new T(function(){return B(unCStr("SP"));}),_oZ=32,_p0=function(_p1){var _p2=new T(function(){return B(A1(_p1,_oZ));});return new T1(1,B(_lE(_oY,function(_p3){return E(_p2);})));},_p4=new T(function(){return B(unCStr("DEL"));}),_p5=127,_p6=function(_p7){var _p8=new T(function(){return B(A1(_p7,_p5));});return new T1(1,B(_lE(_p4,function(_p9){return E(_p8);})));},_pa=new T2(1,_p6,_1),_pb=new T2(1,_p0,_pa),_pc=new T2(1,_oU,_pb),_pd=new T2(1,_oO,_pc),_pe=new T2(1,_oI,_pd),_pf=new T2(1,_oC,_pe),_pg=new T2(1,_ow,_pf),_ph=new T2(1,_oq,_pg),_pi=new T2(1,_ok,_ph),_pj=new T2(1,_oe,_pi),_pk=new T2(1,_o8,_pj),_pl=new T2(1,_o2,_pk),_pm=new T2(1,_nW,_pl),_pn=new T2(1,_nQ,_pm),_po=new T2(1,_nK,_pn),_pp=new T2(1,_nE,_po),_pq=new T2(1,_ny,_pp),_pr=new T2(1,_ns,_pq),_ps=new T2(1,_nm,_pr),_pt=new T2(1,_ng,_ps),_pu=new T2(1,_na,_pt),_pv=new T2(1,_n4,_pu),_pw=new T2(1,_mY,_pv),_px=new T2(1,_mS,_pw),_py=new T2(1,_mM,_px),_pz=new T2(1,_mG,_py),_pA=new T2(1,_mA,_pz),_pB=new T2(1,_mu,_pA),_pC=new T2(1,_mo,_pB),_pD=new T2(1,_mi,_pC),_pE=new T2(1,_mc,_pD),_pF=new T2(1,_m6,_pE),_pG=new T2(1,_m2,_pF),_pH=new T(function(){return B(_lw(_pG));}),_pI=34,_pJ=new T1(0,1114111),_pK=92,_pL=39,_pM=function(_pN){var _pO=new T(function(){return B(A1(_pN,_mF));}),_pP=new T(function(){return B(A1(_pN,_mL));}),_pQ=new T(function(){return B(A1(_pN,_mR));}),_pR=new T(function(){return B(A1(_pN,_mX));}),_pS=new T(function(){return B(A1(_pN,_n3));}),_pT=new T(function(){return B(A1(_pN,_n9));}),_pU=new T(function(){return B(A1(_pN,_nf));}),_pV=new T(function(){return B(A1(_pN,_pK));}),_pW=new T(function(){return B(A1(_pN,_pL));}),_pX=new T(function(){return B(A1(_pN,_pI));}),_pY=new T(function(){var _pZ=function(_q0){var _q1=new T(function(){return B(_jG(E(_q0)));}),_q2=function(_q3){var _q4=B(_kh(_q1,_q3));if(!B(_lm(_q4,_pJ))){return new T0(2);}else{return new F(function(){return A1(_pN,new T(function(){var _q5=B(_bU(_q4));if(_q5>>>0>1114111){return B(_lk(_q5));}else{return _q5;}}));});}};return new T1(1,B(_id(_q0,_q2)));},_q6=new T(function(){var _q7=new T(function(){return B(A1(_pN,_oT));}),_q8=new T(function(){return B(A1(_pN,_oN));}),_q9=new T(function(){return B(A1(_pN,_oH));}),_qa=new T(function(){return B(A1(_pN,_oB));}),_qb=new T(function(){return B(A1(_pN,_ov));}),_qc=new T(function(){return B(A1(_pN,_op));}),_qd=new T(function(){return B(A1(_pN,_oj));}),_qe=new T(function(){return B(A1(_pN,_od));}),_qf=new T(function(){return B(A1(_pN,_o7));}),_qg=new T(function(){return B(A1(_pN,_o1));}),_qh=new T(function(){return B(A1(_pN,_nV));}),_qi=new T(function(){return B(A1(_pN,_nP));}),_qj=new T(function(){return B(A1(_pN,_nJ));}),_qk=new T(function(){return B(A1(_pN,_nD));}),_ql=new T(function(){return B(A1(_pN,_nx));}),_qm=new T(function(){return B(A1(_pN,_nr));}),_qn=new T(function(){return B(A1(_pN,_nl));}),_qo=new T(function(){return B(A1(_pN,_lR));}),_qp=new T(function(){return B(A1(_pN,_mz));}),_qq=new T(function(){return B(A1(_pN,_mt));}),_qr=new T(function(){return B(A1(_pN,_mn));}),_qs=new T(function(){return B(A1(_pN,_mh));}),_qt=new T(function(){return B(A1(_pN,_mb));}),_qu=new T(function(){return B(A1(_pN,_lX));}),_qv=new T(function(){return B(A1(_pN,_m5));}),_qw=function(_qx){switch(E(_qx)){case 64:return E(_qv);case 65:return E(_qu);case 66:return E(_qt);case 67:return E(_qs);case 68:return E(_qr);case 69:return E(_qq);case 70:return E(_qp);case 71:return E(_pO);case 72:return E(_pP);case 73:return E(_pQ);case 74:return E(_pR);case 75:return E(_pS);case 76:return E(_pT);case 77:return E(_pU);case 78:return E(_qo);case 79:return E(_qn);case 80:return E(_qm);case 81:return E(_ql);case 82:return E(_qk);case 83:return E(_qj);case 84:return E(_qi);case 85:return E(_qh);case 86:return E(_qg);case 87:return E(_qf);case 88:return E(_qe);case 89:return E(_qd);case 90:return E(_qc);case 91:return E(_qb);case 92:return E(_qa);case 93:return E(_q9);case 94:return E(_q8);case 95:return E(_q7);default:return new T0(2);}};return B(_ge(new T1(0,function(_qy){return (E(_qy)==94)?E(new T1(0,_qw)):new T0(2);}),new T(function(){return B(A1(_pH,_pN));})));});return B(_ge(new T1(1,B(_hu(_l7,_l9,_pZ))),_q6));});return new F(function(){return _ge(new T1(0,function(_qz){switch(E(_qz)){case 34:return E(_pX);case 39:return E(_pW);case 92:return E(_pV);case 97:return E(_pO);case 98:return E(_pP);case 102:return E(_pT);case 110:return E(_pR);case 114:return E(_pU);case 116:return E(_pQ);case 118:return E(_pS);default:return new T0(2);}}),_pY);});},_qA=function(_qB){return new F(function(){return A1(_qB,_bT);});},_qC=function(_qD){var _qE=E(_qD);if(!_qE._){return E(_qA);}else{var _qF=E(_qE.a),_qG=_qF>>>0,_qH=new T(function(){return B(_qC(_qE.b));});if(_qG>887){var _qI=u_iswspace(_qF);if(!E(_qI)){return E(_qA);}else{var _qJ=function(_qK){var _qL=new T(function(){return B(A1(_qH,_qK));});return new T1(0,function(_qM){return E(_qL);});};return E(_qJ);}}else{var _qN=E(_qG);if(_qN==32){var _qO=function(_qP){var _qQ=new T(function(){return B(A1(_qH,_qP));});return new T1(0,function(_qR){return E(_qQ);});};return E(_qO);}else{if(_qN-9>>>0>4){if(E(_qN)==160){var _qS=function(_qT){var _qU=new T(function(){return B(A1(_qH,_qT));});return new T1(0,function(_qV){return E(_qU);});};return E(_qS);}else{return E(_qA);}}else{var _qW=function(_qX){var _qY=new T(function(){return B(A1(_qH,_qX));});return new T1(0,function(_qZ){return E(_qY);});};return E(_qW);}}}}},_r0=function(_r1){var _r2=new T(function(){return B(_r0(_r1));}),_r3=function(_r4){return (E(_r4)==92)?E(_r2):new T0(2);},_r5=function(_r6){return E(new T1(0,_r3));},_r7=new T1(1,function(_r8){return new F(function(){return A2(_qC,_r8,_r5);});}),_r9=new T(function(){return B(_pM(function(_ra){return new F(function(){return A1(_r1,new T2(0,_ra,_l1));});}));}),_rb=function(_rc){var _rd=E(_rc);if(_rd==38){return E(_r2);}else{var _re=_rd>>>0;if(_re>887){var _rf=u_iswspace(_rd);return (E(_rf)==0)?new T0(2):E(_r7);}else{var _rg=E(_re);return (_rg==32)?E(_r7):(_rg-9>>>0>4)?(E(_rg)==160)?E(_r7):new T0(2):E(_r7);}}};return new F(function(){return _ge(new T1(0,function(_rh){return (E(_rh)==92)?E(new T1(0,_rb)):new T0(2);}),new T1(0,function(_ri){var _rj=E(_ri);if(E(_rj)==92){return E(_r9);}else{return new F(function(){return A1(_r1,new T2(0,_rj,_l0));});}}));});},_rk=function(_rl,_rm){var _rn=new T(function(){return B(A1(_rm,new T1(1,new T(function(){return B(A1(_rl,_1));}))));}),_ro=function(_rp){var _rq=E(_rp),_rr=E(_rq.a);if(E(_rr)==34){if(!E(_rq.b)){return E(_rn);}else{return new F(function(){return _rk(function(_rs){return new F(function(){return A1(_rl,new T2(1,_rr,_rs));});},_rm);});}}else{return new F(function(){return _rk(function(_rt){return new F(function(){return A1(_rl,new T2(1,_rr,_rt));});},_rm);});}};return new F(function(){return _r0(_ro);});},_ru=new T(function(){return B(unCStr("_\'"));}),_rv=function(_rw){var _rx=u_iswalnum(_rw);if(!E(_rx)){return new F(function(){return _kS(_h3,_rw,_ru);});}else{return true;}},_ry=function(_rz){return new F(function(){return _rv(E(_rz));});},_rA=new T(function(){return B(unCStr(",;()[]{}`"));}),_rB=new T(function(){return B(unCStr("=>"));}),_rC=new T2(1,_rB,_1),_rD=new T(function(){return B(unCStr("~"));}),_rE=new T2(1,_rD,_rC),_rF=new T(function(){return B(unCStr("@"));}),_rG=new T2(1,_rF,_rE),_rH=new T(function(){return B(unCStr("->"));}),_rI=new T2(1,_rH,_rG),_rJ=new T(function(){return B(unCStr("<-"));}),_rK=new T2(1,_rJ,_rI),_rL=new T(function(){return B(unCStr("|"));}),_rM=new T2(1,_rL,_rK),_rN=new T(function(){return B(unCStr("\\"));}),_rO=new T2(1,_rN,_rM),_rP=new T(function(){return B(unCStr("="));}),_rQ=new T2(1,_rP,_rO),_rR=new T(function(){return B(unCStr("::"));}),_rS=new T2(1,_rR,_rQ),_rT=new T(function(){return B(unCStr(".."));}),_rU=new T2(1,_rT,_rS),_rV=function(_rW){var _rX=new T(function(){return B(A1(_rW,_i8));}),_rY=new T(function(){var _rZ=new T(function(){var _s0=function(_s1){var _s2=new T(function(){return B(A1(_rW,new T1(0,_s1)));});return new T1(0,function(_s3){return (E(_s3)==39)?E(_s2):new T0(2);});};return B(_pM(_s0));}),_s4=function(_s5){var _s6=E(_s5);switch(E(_s6)){case 39:return new T0(2);case 92:return E(_rZ);default:var _s7=new T(function(){return B(A1(_rW,new T1(0,_s6)));});return new T1(0,function(_s8){return (E(_s8)==39)?E(_s7):new T0(2);});}},_s9=new T(function(){var _sa=new T(function(){return B(_rk(_i9,_rW));}),_sb=new T(function(){var _sc=new T(function(){var _sd=new T(function(){var _se=function(_sf){var _sg=E(_sf),_sh=u_iswalpha(_sg);return (E(_sh)==0)?(E(_sg)==95)?new T1(1,B(_hU(_ry,function(_si){return new F(function(){return A1(_rW,new T1(3,new T2(1,_sg,_si)));});}))):new T0(2):new T1(1,B(_hU(_ry,function(_sj){return new F(function(){return A1(_rW,new T1(3,new T2(1,_sg,_sj)));});})));};return B(_ge(new T1(0,_se),new T(function(){return new T1(1,B(_hu(_j8,_kO,_rW)));})));}),_sk=function(_sl){return (!B(_kS(_h3,_sl,_kX)))?new T0(2):new T1(1,B(_hU(_kY,function(_sm){var _sn=new T2(1,_sl,_sm);if(!B(_kS(_hc,_sn,_rU))){return new F(function(){return A1(_rW,new T1(4,_sn));});}else{return new F(function(){return A1(_rW,new T1(2,_sn));});}})));};return B(_ge(new T1(0,_sk),_sd));});return B(_ge(new T1(0,function(_so){if(!B(_kS(_h3,_so,_rA))){return new T0(2);}else{return new F(function(){return A1(_rW,new T1(2,new T2(1,_so,_1)));});}}),_sc));});return B(_ge(new T1(0,function(_sp){return (E(_sp)==34)?E(_sa):new T0(2);}),_sb));});return B(_ge(new T1(0,function(_sq){return (E(_sq)==39)?E(new T1(0,_s4)):new T0(2);}),_s9));});return new F(function(){return _ge(new T1(1,function(_sr){return (E(_sr)._==0)?E(_rX):new T0(2);}),_rY);});},_ss=0,_st=function(_su,_sv){var _sw=new T(function(){var _sx=new T(function(){var _sy=function(_sz){var _sA=new T(function(){var _sB=new T(function(){return B(A1(_sv,_sz));});return B(_rV(function(_sC){var _sD=E(_sC);return (_sD._==2)?(!B(_gS(_sD.a,_gR)))?new T0(2):E(_sB):new T0(2);}));}),_sE=function(_sF){return E(_sA);};return new T1(1,function(_sG){return new F(function(){return A2(_qC,_sG,_sE);});});};return B(A2(_su,_ss,_sy));});return B(_rV(function(_sH){var _sI=E(_sH);return (_sI._==2)?(!B(_gS(_sI.a,_gQ)))?new T0(2):E(_sx):new T0(2);}));}),_sJ=function(_sK){return E(_sw);};return function(_sL){return new F(function(){return A2(_qC,_sL,_sJ);});};},_sM=function(_sN,_sO){var _sP=function(_sQ){var _sR=new T(function(){return B(A1(_sN,_sQ));}),_sS=function(_sT){return new F(function(){return _ge(B(A1(_sR,_sT)),new T(function(){return new T1(1,B(_st(_sP,_sT)));}));});};return E(_sS);},_sU=new T(function(){return B(A1(_sN,_sO));}),_sV=function(_sW){return new F(function(){return _ge(B(A1(_sU,_sW)),new T(function(){return new T1(1,B(_st(_sP,_sW)));}));});};return E(_sV);},_sX=function(_sY,_sZ){var _t0=function(_t1,_t2){var _t3=function(_t4){return new F(function(){return A1(_t2,new T(function(){return B(_js(_t4));}));});},_t5=new T(function(){return B(_rV(function(_t6){return new F(function(){return A3(_sY,_t6,_t1,_t3);});}));}),_t7=function(_t8){return E(_t5);},_t9=function(_ta){return new F(function(){return A2(_qC,_ta,_t7);});},_tb=new T(function(){return B(_rV(function(_tc){var _td=E(_tc);if(_td._==4){var _te=E(_td.a);if(!_te._){return new F(function(){return A3(_sY,_td,_t1,_t2);});}else{if(E(_te.a)==45){if(!E(_te.b)._){return E(new T1(1,_t9));}else{return new F(function(){return A3(_sY,_td,_t1,_t2);});}}else{return new F(function(){return A3(_sY,_td,_t1,_t2);});}}}else{return new F(function(){return A3(_sY,_td,_t1,_t2);});}}));}),_tf=function(_tg){return E(_tb);};return new T1(1,function(_th){return new F(function(){return A2(_qC,_th,_tf);});});};return new F(function(){return _sM(_t0,_sZ);});},_ti=function(_tj){var _tk=E(_tj);if(!_tk._){var _tl=_tk.b,_tm=new T(function(){return B(_k0(new T(function(){return B(_jG(E(_tk.a)));}),new T(function(){return B(_jx(_tl,0));},1),B(_jC(_jI,_tl))));});return new T1(1,_tm);}else{return (E(_tk.b)._==0)?(E(_tk.c)._==0)?new T1(1,new T(function(){return B(_kh(_jw,_tk.a));})):__Z:__Z;}},_tn=function(_to,_tp){return new T0(2);},_tq=function(_tr){var _ts=E(_tr);if(_ts._==5){var _tt=B(_ti(_ts.a));return (_tt._==0)?E(_tn):function(_tu,_tv){return new F(function(){return A1(_tv,_tt.a);});};}else{return E(_tn);}},_tw=function(_tx){return new F(function(){return _sX(_tq,_tx);});},_ty=new T(function(){return B(unCStr("["));}),_tz=function(_tA,_tB){var _tC=function(_tD,_tE){var _tF=new T(function(){return B(A1(_tE,_1));}),_tG=new T(function(){var _tH=function(_tI){return new F(function(){return _tC(_l1,function(_tJ){return new F(function(){return A1(_tE,new T2(1,_tI,_tJ));});});});};return B(A2(_tA,_ss,_tH));}),_tK=new T(function(){return B(_rV(function(_tL){var _tM=E(_tL);if(_tM._==2){var _tN=E(_tM.a);if(!_tN._){return new T0(2);}else{var _tO=_tN.b;switch(E(_tN.a)){case 44:return (E(_tO)._==0)?(!E(_tD))?new T0(2):E(_tG):new T0(2);case 93:return (E(_tO)._==0)?E(_tF):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_tP=function(_tQ){return E(_tK);};return new T1(1,function(_tR){return new F(function(){return A2(_qC,_tR,_tP);});});},_tS=function(_tT,_tU){return new F(function(){return _tV(_tU);});},_tV=function(_tW){var _tX=new T(function(){var _tY=new T(function(){var _tZ=new T(function(){var _u0=function(_u1){return new F(function(){return _tC(_l1,function(_u2){return new F(function(){return A1(_tW,new T2(1,_u1,_u2));});});});};return B(A2(_tA,_ss,_u0));});return B(_ge(B(_tC(_l0,_tW)),_tZ));});return B(_rV(function(_u3){var _u4=E(_u3);return (_u4._==2)?(!B(_gS(_u4.a,_ty)))?new T0(2):E(_tY):new T0(2);}));}),_u5=function(_u6){return E(_tX);};return new F(function(){return _ge(new T1(1,function(_u7){return new F(function(){return A2(_qC,_u7,_u5);});}),new T(function(){return new T1(1,B(_st(_tS,_tW)));}));});};return new F(function(){return _tV(_tB);});},_u8=function(_u9,_ua){return new F(function(){return _tz(_tw,_ua);});},_ub=function(_uc){var _ud=new T(function(){return B(A3(_sX,_tq,_uc,_eU));});return function(_ue){return new F(function(){return _g4(_ud,_ue);});};},_uf=new T(function(){return B(_tz(_tw,_eU));}),_ug=function(_tx){return new F(function(){return _g4(_uf,_tx);});},_uh=new T4(0,_ub,_ug,_tw,_u8),_ui=11,_uj=new T(function(){return B(unCStr("IdentChoice"));}),_uk=function(_ul,_um){if(_ul>10){return new T0(2);}else{var _un=new T(function(){var _uo=new T(function(){return B(A3(_sX,_tq,_ui,function(_up){return new F(function(){return A1(_um,_up);});}));});return B(_rV(function(_uq){var _ur=E(_uq);return (_ur._==3)?(!B(_gS(_ur.a,_uj)))?new T0(2):E(_uo):new T0(2);}));}),_us=function(_ut){return E(_un);};return new T1(1,function(_uu){return new F(function(){return A2(_qC,_uu,_us);});});}},_uv=function(_uw,_ux){return new F(function(){return _uk(E(_uw),_ux);});},_uy=function(_uz){return new F(function(){return _sM(_uv,_uz);});},_uA=function(_uB,_uC){return new F(function(){return _tz(_uy,_uC);});},_uD=new T(function(){return B(_tz(_uy,_eU));}),_uE=function(_uz){return new F(function(){return _g4(_uD,_uz);});},_uF=function(_uG){var _uH=new T(function(){return B(A3(_sM,_uv,_uG,_eU));});return function(_ue){return new F(function(){return _g4(_uH,_ue);});};},_uI=new T4(0,_uF,_uE,_uy,_uA),_uJ=new T(function(){return B(unCStr(","));}),_uK=function(_uL){return E(E(_uL).c);},_uM=function(_uN,_uO,_uP){var _uQ=new T(function(){return B(_uK(_uO));}),_uR=new T(function(){return B(A2(_uK,_uN,_uP));}),_uS=function(_uT){var _uU=function(_uV){var _uW=new T(function(){var _uX=new T(function(){return B(A2(_uQ,_uP,function(_uY){return new F(function(){return A1(_uT,new T2(0,_uV,_uY));});}));});return B(_rV(function(_uZ){var _v0=E(_uZ);return (_v0._==2)?(!B(_gS(_v0.a,_uJ)))?new T0(2):E(_uX):new T0(2);}));}),_v1=function(_v2){return E(_uW);};return new T1(1,function(_v3){return new F(function(){return A2(_qC,_v3,_v1);});});};return new F(function(){return A1(_uR,_uU);});};return E(_uS);},_v4=function(_v5,_v6,_v7){var _v8=function(_tx){return new F(function(){return _uM(_v5,_v6,_tx);});},_v9=function(_va,_vb){return new F(function(){return _vc(_vb);});},_vc=function(_vd){return new F(function(){return _ge(new T1(1,B(_st(_v8,_vd))),new T(function(){return new T1(1,B(_st(_v9,_vd)));}));});};return new F(function(){return _vc(_v7);});},_ve=function(_vf,_vg){return new F(function(){return _v4(_uI,_uh,_vg);});},_vh=new T(function(){return B(_tz(_ve,_eU));}),_vi=function(_uz){return new F(function(){return _g4(_vh,_uz);});},_vj=new T(function(){return B(_v4(_uI,_uh,_eU));}),_vk=function(_uz){return new F(function(){return _g4(_vj,_uz);});},_vl=function(_vm,_uz){return new F(function(){return _vk(_uz);});},_vn=function(_vo,_vp){return new F(function(){return _tz(_ve,_vp);});},_vq=new T4(0,_vl,_vi,_ve,_vn),_vr=function(_vs,_vt){return new F(function(){return _v4(_vq,_uh,_vt);});},_vu=function(_vv,_vw){return new F(function(){return _tz(_vr,_vw);});},_vx=new T(function(){return B(_tz(_vu,_eU));}),_vy=function(_vz){return new F(function(){return _g4(_vx,_vz);});},_vA=function(_vB){return new F(function(){return _tz(_vu,_vB);});},_vC=function(_vD,_vE){return new F(function(){return _vA(_vE);});},_vF=new T(function(){return B(_tz(_vr,_eU));}),_vG=function(_vz){return new F(function(){return _g4(_vF,_vz);});},_vH=function(_vI,_vz){return new F(function(){return _vG(_vz);});},_vJ=new T4(0,_vH,_vy,_vu,_vC),_vK=new T(function(){return B(unCStr("IdentPay"));}),_vL=function(_vM,_vN){if(_vM>10){return new T0(2);}else{var _vO=new T(function(){var _vP=new T(function(){return B(A3(_sX,_tq,_ui,function(_vQ){return new F(function(){return A1(_vN,_vQ);});}));});return B(_rV(function(_vR){var _vS=E(_vR);return (_vS._==3)?(!B(_gS(_vS.a,_vK)))?new T0(2):E(_vP):new T0(2);}));}),_vT=function(_vU){return E(_vO);};return new T1(1,function(_vV){return new F(function(){return A2(_qC,_vV,_vT);});});}},_vW=function(_vX,_vY){return new F(function(){return _vL(E(_vX),_vY);});},_vZ=function(_uz){return new F(function(){return _sM(_vW,_uz);});},_w0=function(_w1,_w2){return new F(function(){return _tz(_vZ,_w2);});},_w3=new T(function(){return B(_tz(_vZ,_eU));}),_w4=function(_uz){return new F(function(){return _g4(_w3,_uz);});},_w5=function(_w6){var _w7=new T(function(){return B(A3(_sM,_vW,_w6,_eU));});return function(_ue){return new F(function(){return _g4(_w7,_ue);});};},_w8=new T4(0,_w5,_w4,_vZ,_w0),_w9=function(_wa,_wb){return new F(function(){return _v4(_w8,_uh,_wb);});},_wc=new T(function(){return B(_tz(_w9,_eU));}),_wd=function(_uz){return new F(function(){return _g4(_wc,_uz);});},_we=new T(function(){return B(_v4(_w8,_uh,_eU));}),_wf=function(_uz){return new F(function(){return _g4(_we,_uz);});},_wg=function(_wh,_uz){return new F(function(){return _wf(_uz);});},_wi=function(_wj,_wk){return new F(function(){return _tz(_w9,_wk);});},_wl=new T4(0,_wg,_wd,_w9,_wi),_wm=function(_wn,_wo){return new F(function(){return _v4(_wl,_uh,_wo);});},_wp=function(_wq,_wr){return new F(function(){return _tz(_wm,_wr);});},_ws=new T(function(){return B(_tz(_wp,_eU));}),_wt=function(_vz){return new F(function(){return _g4(_ws,_vz);});},_wu=function(_wv){return new F(function(){return _tz(_wp,_wv);});},_ww=function(_wx,_wy){return new F(function(){return _wu(_wy);});},_wz=new T(function(){return B(_tz(_wm,_eU));}),_wA=function(_vz){return new F(function(){return _g4(_wz,_vz);});},_wB=function(_wC,_vz){return new F(function(){return _wA(_vz);});},_wD=new T4(0,_wB,_wt,_wp,_ww),_wE=new T(function(){return B(unCStr("IdentCC"));}),_wF=function(_wG,_wH){if(_wG>10){return new T0(2);}else{var _wI=new T(function(){var _wJ=new T(function(){return B(A3(_sX,_tq,_ui,function(_wK){return new F(function(){return A1(_wH,_wK);});}));});return B(_rV(function(_wL){var _wM=E(_wL);return (_wM._==3)?(!B(_gS(_wM.a,_wE)))?new T0(2):E(_wJ):new T0(2);}));}),_wN=function(_wO){return E(_wI);};return new T1(1,function(_wP){return new F(function(){return A2(_qC,_wP,_wN);});});}},_wQ=function(_wR,_wS){return new F(function(){return _wF(E(_wR),_wS);});},_wT=new T(function(){return B(unCStr("RC"));}),_wU=function(_wV,_wW){if(_wV>10){return new T0(2);}else{var _wX=new T(function(){var _wY=new T(function(){var _wZ=function(_x0){var _x1=function(_x2){return new F(function(){return A3(_sX,_tq,_ui,function(_x3){return new F(function(){return A1(_wW,new T3(0,_x0,_x2,_x3));});});});};return new F(function(){return A3(_sX,_tq,_ui,_x1);});};return B(A3(_sM,_wQ,_ui,_wZ));});return B(_rV(function(_x4){var _x5=E(_x4);return (_x5._==3)?(!B(_gS(_x5.a,_wT)))?new T0(2):E(_wY):new T0(2);}));}),_x6=function(_x7){return E(_wX);};return new T1(1,function(_x8){return new F(function(){return A2(_qC,_x8,_x6);});});}},_x9=function(_xa,_xb){return new F(function(){return _wU(E(_xa),_xb);});},_xc=function(_uz){return new F(function(){return _sM(_x9,_uz);});},_xd=function(_xe,_xf){return new F(function(){return _tz(_xc,_xf);});},_xg=new T(function(){return B(_tz(_xd,_eU));}),_xh=function(_vz){return new F(function(){return _g4(_xg,_vz);});},_xi=new T(function(){return B(_tz(_xc,_eU));}),_xj=function(_vz){return new F(function(){return _g4(_xi,_vz);});},_xk=function(_xl,_vz){return new F(function(){return _xj(_vz);});},_xm=function(_xn,_xo){return new F(function(){return _tz(_xd,_xo);});},_xp=new T4(0,_xk,_xh,_xd,_xm),_xq=new T(function(){return B(unCStr("CC"));}),_xr=function(_xs,_xt){if(_xs>10){return new T0(2);}else{var _xu=new T(function(){var _xv=new T(function(){var _xw=function(_xx){var _xy=function(_xz){var _xA=function(_xB){return new F(function(){return A3(_sX,_tq,_ui,function(_xC){return new F(function(){return A1(_xt,new T4(0,_xx,_xz,_xB,_xC));});});});};return new F(function(){return A3(_sX,_tq,_ui,_xA);});};return new F(function(){return A3(_sX,_tq,_ui,_xy);});};return B(A3(_sM,_wQ,_ui,_xw));});return B(_rV(function(_xD){var _xE=E(_xD);return (_xE._==3)?(!B(_gS(_xE.a,_xq)))?new T0(2):E(_xv):new T0(2);}));}),_xF=function(_xG){return E(_xu);};return new T1(1,function(_xH){return new F(function(){return A2(_qC,_xH,_xF);});});}},_xI=function(_xJ,_xK){return new F(function(){return _xr(E(_xJ),_xK);});},_xL=function(_uz){return new F(function(){return _sM(_xI,_uz);});},_xM=function(_xN,_xO){return new F(function(){return _tz(_xL,_xO);});},_xP=new T(function(){return B(_tz(_xM,_eU));}),_xQ=function(_vz){return new F(function(){return _g4(_xP,_vz);});},_xR=new T(function(){return B(_tz(_xL,_eU));}),_xS=function(_vz){return new F(function(){return _g4(_xR,_vz);});},_xT=function(_xU,_vz){return new F(function(){return _xS(_vz);});},_xV=function(_xW,_xX){return new F(function(){return _tz(_xM,_xX);});},_xY=new T4(0,_xT,_xQ,_xM,_xV),_xZ=function(_y0,_y1,_y2,_y3,_y4){var _y5=new T(function(){return B(_uM(_y0,_y1,_y4));}),_y6=new T(function(){return B(_uK(_y3));}),_y7=function(_y8){var _y9=function(_ya){var _yb=E(_ya),_yc=new T(function(){var _yd=new T(function(){var _ye=function(_yf){var _yg=new T(function(){var _yh=new T(function(){return B(A2(_y6,_y4,function(_yi){return new F(function(){return A1(_y8,new T4(0,_yb.a,_yb.b,_yf,_yi));});}));});return B(_rV(function(_yj){var _yk=E(_yj);return (_yk._==2)?(!B(_gS(_yk.a,_uJ)))?new T0(2):E(_yh):new T0(2);}));}),_yl=function(_ym){return E(_yg);};return new T1(1,function(_yn){return new F(function(){return A2(_qC,_yn,_yl);});});};return B(A3(_uK,_y2,_y4,_ye));});return B(_rV(function(_yo){var _yp=E(_yo);return (_yp._==2)?(!B(_gS(_yp.a,_uJ)))?new T0(2):E(_yd):new T0(2);}));}),_yq=function(_yr){return E(_yc);};return new T1(1,function(_ys){return new F(function(){return A2(_qC,_ys,_yq);});});};return new F(function(){return A1(_y5,_y9);});};return E(_y7);},_yt=function(_yu,_yv,_yw,_yx,_yy){var _yz=function(_tx){return new F(function(){return _xZ(_yu,_yv,_yw,_yx,_tx);});},_yA=function(_yB,_yC){return new F(function(){return _yD(_yC);});},_yD=function(_yE){return new F(function(){return _ge(new T1(1,B(_st(_yz,_yE))),new T(function(){return new T1(1,B(_st(_yA,_yE)));}));});};return new F(function(){return _yD(_yy);});},_yF=function(_yG){var _yH=function(_yI){return E(new T2(3,_yG,_eT));};return new T1(1,function(_yJ){return new F(function(){return A2(_qC,_yJ,_yH);});});},_yK=new T(function(){return B(_yt(_xY,_xp,_wD,_vJ,_yF));}),_yL=function(_yM,_yN,_yO,_yP){var _yQ=E(_yM);if(_yQ==1){var _yR=E(_yP);return (_yR._==0)?new T3(0,new T(function(){return new T5(0,1,E(_yN),_yO,E(_0),E(_0));}),_1,_1):(!B(_e(_yN,E(_yR.a).a)))?new T3(0,new T(function(){return new T5(0,1,E(_yN),_yO,E(_0),E(_0));}),_yR,_1):new T3(0,new T(function(){return new T5(0,1,E(_yN),_yO,E(_0),E(_0));}),_1,_yR);}else{var _yS=B(_yL(_yQ>>1,_yN,_yO,_yP)),_yT=_yS.a,_yU=_yS.c,_yV=E(_yS.b);if(!_yV._){return new T3(0,_yT,_1,_yU);}else{var _yW=E(_yV.a),_yX=_yW.a,_yY=_yW.b,_yZ=E(_yV.b);if(!_yZ._){return new T3(0,new T(function(){return B(_18(_yX,_yY,_yT));}),_1,_yU);}else{var _z0=E(_yZ.a),_z1=_z0.a;if(!B(_e(_yX,_z1))){var _z2=B(_yL(_yQ>>1,_z1,_z0.b,_yZ.b));return new T3(0,new T(function(){return B(_2B(_yX,_yY,_yT,_z2.a));}),_z2.b,_z2.c);}else{return new T3(0,_yT,_1,_yV);}}}}},_z3=function(_z4,_z5,_z6){var _z7=E(_z4),_z8=E(_z6);if(!_z8._){var _z9=_z8.b,_za=_z8.c,_zb=_z8.d,_zc=_z8.e;switch(B(_2(_z7,_z9))){case 0:return new F(function(){return _1h(_z9,_za,B(_z3(_z7,_z5,_zb)),_zc);});break;case 1:return new T5(0,_z8.a,E(_z7),_z5,E(_zb),E(_zc));default:return new F(function(){return _q(_z9,_za,_zb,B(_z3(_z7,_z5,_zc)));});}}else{return new T5(0,1,E(_z7),_z5,E(_0),E(_0));}},_zd=function(_ze,_zf){while(1){var _zg=E(_zf);if(!_zg._){return E(_ze);}else{var _zh=E(_zg.a),_zi=B(_z3(_zh.a,_zh.b,_ze));_ze=_zi;_zf=_zg.b;continue;}}},_zj=function(_zk,_zl,_zm,_zn){return new F(function(){return _zd(B(_z3(_zl,_zm,_zk)),_zn);});},_zo=function(_zp,_zq,_zr){var _zs=E(_zq);return new F(function(){return _zd(B(_z3(_zs.a,_zs.b,_zp)),_zr);});},_zt=function(_zu,_zv,_zw){while(1){var _zx=E(_zw);if(!_zx._){return E(_zv);}else{var _zy=E(_zx.a),_zz=_zy.a,_zA=_zy.b,_zB=E(_zx.b);if(!_zB._){return new F(function(){return _18(_zz,_zA,_zv);});}else{var _zC=E(_zB.a),_zD=_zC.a;if(!B(_e(_zz,_zD))){var _zE=B(_yL(_zu,_zD,_zC.b,_zB.b)),_zF=_zE.a,_zG=E(_zE.c);if(!_zG._){var _zH=_zu<<1,_zI=B(_2B(_zz,_zA,_zv,_zF));_zu=_zH;_zv=_zI;_zw=_zE.b;continue;}else{return new F(function(){return _zo(B(_2B(_zz,_zA,_zv,_zF)),_zG.a,_zG.b);});}}else{return new F(function(){return _zj(_zv,_zz,_zA,_zB);});}}}}},_zJ=function(_zK,_zL,_zM,_zN,_zO){var _zP=E(_zO);if(!_zP._){return new F(function(){return _18(_zM,_zN,_zL);});}else{var _zQ=E(_zP.a),_zR=_zQ.a;if(!B(_e(_zM,_zR))){var _zS=B(_yL(_zK,_zR,_zQ.b,_zP.b)),_zT=_zS.a,_zU=E(_zS.c);if(!_zU._){return new F(function(){return _zt(_zK<<1,B(_2B(_zM,_zN,_zL,_zT)),_zS.b);});}else{return new F(function(){return _zo(B(_2B(_zM,_zN,_zL,_zT)),_zU.a,_zU.b);});}}else{return new F(function(){return _zj(_zL,_zM,_zN,_zP);});}}},_zV=function(_zW){var _zX=E(_zW);if(!_zX._){return new T0(1);}else{var _zY=E(_zX.a),_zZ=_zY.a,_A0=_zY.b,_A1=E(_zX.b);if(!_A1._){return new T5(0,1,E(_zZ),_A0,E(_0),E(_0));}else{var _A2=_A1.b,_A3=E(_A1.a),_A4=_A3.a,_A5=_A3.b;if(!B(_e(_zZ,_A4))){return new F(function(){return _zJ(1,new T5(0,1,E(_zZ),_A0,E(_0),E(_0)),_A4,_A5,_A2);});}else{return new F(function(){return _zj(new T5(0,1,E(_zZ),_A0,E(_0),E(_0)),_A4,_A5,_A2);});}}}},_A6=function(_){return _bT;},_A7=new T(function(){return B(unCStr(": Choose"));}),_A8=new T(function(){return eval("(function (x, y, z) {var a = document.getElementById(\'actions\'); var r = a.insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x + \' \')); var input = document.createElement(\'input\'); input.type = \'number\'; var ch = \'ibox\' + a.childNodes.length; input.id = ch; input.value = 0; input.style.setProperty(\'width\', \'5em\'); c1.appendChild(input); c1.appendChild(document.createTextNode(\' \' + y)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addActionWithNum(z, document.getElementById(ch).value);};})");}),_A9=function(_Aa,_Ab,_){var _Ac=new T(function(){return B(A3(_dr,_c9,new T2(1,function(_Ad){return new F(function(){return _e5(0,_Aa,_Ad);});},new T2(1,function(_Ae){return new F(function(){return _cz(0,_Ab,_Ae);});},_1)),_eu));}),_Af=__app3(E(_A8),toJSStr(B(unAppCStr("P",new T(function(){return B(_ce(B(_cz(0,_Ab,_1)),_A7));})))),toJSStr(B(unAppCStr("for choice with id ",new T(function(){return B(_cz(0,_Aa,_1));})))),toJSStr(new T2(1,_cx,_Ac)));return new F(function(){return _A6(_);});},_Ag=function(_Ah,_Ai,_){while(1){var _Aj=B((function(_Ak,_Al,_){var _Am=E(_Al);if(!_Am._){var _An=E(_Am.b);_Ah=function(_){var _Ao=B(_A9(_An.a,_An.b,_));return new F(function(){return _Ag(_Ak,_Am.e,_);});};_Ai=_Am.d;return __continue;}else{return new F(function(){return A1(_Ak,_);});}})(_Ah,_Ai,_));if(_Aj!=__continue){return _Aj;}}},_Ap=new T(function(){return B(unCStr("SIP "));}),_Aq=new T(function(){return B(unCStr("SIRC "));}),_Ar=new T(function(){return B(unCStr("SICC "));}),_As=function(_At,_Au,_Av){var _Aw=E(_Au);switch(_Aw._){case 0:var _Ax=function(_Ay){var _Az=new T(function(){var _AA=new T(function(){return B(_cz(11,_Aw.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_Aw.d,_Ay));}))));});return B(_cz(11,_Aw.b,new T2(1,_cJ,_AA)));});return new F(function(){return _cE(11,_Aw.a,new T2(1,_cJ,_Az));});};if(_At<11){return new F(function(){return _ce(_Ar,new T(function(){return B(_Ax(_Av));},1));});}else{var _AB=new T(function(){return B(_ce(_Ar,new T(function(){return B(_Ax(new T2(1,_cw,_Av)));},1)));});return new T2(1,_cx,_AB);}break;case 1:var _AC=function(_AD){var _AE=new T(function(){var _AF=new T(function(){return B(_cz(11,_Aw.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_Aw.c,_AD));}))));});return B(_cE(11,_Aw.a,new T2(1,_cJ,_AF)));},1);return new F(function(){return _ce(_Aq,_AE);});};if(_At<11){return new F(function(){return _AC(_Av);});}else{return new T2(1,_cx,new T(function(){return B(_AC(new T2(1,_cw,_Av)));}));}break;default:var _AG=function(_AH){var _AI=new T(function(){var _AJ=new T(function(){return B(_cz(11,_Aw.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_Aw.c,_AH));}))));});return B(_dg(11,_Aw.a,new T2(1,_cJ,_AJ)));},1);return new F(function(){return _ce(_Ap,_AI);});};if(_At<11){return new F(function(){return _AG(_Av);});}else{return new T2(1,_cx,new T(function(){return B(_AG(new T2(1,_cw,_Av)));}));}}},_AK=new T(function(){return B(unCStr(" ADA"));}),_AL=new T(function(){return eval("(function (x, y) {var r = document.getElementById(\'actions\').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addAction(y);};})");}),_AM=function(_AN,_AO,_AP,_){var _AQ=new T(function(){var _AR=new T(function(){var _AS=new T(function(){var _AT=new T(function(){return B(unAppCStr(") of ",new T(function(){return B(_ce(B(_cz(0,_AP,_1)),_AK));})));},1);return B(_ce(B(_cz(0,_AN,_1)),_AT));});return B(unAppCStr(": Claim payment (with id: ",_AS));},1);return B(_ce(B(_cz(0,_AO,_1)),_AR));}),_AU=__app2(E(_AL),toJSStr(B(unAppCStr("P",_AQ))),toJSStr(B(_As(0,new T3(2,_AN,_AO,_AP),_1))));return new F(function(){return _A6(_);});},_AV=function(_AW,_AX,_){while(1){var _AY=B((function(_AZ,_B0,_){var _B1=E(_B0);if(!_B1._){var _B2=E(_B1.b);_AW=function(_){var _B3=B(_AM(_B2.a,_B2.b,_B1.c,_));return new F(function(){return _AV(_AZ,_B1.e,_);});};_AX=_B1.d;return __continue;}else{return new F(function(){return A1(_AZ,_);});}})(_AW,_AX,_));if(_AY!=__continue){return _AY;}}},_B4=new T(function(){return B(unCStr(")"));}),_B5=function(_B6,_B7,_B8,_){var _B9=new T(function(){var _Ba=new T(function(){var _Bb=new T(function(){var _Bc=new T(function(){return B(unAppCStr(" ADA from commit (with id: ",new T(function(){return B(_ce(B(_cz(0,_B6,_1)),_B4));})));},1);return B(_ce(B(_cz(0,_B8,_1)),_Bc));});return B(unAppCStr(": Redeem ",_Bb));},1);return B(_ce(B(_cz(0,_B7,_1)),_Ba));}),_Bd=__app2(E(_AL),toJSStr(B(unAppCStr("P",_B9))),toJSStr(B(_As(0,new T3(1,_B6,_B7,_B8),_1))));return new F(function(){return _A6(_);});},_Be=function(_Bf,_Bg,_){while(1){var _Bh=B((function(_Bi,_Bj,_){var _Bk=E(_Bj);if(!_Bk._){var _Bl=E(_Bk.b);_Bf=function(_){var _Bm=B(_B5(_Bl.a,_Bl.b,_Bl.c,_));return new F(function(){return _Be(_Bi,_Bk.d,_);});};_Bg=_Bk.c;return __continue;}else{return new F(function(){return A1(_Bi,_);});}})(_Bf,_Bg,_));if(_Bh!=__continue){return _Bh;}}},_Bn=function(_){return _bT;},_Bo=function(_Bp,_Bq,_Br,_Bs,_){var _Bt=new T(function(){var _Bu=new T(function(){var _Bv=new T(function(){var _Bw=new T(function(){var _Bx=new T(function(){var _By=new T(function(){return B(unAppCStr(" ADA expiring on: ",new T(function(){return B(_cz(0,_Bs,_1));})));},1);return B(_ce(B(_cz(0,_Br,_1)),_By));});return B(unAppCStr(") of ",_Bx));},1);return B(_ce(B(_cz(0,_Bp,_1)),_Bw));});return B(unAppCStr(": Make commit (with id: ",_Bv));},1);return B(_ce(B(_cz(0,_Bq,_1)),_Bu));}),_Bz=__app2(E(_AL),toJSStr(B(unAppCStr("P",_Bt))),toJSStr(B(_As(0,new T4(0,_Bp,_Bq,_Br,_Bs),_1))));return new F(function(){return _A6(_);});},_BA=function(_BB,_BC,_){while(1){var _BD=B((function(_BE,_BF,_){var _BG=E(_BF);if(!_BG._){var _BH=E(_BG.b);_BB=function(_){var _BI=B(_Bo(_BH.a,_BH.b,_BH.c,_BH.d,_));return new F(function(){return _BA(_BE,_BG.d,_);});};_BC=_BG.c;return __continue;}else{return new F(function(){return A1(_BE,_);});}})(_BB,_BC,_));if(_BD!=__continue){return _BD;}}},_BJ=function(_BK,_BL,_BM,_BN,_){var _BO=B(_BA(_Bn,_BK,_)),_BP=B(_Be(_Bn,_BL,_)),_BQ=B(_AV(_Bn,_BM,_));return new F(function(){return _Ag(_Bn,_BN,_);});},_BR=function(_BS,_BT){while(1){var _BU=E(_BS),_BV=E(_BT);if(!_BV._){switch(B(_2(_BU,_BV.b))){case 0:_BS=_BU;_BT=_BV.d;continue;case 1:return new T1(1,_BV.c);default:_BS=_BU;_BT=_BV.e;continue;}}else{return __Z;}}},_BW=function(_BX,_BY){while(1){var _BZ=E(_BX),_C0=E(_BY);if(!_C0._){switch(B(_2(_BZ,_C0.b))){case 0:_BX=_BZ;_BY=_C0.d;continue;case 1:return true;default:_BX=_BZ;_BY=_C0.e;continue;}}else{return false;}}},_C1=function(_C2,_C3){var _C4=E(_C2);if(!_C4._){var _C5=_C4.a,_C6=E(_C3);return (_C6._==0)?_C5==_C6.a:(I_compareInt(_C6.a,_C5)==0)?true:false;}else{var _C7=_C4.a,_C8=E(_C3);return (_C8._==0)?(I_compareInt(_C7,_C8.a)==0)?true:false:(I_compare(_C7,_C8.a)==0)?true:false;}},_C9=function(_Ca,_Cb){var _Cc=E(_Ca),_Cd=E(_Cb);return (!B(_C1(_Cc.a,_Cd.a)))?true:(!B(_C1(_Cc.b,_Cd.b)))?true:(!B(_C1(_Cc.c,_Cd.c)))?true:(!B(_C1(_Cc.d,_Cd.d)))?true:false;},_Ce=function(_Cf,_Cg,_Ch,_Ci,_Cj,_Ck,_Cl,_Cm){if(!B(_C1(_Cf,_Cj))){return false;}else{if(!B(_C1(_Cg,_Ck))){return false;}else{if(!B(_C1(_Ch,_Cl))){return false;}else{return new F(function(){return _C1(_Ci,_Cm);});}}}},_Cn=function(_Co,_Cp){var _Cq=E(_Co),_Cr=E(_Cp);return new F(function(){return _Ce(_Cq.a,_Cq.b,_Cq.c,_Cq.d,_Cr.a,_Cr.b,_Cr.c,_Cr.d);});},_Cs=new T2(0,_Cn,_C9),_Ct=function(_Cu,_Cv,_Cw,_Cx,_Cy,_Cz,_CA,_CB){switch(B(_2(_Cu,_Cy))){case 0:return true;case 1:switch(B(_2(_Cv,_Cz))){case 0:return true;case 1:switch(B(_2(_Cw,_CA))){case 0:return true;case 1:return new F(function(){return _co(_Cx,_CB);});break;default:return false;}break;default:return false;}break;default:return false;}},_CC=function(_CD,_CE){var _CF=E(_CD),_CG=E(_CE);return new F(function(){return _Ct(_CF.a,_CF.b,_CF.c,_CF.d,_CG.a,_CG.b,_CG.c,_CG.d);});},_CH=function(_CI,_CJ,_CK,_CL,_CM,_CN,_CO,_CP){switch(B(_2(_CI,_CM))){case 0:return true;case 1:switch(B(_2(_CJ,_CN))){case 0:return true;case 1:switch(B(_2(_CK,_CO))){case 0:return true;case 1:return new F(function(){return _lm(_CL,_CP);});break;default:return false;}break;default:return false;}break;default:return false;}},_CQ=function(_CR,_CS){var _CT=E(_CR),_CU=E(_CS);return new F(function(){return _CH(_CT.a,_CT.b,_CT.c,_CT.d,_CU.a,_CU.b,_CU.c,_CU.d);});},_CV=function(_CW,_CX){var _CY=E(_CW);if(!_CY._){var _CZ=_CY.a,_D0=E(_CX);return (_D0._==0)?_CZ>_D0.a:I_compareInt(_D0.a,_CZ)<0;}else{var _D1=_CY.a,_D2=E(_CX);return (_D2._==0)?I_compareInt(_D1,_D2.a)>0:I_compare(_D1,_D2.a)>0;}},_D3=function(_D4,_D5,_D6,_D7,_D8,_D9,_Da,_Db){switch(B(_2(_D4,_D8))){case 0:return false;case 1:switch(B(_2(_D5,_D9))){case 0:return false;case 1:switch(B(_2(_D6,_Da))){case 0:return false;case 1:return new F(function(){return _CV(_D7,_Db);});break;default:return true;}break;default:return true;}break;default:return true;}},_Dc=function(_Dd,_De){var _Df=E(_Dd),_Dg=E(_De);return new F(function(){return _D3(_Df.a,_Df.b,_Df.c,_Df.d,_Dg.a,_Dg.b,_Dg.c,_Dg.d);});},_Dh=function(_Di,_Dj,_Dk,_Dl,_Dm,_Dn,_Do,_Dp){switch(B(_2(_Di,_Dm))){case 0:return false;case 1:switch(B(_2(_Dj,_Dn))){case 0:return false;case 1:switch(B(_2(_Dk,_Do))){case 0:return false;case 1:return new F(function(){return _e(_Dl,_Dp);});break;default:return true;}break;default:return true;}break;default:return true;}},_Dq=function(_Dr,_Ds){var _Dt=E(_Dr),_Du=E(_Ds);return new F(function(){return _Dh(_Dt.a,_Dt.b,_Dt.c,_Dt.d,_Du.a,_Du.b,_Du.c,_Du.d);});},_Dv=function(_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD){switch(B(_2(_Dw,_DA))){case 0:return 0;case 1:switch(B(_2(_Dx,_DB))){case 0:return 0;case 1:switch(B(_2(_Dy,_DC))){case 0:return 0;case 1:return new F(function(){return _2(_Dz,_DD);});break;default:return 2;}break;default:return 2;}break;default:return 2;}},_DE=function(_DF,_DG){var _DH=E(_DF),_DI=E(_DG);return new F(function(){return _Dv(_DH.a,_DH.b,_DH.c,_DH.d,_DI.a,_DI.b,_DI.c,_DI.d);});},_DJ=function(_DK,_DL){var _DM=E(_DK),_DN=E(_DL);switch(B(_2(_DM.a,_DN.a))){case 0:return E(_DN);case 1:switch(B(_2(_DM.b,_DN.b))){case 0:return E(_DN);case 1:switch(B(_2(_DM.c,_DN.c))){case 0:return E(_DN);case 1:return (!B(_lm(_DM.d,_DN.d)))?E(_DM):E(_DN);default:return E(_DM);}break;default:return E(_DM);}break;default:return E(_DM);}},_DO=function(_DP,_DQ){var _DR=E(_DP),_DS=E(_DQ);switch(B(_2(_DR.a,_DS.a))){case 0:return E(_DR);case 1:switch(B(_2(_DR.b,_DS.b))){case 0:return E(_DR);case 1:switch(B(_2(_DR.c,_DS.c))){case 0:return E(_DR);case 1:return (!B(_lm(_DR.d,_DS.d)))?E(_DS):E(_DR);default:return E(_DS);}break;default:return E(_DS);}break;default:return E(_DS);}},_DT={_:0,a:_Cs,b:_DE,c:_CC,d:_CQ,e:_Dc,f:_Dq,g:_DJ,h:_DO},_DU=function(_DV,_DW,_DX,_DY){if(!B(_C1(_DV,_DX))){return false;}else{return new F(function(){return _C1(_DW,_DY);});}},_DZ=function(_E0,_E1){var _E2=E(_E0),_E3=E(_E1);return new F(function(){return _DU(_E2.a,_E2.b,_E3.a,_E3.b);});},_E4=function(_E5,_E6,_E7,_E8){return (!B(_C1(_E5,_E7)))?true:(!B(_C1(_E6,_E8)))?true:false;},_E9=function(_Ea,_Eb){var _Ec=E(_Ea),_Ed=E(_Eb);return new F(function(){return _E4(_Ec.a,_Ec.b,_Ed.a,_Ed.b);});},_Ee=new T2(0,_DZ,_E9),_Ef=function(_Eg,_Eh,_Ei,_Ej){switch(B(_2(_Eg,_Ei))){case 0:return 0;case 1:return new F(function(){return _2(_Eh,_Ej);});break;default:return 2;}},_Ek=function(_El,_Em){var _En=E(_El),_Eo=E(_Em);return new F(function(){return _Ef(_En.a,_En.b,_Eo.a,_Eo.b);});},_Ep=function(_Eq,_Er,_Es,_Et){switch(B(_2(_Eq,_Es))){case 0:return true;case 1:return new F(function(){return _co(_Er,_Et);});break;default:return false;}},_Eu=function(_Ev,_Ew){var _Ex=E(_Ev),_Ey=E(_Ew);return new F(function(){return _Ep(_Ex.a,_Ex.b,_Ey.a,_Ey.b);});},_Ez=function(_EA,_EB,_EC,_ED){switch(B(_2(_EA,_EC))){case 0:return true;case 1:return new F(function(){return _lm(_EB,_ED);});break;default:return false;}},_EE=function(_EF,_EG){var _EH=E(_EF),_EI=E(_EG);return new F(function(){return _Ez(_EH.a,_EH.b,_EI.a,_EI.b);});},_EJ=function(_EK,_EL,_EM,_EN){switch(B(_2(_EK,_EM))){case 0:return false;case 1:return new F(function(){return _CV(_EL,_EN);});break;default:return true;}},_EO=function(_EP,_EQ){var _ER=E(_EP),_ES=E(_EQ);return new F(function(){return _EJ(_ER.a,_ER.b,_ES.a,_ES.b);});},_ET=function(_EU,_EV,_EW,_EX){switch(B(_2(_EU,_EW))){case 0:return false;case 1:return new F(function(){return _e(_EV,_EX);});break;default:return true;}},_EY=function(_EZ,_F0){var _F1=E(_EZ),_F2=E(_F0);return new F(function(){return _ET(_F1.a,_F1.b,_F2.a,_F2.b);});},_F3=function(_F4,_F5){var _F6=E(_F4),_F7=E(_F5);switch(B(_2(_F6.a,_F7.a))){case 0:return E(_F7);case 1:return (!B(_lm(_F6.b,_F7.b)))?E(_F6):E(_F7);default:return E(_F6);}},_F8=function(_F9,_Fa){var _Fb=E(_F9),_Fc=E(_Fa);switch(B(_2(_Fb.a,_Fc.a))){case 0:return E(_Fb);case 1:return (!B(_lm(_Fb.b,_Fc.b)))?E(_Fc):E(_Fb);default:return E(_Fc);}},_Fd={_:0,a:_Ee,b:_Ek,c:_Eu,d:_EE,e:_EO,f:_EY,g:_F3,h:_F8},_Fe=function(_Ff,_Fg,_Fh,_Fi){if(!B(_C1(_Ff,_Fh))){return false;}else{return new F(function(){return _C1(_Fg,_Fi);});}},_Fj=function(_Fk,_Fl){var _Fm=E(_Fk),_Fn=E(_Fl);return new F(function(){return _Fe(_Fm.a,_Fm.b,_Fn.a,_Fn.b);});},_Fo=function(_Fp,_Fq,_Fr,_Fs){return (!B(_C1(_Fp,_Fr)))?true:(!B(_C1(_Fq,_Fs)))?true:false;},_Ft=function(_Fu,_Fv){var _Fw=E(_Fu),_Fx=E(_Fv);return new F(function(){return _Fo(_Fw.a,_Fw.b,_Fx.a,_Fx.b);});},_Fy=new T2(0,_Fj,_Ft),_Fz=function(_FA,_FB,_FC,_FD){switch(B(_2(_FA,_FC))){case 0:return 0;case 1:return new F(function(){return _2(_FB,_FD);});break;default:return 2;}},_FE=function(_FF,_FG){var _FH=E(_FF),_FI=E(_FG);return new F(function(){return _Fz(_FH.a,_FH.b,_FI.a,_FI.b);});},_FJ=function(_FK,_FL,_FM,_FN){switch(B(_2(_FK,_FM))){case 0:return true;case 1:return new F(function(){return _co(_FL,_FN);});break;default:return false;}},_FO=function(_FP,_FQ){var _FR=E(_FP),_FS=E(_FQ);return new F(function(){return _FJ(_FR.a,_FR.b,_FS.a,_FS.b);});},_FT=function(_FU,_FV,_FW,_FX){switch(B(_2(_FU,_FW))){case 0:return true;case 1:return new F(function(){return _lm(_FV,_FX);});break;default:return false;}},_FY=function(_FZ,_G0){var _G1=E(_FZ),_G2=E(_G0);return new F(function(){return _FT(_G1.a,_G1.b,_G2.a,_G2.b);});},_G3=function(_G4,_G5,_G6,_G7){switch(B(_2(_G4,_G6))){case 0:return false;case 1:return new F(function(){return _CV(_G5,_G7);});break;default:return true;}},_G8=function(_G9,_Ga){var _Gb=E(_G9),_Gc=E(_Ga);return new F(function(){return _G3(_Gb.a,_Gb.b,_Gc.a,_Gc.b);});},_Gd=function(_Ge,_Gf,_Gg,_Gh){switch(B(_2(_Ge,_Gg))){case 0:return false;case 1:return new F(function(){return _e(_Gf,_Gh);});break;default:return true;}},_Gi=function(_Gj,_Gk){var _Gl=E(_Gj),_Gm=E(_Gk);return new F(function(){return _Gd(_Gl.a,_Gl.b,_Gm.a,_Gm.b);});},_Gn=function(_Go,_Gp){var _Gq=E(_Go),_Gr=E(_Gp);switch(B(_2(_Gq.a,_Gr.a))){case 0:return E(_Gr);case 1:return (!B(_lm(_Gq.b,_Gr.b)))?E(_Gq):E(_Gr);default:return E(_Gq);}},_Gs=function(_Gt,_Gu){var _Gv=E(_Gt),_Gw=E(_Gu);switch(B(_2(_Gv.a,_Gw.a))){case 0:return E(_Gv);case 1:return (!B(_lm(_Gv.b,_Gw.b)))?E(_Gw):E(_Gv);default:return E(_Gw);}},_Gx={_:0,a:_Fy,b:_FE,c:_FO,d:_FY,e:_G8,f:_Gi,g:_Gn,h:_Gs},_Gy=function(_Gz,_GA){var _GB=E(_Gz),_GC=E(_GA);return (!B(_C1(_GB.a,_GC.a)))?true:(!B(_C1(_GB.b,_GC.b)))?true:(!B(_C1(_GB.c,_GC.c)))?true:false;},_GD=function(_GE,_GF,_GG,_GH,_GI,_GJ){if(!B(_C1(_GE,_GH))){return false;}else{if(!B(_C1(_GF,_GI))){return false;}else{return new F(function(){return _C1(_GG,_GJ);});}}},_GK=function(_GL,_GM){var _GN=E(_GL),_GO=E(_GM);return new F(function(){return _GD(_GN.a,_GN.b,_GN.c,_GO.a,_GO.b,_GO.c);});},_GP=new T2(0,_GK,_Gy),_GQ=function(_GR,_GS,_GT,_GU,_GV,_GW){switch(B(_2(_GR,_GU))){case 0:return true;case 1:switch(B(_2(_GS,_GV))){case 0:return true;case 1:return new F(function(){return _co(_GT,_GW);});break;default:return false;}break;default:return false;}},_GX=function(_GY,_GZ){var _H0=E(_GY),_H1=E(_GZ);return new F(function(){return _GQ(_H0.a,_H0.b,_H0.c,_H1.a,_H1.b,_H1.c);});},_H2=function(_H3,_H4,_H5,_H6,_H7,_H8){switch(B(_2(_H3,_H6))){case 0:return true;case 1:switch(B(_2(_H4,_H7))){case 0:return true;case 1:return new F(function(){return _lm(_H5,_H8);});break;default:return false;}break;default:return false;}},_H9=function(_Ha,_Hb){var _Hc=E(_Ha),_Hd=E(_Hb);return new F(function(){return _H2(_Hc.a,_Hc.b,_Hc.c,_Hd.a,_Hd.b,_Hd.c);});},_He=function(_Hf,_Hg,_Hh,_Hi,_Hj,_Hk){switch(B(_2(_Hf,_Hi))){case 0:return false;case 1:switch(B(_2(_Hg,_Hj))){case 0:return false;case 1:return new F(function(){return _CV(_Hh,_Hk);});break;default:return true;}break;default:return true;}},_Hl=function(_Hm,_Hn){var _Ho=E(_Hm),_Hp=E(_Hn);return new F(function(){return _He(_Ho.a,_Ho.b,_Ho.c,_Hp.a,_Hp.b,_Hp.c);});},_Hq=function(_Hr,_Hs,_Ht,_Hu,_Hv,_Hw){switch(B(_2(_Hr,_Hu))){case 0:return false;case 1:switch(B(_2(_Hs,_Hv))){case 0:return false;case 1:return new F(function(){return _e(_Ht,_Hw);});break;default:return true;}break;default:return true;}},_Hx=function(_Hy,_Hz){var _HA=E(_Hy),_HB=E(_Hz);return new F(function(){return _Hq(_HA.a,_HA.b,_HA.c,_HB.a,_HB.b,_HB.c);});},_HC=function(_HD,_HE,_HF,_HG,_HH,_HI){switch(B(_2(_HD,_HG))){case 0:return 0;case 1:switch(B(_2(_HE,_HH))){case 0:return 0;case 1:return new F(function(){return _2(_HF,_HI);});break;default:return 2;}break;default:return 2;}},_HJ=function(_HK,_HL){var _HM=E(_HK),_HN=E(_HL);return new F(function(){return _HC(_HM.a,_HM.b,_HM.c,_HN.a,_HN.b,_HN.c);});},_HO=function(_HP,_HQ){var _HR=E(_HP),_HS=E(_HQ);switch(B(_2(_HR.a,_HS.a))){case 0:return E(_HS);case 1:switch(B(_2(_HR.b,_HS.b))){case 0:return E(_HS);case 1:return (!B(_lm(_HR.c,_HS.c)))?E(_HR):E(_HS);default:return E(_HR);}break;default:return E(_HR);}},_HT=function(_HU,_HV){var _HW=E(_HU),_HX=E(_HV);switch(B(_2(_HW.a,_HX.a))){case 0:return E(_HW);case 1:switch(B(_2(_HW.b,_HX.b))){case 0:return E(_HW);case 1:return (!B(_lm(_HW.c,_HX.c)))?E(_HX):E(_HW);default:return E(_HX);}break;default:return E(_HX);}},_HY={_:0,a:_GP,b:_HJ,c:_GX,d:_H9,e:_Hl,f:_Hx,g:_HO,h:_HT},_HZ=__Z,_I0=__Z,_I1=function(_I2){return E(E(_I2).b);},_I3=function(_I4,_I5,_I6){var _I7=E(_I5);if(!_I7._){return E(_I6);}else{var _I8=function(_I9,_Ia){while(1){var _Ib=E(_Ia);if(!_Ib._){var _Ic=_Ib.b,_Id=_Ib.e;switch(B(A3(_I1,_I4,_I9,_Ic))){case 0:return new F(function(){return _2B(_Ic,_Ib.c,B(_I8(_I9,_Ib.d)),_Id);});break;case 1:return E(_Id);default:_Ia=_Id;continue;}}else{return new T0(1);}}};return new F(function(){return _I8(_I7.a,_I6);});}},_Ie=function(_If,_Ig,_Ih){var _Ii=E(_Ig);if(!_Ii._){return E(_Ih);}else{var _Ij=function(_Ik,_Il){while(1){var _Im=E(_Il);if(!_Im._){var _In=_Im.b,_Io=_Im.d;switch(B(A3(_I1,_If,_In,_Ik))){case 0:return new F(function(){return _2B(_In,_Im.c,_Io,B(_Ij(_Ik,_Im.e)));});break;case 1:return E(_Io);default:_Il=_Io;continue;}}else{return new T0(1);}}};return new F(function(){return _Ij(_Ii.a,_Ih);});}},_Ip=function(_Iq,_Ir,_Is,_It){var _Iu=E(_Ir),_Iv=E(_It);if(!_Iv._){var _Iw=_Iv.b,_Ix=_Iv.c,_Iy=_Iv.d,_Iz=_Iv.e;switch(B(A3(_I1,_Iq,_Iu,_Iw))){case 0:return new F(function(){return _1h(_Iw,_Ix,B(_Ip(_Iq,_Iu,_Is,_Iy)),_Iz);});break;case 1:return E(_Iv);default:return new F(function(){return _q(_Iw,_Ix,_Iy,B(_Ip(_Iq,_Iu,_Is,_Iz)));});}}else{return new T5(0,1,E(_Iu),_Is,E(_0),E(_0));}},_IA=function(_IB,_IC,_ID,_IE){return new F(function(){return _Ip(_IB,_IC,_ID,_IE);});},_IF=function(_IG){return E(E(_IG).d);},_IH=function(_II){return E(E(_II).f);},_IJ=function(_IK,_IL,_IM,_IN){var _IO=E(_IL);if(!_IO._){var _IP=E(_IM);if(!_IP._){return E(_IN);}else{var _IQ=function(_IR,_IS){while(1){var _IT=E(_IS);if(!_IT._){if(!B(A3(_IH,_IK,_IT.b,_IR))){return E(_IT);}else{_IS=_IT.d;continue;}}else{return new T0(1);}}};return new F(function(){return _IQ(_IP.a,_IN);});}}else{var _IU=_IO.a,_IV=E(_IM);if(!_IV._){var _IW=function(_IX,_IY){while(1){var _IZ=E(_IY);if(!_IZ._){if(!B(A3(_IF,_IK,_IZ.b,_IX))){return E(_IZ);}else{_IY=_IZ.e;continue;}}else{return new T0(1);}}};return new F(function(){return _IW(_IU,_IN);});}else{var _J0=function(_J1,_J2,_J3){while(1){var _J4=E(_J3);if(!_J4._){var _J5=_J4.b;if(!B(A3(_IF,_IK,_J5,_J1))){if(!B(A3(_IH,_IK,_J5,_J2))){return E(_J4);}else{_J3=_J4.d;continue;}}else{_J3=_J4.e;continue;}}else{return new T0(1);}}};return new F(function(){return _J0(_IU,_IV.a,_IN);});}}},_J6=function(_J7,_J8,_J9,_Ja,_Jb){var _Jc=E(_Jb);if(!_Jc._){var _Jd=_Jc.b,_Je=_Jc.c,_Jf=_Jc.d,_Jg=_Jc.e,_Jh=E(_Ja);if(!_Jh._){var _Ji=_Jh.b,_Jj=function(_Jk){var _Jl=new T1(1,E(_Ji));return new F(function(){return _2B(_Ji,_Jh.c,B(_J6(_J7,_J8,_Jl,_Jh.d,B(_IJ(_J7,_J8,_Jl,_Jc)))),B(_J6(_J7,_Jl,_J9,_Jh.e,B(_IJ(_J7,_Jl,_J9,_Jc)))));});};if(!E(_Jf)._){return new F(function(){return _Jj(_);});}else{if(!E(_Jg)._){return new F(function(){return _Jj(_);});}else{return new F(function(){return _IA(_J7,_Jd,_Je,_Jh);});}}}else{return new F(function(){return _2B(_Jd,_Je,B(_I3(_J7,_J8,_Jf)),B(_Ie(_J7,_J9,_Jg)));});}}else{return E(_Ja);}},_Jm=function(_Jn,_Jo,_Jp,_Jq,_Jr,_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz){var _JA=function(_JB){var _JC=new T1(1,E(_Jr));return new F(function(){return _2B(_Jr,_Js,B(_J6(_Jn,_Jo,_JC,_Jt,B(_IJ(_Jn,_Jo,_JC,new T5(0,_Jv,E(_Jw),_Jx,E(_Jy),E(_Jz)))))),B(_J6(_Jn,_JC,_Jp,_Ju,B(_IJ(_Jn,_JC,_Jp,new T5(0,_Jv,E(_Jw),_Jx,E(_Jy),E(_Jz)))))));});};if(!E(_Jy)._){return new F(function(){return _JA(_);});}else{if(!E(_Jz)._){return new F(function(){return _JA(_);});}else{return new F(function(){return _IA(_Jn,_Jw,_Jx,new T5(0,_Jq,E(_Jr),_Js,E(_Jt),E(_Ju)));});}}},_JD=function(_JE,_JF,_JG){var _JH=E(_JF);if(!_JH._){return E(_JG);}else{var _JI=function(_JJ,_JK){while(1){var _JL=E(_JK);if(!_JL._){var _JM=_JL.b,_JN=_JL.d;switch(B(A3(_I1,_JE,_JJ,_JM))){case 0:return new F(function(){return _6C(_JM,B(_JI(_JJ,_JL.c)),_JN);});break;case 1:return E(_JN);default:_JK=_JN;continue;}}else{return new T0(1);}}};return new F(function(){return _JI(_JH.a,_JG);});}},_JO=function(_JP,_JQ,_JR){var _JS=E(_JQ);if(!_JS._){return E(_JR);}else{var _JT=function(_JU,_JV){while(1){var _JW=E(_JV);if(!_JW._){var _JX=_JW.b,_JY=_JW.c;switch(B(A3(_I1,_JP,_JX,_JU))){case 0:return new F(function(){return _6C(_JX,_JY,B(_JT(_JU,_JW.d)));});break;case 1:return E(_JY);default:_JV=_JY;continue;}}else{return new T0(1);}}};return new F(function(){return _JT(_JS.a,_JR);});}},_JZ=function(_K0,_K1,_K2){var _K3=E(_K1),_K4=E(_K2);if(!_K4._){var _K5=_K4.b,_K6=_K4.c,_K7=_K4.d;switch(B(A3(_I1,_K0,_K3,_K5))){case 0:return new F(function(){return _5q(_K5,B(_JZ(_K0,_K3,_K6)),_K7);});break;case 1:return E(_K4);default:return new F(function(){return _4G(_K5,_K6,B(_JZ(_K0,_K3,_K7)));});}}else{return new T4(0,1,E(_K3),E(_4B),E(_4B));}},_K8=function(_K9,_Ka,_Kb){return new F(function(){return _JZ(_K9,_Ka,_Kb);});},_Kc=function(_Kd,_Ke,_Kf,_Kg){var _Kh=E(_Ke);if(!_Kh._){var _Ki=E(_Kf);if(!_Ki._){return E(_Kg);}else{var _Kj=function(_Kk,_Kl){while(1){var _Km=E(_Kl);if(!_Km._){if(!B(A3(_IH,_Kd,_Km.b,_Kk))){return E(_Km);}else{_Kl=_Km.c;continue;}}else{return new T0(1);}}};return new F(function(){return _Kj(_Ki.a,_Kg);});}}else{var _Kn=_Kh.a,_Ko=E(_Kf);if(!_Ko._){var _Kp=function(_Kq,_Kr){while(1){var _Ks=E(_Kr);if(!_Ks._){if(!B(A3(_IF,_Kd,_Ks.b,_Kq))){return E(_Ks);}else{_Kr=_Ks.d;continue;}}else{return new T0(1);}}};return new F(function(){return _Kp(_Kn,_Kg);});}else{var _Kt=function(_Ku,_Kv,_Kw){while(1){var _Kx=E(_Kw);if(!_Kx._){var _Ky=_Kx.b;if(!B(A3(_IF,_Kd,_Ky,_Ku))){if(!B(A3(_IH,_Kd,_Ky,_Kv))){return E(_Kx);}else{_Kw=_Kx.c;continue;}}else{_Kw=_Kx.d;continue;}}else{return new T0(1);}}};return new F(function(){return _Kt(_Kn,_Ko.a,_Kg);});}}},_Kz=function(_KA,_KB,_KC,_KD,_KE){var _KF=E(_KE);if(!_KF._){var _KG=_KF.b,_KH=_KF.c,_KI=_KF.d,_KJ=E(_KD);if(!_KJ._){var _KK=_KJ.b,_KL=function(_KM){var _KN=new T1(1,E(_KK));return new F(function(){return _6C(_KK,B(_Kz(_KA,_KB,_KN,_KJ.c,B(_Kc(_KA,_KB,_KN,_KF)))),B(_Kz(_KA,_KN,_KC,_KJ.d,B(_Kc(_KA,_KN,_KC,_KF)))));});};if(!E(_KH)._){return new F(function(){return _KL(_);});}else{if(!E(_KI)._){return new F(function(){return _KL(_);});}else{return new F(function(){return _K8(_KA,_KG,_KJ);});}}}else{return new F(function(){return _6C(_KG,B(_JD(_KA,_KB,_KH)),B(_JO(_KA,_KC,_KI)));});}}else{return E(_KD);}},_KO=function(_KP,_KQ,_KR,_KS,_KT,_KU,_KV,_KW,_KX,_KY,_KZ){var _L0=function(_L1){var _L2=new T1(1,E(_KT));return new F(function(){return _6C(_KT,B(_Kz(_KP,_KQ,_L2,_KU,B(_Kc(_KP,_KQ,_L2,new T4(0,_KW,E(_KX),E(_KY),E(_KZ)))))),B(_Kz(_KP,_L2,_KR,_KV,B(_Kc(_KP,_L2,_KR,new T4(0,_KW,E(_KX),E(_KY),E(_KZ)))))));});};if(!E(_KY)._){return new F(function(){return _L0(_);});}else{if(!E(_KZ)._){return new F(function(){return _L0(_);});}else{return new F(function(){return _K8(_KP,_KX,new T4(0,_KS,E(_KT),E(_KU),E(_KV)));});}}},_L3=function(_L4,_L5,_L6,_L7,_L8,_L9,_La,_Lb){return new T4(0,new T(function(){var _Lc=E(_L4);if(!_Lc._){var _Ld=E(_L8);if(!_Ld._){return B(_KO(_DT,_I0,_I0,_Lc.a,_Lc.b,_Lc.c,_Lc.d,_Ld.a,_Ld.b,_Ld.c,_Ld.d));}else{return E(_Lc);}}else{return E(_L8);}}),new T(function(){var _Le=E(_L5);if(!_Le._){var _Lf=E(_L9);if(!_Lf._){return B(_KO(_HY,_I0,_I0,_Le.a,_Le.b,_Le.c,_Le.d,_Lf.a,_Lf.b,_Lf.c,_Lf.d));}else{return E(_Le);}}else{return E(_L9);}}),new T(function(){var _Lg=E(_L6);if(!_Lg._){var _Lh=E(_La);if(!_Lh._){return B(_Jm(_Gx,_HZ,_HZ,_Lg.a,_Lg.b,_Lg.c,_Lg.d,_Lg.e,_Lh.a,_Lh.b,_Lh.c,_Lh.d,_Lh.e));}else{return E(_Lg);}}else{return E(_La);}}),new T(function(){var _Li=E(_L7);if(!_Li._){var _Lj=E(_Lb);if(!_Lj._){return B(_Jm(_Fd,_HZ,_HZ,_Li.a,_Li.b,_Li.c,_Li.d,_Li.e,_Lj.a,_Lj.b,_Lj.c,_Lj.d,_Lj.e));}else{return E(_Li);}}else{return E(_Lb);}}));},_Lk=function(_Ll,_Lm){while(1){var _Ln=E(_Ll),_Lo=E(_Lm);if(!_Lo._){switch(B(_2(_Ln,_Lo.b))){case 0:_Ll=_Ln;_Lm=_Lo.d;continue;case 1:return new T1(1,_Lo.c);default:_Ll=_Ln;_Lm=_Lo.e;continue;}}else{return __Z;}}},_Lp=function(_Lq,_Lr,_Ls){while(1){var _Lt=E(_Ls);if(!_Lt._){var _Lu=_Lt.d,_Lv=_Lt.e,_Lw=E(_Lt.b);switch(B(_2(_Lq,_Lw.a))){case 0:_Ls=_Lu;continue;case 1:switch(B(_2(_Lr,_Lw.b))){case 0:_Ls=_Lu;continue;case 1:return new T1(1,_Lt.c);default:_Ls=_Lv;continue;}break;default:_Ls=_Lv;continue;}}else{return __Z;}}},_Lx=function(_Ly){return new T1(0,0);},_Lz=new T(function(){return B(_Lx(_));}),_LA=function(_LB,_LC,_LD){while(1){var _LE=E(_LD);switch(_LE._){case 0:var _LF=B(_Lk(_LE.a,_LB));if(!_LF._){return E(_Lz);}else{var _LG=E(E(_LF.a).b);return (_LG._==0)?E(_LG.a):E(_Lz);}break;case 1:return new F(function(){return _ji(B(_LA(_LB,_LC,_LE.a)),B(_LA(_LB,_LC,_LE.b)));});break;case 2:return E(_LE.a);default:var _LH=B(_Lp(_LE.a,_LE.b,_LC));if(!_LH._){_LD=_LE.c;continue;}else{return E(_LH.a);}}}},_LI=function(_LJ,_LK){var _LL=E(_LJ);return new F(function(){return _LA(_LL.a,_LL.b,_LK);});},_LM=function(_LN,_LO){var _LP=E(_LN);switch(_LP._){case 1:var _LQ=_LP.a,_LR=E(_LO),_LS=_LR.a;return (!B(_BW(_LQ,_LS)))?new T4(0,new T4(0,1,E(new T4(0,_LQ,_LP.b,new T(function(){return B(_LA(_LS,_LR.b,_LP.c));}),_LP.e)),E(_4B),E(_4B)),_4B,_0,_0):new T4(0,_4B,_4B,_0,_0);case 2:var _LT=_LP.a,_LU=B(_BR(_LT,E(_LO).a));if(!_LU._){return new T4(0,_4B,_4B,_0,_0);}else{var _LV=E(_LU.a),_LW=E(_LV.b);return (_LW._==0)?new T4(0,_4B,new T4(0,1,E(new T3(0,_LT,_LV.a,_LW.a)),E(_4B),E(_4B)),_0,_0):new T4(0,_4B,_4B,_0,_0);}break;case 3:return new T4(0,_4B,_4B,new T5(0,1,E(new T2(0,_LP.a,_LP.c)),new T(function(){return B(_LI(_LO,_LP.d));}),E(_0),E(_0)),_0);case 4:var _LX=B(_LM(_LP.a,_LO)),_LY=B(_LM(_LP.b,_LO));return new F(function(){return _L3(_LX.a,_LX.b,_LX.c,_LX.d,_LY.a,_LY.b,_LY.c,_LY.d);});break;default:return new T4(0,_4B,_4B,_0,_0);}},_LZ=function(_M0,_M1){var _M2=new T(function(){var _M3=new T(function(){return E(E(_M0).b);}),_M4=function(_M5,_M6){while(1){var _M7=B((function(_M8,_M9){var _Ma=E(_M9);if(!_Ma._){var _Mb=_Ma.e,_Mc=new T(function(){var _Md=E(_Ma.c),_Me=E(_Md.b);if(!_Me._){if(!B(_lm(_Me.b,_M3))){return B(_M4(_M8,_Mb));}else{return new T2(1,new T3(0,_Ma.b,_Md.a,_Me.a),new T(function(){return B(_M4(_M8,_Mb));}));}}else{return B(_M4(_M8,_Mb));}},1);_M5=_Mc;_M6=_Ma.d;return __continue;}else{return E(_M8);}})(_M5,_M6));if(_M7!=__continue){return _M7;}}};return B(_8f(B(_M4(_1,_M1))));});return new T4(0,_4B,_M2,_0,_0);},_Mf=function(_Mg,_Mh,_Mi,_Mj,_Mk){while(1){var _Ml=E(_Mg);if(!_Ml._){return new T4(0,_Mh,_Mi,_Mj,_Mk);}else{var _Mm=E(_Ml.a),_Mn=B(_L3(_Mh,_Mi,_Mj,_Mk,_Mm.a,_Mm.b,_Mm.c,_Mm.d));_Mg=_Ml.b;_Mh=_Mn.a;_Mi=_Mn.b;_Mj=_Mn.c;_Mk=_Mn.d;continue;}}},_Mo=function(_Mp,_Mq,_Mr,_Ms,_Mt,_Mu){var _Mv=E(_Mp),_Mw=B(_L3(_Mr,_Ms,_Mt,_Mu,_Mv.a,_Mv.b,_Mv.c,_Mv.d));return new F(function(){return _Mf(_Mq,_Mw.a,_Mw.b,_Mw.c,_Mw.d);});},_Mx=function(_My,_Mz,_MA){while(1){var _MB=E(_MA);if(!_MB._){var _MC=_MB.d,_MD=_MB.e,_ME=E(_MB.b);switch(B(_2(_My,_ME.a))){case 0:_MA=_MC;continue;case 1:switch(B(_2(_Mz,_ME.b))){case 0:_MA=_MC;continue;case 1:return true;default:_MA=_MD;continue;}break;default:_MA=_MD;continue;}}else{return false;}}},_MF=new T1(0,0),_MG=function(_MH,_MI,_MJ){while(1){var _MK=B((function(_ML,_MM,_MN){var _MO=E(_MN);switch(_MO._){case 1:var _MP=B(_MG(_ML,_MM,_MO.a));return new F(function(){return _Mo(new T(function(){var _MQ=B(_MG(_ML,_MM,_MO.b));return new T4(0,_MQ.a,_MQ.b,_MQ.c,_MQ.d);}),_1,_MP.a,_MP.b,_MP.c,_MP.d);});break;case 3:var _MR=_MO.a,_MS=_MO.b,_MT=_MO.c;if(!B(_Mx(_MR,_MS,_MM))){var _MU=B(_MG(_ML,_MM,_MT));return new F(function(){return _L3(_4B,_4B,_0,new T5(0,1,E(new T2(0,_MR,_MS)),_MF,E(_0),E(_0)),_MU.a,_MU.b,_MU.c,_MU.d);});}else{var _MV=_ML,_MW=_MM;_MH=_MV;_MI=_MW;_MJ=_MT;return __continue;}break;default:return new T4(0,_4B,_4B,_0,_0);}})(_MH,_MI,_MJ));if(_MK!=__continue){return _MK;}}},_MX=function(_MY,_MZ){var _N0=E(_MZ);switch(_N0._){case 1:var _N1=B(_MX(_MY,_N0.a));return new F(function(){return _Mo(new T(function(){var _N2=B(_MX(_MY,_N0.b));return new T4(0,_N2.a,_N2.b,_N2.c,_N2.d);}),_1,_N1.a,_N1.b,_N1.c,_N1.d);});break;case 3:var _N3=_N0.a,_N4=_N0.b,_N5=_N0.c,_N6=E(_MY),_N7=_N6.a,_N8=_N6.b;if(!B(_Mx(_N3,_N4,_N8))){var _N9=B(_MG(_N7,_N8,_N5));return new F(function(){return _L3(_4B,_4B,_0,new T5(0,1,E(new T2(0,_N3,_N4)),_MF,E(_0),E(_0)),_N9.a,_N9.b,_N9.c,_N9.d);});}else{return new F(function(){return _MG(_N7,_N8,_N5);});}break;default:return new T4(0,_4B,_4B,_0,_0);}},_Na=function(_Nb,_Nc,_Nd,_Ne,_Nf){while(1){var _Ng=E(_Nb);if(!_Ng._){return new T4(0,_Nc,_Nd,_Ne,_Nf);}else{var _Nh=E(_Ng.a),_Ni=B(_L3(_Nc,_Nd,_Ne,_Nf,_Nh.a,_Nh.b,_Nh.c,_Nh.d));_Nb=_Ng.b;_Nc=_Ni.a;_Nd=_Ni.b;_Ne=_Ni.c;_Nf=_Ni.d;continue;}}},_Nj=function(_Nk,_Nl,_Nm,_Nn,_No){while(1){var _Np=E(_Nk);if(!_Np._){return new T4(0,_Nl,_Nm,_Nn,_No);}else{var _Nq=E(_Np.a),_Nr=B(_L3(_Nl,_Nm,_Nn,_No,_Nq.a,_Nq.b,_Nq.c,_Nq.d));_Nk=_Np.b;_Nl=_Nr.a;_Nm=_Nr.b;_Nn=_Nr.c;_No=_Nr.d;continue;}}},_Ns=function(_Nt,_Nu,_Nv,_Nw,_Nx){while(1){var _Ny=E(_Nt);if(!_Ny._){return new T4(0,_Nu,_Nv,_Nw,_Nx);}else{var _Nz=E(_Ny.a),_NA=B(_L3(_Nu,_Nv,_Nw,_Nx,_Nz.a,_Nz.b,_Nz.c,_Nz.d));_Nt=_Ny.b;_Nu=_NA.a;_Nv=_NA.b;_Nw=_NA.c;_Nx=_NA.d;continue;}}},_NB=function(_NC,_ND){var _NE=B(_MX(_NC,_ND));return new T4(0,_NE.a,_NE.b,_NE.c,_NE.d);},_NF=function(_NG,_NH){var _NI=B(_NJ(_NG,_NH));return new T4(0,_NI.a,_NI.b,_NI.c,_NI.d);},_NJ=function(_NK,_NL){while(1){var _NM=B((function(_NN,_NO){var _NP=E(_NO);switch(_NP._){case 1:var _NQ=B(_NJ(_NN,_NP.a));return new F(function(){return _Ns(new T2(1,new T(function(){return B(_NF(_NN,_NP.b));}),_1),_NQ.a,_NQ.b,_NQ.c,_NQ.d);});break;case 2:var _NR=B(_NJ(_NN,_NP.a));return new F(function(){return _Nj(new T2(1,new T(function(){return B(_NF(_NN,_NP.b));}),_1),_NR.a,_NR.b,_NR.c,_NR.d);});break;case 3:var _NS=_NN;_NK=_NS;_NL=_NP.a;return __continue;case 4:var _NT=_NP.a,_NU=_NP.b;return (!B(_Mx(_NT,_NU,E(_NN).b)))?new T4(0,_4B,_4B,_0,new T5(0,1,E(new T2(0,_NT,_NU)),_MF,E(_0),E(_0))):new T4(0,_4B,_4B,_0,_0);case 5:var _NV=_NP.a,_NW=_NP.b;return (!B(_Mx(_NV,_NW,E(_NN).b)))?new T4(0,_4B,_4B,_0,new T5(0,1,E(new T2(0,_NV,_NW)),_MF,E(_0),E(_0))):new T4(0,_4B,_4B,_0,_0);case 6:var _NX=B(_MX(_NN,_NP.a));return new F(function(){return _Na(new T2(1,new T(function(){return B(_NB(_NN,_NP.b));}),_1),_NX.a,_NX.b,_NX.c,_NX.d);});break;default:return new T4(0,_4B,_4B,_0,_0);}})(_NK,_NL));if(_NM!=__continue){return _NM;}}},_NY=function(_NZ,_O0,_O1,_O2,_O3){while(1){var _O4=E(_NZ);if(!_O4._){return new T4(0,_O0,_O1,_O2,_O3);}else{var _O5=E(_O4.a),_O6=B(_L3(_O0,_O1,_O2,_O3,_O5.a,_O5.b,_O5.c,_O5.d));_NZ=_O4.b;_O0=_O6.a;_O1=_O6.b;_O2=_O6.c;_O3=_O6.d;continue;}}},_O7=function(_O8,_O9){var _Oa=B(_Ob(_O8,_O9));return new T4(0,_Oa.a,_Oa.b,_Oa.c,_Oa.d);},_Ob=function(_Oc,_Od){while(1){var _Oe=B((function(_Of,_Og){var _Oh=E(_Og);switch(_Oh._){case 0:return new T4(0,_4B,_4B,_0,_0);case 1:var _Oi=B(_MX(_Of,_Oh.c)),_Oj=B(_Ob(_Of,_Oh.f)),_Ok=B(_L3(_Oi.a,_Oi.b,_Oi.c,_Oi.d,_Oj.a,_Oj.b,_Oj.c,_Oj.d)),_Ol=B(_Ob(_Of,_Oh.g));return new F(function(){return _L3(_Ok.a,_Ok.b,_Ok.c,_Ok.d,_Ol.a,_Ol.b,_Ol.c,_Ol.d);});break;case 2:var _Om=_Of;_Oc=_Om;_Od=_Oh.b;return __continue;case 3:var _On=B(_MX(_Of,_Oh.d)),_Oo=B(_Ob(_Of,_Oh.f));return new F(function(){return _L3(_On.a,_On.b,_On.c,_On.d,_Oo.a,_Oo.b,_Oo.c,_Oo.d);});break;case 4:var _Op=B(_Ob(_Of,_Oh.a));return new F(function(){return _NY(new T2(1,new T(function(){return B(_O7(_Of,_Oh.b));}),_1),_Op.a,_Op.b,_Op.c,_Op.d);});break;case 5:var _Oq=B(_NJ(_Of,_Oh.a)),_Or=B(_Ob(_Of,_Oh.b)),_Os=B(_L3(_Oq.a,_Oq.b,_Oq.c,_Oq.d,_Or.a,_Or.b,_Or.c,_Or.d)),_Ot=B(_Ob(_Of,_Oh.c));return new F(function(){return _L3(_Os.a,_Os.b,_Os.c,_Os.d,_Ot.a,_Ot.b,_Ot.c,_Ot.d);});break;default:var _Ou=B(_NJ(_Of,_Oh.a)),_Ov=B(_Ob(_Of,_Oh.c)),_Ow=B(_L3(_Ou.a,_Ou.b,_Ou.c,_Ou.d,_Ov.a,_Ov.b,_Ov.c,_Ov.d)),_Ox=B(_Ob(_Of,_Oh.d));return new F(function(){return _L3(_Ow.a,_Ow.b,_Ow.c,_Ow.d,_Ox.a,_Ox.b,_Ox.c,_Ox.d);});}})(_Oc,_Od));if(_Oe!=__continue){return _Oe;}}},_Oy=function(_Oz,_OA){var _OB=E(_Oz);if(!_OB._){var _OC=_OB.a,_OD=E(_OA);return (_OD._==0)?_OC!=_OD.a:(I_compareInt(_OD.a,_OC)==0)?false:true;}else{var _OE=_OB.a,_OF=E(_OA);return (_OF._==0)?(I_compareInt(_OE,_OF.a)==0)?false:true:(I_compare(_OE,_OF.a)==0)?false:true;}},_OG=new T2(0,_C1,_Oy),_OH=function(_OI,_OJ){return (!B(_lm(_OI,_OJ)))?E(_OI):E(_OJ);},_OK=function(_OL,_OM){return (!B(_lm(_OL,_OM)))?E(_OM):E(_OL);},_ON={_:0,a:_OG,b:_2,c:_co,d:_lm,e:_CV,f:_e,g:_OH,h:_OK},_OO=function(_OP,_OQ,_OR,_OS){while(1){var _OT=E(_OS);if(!_OT._){var _OU=_OT.c,_OV=_OT.d,_OW=E(_OT.b);switch(B(_2(_OP,_OW.a))){case 0:_OS=_OU;continue;case 1:switch(B(_2(_OQ,_OW.b))){case 0:_OS=_OU;continue;case 1:switch(B(_2(_OR,_OW.c))){case 0:_OS=_OU;continue;case 1:return true;default:_OS=_OV;continue;}break;default:_OS=_OV;continue;}break;default:_OS=_OV;continue;}}else{return false;}}},_OX=function(_OY,_OZ,_P0,_P1,_P2){var _P3=E(_P2);if(!_P3._){if(!B(_lm(_P3.b,_OZ))){return false;}else{return new F(function(){return _OO(_P0,_P1,_P3.a,E(_OY).b);});}}else{return false;}},_P4=function(_P5,_P6,_P7,_P8,_P9){var _Pa=E(_P9);if(!_Pa._){var _Pb=new T(function(){var _Pc=B(_P4(_Pa.a,_Pa.b,_Pa.c,_Pa.d,_Pa.e));return new T2(0,_Pc.a,_Pc.b);});return new T2(0,new T(function(){return E(E(_Pb).a);}),new T(function(){return B(_1h(_P6,_P7,_P8,E(_Pb).b));}));}else{return new T2(0,new T2(0,_P6,_P7),_P8);}},_Pd=function(_Pe,_Pf,_Pg,_Ph,_Pi){var _Pj=E(_Ph);if(!_Pj._){var _Pk=new T(function(){var _Pl=B(_Pd(_Pj.a,_Pj.b,_Pj.c,_Pj.d,_Pj.e));return new T2(0,_Pl.a,_Pl.b);});return new T2(0,new T(function(){return E(E(_Pk).a);}),new T(function(){return B(_q(_Pf,_Pg,E(_Pk).b,_Pi));}));}else{return new T2(0,new T2(0,_Pf,_Pg),_Pi);}},_Pm=function(_Pn,_Po){var _Pp=E(_Pn);if(!_Pp._){var _Pq=_Pp.a,_Pr=E(_Po);if(!_Pr._){var _Ps=_Pr.a;if(_Pq<=_Ps){var _Pt=B(_Pd(_Ps,_Pr.b,_Pr.c,_Pr.d,_Pr.e)),_Pu=E(_Pt.a);return new F(function(){return _1h(_Pu.a,_Pu.b,_Pp,_Pt.b);});}else{var _Pv=B(_P4(_Pq,_Pp.b,_Pp.c,_Pp.d,_Pp.e)),_Pw=E(_Pv.a);return new F(function(){return _q(_Pw.a,_Pw.b,_Pv.b,_Pr);});}}else{return E(_Pp);}}else{return E(_Po);}},_Px=function(_Py,_Pz,_PA,_PB,_PC,_PD){var _PE=E(_Py);if(!_PE._){var _PF=_PE.a,_PG=_PE.b,_PH=_PE.c,_PI=_PE.d,_PJ=_PE.e;if((imul(3,_PF)|0)>=_Pz){if((imul(3,_Pz)|0)>=_PF){return new F(function(){return _Pm(_PE,new T5(0,_Pz,E(_PA),_PB,E(_PC),E(_PD)));});}else{return new F(function(){return _q(_PG,_PH,_PI,B(_Px(_PJ,_Pz,_PA,_PB,_PC,_PD)));});}}else{return new F(function(){return _1h(_PA,_PB,B(_PK(_PF,_PG,_PH,_PI,_PJ,_PC)),_PD);});}}else{return new T5(0,_Pz,E(_PA),_PB,E(_PC),E(_PD));}},_PK=function(_PL,_PM,_PN,_PO,_PP,_PQ){var _PR=E(_PQ);if(!_PR._){var _PS=_PR.a,_PT=_PR.b,_PU=_PR.c,_PV=_PR.d,_PW=_PR.e;if((imul(3,_PL)|0)>=_PS){if((imul(3,_PS)|0)>=_PL){return new F(function(){return _Pm(new T5(0,_PL,E(_PM),_PN,E(_PO),E(_PP)),_PR);});}else{return new F(function(){return _q(_PM,_PN,_PO,B(_Px(_PP,_PS,_PT,_PU,_PV,_PW)));});}}else{return new F(function(){return _1h(_PT,_PU,B(_PK(_PL,_PM,_PN,_PO,_PP,_PV)),_PW);});}}else{return new T5(0,_PL,E(_PM),_PN,E(_PO),E(_PP));}},_PX=function(_PY,_PZ){var _Q0=E(_PY);if(!_Q0._){var _Q1=_Q0.a,_Q2=_Q0.b,_Q3=_Q0.c,_Q4=_Q0.d,_Q5=_Q0.e,_Q6=E(_PZ);if(!_Q6._){var _Q7=_Q6.a,_Q8=_Q6.b,_Q9=_Q6.c,_Qa=_Q6.d,_Qb=_Q6.e;if((imul(3,_Q1)|0)>=_Q7){if((imul(3,_Q7)|0)>=_Q1){return new F(function(){return _Pm(_Q0,_Q6);});}else{return new F(function(){return _q(_Q2,_Q3,_Q4,B(_Px(_Q5,_Q7,_Q8,_Q9,_Qa,_Qb)));});}}else{return new F(function(){return _1h(_Q8,_Q9,B(_PK(_Q1,_Q2,_Q3,_Q4,_Q5,_Qa)),_Qb);});}}else{return E(_Q0);}}else{return E(_PZ);}},_Qc=function(_Qd,_Qe){var _Qf=E(_Qe);if(!_Qf._){var _Qg=_Qf.b,_Qh=_Qf.c,_Qi=B(_Qc(_Qd,_Qf.d)),_Qj=_Qi.a,_Qk=_Qi.b,_Ql=B(_Qc(_Qd,_Qf.e)),_Qm=_Ql.a,_Qn=_Ql.b;return (!B(A2(_Qd,_Qg,_Qh)))?new T2(0,B(_PX(_Qj,_Qm)),B(_2B(_Qg,_Qh,_Qk,_Qn))):new T2(0,B(_2B(_Qg,_Qh,_Qj,_Qm)),B(_PX(_Qk,_Qn)));}else{return new T2(0,_0,_0);}},_Qo=function(_Qp,_Qq){while(1){var _Qr=B((function(_Qs,_Qt){var _Qu=E(_Qt);if(!_Qu._){var _Qv=_Qu.e,_Qw=new T(function(){var _Qx=E(_Qu.c),_Qy=E(_Qx.b);if(!_Qy._){return new T2(1,new T3(5,_Qu.b,_Qx.a,_Qy.a),new T(function(){return B(_Qo(_Qs,_Qv));}));}else{return B(_Qo(_Qs,_Qv));}},1);_Qp=_Qw;_Qq=_Qu.d;return __continue;}else{return E(_Qs);}})(_Qp,_Qq));if(_Qr!=__continue){return _Qr;}}},_Qz=function(_QA,_QB){var _QC=E(_QB);return (_QC._==0)?new T5(0,_QC.a,E(_QC.b),new T(function(){return B(A1(_QA,_QC.c));}),E(B(_Qz(_QA,_QC.d))),E(B(_Qz(_QA,_QC.e)))):new T0(1);},_QD=new T0(2),_QE=function(_QF){var _QG=E(_QF);return (E(_QG.b)._==0)?new T2(0,_QG.a,_QD):E(_QG);},_QH=function(_QI,_QJ,_QK){var _QL=new T(function(){var _QM=new T(function(){return E(E(_QK).b);}),_QN=B(_Qc(function(_QO,_QP){var _QQ=E(_QP);return new F(function(){return _OX(_QI,_QM,_QO,_QQ.a,_QQ.b);});},_QJ));return new T2(0,_QN.a,_QN.b);}),_QR=new T(function(){return E(E(_QL).a);});return new T2(0,new T(function(){var _QS=B(_Qz(_QE,_QR));if(!_QS._){var _QT=E(E(_QL).b);if(!_QT._){return B(_Jm(_ON,_HZ,_HZ,_QS.a,_QS.b,_QS.c,_QS.d,_QS.e,_QT.a,_QT.b,_QT.c,_QT.d,_QT.e));}else{return E(_QS);}}else{return E(E(_QL).b);}}),new T(function(){return B(_Qo(_1,_QR));}));},_QU=function(_QV,_QW,_QX,_QY){var _QZ=E(_QY);if(!_QZ._){var _R0=_QZ.c,_R1=_QZ.d,_R2=_QZ.e,_R3=E(_QZ.b);switch(B(_2(_QV,_R3.a))){case 0:return new F(function(){return _1h(_R3,_R0,B(_QU(_QV,_QW,_QX,_R1)),_R2);});break;case 1:switch(B(_2(_QW,_R3.b))){case 0:return new F(function(){return _1h(_R3,_R0,B(_QU(_QV,_QW,_QX,_R1)),_R2);});break;case 1:return new T5(0,_QZ.a,E(new T2(0,_QV,_QW)),_QX,E(_R1),E(_R2));default:return new F(function(){return _q(_R3,_R0,_R1,B(_QU(_QV,_QW,_QX,_R2)));});}break;default:return new F(function(){return _q(_R3,_R0,_R1,B(_QU(_QV,_QW,_QX,_R2)));});}}else{return new T5(0,1,E(new T2(0,_QV,_QW)),_QX,E(_0),E(_0));}},_R4=function(_R5,_R6,_R7){while(1){var _R8=E(_R7);if(!_R8._){var _R9=_R8.d,_Ra=_R8.e,_Rb=E(_R8.b);switch(B(_2(_R5,_Rb.a))){case 0:_R7=_R9;continue;case 1:switch(B(_2(_R6,_Rb.b))){case 0:_R7=_R9;continue;case 1:return true;default:_R7=_Ra;continue;}break;default:_R7=_Ra;continue;}}else{return false;}}},_Rc=function(_Rd,_Re,_Rf){while(1){var _Rg=B((function(_Rh,_Ri,_Rj){var _Rk=E(_Rj);if(!_Rk._){var _Rl=_Rk.c,_Rm=_Rk.e,_Rn=E(_Rk.b),_Ro=_Rn.a,_Rp=_Rn.b,_Rq=B(_Rc(_Rh,_Ri,_Rk.d)),_Rr=_Rq.a,_Rs=_Rq.b;if(!B(_R4(_Ro,_Rp,_Rr))){_Rd=new T(function(){return B(_QU(_Ro,_Rp,_Rl,_Rr));});_Re=new T2(1,new T3(7,_Ro,_Rp,_Rl),_Rs);_Rf=_Rm;return __continue;}else{_Rd=_Rr;_Re=_Rs;_Rf=_Rm;return __continue;}}else{return new T2(0,_Rh,_Ri);}})(_Rd,_Re,_Rf));if(_Rg!=__continue){return _Rg;}}},_Rt=function(_Ru,_Rv){while(1){var _Rw=E(_Ru);switch(_Rw._){case 0:var _Rx=E(_Rv);if(!_Rx._){return new F(function(){return _C1(_Rw.a,_Rx.a);});}else{return false;}break;case 1:var _Ry=E(_Rv);if(_Ry._==1){if(!B(_Rt(_Rw.a,_Ry.a))){return false;}else{_Ru=_Rw.b;_Rv=_Ry.b;continue;}}else{return false;}break;case 2:var _Rz=E(_Rv);if(_Rz._==2){return new F(function(){return _C1(_Rw.a,_Rz.a);});}else{return false;}break;default:var _RA=E(_Rv);if(_RA._==3){if(!B(_C1(_Rw.a,_RA.a))){return false;}else{if(!B(_C1(_Rw.b,_RA.b))){return false;}else{_Ru=_Rw.c;_Rv=_RA.c;continue;}}}else{return false;}}}},_RB=function(_RC,_RD){while(1){var _RE=E(_RC);switch(_RE._){case 0:var _RF=E(_RD);if(!_RF._){return new F(function(){return _C1(_RE.a,_RF.a);});}else{return false;}break;case 1:var _RG=E(_RD);if(_RG._==1){if(!B(_RB(_RE.a,_RG.a))){return false;}else{_RC=_RE.b;_RD=_RG.b;continue;}}else{return false;}break;case 2:var _RH=E(_RD);if(_RH._==2){if(!B(_RB(_RE.a,_RH.a))){return false;}else{_RC=_RE.b;_RD=_RH.b;continue;}}else{return false;}break;case 3:var _RI=E(_RD);if(_RI._==3){_RC=_RE.a;_RD=_RI.a;continue;}else{return false;}break;case 4:var _RJ=E(_RD);if(_RJ._==4){if(!B(_C1(_RE.a,_RJ.a))){return false;}else{if(!B(_C1(_RE.b,_RJ.b))){return false;}else{return new F(function(){return _C1(_RE.c,_RJ.c);});}}}else{return false;}break;case 5:var _RK=E(_RD);if(_RK._==5){if(!B(_C1(_RE.a,_RK.a))){return false;}else{return new F(function(){return _C1(_RE.b,_RK.b);});}}else{return false;}break;case 6:var _RL=E(_RD);if(_RL._==6){if(!B(_Rt(_RE.a,_RL.a))){return false;}else{return new F(function(){return _Rt(_RE.b,_RL.b);});}}else{return false;}break;case 7:return (E(_RD)._==7)?true:false;default:return (E(_RD)._==8)?true:false;}}},_RM=function(_RN,_RO){while(1){var _RP=E(_RN);switch(_RP._){case 0:return (E(_RO)._==0)?true:false;case 1:var _RQ=E(_RO);if(_RQ._==1){if(!B(_C1(_RP.a,_RQ.a))){return false;}else{if(!B(_C1(_RP.b,_RQ.b))){return false;}else{if(!B(_Rt(_RP.c,_RQ.c))){return false;}else{if(!B(_C1(_RP.d,_RQ.d))){return false;}else{if(!B(_C1(_RP.e,_RQ.e))){return false;}else{if(!B(_RM(_RP.f,_RQ.f))){return false;}else{_RN=_RP.g;_RO=_RQ.g;continue;}}}}}}}else{return false;}break;case 2:var _RR=E(_RO);if(_RR._==2){if(!B(_C1(_RP.a,_RR.a))){return false;}else{_RN=_RP.b;_RO=_RR.b;continue;}}else{return false;}break;case 3:var _RS=E(_RO);if(_RS._==3){if(!B(_C1(_RP.a,_RS.a))){return false;}else{if(!B(_C1(_RP.b,_RS.b))){return false;}else{if(!B(_C1(_RP.c,_RS.c))){return false;}else{if(!B(_Rt(_RP.d,_RS.d))){return false;}else{if(!B(_C1(_RP.e,_RS.e))){return false;}else{_RN=_RP.f;_RO=_RS.f;continue;}}}}}}else{return false;}break;case 4:var _RT=E(_RO);if(_RT._==4){if(!B(_RM(_RP.a,_RT.a))){return false;}else{_RN=_RP.b;_RO=_RT.b;continue;}}else{return false;}break;case 5:var _RU=E(_RO);if(_RU._==5){if(!B(_RB(_RP.a,_RU.a))){return false;}else{if(!B(_RM(_RP.b,_RU.b))){return false;}else{_RN=_RP.c;_RO=_RU.c;continue;}}}else{return false;}break;default:var _RV=E(_RO);if(_RV._==6){if(!B(_RB(_RP.a,_RV.a))){return false;}else{if(!B(_C1(_RP.b,_RV.b))){return false;}else{if(!B(_RM(_RP.c,_RV.c))){return false;}else{_RN=_RP.d;_RO=_RV.d;continue;}}}}else{return false;}}}},_RW=new T2(0,_C1,_Oy),_RX=function(_RY,_RZ,_S0,_S1,_S2,_S3){return (!B(A3(_kQ,_RY,_S0,_S2)))?true:(!B(A3(_kQ,_RZ,_S1,_S3)))?true:false;},_S4=function(_S5,_S6,_S7,_S8){var _S9=E(_S7),_Sa=E(_S8);return new F(function(){return _RX(_S5,_S6,_S9.a,_S9.b,_Sa.a,_Sa.b);});},_Sb=function(_Sc,_Sd,_Se,_Sf,_Sg,_Sh){if(!B(A3(_kQ,_Sc,_Se,_Sg))){return false;}else{return new F(function(){return A3(_kQ,_Sd,_Sf,_Sh);});}},_Si=function(_Sj,_Sk,_Sl,_Sm){var _Sn=E(_Sl),_So=E(_Sm);return new F(function(){return _Sb(_Sj,_Sk,_Sn.a,_Sn.b,_So.a,_So.b);});},_Sp=function(_Sq,_Sr){return new T2(0,function(_Ss,_St){return new F(function(){return _Si(_Sq,_Sr,_Ss,_St);});},function(_Ss,_St){return new F(function(){return _S4(_Sq,_Sr,_Ss,_St);});});},_Su=function(_Sv,_Sw,_Sx){while(1){var _Sy=E(_Sw);if(!_Sy._){return (E(_Sx)._==0)?true:false;}else{var _Sz=E(_Sx);if(!_Sz._){return false;}else{if(!B(A3(_kQ,_Sv,_Sy.a,_Sz.a))){return false;}else{_Sw=_Sy.b;_Sx=_Sz.b;continue;}}}}},_SA=function(_SB,_SC){var _SD=new T(function(){return B(_Sp(_SB,_SC));}),_SE=function(_SF,_SG){var _SH=function(_SI){var _SJ=function(_SK){if(_SI!=_SK){return false;}else{return new F(function(){return _Su(_SD,B(_c1(_1,_SF)),B(_c1(_1,_SG)));});}},_SL=E(_SG);if(!_SL._){return new F(function(){return _SJ(_SL.a);});}else{return new F(function(){return _SJ(0);});}},_SM=E(_SF);if(!_SM._){return new F(function(){return _SH(_SM.a);});}else{return new F(function(){return _SH(0);});}};return E(_SE);},_SN=new T(function(){return B(_SA(_Ee,_RW));}),_SO=function(_SP,_SQ){var _SR=E(_SP);switch(_SR._){case 0:var _SS=E(_SQ);if(!_SS._){if(!B(_C1(_SR.a,_SS.a))){return false;}else{return new F(function(){return _C1(_SR.b,_SS.b);});}}else{return false;}break;case 1:return (E(_SQ)._==1)?true:false;default:return (E(_SQ)._==2)?true:false;}},_ST=function(_SU,_SV,_SW,_SX){if(!B(_C1(_SU,_SW))){return false;}else{return new F(function(){return _SO(_SV,_SX);});}},_SY=function(_SZ,_T0){var _T1=E(_SZ),_T2=E(_T0);return new F(function(){return _ST(_T1.a,_T1.b,_T2.a,_T2.b);});},_T3=function(_T4,_T5,_T6,_T7){if(!B(_C1(_T4,_T6))){return true;}else{var _T8=E(_T5);switch(_T8._){case 0:var _T9=E(_T7);return (_T9._==0)?(!B(_C1(_T8.a,_T9.a)))?true:(!B(_C1(_T8.b,_T9.b)))?true:false:true;case 1:return (E(_T7)._==1)?false:true;default:return (E(_T7)._==2)?false:true;}}},_Ta=function(_Tb,_Tc){var _Td=E(_Tb),_Te=E(_Tc);return new F(function(){return _T3(_Td.a,_Td.b,_Te.a,_Te.b);});},_Tf=new T2(0,_SY,_Ta),_Tg=new T(function(){return B(_SA(_OG,_Tf));}),_Th=new T1(0,0),_Ti=function(_Tj,_Tk,_Tl){var _Tm=function(_Tn,_To){while(1){var _Tp=B((function(_Tq,_Tr){var _Ts=E(_Tr);if(!_Ts._){var _Tt=new T(function(){return B(_Tm(_Tq,_Ts.e));}),_Tu=function(_Tv){var _Tw=E(_Ts.c),_Tx=E(_Tw.b);if(!_Tx._){if(!B(_C1(_Tw.a,_Tk))){return new F(function(){return A1(_Tt,_Tv);});}else{if(!B(_lm(_Tx.b,_Tl))){return new F(function(){return A1(_Tt,new T(function(){return B(_ji(_Tv,_Tx.a));}));});}else{return new F(function(){return A1(_Tt,_Tv);});}}}else{return new F(function(){return A1(_Tt,_Tv);});}};_Tn=_Tu;_To=_Ts.d;return __continue;}else{return E(_Tq);}})(_Tn,_To));if(_Tp!=__continue){return _Tp;}}};return new F(function(){return A3(_Tm,_i9,_Tj,_Th);});},_Ty=function(_Tz,_TA,_TB,_TC,_TD){while(1){var _TE=E(_TD);if(!_TE._){var _TF=_TE.c,_TG=_TE.d,_TH=E(_TE.b);switch(B(_2(_Tz,_TH.a))){case 0:_TD=_TF;continue;case 1:switch(B(_2(_TA,_TH.b))){case 0:_TD=_TF;continue;case 1:switch(B(_2(_TB,_TH.c))){case 0:_TD=_TF;continue;case 1:switch(B(_2(_TC,_TH.d))){case 0:_TD=_TF;continue;case 1:return true;default:_TD=_TG;continue;}break;default:_TD=_TG;continue;}break;default:_TD=_TG;continue;}break;default:_TD=_TG;continue;}}else{return false;}}},_TI=function(_TJ,_TK,_TL){while(1){var _TM=E(_TL);if(!_TM._){var _TN=_TM.d,_TO=_TM.e,_TP=E(_TM.b);switch(B(_2(_TJ,_TP.a))){case 0:_TL=_TN;continue;case 1:switch(B(_2(_TK,_TP.b))){case 0:_TL=_TN;continue;case 1:return new T1(1,_TM.c);default:_TL=_TO;continue;}break;default:_TL=_TO;continue;}}else{return __Z;}}},_TQ=new T0(1),_TR=__Z,_TS=function(_TT,_TU,_TV){return new F(function(){return _Ti(E(_TT).a,_TU,_TV);});},_TW=function(_TX,_TY,_TZ){while(1){var _U0=E(_TY);switch(_U0._){case 0:return (!B(_lm(_U0.a,E(_TZ).b)))?true:false;case 1:if(!B(_TW(_TX,_U0.a,_TZ))){return false;}else{_TY=_U0.b;continue;}break;case 2:if(!B(_TW(_TX,_U0.a,_TZ))){_TY=_U0.b;continue;}else{return true;}break;case 3:return (!B(_TW(_TX,_U0.a,_TZ)))?true:false;case 4:var _U1=B(_Lp(_U0.a,_U0.b,E(_TX).b));if(!_U1._){return false;}else{return new F(function(){return _C1(_U1.a,_U0.c);});}break;case 5:return new F(function(){return _R4(_U0.a,_U0.b,E(_TX).b);});break;case 6:return new F(function(){return _e(B(_LI(_TX,_U0.a)),B(_LI(_TX,_U0.b)));});break;case 7:return true;default:return false;}}},_U2=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_U3=new T(function(){return B(err(_U2));}),_U4=function(_U5,_U6){while(1){var _U7=E(_U5);if(!_U7._){var _U8=_U7.a,_U9=E(_U6);if(!_U9._){var _Ua=_U9.a,_Ub=subC(_U8,_Ua);if(!E(_Ub.b)){return new T1(0,_Ub.a);}else{_U5=new T1(1,I_fromInt(_U8));_U6=new T1(1,I_fromInt(_Ua));continue;}}else{_U5=new T1(1,I_fromInt(_U8));_U6=_U9;continue;}}else{var _Uc=E(_U6);if(!_Uc._){_U5=_U7;_U6=new T1(1,I_fromInt(_Uc.a));continue;}else{return new T1(1,I_sub(_U7.a,_Uc.a));}}}},_Ud=function(_Ue,_Uf){var _Ug=E(_Uf);if(!_Ug._){return (!B(_C1(_Ue,_Th)))?E(_U3):__Z;}else{var _Uh=_Ug.b,_Ui=E(_Ug.a),_Uj=_Ui.a,_Uk=E(_Ui.b),_Ul=_Uk.a,_Um=E(_Uk.b);if(!_Um._){var _Un=_Um.a,_Uo=_Um.b;if(!B(_lm(_Ue,_Un))){if(!B(_co(_Un,_Ue))){return E(_Uh);}else{var _Up=new T(function(){return B(_Ud(new T(function(){return B(_U4(_Ue,_Un));}),_Uh));});return new T2(1,new T2(0,_Uj,new T2(0,_Ul,new T2(0,_Th,_Uo))),_Up);}}else{return new T2(1,new T2(0,_Uj,new T2(0,_Ul,new T2(0,new T(function(){return B(_U4(_Un,_Ue));}),_Uo))),_1);}}else{return E(_Uh);}}},_Uq=function(_Ur,_Us){var _Ut=E(_Us);if(!_Ut._){var _Uu=_Ut.b,_Uv=_Ut.c,_Uw=_Ut.d,_Ux=_Ut.e;if(!B(A2(_Ur,_Uu,_Uv))){return new F(function(){return _PX(B(_Uq(_Ur,_Uw)),B(_Uq(_Ur,_Ux)));});}else{return new F(function(){return _2B(_Uu,_Uv,B(_Uq(_Ur,_Uw)),B(_Uq(_Ur,_Ux)));});}}else{return new T0(1);}},_Uy=function(_Uz,_UA,_UB,_UC){var _UD=E(_UA);if(!_UD._){var _UE=E(_UC);if(!_UE._){var _UF=B(_2(_UD.b,_UE.b));if(_UF==1){return new F(function(){return _2(_Uz,_UB);});}else{return E(_UF);}}else{return 0;}}else{return (E(_UC)._==0)?2:1;}},_UG=function(_UH,_UI){var _UJ=E(_UH),_UK=E(_UI);return new F(function(){return _Uy(_UJ.a,E(_UJ.b).b,_UK.a,E(_UK.b).b);});},_UL=new T2(1,_1,_1),_UM=function(_UN,_UO){var _UP=function(_UQ,_UR){var _US=E(_UQ);if(!_US._){return E(_UR);}else{var _UT=_US.a,_UU=E(_UR);if(!_UU._){return E(_US);}else{var _UV=_UU.a;return (B(A2(_UN,_UT,_UV))==2)?new T2(1,_UV,new T(function(){return B(_UP(_US,_UU.b));})):new T2(1,_UT,new T(function(){return B(_UP(_US.b,_UU));}));}}},_UW=function(_UX){var _UY=E(_UX);if(!_UY._){return __Z;}else{var _UZ=E(_UY.b);return (_UZ._==0)?E(_UY):new T2(1,new T(function(){return B(_UP(_UY.a,_UZ.a));}),new T(function(){return B(_UW(_UZ.b));}));}},_V0=new T(function(){return B(_V1(B(_UW(_1))));}),_V1=function(_V2){while(1){var _V3=E(_V2);if(!_V3._){return E(_V0);}else{if(!E(_V3.b)._){return E(_V3.a);}else{_V2=B(_UW(_V3));continue;}}}},_V4=new T(function(){return B(_V5(_1));}),_V6=function(_V7,_V8,_V9){while(1){var _Va=B((function(_Vb,_Vc,_Vd){var _Ve=E(_Vd);if(!_Ve._){return new T2(1,new T2(1,_Vb,_Vc),_V4);}else{var _Vf=_Ve.a;if(B(A2(_UN,_Vb,_Vf))==2){var _Vg=new T2(1,_Vb,_Vc);_V7=_Vf;_V8=_Vg;_V9=_Ve.b;return __continue;}else{return new T2(1,new T2(1,_Vb,_Vc),new T(function(){return B(_V5(_Ve));}));}}})(_V7,_V8,_V9));if(_Va!=__continue){return _Va;}}},_Vh=function(_Vi,_Vj,_Vk){while(1){var _Vl=B((function(_Vm,_Vn,_Vo){var _Vp=E(_Vo);if(!_Vp._){return new T2(1,new T(function(){return B(A1(_Vn,new T2(1,_Vm,_1)));}),_V4);}else{var _Vq=_Vp.a,_Vr=_Vp.b;switch(B(A2(_UN,_Vm,_Vq))){case 0:_Vi=_Vq;_Vj=function(_Vs){return new F(function(){return A1(_Vn,new T2(1,_Vm,_Vs));});};_Vk=_Vr;return __continue;case 1:_Vi=_Vq;_Vj=function(_Vt){return new F(function(){return A1(_Vn,new T2(1,_Vm,_Vt));});};_Vk=_Vr;return __continue;default:return new T2(1,new T(function(){return B(A1(_Vn,new T2(1,_Vm,_1)));}),new T(function(){return B(_V5(_Vp));}));}}})(_Vi,_Vj,_Vk));if(_Vl!=__continue){return _Vl;}}},_V5=function(_Vu){var _Vv=E(_Vu);if(!_Vv._){return E(_UL);}else{var _Vw=_Vv.a,_Vx=E(_Vv.b);if(!_Vx._){return new T2(1,_Vv,_1);}else{var _Vy=_Vx.a,_Vz=_Vx.b;if(B(A2(_UN,_Vw,_Vy))==2){return new F(function(){return _V6(_Vy,new T2(1,_Vw,_1),_Vz);});}else{return new F(function(){return _Vh(_Vy,function(_VA){return new T2(1,_Vw,_VA);},_Vz);});}}}};return new F(function(){return _V1(B(_V5(_UO)));});},_VB=function(_VC,_VD,_VE){var _VF=B(_zV(B(_Ud(_VD,B(_UM(_UG,B(_c1(_1,B(_Uq(function(_VG,_VH){return new F(function(){return A1(_VC,_VH);});},_VE))))))))));if(!_VF._){var _VI=E(_VE);if(!_VI._){return new F(function(){return _Jm(_ON,_HZ,_HZ,_VF.a,_VF.b,_VF.c,_VF.d,_VF.e,_VI.a,_VI.b,_VI.c,_VI.d,_VI.e);});}else{return E(_VF);}}else{return E(_VE);}},_VJ=function(_VK,_VL,_VM,_VN){var _VO=E(_VN);return (_VO._==0)?(!B(_C1(_VM,_VK)))?false:(!B(_lm(_VO.b,_VL)))?true:false:false;},_VP=function(_VQ,_VR,_VS){var _VT=E(_VS);return new F(function(){return _VJ(_VQ,_VR,_VT.a,_VT.b);});},_VU=function(_VV,_VW,_VX,_VY,_VZ){var _W0=E(_VV),_W1=new T(function(){return B(_VB(function(_uz){return new F(function(){return _VP(_VW,_VY,_uz);});},_VZ,_W0.a));});return new T2(0,_W1,_W0.b);},_W2=function(_W3,_W4,_W5,_W6){var _W7=E(_W5);switch(_W7._){case 0:return new T3(0,_W4,_TR,_1);case 1:var _W8=_W7.a,_W9=_W7.b,_Wa=_W7.e,_Wb=_W7.g,_Wc=E(_W6).b,_Wd=B(_lm(_Wa,_Wc)),_We=new T(function(){var _Wf=E(_W4);return B(_LA(_Wf.a,_Wf.b,_W7.c));}),_Wg=new T(function(){return B(_lm(_W7.d,_Wc));}),_Wh=new T(function(){return B(_z3(_W8,new T2(0,_W9,new T(function(){if(!E(_Wd)){if(!E(_Wg)){return new T2(0,_We,_Wa);}else{return new T0(1);}}else{return new T0(1);}})),E(_W4).a));});return (!E(_Wd))?(!E(_Wg))?(!B(_Ty(_W8,_W9,_We,_Wa,E(_W3).a)))?new T3(0,_W4,_W7,_1):new T3(0,new T(function(){return new T2(0,_Wh,E(_W4).b);}),_W7.f,new T2(1,new T4(3,_W8,_W9,_We,_Wa),_1)):new T3(0,new T(function(){return new T2(0,_Wh,E(_W4).b);}),_Wb,_1):new T3(0,new T(function(){return new T2(0,_Wh,E(_W4).b);}),_Wb,_1);case 2:var _Wi=_W7.a,_Wj=_W7.b,_Wk=E(_W4),_Wl=_Wk.a,_Wm=B(_Lk(_Wi,_Wl));if(!_Wm._){return new T3(0,_Wk,_W7,_1);}else{var _Wn=E(_Wm.a),_Wo=_Wn.a,_Wp=E(_Wn.b);switch(_Wp._){case 0:var _Wq=_Wp.a;return (!B(_lm(_Wp.b,E(_W6).b)))?(!B(_OO(_Wi,_Wo,_Wq,E(_W3).b)))?new T3(0,_Wk,_W7,_1):new T3(0,new T2(0,new T(function(){return B(_z3(_Wi,new T2(0,_Wo,_TQ),_Wl));}),_Wk.b),_Wj,new T2(1,new T3(4,_Wi,_Wo,_Wq),_1)):new T3(0,_Wk,_Wj,_1);case 1:return new T3(0,_Wk,_Wj,new T2(1,new T2(6,_Wi,_Wo),_1));default:return new T3(0,_Wk,_Wj,_1);}}break;case 3:var _Wr=_W7.a,_Ws=_W7.b,_Wt=_W7.c,_Wu=_W7.f,_Wv=E(_W6).b,_Ww=new T(function(){var _Wx=E(_W4);return B(_LA(_Wx.a,_Wx.b,_W7.d));});if(!B(_lm(_W7.e,_Wv))){var _Wy=B(_TI(_Wr,_Wt,E(_W3).c));return (_Wy._==0)?new T3(0,_W4,_W7,_1):(!B(_C1(_Wy.a,_Ww)))?new T3(0,_W4,_W7,_1):(!B(_e(B(_TS(_W4,_Ws,_Wv)),_Ww)))?new T3(0,_W4,_Wu,new T2(1,new T4(2,_Wr,_Ws,_Wt,_Ww),_1)):(!B(_e(_Ww,_Th)))?new T3(0,_W4,_Wu,new T2(1,new T4(2,_Wr,_Ws,_Wt,_Ww),_1)):new T3(0,new T(function(){return B(_VU(_W4,_Ws,_Wt,_Wv,_Ww));}),_Wu,new T2(1,new T4(0,_Wr,_Ws,_Wt,_Ww),_1));}else{return new T3(0,_W4,_Wu,new T2(1,new T4(1,_Wr,_Ws,_Wt,_Ww),_1));}break;case 4:var _Wz=new T(function(){var _WA=B(_W2(_W3,_W4,_W7.a,_W6));return new T3(0,_WA.a,_WA.b,_WA.c);}),_WB=new T(function(){var _WC=B(_W2(_W3,new T(function(){return E(E(_Wz).a);}),_W7.b,_W6));return new T3(0,_WC.a,_WC.b,_WC.c);}),_WD=new T(function(){return B(_ce(E(_Wz).c,new T(function(){return E(E(_WB).c);},1)));}),_WE=new T(function(){var _WF=E(_Wz).b,_WG=E(_WB).b,_WH=function(_WI){var _WJ=E(_WG);switch(_WJ._){case 0:return E(_WF);case 1:return new T2(4,_WF,_WJ);case 2:return new T2(4,_WF,_WJ);case 3:return new T2(4,_WF,_WJ);case 4:return new T2(4,_WF,_WJ);case 5:return new T2(4,_WF,_WJ);default:return new T2(4,_WF,_WJ);}};switch(E(_WF)._){case 0:return E(_WG);break;case 1:return B(_WH(_));break;case 2:return B(_WH(_));break;case 3:return B(_WH(_));break;case 4:return B(_WH(_));break;case 5:return B(_WH(_));break;default:return B(_WH(_));}});return new T3(0,new T(function(){return E(E(_WB).a);}),_WE,_WD);case 5:return (!B(_TW(_W4,_W7.a,_W6)))?new T3(0,_W4,_W7.c,_1):new T3(0,_W4,_W7.b,_1);default:var _WK=E(_W6);return (!B(_lm(_W7.b,_WK.b)))?(!B(_TW(_W4,_W7.a,_WK)))?new T3(0,_W4,_W7,_1):new T3(0,_W4,_W7.c,_1):new T3(0,_W4,_W7.d,_1);}},_WL=function(_WM,_WN,_WO,_WP,_WQ){var _WR=E(_WP);switch(_WR._){case 0:return new T3(0,new T2(0,_WN,_WO),_TR,_1);case 1:var _WS=_WR.a,_WT=_WR.b,_WU=_WR.e,_WV=_WR.g,_WW=E(_WQ).b,_WX=B(_lm(_WU,_WW)),_WY=new T(function(){return B(_LA(_WN,_WO,_WR.c));}),_WZ=new T(function(){return B(_lm(_WR.d,_WW));}),_X0=new T(function(){return B(_z3(_WS,new T2(0,_WT,new T(function(){if(!E(_WX)){if(!E(_WZ)){return new T2(0,_WY,_WU);}else{return new T0(1);}}else{return new T0(1);}})),_WN));});return (!E(_WX))?(!E(_WZ))?(!B(_Ty(_WS,_WT,_WY,_WU,E(_WM).a)))?new T3(0,new T2(0,_WN,_WO),_WR,_1):new T3(0,new T2(0,_X0,_WO),_WR.f,new T2(1,new T4(3,_WS,_WT,_WY,_WU),_1)):new T3(0,new T2(0,_X0,_WO),_WV,_1):new T3(0,new T2(0,_X0,_WO),_WV,_1);case 2:var _X1=_WR.a,_X2=_WR.b,_X3=B(_Lk(_X1,_WN));if(!_X3._){return new T3(0,new T2(0,_WN,_WO),_WR,_1);}else{var _X4=E(_X3.a),_X5=_X4.a,_X6=E(_X4.b);switch(_X6._){case 0:var _X7=_X6.a;return (!B(_lm(_X6.b,E(_WQ).b)))?(!B(_OO(_X1,_X5,_X7,E(_WM).b)))?new T3(0,new T2(0,_WN,_WO),_WR,_1):new T3(0,new T2(0,new T(function(){return B(_z3(_X1,new T2(0,_X5,_TQ),_WN));}),_WO),_X2,new T2(1,new T3(4,_X1,_X5,_X7),_1)):new T3(0,new T2(0,_WN,_WO),_X2,_1);case 1:return new T3(0,new T2(0,_WN,_WO),_X2,new T2(1,new T2(6,_X1,_X5),_1));default:return new T3(0,new T2(0,_WN,_WO),_X2,_1);}}break;case 3:var _X8=_WR.a,_X9=_WR.b,_Xa=_WR.c,_Xb=_WR.f,_Xc=E(_WQ).b,_Xd=new T(function(){return B(_LA(_WN,_WO,_WR.d));});if(!B(_lm(_WR.e,_Xc))){var _Xe=B(_TI(_X8,_Xa,E(_WM).c));if(!_Xe._){return new T3(0,new T2(0,_WN,_WO),_WR,_1);}else{if(!B(_C1(_Xe.a,_Xd))){return new T3(0,new T2(0,_WN,_WO),_WR,_1);}else{if(!B(_e(B(_Ti(_WN,_X9,_Xc)),_Xd))){return new T3(0,new T2(0,_WN,_WO),_Xb,new T2(1,new T4(2,_X8,_X9,_Xa,_Xd),_1));}else{if(!B(_e(_Xd,_Th))){return new T3(0,new T2(0,_WN,_WO),_Xb,new T2(1,new T4(2,_X8,_X9,_Xa,_Xd),_1));}else{var _Xf=new T(function(){return B(_VB(function(_uz){return new F(function(){return _VP(_X9,_Xc,_uz);});},_Xd,_WN));});return new T3(0,new T2(0,_Xf,_WO),_Xb,new T2(1,new T4(0,_X8,_X9,_Xa,_Xd),_1));}}}}}else{return new T3(0,new T2(0,_WN,_WO),_Xb,new T2(1,new T4(1,_X8,_X9,_Xa,_Xd),_1));}break;case 4:var _Xg=new T(function(){var _Xh=B(_WL(_WM,_WN,_WO,_WR.a,_WQ));return new T3(0,_Xh.a,_Xh.b,_Xh.c);}),_Xi=new T(function(){var _Xj=B(_W2(_WM,new T(function(){return E(E(_Xg).a);}),_WR.b,_WQ));return new T3(0,_Xj.a,_Xj.b,_Xj.c);}),_Xk=new T(function(){return B(_ce(E(_Xg).c,new T(function(){return E(E(_Xi).c);},1)));}),_Xl=new T(function(){var _Xm=E(_Xg).b,_Xn=E(_Xi).b,_Xo=function(_Xp){var _Xq=E(_Xn);switch(_Xq._){case 0:return E(_Xm);case 1:return new T2(4,_Xm,_Xq);case 2:return new T2(4,_Xm,_Xq);case 3:return new T2(4,_Xm,_Xq);case 4:return new T2(4,_Xm,_Xq);case 5:return new T2(4,_Xm,_Xq);default:return new T2(4,_Xm,_Xq);}};switch(E(_Xm)._){case 0:return E(_Xn);break;case 1:return B(_Xo(_));break;case 2:return B(_Xo(_));break;case 3:return B(_Xo(_));break;case 4:return B(_Xo(_));break;case 5:return B(_Xo(_));break;default:return B(_Xo(_));}});return new T3(0,new T(function(){return E(E(_Xi).a);}),_Xl,_Xk);case 5:return (!B(_TW(new T2(0,_WN,_WO),_WR.a,_WQ)))?new T3(0,new T2(0,_WN,_WO),_WR.c,_1):new T3(0,new T2(0,_WN,_WO),_WR.b,_1);default:var _Xr=E(_WQ);return (!B(_lm(_WR.b,_Xr.b)))?(!B(_TW(new T2(0,_WN,_WO),_WR.a,_Xr)))?new T3(0,new T2(0,_WN,_WO),_WR,_1):new T3(0,new T2(0,_WN,_WO),_WR.c,_1):new T3(0,new T2(0,_WN,_WO),_WR.d,_1);}},_Xs=function(_Xt,_Xu,_Xv,_Xw,_Xx,_Xy){var _Xz=B(_WL(_Xt,_Xu,_Xv,_Xw,_Xx)),_XA=_Xz.b,_XB=_Xz.c,_XC=E(_Xz.a),_XD=_XC.a,_XE=_XC.b,_XF=function(_XG){return new F(function(){return _Xs(_Xt,_XD,_XE,_XA,_Xx,new T(function(){return B(_ce(_Xy,_XB));}));});};if(!B(A2(_Tg,_XD,_Xu))){return new F(function(){return _XF(_);});}else{if(!B(A2(_SN,_XE,_Xv))){return new F(function(){return _XF(_);});}else{if(!B(_RM(_XA,_Xw))){return new F(function(){return _XF(_);});}else{if(!E(_XB)._){return new T3(0,new T2(0,_Xu,_Xv),_Xw,_Xy);}else{return new F(function(){return _XF(_);});}}}}},_XH=function(_XI,_XJ,_XK,_XL){var _XM=new T(function(){var _XN=B(_QH(_XI,new T(function(){return E(E(_XJ).a);},1),_XL));return new T2(0,_XN.a,_XN.b);}),_XO=new T(function(){var _XP=B(_Rc(new T(function(){return E(E(_XJ).b);}),_1,E(_XI).d));return new T2(0,_XP.a,_XP.b);}),_XQ=new T(function(){var _XR=E(_XJ),_XS=B(_Xs(_XI,new T(function(){return E(E(_XM).a);}),new T(function(){return E(E(_XO).a);}),_XK,_XL,_1));return new T3(0,_XS.a,_XS.b,_XS.c);}),_XT=new T(function(){var _XU=new T(function(){return B(_ce(E(_XM).b,new T(function(){return E(E(_XQ).c);},1)));},1);return B(_ce(E(_XO).b,_XU));});return new T3(0,new T(function(){return E(E(_XQ).a);}),new T(function(){return E(E(_XQ).b);}),_XT);},_XV=function(_XW,_XX,_XY,_XZ,_Y0){while(1){var _Y1=E(_XW);if(!_Y1._){return new T4(0,_XX,_XY,_XZ,_Y0);}else{var _Y2=E(_Y1.a),_Y3=B(_L3(_XX,_XY,_XZ,_Y0,_Y2.a,_Y2.b,_Y2.c,_Y2.d));_XW=_Y1.b;_XX=_Y3.a;_XY=_Y3.b;_XZ=_Y3.c;_Y0=_Y3.d;continue;}}},_Y4=function(_Y5,_Y6,_Y7,_Y8,_Y9,_Ya){var _Yb=E(_Y5),_Yc=B(_L3(_Y7,_Y8,_Y9,_Ya,_Yb.a,_Yb.b,_Yb.c,_Yb.d));return new F(function(){return _XV(_Y6,_Yc.a,_Yc.b,_Yc.c,_Yc.d);});},_Yd=function(_Ye,_Yf,_Yg,_Yh){var _Yi=B(_XH(_Yf,_Yh,_Yg,_Ye)),_Yj=_Yi.a,_Yk=_Yi.b,_Yl=B(_LM(_Yk,_Yj));return new F(function(){return _Y4(new T(function(){var _Ym=B(_LZ(_Ye,E(_Yj).a));return new T4(0,_Ym.a,_Ym.b,_Ym.c,_Ym.d);}),new T2(1,new T(function(){var _Yn=B(_Ob(_Yj,_Yk));return new T4(0,_Yn.a,_Yn.b,_Yn.c,_Yn.d);}),_1),_Yl.a,_Yl.b,_Yl.c,_Yl.d);});},_Yo="(function (t) {return window[t].getValue()})",_Yp=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_Yq=new T(function(){return B(unCStr("contractState"));}),_Yr=new T(function(){return B(unCStr("currBlock"));}),_Ys=new T(function(){return eval("(function (x) { var node = document.getElementById(x); while (node.hasChildNodes()) { node.removeChild(node.lastChild); } })");}),_Yt=new T(function(){return B(err(_bZ));}),_Yu=new T(function(){return B(err(_eR));}),_Yv=new T(function(){return B(A3(_sX,_tq,_ss,_yF));}),_Yw="(function (t) {return document.getElementById(t).value})",_Yx=new T(function(){return B(err(_bZ));}),_Yy=new T(function(){return B(err(_eR));}),_Yz=function(_uz){return new F(function(){return _sM(_wQ,_uz);});},_YA=function(_YB,_YC){return new F(function(){return _tz(_Yz,_YC);});},_YD=new T(function(){return B(_tz(_Yz,_eU));}),_YE=function(_uz){return new F(function(){return _g4(_YD,_uz);});},_YF=function(_YG){var _YH=new T(function(){return B(A3(_sM,_wQ,_YG,_eU));});return function(_ue){return new F(function(){return _g4(_YH,_ue);});};},_YI=new T4(0,_YF,_YE,_Yz,_YA),_YJ=new T(function(){return B(unCStr("NotRedeemed"));}),_YK=function(_YL,_YM){return new F(function(){return A1(_YM,_TQ);});},_YN=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_YO=new T2(0,_YN,_YK),_YP=function(_YQ,_YR){return new F(function(){return A1(_YR,_QD);});},_YS=new T(function(){return B(unCStr("ExpiredAndRedeemed"));}),_YT=new T2(0,_YS,_YP),_YU=new T2(1,_YT,_1),_YV=new T2(1,_YO,_YU),_YW=function(_YX,_YY,_YZ){var _Z0=E(_YX);if(!_Z0._){return new T0(2);}else{var _Z1=E(_Z0.a),_Z2=_Z1.a,_Z3=new T(function(){return B(A2(_Z1.b,_YY,_YZ));}),_Z4=new T(function(){return B(_rV(function(_Z5){var _Z6=E(_Z5);switch(_Z6._){case 3:return (!B(_gS(_Z2,_Z6.a)))?new T0(2):E(_Z3);case 4:return (!B(_gS(_Z2,_Z6.a)))?new T0(2):E(_Z3);default:return new T0(2);}}));}),_Z7=function(_Z8){return E(_Z4);};return new F(function(){return _ge(new T1(1,function(_Z9){return new F(function(){return A2(_qC,_Z9,_Z7);});}),new T(function(){return B(_YW(_Z0.b,_YY,_YZ));}));});}},_Za=function(_Zb,_Zc){var _Zd=new T(function(){if(E(_Zb)>10){return new T0(2);}else{var _Ze=new T(function(){var _Zf=new T(function(){var _Zg=function(_Zh){return new F(function(){return A3(_sX,_tq,_ui,function(_Zi){return new F(function(){return A1(_Zc,new T2(0,_Zh,_Zi));});});});};return B(A3(_sX,_tq,_ui,_Zg));});return B(_rV(function(_Zj){var _Zk=E(_Zj);return (_Zk._==3)?(!B(_gS(_Zk.a,_YJ)))?new T0(2):E(_Zf):new T0(2);}));}),_Zl=function(_Zm){return E(_Ze);};return new T1(1,function(_Zn){return new F(function(){return A2(_qC,_Zn,_Zl);});});}});return new F(function(){return _ge(B(_YW(_YV,_Zb,_Zc)),_Zd);});},_Zo=function(_uz){return new F(function(){return _sM(_Za,_uz);});},_Zp=function(_Zq,_Zr){return new F(function(){return _tz(_Zo,_Zr);});},_Zs=new T(function(){return B(_tz(_Zo,_eU));}),_Zt=function(_uz){return new F(function(){return _g4(_Zs,_uz);});},_Zu=function(_Zv){var _Zw=new T(function(){return B(A3(_sM,_Za,_Zv,_eU));});return function(_ue){return new F(function(){return _g4(_Zw,_ue);});};},_Zx=new T4(0,_Zu,_Zt,_Zo,_Zp),_Zy=function(_Zz,_ZA){return new F(function(){return _v4(_uh,_Zx,_ZA);});},_ZB=new T(function(){return B(_tz(_Zy,_eU));}),_ZC=function(_uz){return new F(function(){return _g4(_ZB,_uz);});},_ZD=new T(function(){return B(_v4(_uh,_Zx,_eU));}),_ZE=function(_uz){return new F(function(){return _g4(_ZD,_uz);});},_ZF=function(_ZG,_uz){return new F(function(){return _ZE(_uz);});},_ZH=function(_ZI,_ZJ){return new F(function(){return _tz(_Zy,_ZJ);});},_ZK=new T4(0,_ZF,_ZC,_Zy,_ZH),_ZL=function(_ZM,_ZN){return new F(function(){return _v4(_YI,_ZK,_ZN);});},_ZO=function(_ZP,_ZQ){return new F(function(){return _tz(_ZL,_ZQ);});},_ZR=new T(function(){return B(_tz(_ZO,_eU));}),_ZS=function(_vz){return new F(function(){return _g4(_ZR,_vz);});},_ZT=function(_ZU){return new F(function(){return _tz(_ZO,_ZU);});},_ZV=function(_ZW,_ZX){return new F(function(){return _ZT(_ZX);});},_ZY=new T(function(){return B(_tz(_ZL,_eU));}),_ZZ=function(_vz){return new F(function(){return _g4(_ZY,_vz);});},_100=function(_101,_vz){return new F(function(){return _ZZ(_vz);});},_102=new T4(0,_100,_ZS,_ZO,_ZV),_103=new T(function(){return B(_v4(_102,_vJ,_yF));}),_104=new T1(0,42),_105=new T(function(){return B(unCStr("actions"));}),_106=function(_107){while(1){var _108=B((function(_109){var _10a=E(_109);if(!_10a._){return __Z;}else{var _10b=_10a.b,_10c=E(_10a.a);if(!E(_10c.b)._){return new T2(1,_10c.a,new T(function(){return B(_106(_10b));}));}else{_107=_10b;return __continue;}}})(_107));if(_108!=__continue){return _108;}}},_10d=new T(function(){return B(err(_bZ));}),_10e=new T(function(){return B(err(_eR));}),_10f=new T(function(){return B(unCStr("ConstMoney"));}),_10g=new T(function(){return B(unCStr("AvailableMoney"));}),_10h=new T(function(){return B(unCStr("AddMoney"));}),_10i=new T(function(){return B(unCStr("MoneyFromChoice"));}),_10j=function(_10k,_10l){var _10m=new T(function(){var _10n=new T(function(){var _10o=new T(function(){if(_10k>10){return new T0(2);}else{var _10p=new T(function(){var _10q=new T(function(){var _10r=function(_10s){var _10t=function(_10u){return new F(function(){return A3(_sM,_10v,_ui,function(_10w){return new F(function(){return A1(_10l,new T3(3,_10s,_10u,_10w));});});});};return new F(function(){return A3(_sX,_tq,_ui,_10t);});};return B(A3(_sM,_uv,_ui,_10r));});return B(_rV(function(_10x){var _10y=E(_10x);return (_10y._==3)?(!B(_gS(_10y.a,_10i)))?new T0(2):E(_10q):new T0(2);}));}),_10z=function(_10A){return E(_10p);};return new T1(1,function(_10B){return new F(function(){return A2(_qC,_10B,_10z);});});}});if(_10k>10){return B(_ge(_eT,_10o));}else{var _10C=new T(function(){var _10D=new T(function(){return B(A3(_sX,_tq,_ui,function(_10E){return new F(function(){return A1(_10l,new T1(2,_10E));});}));});return B(_rV(function(_10F){var _10G=E(_10F);return (_10G._==3)?(!B(_gS(_10G.a,_10f)))?new T0(2):E(_10D):new T0(2);}));}),_10H=function(_10I){return E(_10C);};return B(_ge(new T1(1,function(_10J){return new F(function(){return A2(_qC,_10J,_10H);});}),_10o));}});if(_10k>10){return B(_ge(_eT,_10n));}else{var _10K=new T(function(){var _10L=new T(function(){var _10M=function(_10N){return new F(function(){return A3(_sM,_10v,_ui,function(_10O){return new F(function(){return A1(_10l,new T2(1,_10N,_10O));});});});};return B(A3(_sM,_10v,_ui,_10M));});return B(_rV(function(_10P){var _10Q=E(_10P);return (_10Q._==3)?(!B(_gS(_10Q.a,_10h)))?new T0(2):E(_10L):new T0(2);}));}),_10R=function(_10S){return E(_10K);};return B(_ge(new T1(1,function(_10T){return new F(function(){return A2(_qC,_10T,_10R);});}),_10n));}});if(_10k>10){return new F(function(){return _ge(_eT,_10m);});}else{var _10U=new T(function(){var _10V=new T(function(){return B(A3(_sM,_wQ,_ui,function(_10W){return new F(function(){return A1(_10l,new T1(0,_10W));});}));});return B(_rV(function(_10X){var _10Y=E(_10X);return (_10Y._==3)?(!B(_gS(_10Y.a,_10g)))?new T0(2):E(_10V):new T0(2);}));}),_10Z=function(_110){return E(_10U);};return new F(function(){return _ge(new T1(1,function(_111){return new F(function(){return A2(_qC,_111,_10Z);});}),_10m);});}},_10v=function(_112,_113){return new F(function(){return _10j(E(_112),_113);});},_114=new T0(7),_115=function(_116,_117){return new F(function(){return A1(_117,_114);});},_118=new T(function(){return B(unCStr("TrueObs"));}),_119=new T2(0,_118,_115),_11a=new T0(8),_11b=function(_11c,_11d){return new F(function(){return A1(_11d,_11a);});},_11e=new T(function(){return B(unCStr("FalseObs"));}),_11f=new T2(0,_11e,_11b),_11g=new T2(1,_11f,_1),_11h=new T2(1,_119,_11g),_11i=new T(function(){return B(unCStr("ValueGE"));}),_11j=new T(function(){return B(unCStr("PersonChoseSomething"));}),_11k=new T(function(){return B(unCStr("PersonChoseThis"));}),_11l=new T(function(){return B(unCStr("BelowTimeout"));}),_11m=new T(function(){return B(unCStr("AndObs"));}),_11n=new T(function(){return B(unCStr("OrObs"));}),_11o=new T(function(){return B(unCStr("NotObs"));}),_11p=function(_11q,_11r){var _11s=new T(function(){var _11t=E(_11q),_11u=new T(function(){var _11v=new T(function(){var _11w=new T(function(){var _11x=new T(function(){var _11y=new T(function(){var _11z=new T(function(){if(_11t>10){return new T0(2);}else{var _11A=new T(function(){var _11B=new T(function(){var _11C=function(_11D){return new F(function(){return A3(_sM,_10v,_ui,function(_11E){return new F(function(){return A1(_11r,new T2(6,_11D,_11E));});});});};return B(A3(_sM,_10v,_ui,_11C));});return B(_rV(function(_11F){var _11G=E(_11F);return (_11G._==3)?(!B(_gS(_11G.a,_11i)))?new T0(2):E(_11B):new T0(2);}));}),_11H=function(_11I){return E(_11A);};return new T1(1,function(_11J){return new F(function(){return A2(_qC,_11J,_11H);});});}});if(_11t>10){return B(_ge(_eT,_11z));}else{var _11K=new T(function(){var _11L=new T(function(){var _11M=function(_11N){return new F(function(){return A3(_sX,_tq,_ui,function(_11O){return new F(function(){return A1(_11r,new T2(5,_11N,_11O));});});});};return B(A3(_sM,_uv,_ui,_11M));});return B(_rV(function(_11P){var _11Q=E(_11P);return (_11Q._==3)?(!B(_gS(_11Q.a,_11j)))?new T0(2):E(_11L):new T0(2);}));}),_11R=function(_11S){return E(_11K);};return B(_ge(new T1(1,function(_11T){return new F(function(){return A2(_qC,_11T,_11R);});}),_11z));}});if(_11t>10){return B(_ge(_eT,_11y));}else{var _11U=new T(function(){var _11V=new T(function(){var _11W=function(_11X){var _11Y=function(_11Z){return new F(function(){return A3(_sX,_tq,_ui,function(_120){return new F(function(){return A1(_11r,new T3(4,_11X,_11Z,_120));});});});};return new F(function(){return A3(_sX,_tq,_ui,_11Y);});};return B(A3(_sM,_uv,_ui,_11W));});return B(_rV(function(_121){var _122=E(_121);return (_122._==3)?(!B(_gS(_122.a,_11k)))?new T0(2):E(_11V):new T0(2);}));}),_123=function(_124){return E(_11U);};return B(_ge(new T1(1,function(_125){return new F(function(){return A2(_qC,_125,_123);});}),_11y));}});if(_11t>10){return B(_ge(_eT,_11x));}else{var _126=new T(function(){var _127=new T(function(){return B(A3(_sM,_11p,_ui,function(_128){return new F(function(){return A1(_11r,new T1(3,_128));});}));});return B(_rV(function(_129){var _12a=E(_129);return (_12a._==3)?(!B(_gS(_12a.a,_11o)))?new T0(2):E(_127):new T0(2);}));}),_12b=function(_12c){return E(_126);};return B(_ge(new T1(1,function(_12d){return new F(function(){return A2(_qC,_12d,_12b);});}),_11x));}});if(_11t>10){return B(_ge(_eT,_11w));}else{var _12e=new T(function(){var _12f=new T(function(){var _12g=function(_12h){return new F(function(){return A3(_sM,_11p,_ui,function(_12i){return new F(function(){return A1(_11r,new T2(2,_12h,_12i));});});});};return B(A3(_sM,_11p,_ui,_12g));});return B(_rV(function(_12j){var _12k=E(_12j);return (_12k._==3)?(!B(_gS(_12k.a,_11n)))?new T0(2):E(_12f):new T0(2);}));}),_12l=function(_12m){return E(_12e);};return B(_ge(new T1(1,function(_12n){return new F(function(){return A2(_qC,_12n,_12l);});}),_11w));}});if(_11t>10){return B(_ge(_eT,_11v));}else{var _12o=new T(function(){var _12p=new T(function(){var _12q=function(_12r){return new F(function(){return A3(_sM,_11p,_ui,function(_12s){return new F(function(){return A1(_11r,new T2(1,_12r,_12s));});});});};return B(A3(_sM,_11p,_ui,_12q));});return B(_rV(function(_12t){var _12u=E(_12t);return (_12u._==3)?(!B(_gS(_12u.a,_11m)))?new T0(2):E(_12p):new T0(2);}));}),_12v=function(_12w){return E(_12o);};return B(_ge(new T1(1,function(_12x){return new F(function(){return A2(_qC,_12x,_12v);});}),_11v));}});if(_11t>10){return B(_ge(_eT,_11u));}else{var _12y=new T(function(){var _12z=new T(function(){return B(A3(_sX,_tq,_ui,function(_12A){return new F(function(){return A1(_11r,new T1(0,_12A));});}));});return B(_rV(function(_12B){var _12C=E(_12B);return (_12C._==3)?(!B(_gS(_12C.a,_11l)))?new T0(2):E(_12z):new T0(2);}));}),_12D=function(_12E){return E(_12y);};return B(_ge(new T1(1,function(_12F){return new F(function(){return A2(_qC,_12F,_12D);});}),_11u));}});return new F(function(){return _ge(B(_YW(_11h,_11q,_11r)),_11s);});},_12G=new T(function(){return B(unCStr("Null"));}),_12H=new T(function(){return B(unCStr("CommitCash"));}),_12I=new T(function(){return B(unCStr("RedeemCC"));}),_12J=new T(function(){return B(unCStr("Pay"));}),_12K=new T(function(){return B(unCStr("Both"));}),_12L=new T(function(){return B(unCStr("Choice"));}),_12M=new T(function(){return B(unCStr("When"));}),_12N=function(_12O,_12P){var _12Q=new T(function(){var _12R=new T(function(){return B(A1(_12P,_TR));});return B(_rV(function(_12S){var _12T=E(_12S);return (_12T._==3)?(!B(_gS(_12T.a,_12G)))?new T0(2):E(_12R):new T0(2);}));}),_12U=function(_12V){return E(_12Q);},_12W=new T(function(){var _12X=E(_12O),_12Y=new T(function(){var _12Z=new T(function(){var _130=new T(function(){var _131=new T(function(){var _132=new T(function(){if(_12X>10){return new T0(2);}else{var _133=new T(function(){var _134=new T(function(){var _135=function(_136){var _137=function(_138){var _139=function(_13a){return new F(function(){return A3(_sM,_12N,_ui,function(_13b){return new F(function(){return A1(_12P,new T4(6,_136,_138,_13a,_13b));});});});};return new F(function(){return A3(_sM,_12N,_ui,_139);});};return new F(function(){return A3(_sX,_tq,_ui,_137);});};return B(A3(_sM,_11p,_ui,_135));});return B(_rV(function(_13c){var _13d=E(_13c);return (_13d._==3)?(!B(_gS(_13d.a,_12M)))?new T0(2):E(_134):new T0(2);}));}),_13e=function(_13f){return E(_133);};return new T1(1,function(_13g){return new F(function(){return A2(_qC,_13g,_13e);});});}});if(_12X>10){return B(_ge(_eT,_132));}else{var _13h=new T(function(){var _13i=new T(function(){var _13j=function(_13k){var _13l=function(_13m){return new F(function(){return A3(_sM,_12N,_ui,function(_13n){return new F(function(){return A1(_12P,new T3(5,_13k,_13m,_13n));});});});};return new F(function(){return A3(_sM,_12N,_ui,_13l);});};return B(A3(_sM,_11p,_ui,_13j));});return B(_rV(function(_13o){var _13p=E(_13o);return (_13p._==3)?(!B(_gS(_13p.a,_12L)))?new T0(2):E(_13i):new T0(2);}));}),_13q=function(_13r){return E(_13h);};return B(_ge(new T1(1,function(_13s){return new F(function(){return A2(_qC,_13s,_13q);});}),_132));}});if(_12X>10){return B(_ge(_eT,_131));}else{var _13t=new T(function(){var _13u=new T(function(){var _13v=function(_13w){return new F(function(){return A3(_sM,_12N,_ui,function(_13x){return new F(function(){return A1(_12P,new T2(4,_13w,_13x));});});});};return B(A3(_sM,_12N,_ui,_13v));});return B(_rV(function(_13y){var _13z=E(_13y);return (_13z._==3)?(!B(_gS(_13z.a,_12K)))?new T0(2):E(_13u):new T0(2);}));}),_13A=function(_13B){return E(_13t);};return B(_ge(new T1(1,function(_13C){return new F(function(){return A2(_qC,_13C,_13A);});}),_131));}});if(_12X>10){return B(_ge(_eT,_130));}else{var _13D=new T(function(){var _13E=new T(function(){var _13F=function(_13G){var _13H=function(_13I){var _13J=function(_13K){var _13L=function(_13M){var _13N=function(_13O){return new F(function(){return A3(_sM,_12N,_ui,function(_13P){return new F(function(){return A1(_12P,new T6(3,_13G,_13I,_13K,_13M,_13O,_13P));});});});};return new F(function(){return A3(_sX,_tq,_ui,_13N);});};return new F(function(){return A3(_sM,_10v,_ui,_13L);});};return new F(function(){return A3(_sX,_tq,_ui,_13J);});};return new F(function(){return A3(_sX,_tq,_ui,_13H);});};return B(A3(_sM,_vW,_ui,_13F));});return B(_rV(function(_13Q){var _13R=E(_13Q);return (_13R._==3)?(!B(_gS(_13R.a,_12J)))?new T0(2):E(_13E):new T0(2);}));}),_13S=function(_13T){return E(_13D);};return B(_ge(new T1(1,function(_13U){return new F(function(){return A2(_qC,_13U,_13S);});}),_130));}});if(_12X>10){return B(_ge(_eT,_12Z));}else{var _13V=new T(function(){var _13W=new T(function(){var _13X=function(_13Y){return new F(function(){return A3(_sM,_12N,_ui,function(_13Z){return new F(function(){return A1(_12P,new T2(2,_13Y,_13Z));});});});};return B(A3(_sM,_wQ,_ui,_13X));});return B(_rV(function(_140){var _141=E(_140);return (_141._==3)?(!B(_gS(_141.a,_12I)))?new T0(2):E(_13W):new T0(2);}));}),_142=function(_143){return E(_13V);};return B(_ge(new T1(1,function(_144){return new F(function(){return A2(_qC,_144,_142);});}),_12Z));}});if(_12X>10){return B(_ge(_eT,_12Y));}else{var _145=new T(function(){var _146=new T(function(){var _147=function(_148){var _149=function(_14a){var _14b=function(_14c){var _14d=function(_14e){var _14f=function(_14g){var _14h=function(_14i){return new F(function(){return A3(_sM,_12N,_ui,function(_14j){return new F(function(){return A1(_12P,{_:1,a:_148,b:_14a,c:_14c,d:_14e,e:_14g,f:_14i,g:_14j});});});});};return new F(function(){return A3(_sM,_12N,_ui,_14h);});};return new F(function(){return A3(_sX,_tq,_ui,_14f);});};return new F(function(){return A3(_sX,_tq,_ui,_14d);});};return new F(function(){return A3(_sM,_10v,_ui,_14b);});};return new F(function(){return A3(_sX,_tq,_ui,_149);});};return B(A3(_sM,_wQ,_ui,_147));});return B(_rV(function(_14k){var _14l=E(_14k);return (_14l._==3)?(!B(_gS(_14l.a,_12H)))?new T0(2):E(_146):new T0(2);}));}),_14m=function(_14n){return E(_145);};return B(_ge(new T1(1,function(_14o){return new F(function(){return A2(_qC,_14o,_14m);});}),_12Y));}});return new F(function(){return _ge(new T1(1,function(_14p){return new F(function(){return A2(_qC,_14p,_12U);});}),_12W);});},_14q=new T(function(){return B(A3(_sM,_12N,_ss,_yF));}),_14r=function(_14s,_){var _14t=__app0(E(_Yp)),_14u=eval(E(_Yw)),_14v=__app1(E(_14u),toJSStr(E(_Yr))),_14w=eval(E(_Yo)),_14x=__app1(E(_14w),toJSStr(E(_Yq))),_14y=__app1(E(_Ys),toJSStr(_105)),_14z=new T(function(){var _14A=B(_106(B(_g4(_103,new T(function(){var _14B=String(_14x);return fromJSStr(_14B);})))));if(!_14A._){return E(_Yy);}else{if(!E(_14A.b)._){var _14C=E(_14A.a);return new T2(0,new T(function(){return B(_zV(_14C.a));}),new T(function(){return B(_4n(_14C.b));}));}else{return E(_Yx);}}}),_14D=new T(function(){var _14E=B(_106(B(_g4(_14q,new T(function(){var _14F=String(_14t);return fromJSStr(_14F);})))));if(!_14E._){return E(_10e);}else{if(!E(_14E.b)._){return E(_14E.a);}else{return E(_10d);}}}),_14G=new T(function(){var _14H=B(_106(B(_g4(_Yv,new T(function(){var _14I=String(_14v);return fromJSStr(_14I);})))));if(!_14H._){return E(_Yu);}else{if(!E(_14H.b)._){return E(_14H.a);}else{return E(_Yt);}}}),_14J=B(_Yd(new T2(0,_104,_14G),_14s,_14D,_14z));return new F(function(){return _BJ(_14J.a,_14J.b,_14J.c,_14J.d,_);});},_14K=new T(function(){return B(unCStr("contractInput"));}),_14L="(function (t, s) {window[t].setValue(s)})",_14M=function(_14N,_14O,_){var _14P=eval(E(_14L)),_14Q=__app2(E(_14P),toJSStr(E(_14N)),toJSStr(E(_14O)));return new F(function(){return _A6(_);});},_14R=function(_14S,_14T,_14U,_){var _14V=E(_14K),_14W=toJSStr(_14V),_14X=eval(E(_Yo)),_14Y=__app1(E(_14X),_14W),_14Z=B(_106(B(_g4(_yK,new T(function(){var _150=String(_14Y);return fromJSStr(_150);})))));if(!_14Z._){return E(_eS);}else{if(!E(_14Z.b)._){var _151=E(_14Z.a),_152=new T(function(){return B(_8Q(new T(function(){return B(_jG(E(_14U)));}),new T(function(){return B(_jG(E(_14S)));}),new T(function(){return B(_jG(E(_14T)));}),B(_9V(_151.c))));},1),_153=B(_eC(new T(function(){return B(_bH(_151.a));},1),new T(function(){return B(_8f(_151.b));},1),_152,new T(function(){return B(_4n(_151.d));},1))),_154=B(_14M(_14V,new T2(1,_153.a,_153.b),_)),_155=__app1(E(_14X),_14W),_156=new T(function(){var _157=B(_106(B(_g4(_yK,new T(function(){var _158=String(_155);return fromJSStr(_158);})))));if(!_157._){return E(_eS);}else{if(!E(_157.b)._){var _159=E(_157.a);return new T4(0,new T(function(){return B(_bH(_159.a));}),new T(function(){return B(_8f(_159.b));}),new T(function(){return B(_9V(_159.c));}),new T(function(){return B(_4n(_159.d));}));}else{return E(_eQ);}}});return new F(function(){return _14r(_156,_);});}else{return E(_eQ);}}},_15a=function(_15b,_15c,_15d,_15e){var _15f=E(_15e);if(!_15f._){var _15g=_15f.c,_15h=_15f.d,_15i=E(_15f.b);switch(B(_2(_15b,_15i.a))){case 0:return new F(function(){return _5q(_15i,B(_15a(_15b,_15c,_15d,_15g)),_15h);});break;case 1:switch(B(_2(_15c,_15i.b))){case 0:return new F(function(){return _5q(_15i,B(_15a(_15b,_15c,_15d,_15g)),_15h);});break;case 1:switch(B(_2(_15d,_15i.c))){case 0:return new F(function(){return _5q(_15i,B(_15a(_15b,_15c,_15d,_15g)),_15h);});break;case 1:return new T4(0,_15f.a,E(new T3(0,_15b,_15c,_15d)),E(_15g),E(_15h));default:return new F(function(){return _4G(_15i,_15g,B(_15a(_15b,_15c,_15d,_15h)));});}break;default:return new F(function(){return _4G(_15i,_15g,B(_15a(_15b,_15c,_15d,_15h)));});}break;default:return new F(function(){return _4G(_15i,_15g,B(_15a(_15b,_15c,_15d,_15h)));});}}else{return new T4(0,1,E(new T3(0,_15b,_15c,_15d)),E(_4B),E(_4B));}},_15j=function(_15k,_15l,_15m,_){var _15n=E(_14K),_15o=toJSStr(_15n),_15p=eval(E(_Yo)),_15q=__app1(E(_15p),_15o),_15r=B(_106(B(_g4(_yK,new T(function(){var _15s=String(_15q);return fromJSStr(_15s);})))));if(!_15r._){return E(_eS);}else{if(!E(_15r.b)._){var _15t=E(_15r.a),_15u=new T(function(){return B(_15a(new T(function(){return B(_jG(E(_15m)));}),new T(function(){return B(_jG(E(_15k)));}),new T(function(){return B(_jG(E(_15l)));}),B(_8f(_15t.b))));},1),_15v=B(_eC(new T(function(){return B(_bH(_15t.a));},1),_15u,new T(function(){return B(_9V(_15t.c));},1),new T(function(){return B(_4n(_15t.d));},1))),_15w=B(_14M(_15n,new T2(1,_15v.a,_15v.b),_)),_15x=__app1(E(_15p),_15o),_15y=new T(function(){var _15z=B(_106(B(_g4(_yK,new T(function(){var _15A=String(_15x);return fromJSStr(_15A);})))));if(!_15z._){return E(_eS);}else{if(!E(_15z.b)._){var _15B=E(_15z.a);return new T4(0,new T(function(){return B(_bH(_15B.a));}),new T(function(){return B(_8f(_15B.b));}),new T(function(){return B(_9V(_15B.c));}),new T(function(){return B(_4n(_15B.d));}));}else{return E(_eQ);}}});return new F(function(){return _14r(_15y,_);});}else{return E(_eQ);}}},_15C=function(_15D,_15E,_15F,_15G,_){var _15H=E(_14K),_15I=toJSStr(_15H),_15J=eval(E(_Yo)),_15K=__app1(E(_15J),_15I),_15L=B(_106(B(_g4(_yK,new T(function(){var _15M=String(_15K);return fromJSStr(_15M);})))));if(!_15L._){return E(_eS);}else{if(!E(_15L.b)._){var _15N=E(_15L.a),_15O=new T(function(){return B(_aA(new T(function(){return B(_jG(E(_15F)));}),new T(function(){return B(_jG(E(_15D)));}),new T(function(){return B(_jG(E(_15E)));}),new T(function(){return B(_jG(E(_15G)));}),B(_bH(_15N.a))));},1),_15P=B(_eC(_15O,new T(function(){return B(_8f(_15N.b));},1),new T(function(){return B(_9V(_15N.c));},1),new T(function(){return B(_4n(_15N.d));},1))),_15Q=B(_14M(_15H,new T2(1,_15P.a,_15P.b),_)),_15R=__app1(E(_15J),_15I),_15S=new T(function(){var _15T=B(_106(B(_g4(_yK,new T(function(){var _15U=String(_15R);return fromJSStr(_15U);})))));if(!_15T._){return E(_eS);}else{if(!E(_15T.b)._){var _15V=E(_15T.a);return new T4(0,new T(function(){return B(_bH(_15V.a));}),new T(function(){return B(_8f(_15V.b));}),new T(function(){return B(_9V(_15V.c));}),new T(function(){return B(_4n(_15V.d));}));}else{return E(_eQ);}}});return new F(function(){return _14r(_15S,_);});}else{return E(_eQ);}}},_15W=new T(function(){return B(err(_eR));}),_15X=new T(function(){return B(unCStr("SICC"));}),_15Y=new T(function(){return B(unCStr("SIRC"));}),_15Z=new T(function(){return B(unCStr("SIP"));}),_160=11,_161=function(_162,_163){var _164=new T(function(){var _165=new T(function(){if(_162>10){return new T0(2);}else{var _166=new T(function(){var _167=new T(function(){var _168=function(_169){var _16a=function(_16b){return new F(function(){return A3(_sX,_tq,_160,function(_16c){return new F(function(){return A1(_163,new T3(2,_169,_16b,_16c));});});});};return new F(function(){return A3(_sX,_tq,_160,_16a);});};return B(A3(_sM,_vW,_160,_168));});return B(_rV(function(_16d){var _16e=E(_16d);return (_16e._==3)?(!B(_gS(_16e.a,_15Z)))?new T0(2):E(_167):new T0(2);}));}),_16f=function(_16g){return E(_166);};return new T1(1,function(_16h){return new F(function(){return A2(_qC,_16h,_16f);});});}});if(_162>10){return B(_ge(_eT,_165));}else{var _16i=new T(function(){var _16j=new T(function(){var _16k=function(_16l){var _16m=function(_16n){return new F(function(){return A3(_sX,_tq,_160,function(_16o){return new F(function(){return A1(_163,new T3(1,_16l,_16n,_16o));});});});};return new F(function(){return A3(_sX,_tq,_160,_16m);});};return B(A3(_sM,_wQ,_160,_16k));});return B(_rV(function(_16p){var _16q=E(_16p);return (_16q._==3)?(!B(_gS(_16q.a,_15Y)))?new T0(2):E(_16j):new T0(2);}));}),_16r=function(_16s){return E(_16i);};return B(_ge(new T1(1,function(_16t){return new F(function(){return A2(_qC,_16t,_16r);});}),_165));}});if(_162>10){return new F(function(){return _ge(_eT,_164);});}else{var _16u=new T(function(){var _16v=new T(function(){var _16w=function(_16x){var _16y=function(_16z){var _16A=function(_16B){return new F(function(){return A3(_sX,_tq,_160,function(_16C){return new F(function(){return A1(_163,new T4(0,_16x,_16z,_16B,_16C));});});});};return new F(function(){return A3(_sX,_tq,_160,_16A);});};return new F(function(){return A3(_sX,_tq,_160,_16y);});};return B(A3(_sM,_wQ,_160,_16w));});return B(_rV(function(_16D){var _16E=E(_16D);return (_16E._==3)?(!B(_gS(_16E.a,_15X)))?new T0(2):E(_16v):new T0(2);}));}),_16F=function(_16G){return E(_16u);};return new F(function(){return _ge(new T1(1,function(_16H){return new F(function(){return A2(_qC,_16H,_16F);});}),_164);});}},_16I=function(_16J,_16K){return new F(function(){return _161(E(_16J),_16K);});},_16L=new T(function(){return B(A3(_sM,_16I,_ss,_yF));}),_16M=function(_16N){var _16O=B(_106(B(_g4(_16L,_16N))));if(!_16O._){return E(_15W);}else{if(!E(_16O.b)._){var _16P=E(_16O.a);switch(_16P._){case 0:var _16Q=new T(function(){return B(_bX(_16P.d));}),_16R=new T(function(){return B(_bX(_16P.a));}),_16S=new T(function(){return B(_bX(_16P.c));}),_16T=new T(function(){return B(_bX(_16P.b));});return function(_ue){return new F(function(){return _15C(_16T,_16S,_16R,_16Q,_ue);});};case 1:var _16U=new T(function(){return B(_bX(_16P.a));}),_16V=new T(function(){return B(_bX(_16P.c));}),_16W=new T(function(){return B(_bX(_16P.b));});return function(_ue){return new F(function(){return _15j(_16W,_16V,_16U,_ue);});};default:var _16X=new T(function(){return B(_bX(_16P.a));}),_16Y=new T(function(){return B(_bX(_16P.c));}),_16Z=new T(function(){return B(_bX(_16P.b));});return function(_ue){return new F(function(){return _14R(_16Z,_16Y,_16X,_ue);});};}}else{return E(_c0);}}},_170=function(_171,_172,_173,_){var _174=E(_14K),_175=toJSStr(_174),_176=eval(E(_Yo)),_177=__app1(E(_176),_175),_178=B(_106(B(_g4(_yK,new T(function(){var _179=String(_177);return fromJSStr(_179);})))));if(!_178._){return E(_eS);}else{if(!E(_178.b)._){var _17a=E(_178.a),_17b=new T(function(){return B(_3i(new T(function(){return B(_jG(E(_173)));}),new T(function(){return B(_jG(E(_171)));}),new T(function(){return B(_jG(E(_172)));}),B(_4n(_17a.d))));},1),_17c=B(_eC(new T(function(){return B(_bH(_17a.a));},1),new T(function(){return B(_8f(_17a.b));},1),new T(function(){return B(_9V(_17a.c));},1),_17b)),_17d=B(_14M(_174,new T2(1,_17c.a,_17c.b),_)),_17e=__app1(E(_176),_175),_17f=new T(function(){var _17g=B(_106(B(_g4(_yK,new T(function(){var _17h=String(_17e);return fromJSStr(_17h);})))));if(!_17g._){return E(_eS);}else{if(!E(_17g.b)._){var _17i=E(_17g.a);return new T4(0,new T(function(){return B(_bH(_17i.a));}),new T(function(){return B(_8f(_17i.b));}),new T(function(){return B(_9V(_17i.c));}),new T(function(){return B(_4n(_17i.d));}));}else{return E(_eQ);}}});return new F(function(){return _14r(_17f,_);});}else{return E(_eQ);}}},_17j=new T(function(){return B(err(_bZ));}),_17k=new T(function(){return B(err(_eR));}),_17l=new T(function(){return B(_v4(_uI,_uh,_yF));}),_17m=function(_17n,_17o){var _17p=new T(function(){var _17q=B(_106(B(_g4(_17l,_17n))));if(!_17q._){return E(_17k);}else{if(!E(_17q.b)._){var _17r=E(_17q.a);return new T2(0,_17r.a,_17r.b);}else{return E(_17j);}}}),_17s=new T(function(){return B(_bU(E(_17p).a));}),_17t=new T(function(){return B(_bU(E(_17p).b));});return function(_ue){return new F(function(){return _170(_17t,_17o,_17s,_ue);});};},_17u=new T1(0,1),_17v=function(_17w,_17x){var _17y=E(_17w);return new T2(0,_17y,new T(function(){var _17z=B(_17v(B(_ji(_17y,_17x)),_17x));return new T2(1,_17z.a,_17z.b);}));},_17A=function(_17B){var _17C=B(_17v(_17B,_17u));return new T2(1,_17C.a,_17C.b);},_17D=function(_17E,_17F){var _17G=B(_17v(_17E,new T(function(){return B(_U4(_17F,_17E));})));return new T2(1,_17G.a,_17G.b);},_17H=new T1(0,0),_17I=function(_17J,_17K,_17L){if(!B(_e(_17K,_17H))){var _17M=function(_17N){return (!B(_co(_17N,_17L)))?new T2(1,_17N,new T(function(){return B(_17M(B(_ji(_17N,_17K))));})):__Z;};return new F(function(){return _17M(_17J);});}else{var _17O=function(_17P){return (!B(_CV(_17P,_17L)))?new T2(1,_17P,new T(function(){return B(_17O(B(_ji(_17P,_17K))));})):__Z;};return new F(function(){return _17O(_17J);});}},_17Q=function(_17R,_17S,_17T){return new F(function(){return _17I(_17R,B(_U4(_17S,_17R)),_17T);});},_17U=function(_17V,_17W){return new F(function(){return _17I(_17V,_17u,_17W);});},_17X=function(_17Y){return new F(function(){return _bU(_17Y);});},_17Z=function(_180){return new F(function(){return _U4(_180,_17u);});},_181=function(_182){return new F(function(){return _ji(_182,_17u);});},_183=function(_184){return new F(function(){return _jG(E(_184));});},_185={_:0,a:_181,b:_17Z,c:_183,d:_17X,e:_17A,f:_17D,g:_17U,h:_17Q},_186=function(_187,_188){if(_187<=0){if(_187>=0){return new F(function(){return quot(_187,_188);});}else{if(_188<=0){return new F(function(){return quot(_187,_188);});}else{return quot(_187+1|0,_188)-1|0;}}}else{if(_188>=0){if(_187>=0){return new F(function(){return quot(_187,_188);});}else{if(_188<=0){return new F(function(){return quot(_187,_188);});}else{return quot(_187+1|0,_188)-1|0;}}}else{return quot(_187-1|0,_188)-1|0;}}},_189=function(_18a,_18b){while(1){var _18c=E(_18a);if(!_18c._){var _18d=E(_18c.a);if(_18d==( -2147483648)){_18a=new T1(1,I_fromInt( -2147483648));continue;}else{var _18e=E(_18b);if(!_18e._){return new T1(0,B(_186(_18d,_18e.a)));}else{_18a=new T1(1,I_fromInt(_18d));_18b=_18e;continue;}}}else{var _18f=_18c.a,_18g=E(_18b);return (_18g._==0)?new T1(1,I_div(_18f,I_fromInt(_18g.a))):new T1(1,I_div(_18f,_18g.a));}}},_18h=new T(function(){return B(unCStr("base"));}),_18i=new T(function(){return B(unCStr("GHC.Exception"));}),_18j=new T(function(){return B(unCStr("ArithException"));}),_18k=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_18h,_18i,_18j),_18l=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_18k,_1,_1),_18m=function(_18n){return E(_18l);},_18o=function(_18p){var _18q=E(_18p);return new F(function(){return _f5(B(_f3(_18q.a)),_18m,_18q.b);});},_18r=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_18s=new T(function(){return B(unCStr("denormal"));}),_18t=new T(function(){return B(unCStr("divide by zero"));}),_18u=new T(function(){return B(unCStr("loss of precision"));}),_18v=new T(function(){return B(unCStr("arithmetic underflow"));}),_18w=new T(function(){return B(unCStr("arithmetic overflow"));}),_18x=function(_18y,_18z){switch(E(_18y)){case 0:return new F(function(){return _ce(_18w,_18z);});break;case 1:return new F(function(){return _ce(_18v,_18z);});break;case 2:return new F(function(){return _ce(_18u,_18z);});break;case 3:return new F(function(){return _ce(_18t,_18z);});break;case 4:return new F(function(){return _ce(_18s,_18z);});break;default:return new F(function(){return _ce(_18r,_18z);});}},_18A=function(_18B){return new F(function(){return _18x(_18B,_1);});},_18C=function(_18D,_18E,_18F){return new F(function(){return _18x(_18E,_18F);});},_18G=function(_18H,_18I){return new F(function(){return _dQ(_18x,_18H,_18I);});},_18J=new T3(0,_18C,_18A,_18G),_18K=new T(function(){return new T5(0,_18m,_18J,_18L,_18o,_18A);}),_18L=function(_fE){return new T2(0,_18K,_fE);},_18M=3,_18N=new T(function(){return B(_18L(_18M));}),_18O=new T(function(){return die(_18N);}),_18P=new T1(0,0),_18Q=function(_18R,_18S){if(!B(_C1(_18S,_18P))){return new F(function(){return _189(_18R,_18S);});}else{return E(_18O);}},_18T=function(_18U,_18V){var _18W=_18U%_18V;if(_18U<=0){if(_18U>=0){return E(_18W);}else{if(_18V<=0){return E(_18W);}else{var _18X=E(_18W);return (_18X==0)?0:_18X+_18V|0;}}}else{if(_18V>=0){if(_18U>=0){return E(_18W);}else{if(_18V<=0){return E(_18W);}else{var _18Y=E(_18W);return (_18Y==0)?0:_18Y+_18V|0;}}}else{var _18Z=E(_18W);return (_18Z==0)?0:_18Z+_18V|0;}}},_190=function(_191,_192){while(1){var _193=E(_191);if(!_193._){var _194=E(_193.a);if(_194==( -2147483648)){_191=new T1(1,I_fromInt( -2147483648));continue;}else{var _195=E(_192);if(!_195._){var _196=_195.a;return new T2(0,new T1(0,B(_186(_194,_196))),new T1(0,B(_18T(_194,_196))));}else{_191=new T1(1,I_fromInt(_194));_192=_195;continue;}}}else{var _197=E(_192);if(!_197._){_191=_193;_192=new T1(1,I_fromInt(_197.a));continue;}else{var _198=I_divMod(_193.a,_197.a);return new T2(0,new T1(1,_198.a),new T1(1,_198.b));}}}},_199=function(_19a,_19b){if(!B(_C1(_19b,_18P))){var _19c=B(_190(_19a,_19b));return new T2(0,_19c.a,_19c.b);}else{return E(_18O);}},_19d=function(_19e,_19f){while(1){var _19g=E(_19e);if(!_19g._){var _19h=E(_19g.a);if(_19h==( -2147483648)){_19e=new T1(1,I_fromInt( -2147483648));continue;}else{var _19i=E(_19f);if(!_19i._){return new T1(0,B(_18T(_19h,_19i.a)));}else{_19e=new T1(1,I_fromInt(_19h));_19f=_19i;continue;}}}else{var _19j=_19g.a,_19k=E(_19f);return (_19k._==0)?new T1(1,I_mod(_19j,I_fromInt(_19k.a))):new T1(1,I_mod(_19j,_19k.a));}}},_19l=function(_19m,_19n){if(!B(_C1(_19n,_18P))){return new F(function(){return _19d(_19m,_19n);});}else{return E(_18O);}},_19o=function(_19p,_19q){while(1){var _19r=E(_19p);if(!_19r._){var _19s=E(_19r.a);if(_19s==( -2147483648)){_19p=new T1(1,I_fromInt( -2147483648));continue;}else{var _19t=E(_19q);if(!_19t._){return new T1(0,quot(_19s,_19t.a));}else{_19p=new T1(1,I_fromInt(_19s));_19q=_19t;continue;}}}else{var _19u=_19r.a,_19v=E(_19q);return (_19v._==0)?new T1(0,I_toInt(I_quot(_19u,I_fromInt(_19v.a)))):new T1(1,I_quot(_19u,_19v.a));}}},_19w=function(_19x,_19y){if(!B(_C1(_19y,_18P))){return new F(function(){return _19o(_19x,_19y);});}else{return E(_18O);}},_19z=function(_19A,_19B){while(1){var _19C=E(_19A);if(!_19C._){var _19D=E(_19C.a);if(_19D==( -2147483648)){_19A=new T1(1,I_fromInt( -2147483648));continue;}else{var _19E=E(_19B);if(!_19E._){var _19F=_19E.a;return new T2(0,new T1(0,quot(_19D,_19F)),new T1(0,_19D%_19F));}else{_19A=new T1(1,I_fromInt(_19D));_19B=_19E;continue;}}}else{var _19G=E(_19B);if(!_19G._){_19A=_19C;_19B=new T1(1,I_fromInt(_19G.a));continue;}else{var _19H=I_quotRem(_19C.a,_19G.a);return new T2(0,new T1(1,_19H.a),new T1(1,_19H.b));}}}},_19I=function(_19J,_19K){if(!B(_C1(_19K,_18P))){var _19L=B(_19z(_19J,_19K));return new T2(0,_19L.a,_19L.b);}else{return E(_18O);}},_19M=function(_19N,_19O){while(1){var _19P=E(_19N);if(!_19P._){var _19Q=E(_19P.a);if(_19Q==( -2147483648)){_19N=new T1(1,I_fromInt( -2147483648));continue;}else{var _19R=E(_19O);if(!_19R._){return new T1(0,_19Q%_19R.a);}else{_19N=new T1(1,I_fromInt(_19Q));_19O=_19R;continue;}}}else{var _19S=_19P.a,_19T=E(_19O);return (_19T._==0)?new T1(1,I_rem(_19S,I_fromInt(_19T.a))):new T1(1,I_rem(_19S,_19T.a));}}},_19U=function(_19V,_19W){if(!B(_C1(_19W,_18P))){return new F(function(){return _19M(_19V,_19W);});}else{return E(_18O);}},_19X=function(_19Y){return E(_19Y);},_19Z=function(_1a0){return E(_1a0);},_1a1=function(_1a2){var _1a3=E(_1a2);if(!_1a3._){var _1a4=E(_1a3.a);return (_1a4==( -2147483648))?E(_jr):(_1a4<0)?new T1(0, -_1a4):E(_1a3);}else{var _1a5=_1a3.a;return (I_compareInt(_1a5,0)>=0)?E(_1a3):new T1(1,I_negate(_1a5));}},_1a6=new T1(0,0),_1a7=new T1(0, -1),_1a8=function(_1a9){var _1aa=E(_1a9);if(!_1aa._){var _1ab=_1aa.a;return (_1ab>=0)?(E(_1ab)==0)?E(_1a6):E(_jg):E(_1a7);}else{var _1ac=I_compareInt(_1aa.a,0);return (_1ac<=0)?(E(_1ac)==0)?E(_1a6):E(_1a7):E(_jg);}},_1ad={_:0,a:_ji,b:_U4,c:_jM,d:_js,e:_1a1,f:_1a8,g:_19Z},_1ae={_:0,a:_RW,b:_2,c:_co,d:_lm,e:_CV,f:_e,g:_OH,h:_OK},_1af=new T1(0,1),_1ag=function(_1ah){return new T2(0,E(_1ah),E(_1af));},_1ai=new T3(0,_1ad,_1ae,_1ag),_1aj={_:0,a:_1ai,b:_185,c:_19w,d:_19U,e:_18Q,f:_19l,g:_19I,h:_199,i:_19X},_1ak=new T(function(){return B(unCStr("head"));}),_1al=new T(function(){return B(_dn(_1ak));}),_1am=function(_1an){return new F(function(){return _cz(0,_1an,_1);});},_1ao=new T(function(){return B(unCStr("IdentPay"));}),_1ap=new T(function(){return B(unCStr("ValueGE"));}),_1aq=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1ar=new T(function(){return B(unCStr("PersonChoseThis"));}),_1as=new T(function(){return B(unCStr("NotObs"));}),_1at=new T(function(){return B(unCStr("OrObs"));}),_1au=new T(function(){return B(unCStr("AndObs"));}),_1av=new T(function(){return B(unCStr("BelowTimeout"));}),_1aw=new T(function(){return B(unCStr("When"));}),_1ax=new T(function(){return B(unCStr("Choice"));}),_1ay=new T(function(){return B(unCStr("Both"));}),_1az=new T(function(){return B(unCStr("IdentChoice"));}),_1aA=new T(function(){return B(unCStr("Pay"));}),_1aB=new T(function(){return B(unCStr("RedeemCC"));}),_1aC=new T(function(){return B(unCStr("CommitCash"));}),_1aD=new T(function(){return B(unCStr("Null"));}),_1aE=new T(function(){return B(unCStr("IdentCC"));}),_1aF=new T(function(){return B(unCStr("MoneyFromChoice"));}),_1aG=new T(function(){return B(unCStr("ConstMoney"));}),_1aH=new T(function(){return B(unCStr("AddMoney"));}),_1aI=new T(function(){return B(unCStr("AvailableMoney"));}),_1aJ=new T(function(){return B(unCStr("FalseObs"));}),_1aK=new T(function(){return B(unCStr("TrueObs"));}),_1aL=function(_1aM){var _1aN=E(_1aM);switch(_1aN._){case 0:var _1aO=E(_1aN.a);switch(_1aO._){case 0:return new T2(0,_1aD,_1);case 1:return new T2(0,_1aC,new T2(1,new T1(3,_1aO.a),new T2(1,new T1(6,_1aO.b),new T2(1,new T1(2,_1aO.c),new T2(1,new T1(6,_1aO.d),new T2(1,new T1(6,_1aO.e),new T2(1,new T1(0,_1aO.f),new T2(1,new T1(0,_1aO.g),_1))))))));case 2:return new T2(0,_1aB,new T2(1,new T1(3,_1aO.a),new T2(1,new T1(0,_1aO.b),_1)));case 3:return new T2(0,_1aA,new T2(1,new T1(5,_1aO.a),new T2(1,new T1(6,_1aO.b),new T2(1,new T1(6,_1aO.c),new T2(1,new T1(2,_1aO.d),new T2(1,new T1(6,_1aO.e),new T2(1,new T1(0,_1aO.f),_1)))))));case 4:return new T2(0,_1ay,new T2(1,new T1(0,_1aO.a),new T2(1,new T1(0,_1aO.b),_1)));case 5:return new T2(0,_1ax,new T2(1,new T1(1,_1aO.a),new T2(1,new T1(0,_1aO.b),new T2(1,new T1(0,_1aO.c),_1))));default:return new T2(0,_1aw,new T2(1,new T1(1,_1aO.a),new T2(1,new T1(6,_1aO.b),new T2(1,new T1(0,_1aO.c),new T2(1,new T1(0,_1aO.d),_1)))));}break;case 1:var _1aP=E(_1aN.a);switch(_1aP._){case 0:return new T2(0,_1av,new T2(1,new T1(6,_1aP.a),_1));case 1:return new T2(0,_1au,new T2(1,new T1(1,_1aP.a),new T2(1,new T1(1,_1aP.b),_1)));case 2:return new T2(0,_1at,new T2(1,new T1(1,_1aP.a),new T2(1,new T1(1,_1aP.b),_1)));case 3:return new T2(0,_1as,new T2(1,new T1(1,_1aP.a),_1));case 4:return new T2(0,_1ar,new T2(1,new T1(4,_1aP.a),new T2(1,new T1(6,_1aP.b),new T2(1,new T1(6,_1aP.c),_1))));case 5:return new T2(0,_1aq,new T2(1,new T1(4,_1aP.a),new T2(1,new T1(6,_1aP.b),_1)));case 6:return new T2(0,_1ap,new T2(1,new T1(2,_1aP.a),new T2(1,new T1(2,_1aP.b),_1)));case 7:return new T2(0,_1aK,_1);default:return new T2(0,_1aJ,_1);}break;case 2:var _1aQ=E(_1aN.a);switch(_1aQ._){case 0:return new T2(0,_1aI,new T2(1,new T1(3,_1aQ.a),_1));case 1:return new T2(0,_1aH,new T2(1,new T1(2,_1aQ.a),new T2(1,new T1(2,_1aQ.b),_1)));case 2:return new T2(0,_1aG,new T2(1,new T1(6,_1aQ.a),_1));default:return new T2(0,_1aF,new T2(1,new T1(4,_1aQ.a),new T2(1,new T1(6,_1aQ.b),new T2(1,new T1(2,_1aQ.c),_1))));}break;case 3:return new T2(0,_1aE,new T2(1,new T1(6,_1aN.a),_1));case 4:return new T2(0,_1az,new T2(1,new T1(6,_1aN.a),_1));case 5:return new T2(0,_1ao,new T2(1,new T1(6,_1aN.a),_1));default:return new T2(0,new T(function(){return B(_1am(_1aN.a));}),_1);}},_1aR=function(_1aS){var _1aT=B(_1aL(_1aS)),_1aU=_1aT.a,_1aV=E(_1aT.b);if(!_1aV._){return new T1(0,new T2(0,_1aU,_1));}else{switch(E(_1aS)._){case 0:return new T1(2,new T2(0,_1aU,_1aV));case 1:return new T1(2,new T2(0,_1aU,_1aV));case 2:return new T1(2,new T2(0,_1aU,_1aV));default:return new T1(1,new T2(0,_1aU,_1aV));}}},_1aW=function(_1aX){return E(E(_1aX).a);},_1aY=function(_1aZ){return E(E(_1aZ).a);},_1b0=function(_1b1){return E(E(_1b1).b);},_1b2=function(_1b3){return E(E(_1b3).b);},_1b4=function(_1b5){return E(E(_1b5).g);},_1b6=new T1(0,0),_1b7=new T1(0,1),_1b8=function(_1b9,_1ba,_1bb){var _1bc=B(_1aW(_1b9)),_1bd=new T(function(){return B(_1aY(_1bc));});if(!B(A3(_IF,B(_1b0(_1bc)),_1ba,new T(function(){return B(A2(_1b4,_1bd,_1b6));})))){var _1be=E(_1bb);if(!_1be._){return __Z;}else{var _1bf=new T(function(){var _1bg=new T(function(){return B(A3(_1b2,_1bd,_1ba,new T(function(){return B(A2(_1b4,_1bd,_1b7));})));});return B(_1b8(_1b9,_1bg,_1be.b));});return new T2(1,_1be.a,_1bf);}}else{return __Z;}},_1bh=function(_1bi,_1bj){var _1bk=E(_1bj);if(!_1bk._){return __Z;}else{var _1bl=_1bk.a,_1bm=new T(function(){var _1bn=B(_fF(new T(function(){return B(A1(_1bi,_1bl));}),_1bk.b));return new T2(0,_1bn.a,_1bn.b);});return new T2(1,new T2(1,_1bl,new T(function(){return E(E(_1bm).a);})),new T(function(){return B(_1bh(_1bi,E(_1bm).b));}));}},_1bo=function(_1bp){var _1bq=E(_1bp);if(!_1bq._){return __Z;}else{return new F(function(){return _ce(_1bq.a,new T(function(){return B(_1bo(_1bq.b));},1));});}},_1br=new T(function(){return B(unCStr("\n"));}),_1bs=new T1(0,1),_1bt=function(_1bu,_1bv){return (E(_1bu)._==2)?false:(E(_1bv)._==2)?false:true;},_1bw=function(_1bx,_1by){var _1bz=E(_1by);return (_1bz._==0)?__Z:new T2(1,_1bx,new T2(1,_1bz.a,new T(function(){return B(_1bw(_1bx,_1bz.b));})));},_1bA=new T(function(){return B(unCStr("tail"));}),_1bB=new T(function(){return B(_dn(_1bA));}),_1bC=new T(function(){return B(unCStr(")"));}),_1bD=new T1(0,0),_1bE=function(_1bF,_1bG){var _1bH=E(_1bG);switch(_1bH._){case 0:var _1bI=E(_1bH.a);return new F(function(){return _1bJ(_1bD,_1bI.a,_1bI.b);});break;case 1:return new F(function(){return unAppCStr("(",new T(function(){var _1bK=E(_1bH.a);return B(_ce(B(_1bJ(_1bD,_1bK.a,_1bK.b)),_1bC));}));});break;default:var _1bL=new T(function(){var _1bM=E(_1bH.a);return B(_ce(B(_1bJ(new T(function(){return B(_ji(_1bF,_1bs));},1),_1bM.a,_1bM.b)),_1bC));});return new F(function(){return unAppCStr("(",_1bL);});}},_1bN=function(_1bO){return E(E(_1bO).a);},_1bP=function(_1bQ,_1bR){var _1bS=new T(function(){return B(A2(_1b4,_1bQ,_1b7));}),_1bT=function(_1bU,_1bV){while(1){var _1bW=E(_1bU);if(!_1bW._){return E(_1bV);}else{var _1bX=B(A3(_1bN,_1bQ,_1bV,_1bS));_1bU=_1bW.b;_1bV=_1bX;continue;}}};return new F(function(){return _1bT(_1bR,new T(function(){return B(A2(_1b4,_1bQ,_1b6));}));});},_1bY=32,_1bZ=new T(function(){return new T2(1,_1bY,_1bZ);}),_1bJ=function(_1c0,_1c1,_1c2){var _1c3=E(_1c2);if(!_1c3._){return E(_1c1);}else{var _1c4=new T(function(){return B(_ji(B(_ji(_1c0,B(_1bP(_1ad,_1c1)))),_1bs));}),_1c5=new T(function(){return B(_1bh(_1bt,B(_jC(_1aR,_1c3))));}),_1c6=new T(function(){var _1c7=E(_1c5);if(!_1c7._){return E(_1bB);}else{var _1c8=new T(function(){return B(_1b8(_1aj,_1c4,_1bZ));}),_1c9=function(_1ca){var _1cb=new T(function(){var _1cc=function(_1cd){var _1ce=E(_1cd);if(!_1ce._){return __Z;}else{var _1cf=new T(function(){return B(_ce(B(_1bE(_1c4,_1ce.a)),new T(function(){return B(_1cc(_1ce.b));},1)));});return new T2(1,_1bY,_1cf);}},_1cg=B(_1cc(_1ca));if(!_1cg._){return __Z;}else{return E(_1cg.b);}},1);return new F(function(){return _ce(_1c8,_1cb);});};return B(_1bw(_1br,B(_jC(_1c9,_1c7.b))));}}),_1ch=new T(function(){var _1ci=new T(function(){var _1cj=E(_1c5);if(!_1cj._){return E(_1al);}else{var _1ck=function(_1cl){var _1cm=E(_1cl);if(!_1cm._){return __Z;}else{var _1cn=new T(function(){return B(_ce(B(_1bE(_1c4,_1cm.a)),new T(function(){return B(_1ck(_1cm.b));},1)));});return new T2(1,_1bY,_1cn);}};return B(_1ck(_1cj.a));}},1);return B(_ce(_1c1,_1ci));});return new F(function(){return _1bo(new T2(1,_1ch,_1c6));});}},_1co=new T(function(){return B(_1bJ(_1bD,_1aD,_1));}),_1cp=function(_1cq,_){return new T(function(){var _1cr=B(_106(B(_g4(_14q,_1cq))));if(!_1cr._){return E(_10e);}else{if(!E(_1cr.b)._){var _1cs=E(_1cr.a);switch(_1cs._){case 0:return E(_1co);break;case 1:return B(_1bJ(_1bD,_1aC,new T2(1,new T1(3,_1cs.a),new T2(1,new T1(6,_1cs.b),new T2(1,new T1(2,_1cs.c),new T2(1,new T1(6,_1cs.d),new T2(1,new T1(6,_1cs.e),new T2(1,new T1(0,_1cs.f),new T2(1,new T1(0,_1cs.g),_1)))))))));break;case 2:return B(_1bJ(_1bD,_1aB,new T2(1,new T1(3,_1cs.a),new T2(1,new T1(0,_1cs.b),_1))));break;case 3:return B(_1bJ(_1bD,_1aA,new T2(1,new T1(5,_1cs.a),new T2(1,new T1(6,_1cs.b),new T2(1,new T1(6,_1cs.c),new T2(1,new T1(2,_1cs.d),new T2(1,new T1(6,_1cs.e),new T2(1,new T1(0,_1cs.f),_1))))))));break;case 4:return B(_1bJ(_1bD,_1ay,new T2(1,new T1(0,_1cs.a),new T2(1,new T1(0,_1cs.b),_1))));break;case 5:return B(_1bJ(_1bD,_1ax,new T2(1,new T1(1,_1cs.a),new T2(1,new T1(0,_1cs.b),new T2(1,new T1(0,_1cs.c),_1)))));break;default:return B(_1bJ(_1bD,_1aw,new T2(1,new T1(1,_1cs.a),new T2(1,new T1(6,_1cs.b),new T2(1,new T1(0,_1cs.c),new T2(1,new T1(0,_1cs.d),_1))))));}}else{return E(_10d);}}});},_1ct=new T(function(){return B(unCStr("codeArea"));}),_1cu=function(_){var _1cv=__app0(E(_Yp)),_1cw=B(_1cp(new T(function(){var _1cx=String(_1cv);return fromJSStr(_1cx);}),_)),_1cy=B(_14M(_1ct,_1cw,_)),_1cz=eval(E(_Yo)),_1cA=__app1(E(_1cz),toJSStr(E(_14K))),_1cB=new T(function(){var _1cC=B(_106(B(_g4(_yK,new T(function(){var _1cD=String(_1cA);return fromJSStr(_1cD);})))));if(!_1cC._){return E(_eS);}else{if(!E(_1cC.b)._){var _1cE=E(_1cC.a);return new T4(0,new T(function(){return B(_bH(_1cE.a));}),new T(function(){return B(_8f(_1cE.b));}),new T(function(){return B(_9V(_1cE.c));}),new T(function(){return B(_4n(_1cE.d));}));}else{return E(_eQ);}}});return new F(function(){return _14r(_1cB,_);});},_1cF="(function (b) { return (b.inputList.length); })",_1cG="(function (b, x) { return (b.inputList[x]); })",_1cH=function(_1cI,_1cJ,_){var _1cK=eval(E(_1cG)),_1cL=__app2(E(_1cK),_1cI,_1cJ);return new T1(0,_1cL);},_1cM=function(_1cN,_1cO,_1cP,_){var _1cQ=E(_1cP);if(!_1cQ._){return _1;}else{var _1cR=B(_1cH(_1cN,E(_1cQ.a),_)),_1cS=B(_1cM(_1cN,_,_1cQ.b,_));return new T2(1,_1cR,_1cS);}},_1cT=function(_1cU,_1cV){if(_1cU<=_1cV){var _1cW=function(_1cX){return new T2(1,_1cX,new T(function(){if(_1cX!=_1cV){return B(_1cW(_1cX+1|0));}else{return __Z;}}));};return new F(function(){return _1cW(_1cU);});}else{return __Z;}},_1cY=function(_1cZ,_){var _1d0=eval(E(_1cF)),_1d1=__app1(E(_1d0),_1cZ),_1d2=Number(_1d1),_1d3=jsTrunc(_1d2);return new F(function(){return _1cM(_1cZ,_,new T(function(){return B(_1cT(0,_1d3-1|0));}),_);});},_1d4="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_1d5="(function (x) { return x.name; })",_1d6=new T(function(){return B(unCStr("\""));}),_1d7=function(_1d8){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_ce(_1d8,_1d6));}))));});},_1d9=function(_1da,_1db,_){var _1dc=E(_1db);if(!_1dc._){return new F(function(){return _1d7(_1da);});}else{var _1dd=E(_1dc.a),_1de=E(_1d5),_1df=eval(_1de),_1dg=__app1(E(_1df),E(_1dd.a)),_1dh=String(_1dg);if(!B(_gS(fromJSStr(_1dh),_1da))){var _1di=function(_1dj,_1dk,_){while(1){var _1dl=E(_1dk);if(!_1dl._){return new F(function(){return _1d7(_1dj);});}else{var _1dm=E(_1dl.a),_1dn=eval(_1de),_1do=__app1(E(_1dn),E(_1dm.a)),_1dp=String(_1do);if(!B(_gS(fromJSStr(_1dp),_1dj))){_1dk=_1dl.b;continue;}else{return _1dm;}}}};return new F(function(){return _1di(_1da,_1dc.b,_);});}else{return _1dd;}}},_1dq=function(_1dr,_1ds,_1dt,_){var _1du=B(_1cY(_1ds,_)),_1dv=B(_1d9(_1dr,_1du,_)),_1dw=eval(E(_1d4)),_1dx=__app2(E(_1dw),E(E(_1dt).a),E(E(_1dv).a));return new F(function(){return _A6(_);});},_1dy="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_1dz=function(_1dA,_1dB,_1dC,_){var _1dD=B(_1cY(_1dB,_)),_1dE=B(_1d9(_1dA,_1dD,_)),_1dF=eval(E(_1dy)),_1dG=__app2(E(_1dF),E(E(_1dC).a),E(E(_1dE).a));return new F(function(){return _A6(_);});},_1dH=function(_1dI){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_ce(_1dI,_1d6));}))));});},_1dJ=function(_1dK,_1dL,_){var _1dM=E(_1dL);if(!_1dM._){return new F(function(){return _1dH(_1dK);});}else{var _1dN=E(_1dM.a),_1dO=E(_1d5),_1dP=eval(_1dO),_1dQ=__app1(E(_1dP),E(_1dN.a)),_1dR=String(_1dQ);if(!B(_gS(fromJSStr(_1dR),_1dK))){var _1dS=function(_1dT,_1dU,_){while(1){var _1dV=E(_1dU);if(!_1dV._){return new F(function(){return _1dH(_1dT);});}else{var _1dW=E(_1dV.a),_1dX=eval(_1dO),_1dY=__app1(E(_1dX),E(_1dW.a)),_1dZ=String(_1dY);if(!B(_gS(fromJSStr(_1dZ),_1dT))){_1dU=_1dV.b;continue;}else{return _1dW;}}}};return new F(function(){return _1dS(_1dK,_1dM.b,_);});}else{return _1dN;}}},_1e0="(function (b) { return (b.fieldRow.length); })",_1e1="(function (b, x) { return (b.fieldRow[x]); })",_1e2=function(_1e3,_1e4,_){var _1e5=eval(E(_1e1)),_1e6=__app2(E(_1e5),_1e3,_1e4);return new T1(0,_1e6);},_1e7=function(_1e8,_1e9,_1ea,_){var _1eb=E(_1ea);if(!_1eb._){return _1;}else{var _1ec=B(_1e2(_1e8,E(_1eb.a),_)),_1ed=B(_1e7(_1e8,_,_1eb.b,_));return new T2(1,_1ec,_1ed);}},_1ee=function(_1ef,_){var _1eg=eval(E(_1e0)),_1eh=__app1(E(_1eg),_1ef),_1ei=Number(_1eh),_1ej=jsTrunc(_1ei);return new F(function(){return _1e7(_1ef,_,new T(function(){return B(_1cT(0,_1ej-1|0));}),_);});},_1ek=function(_1el,_){var _1em=E(_1el);if(!_1em._){return _1;}else{var _1en=B(_1ee(E(E(_1em.a).a),_)),_1eo=B(_1ek(_1em.b,_));return new T2(1,_1en,_1eo);}},_1ep=function(_1eq){var _1er=E(_1eq);if(!_1er._){return __Z;}else{return new F(function(){return _ce(_1er.a,new T(function(){return B(_1ep(_1er.b));},1));});}},_1es=function(_1et,_1eu,_){var _1ev=B(_1cY(_1eu,_)),_1ew=B(_1ek(_1ev,_));return new F(function(){return _1dJ(_1et,B(_1ep(_1ew)),_);});},_1ex=function(_1ey,_1ez,_1eA,_){var _1eB=B(_1cY(_1ez,_)),_1eC=B(_1d9(_1ey,_1eB,_)),_1eD=eval(E(_1dy)),_1eE=__app2(E(_1eD),E(E(_1eA).a),E(E(_1eC).a));return new F(function(){return _A6(_);});},_1eF=new T(function(){return B(unCStr("contract_commitcash"));}),_1eG=new T(function(){return B(unCStr("contract_redeemcc"));}),_1eH=new T(function(){return B(unCStr("contract_pay"));}),_1eI=new T(function(){return B(unCStr("contract_both"));}),_1eJ=new T(function(){return B(unCStr("contract_choice"));}),_1eK=new T(function(){return B(unCStr("contract_when"));}),_1eL="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_1eM=function(_1eN,_){var _1eO=eval(E(_1eL)),_1eP=__app1(E(_1eO),toJSStr(E(_1eN)));return new T1(0,_1eP);},_1eQ=new T(function(){return B(unCStr("payer_id"));}),_1eR=new T(function(){return B(unCStr("pay_id"));}),_1eS=new T(function(){return B(unCStr("ccommit_id"));}),_1eT=new T(function(){return B(unCStr("end_expiration"));}),_1eU=new T(function(){return B(unCStr("start_expiration"));}),_1eV=new T(function(){return B(unCStr("person_id"));}),_1eW=new T(function(){return B(unCStr("contract_null"));}),_1eX=new T(function(){return B(unCStr("contract2"));}),_1eY=new T(function(){return B(unCStr("contract1"));}),_1eZ=new T(function(){return B(unCStr("observation"));}),_1f0=new T(function(){return B(unCStr("timeout"));}),_1f1=new T(function(){return B(unCStr("contract"));}),_1f2=new T(function(){return B(unCStr("expiration"));}),_1f3=new T(function(){return B(unCStr("ammount"));}),_1f4=new T(function(){return B(unCStr("payee_id"));}),_1f5=new T(function(){return B(unCStr("value_available_money"));}),_1f6=new T(function(){return B(unCStr("value_add_money"));}),_1f7=new T(function(){return B(unCStr("value_const_money"));}),_1f8=new T(function(){return B(unCStr("money_from_choice"));}),_1f9=new T(function(){return B(unCStr("value2"));}),_1fa=new T(function(){return B(unCStr("value1"));}),_1fb=new T(function(){return B(unCStr("choice_id"));}),_1fc=new T(function(){return B(unCStr("default"));}),_1fd=new T(function(){return B(unCStr("money"));}),_1fe=new T(function(){return B(unCStr("commit_id"));}),_1ff="(function (b, s) { return (b.setText(s)); })",_1fg=function(_1fh,_){var _1fi=E(_1fh);switch(_1fi._){case 0:var _1fj=B(_1eM(_1f5,_)),_1fk=E(_1fj),_1fl=B(_1es(_1fe,E(_1fk.a),_)),_1fm=eval(E(_1ff)),_1fn=__app2(E(_1fm),E(E(_1fl).a),toJSStr(B(_cz(0,_1fi.a,_1))));return _1fk;case 1:var _1fo=B(_1fg(_1fi.a,_)),_1fp=B(_1fg(_1fi.b,_)),_1fq=B(_1eM(_1f6,_)),_1fr=E(_1fq),_1fs=E(_1fr.a),_1ft=B(_1dz(_1fa,_1fs,_1fo,_)),_1fu=B(_1dz(_1f9,_1fs,_1fp,_));return _1fr;case 2:var _1fv=B(_1eM(_1f7,_)),_1fw=E(_1fv),_1fx=B(_1es(_1fd,E(_1fw.a),_)),_1fy=eval(E(_1ff)),_1fz=__app2(E(_1fy),E(E(_1fx).a),toJSStr(B(_cz(0,_1fi.a,_1))));return _1fw;default:var _1fA=B(_1fg(_1fi.c,_)),_1fB=B(_1eM(_1f8,_)),_1fC=E(_1fB),_1fD=E(_1fC.a),_1fE=B(_1es(_1fb,_1fD,_)),_1fF=eval(E(_1ff)),_1fG=__app2(E(_1fF),E(E(_1fE).a),toJSStr(B(_cz(0,_1fi.a,_1)))),_1fH=B(_1es(_1eV,_1fD,_)),_1fI=__app2(E(_1fF),E(E(_1fH).a),toJSStr(B(_cz(0,_1fi.b,_1)))),_1fJ=B(_1dz(_1fc,_1fD,_1fA,_));return _1fC;}},_1fK=new T(function(){return B(unCStr("observation_personchosethis"));}),_1fL=new T(function(){return B(unCStr("observation_personchosesomething"));}),_1fM=new T(function(){return B(unCStr("observation_value_ge"));}),_1fN=new T(function(){return B(unCStr("observation_trueobs"));}),_1fO=new T(function(){return B(unCStr("observation_falseobs"));}),_1fP=new T(function(){return B(unCStr("observation_belowtimeout"));}),_1fQ=new T(function(){return B(unCStr("observation_andobs"));}),_1fR=new T(function(){return B(unCStr("observation_orobs"));}),_1fS=new T(function(){return B(unCStr("observation_notobs"));}),_1fT=new T(function(){return B(unCStr("person"));}),_1fU=new T(function(){return B(unCStr("choice_value"));}),_1fV=new T(function(){return B(unCStr("observation2"));}),_1fW=new T(function(){return B(unCStr("observation1"));}),_1fX=new T(function(){return B(unCStr("block_number"));}),_1fY=function(_1fZ,_){var _1g0=E(_1fZ);switch(_1g0._){case 0:var _1g1=B(_1eM(_1fP,_)),_1g2=E(_1g1),_1g3=B(_1es(_1fX,E(_1g2.a),_)),_1g4=eval(E(_1ff)),_1g5=__app2(E(_1g4),E(E(_1g3).a),toJSStr(B(_cz(0,_1g0.a,_1))));return _1g2;case 1:var _1g6=B(_1fY(_1g0.a,_)),_1g7=B(_1fY(_1g0.b,_)),_1g8=B(_1eM(_1fQ,_)),_1g9=E(_1g8),_1ga=E(_1g9.a),_1gb=B(_1ex(_1fW,_1ga,_1g6,_)),_1gc=B(_1ex(_1fV,_1ga,_1g7,_));return _1g9;case 2:var _1gd=B(_1fY(_1g0.a,_)),_1ge=B(_1fY(_1g0.b,_)),_1gf=B(_1eM(_1fR,_)),_1gg=E(_1gf),_1gh=E(_1gg.a),_1gi=B(_1ex(_1fW,_1gh,_1gd,_)),_1gj=B(_1ex(_1fV,_1gh,_1ge,_));return _1gg;case 3:var _1gk=B(_1fY(_1g0.a,_)),_1gl=B(_1eM(_1fS,_)),_1gm=E(_1gl),_1gn=B(_1ex(_1eZ,E(_1gm.a),_1gk,_));return _1gm;case 4:var _1go=B(_1eM(_1fK,_)),_1gp=E(_1go),_1gq=E(_1gp.a),_1gr=B(_1es(_1fb,_1gq,_)),_1gs=eval(E(_1ff)),_1gt=__app2(E(_1gs),E(E(_1gr).a),toJSStr(B(_cz(0,_1g0.a,_1)))),_1gu=B(_1es(_1fT,_1gq,_)),_1gv=__app2(E(_1gs),E(E(_1gu).a),toJSStr(B(_cz(0,_1g0.b,_1)))),_1gw=B(_1es(_1fU,_1gq,_)),_1gx=__app2(E(_1gs),E(E(_1gw).a),toJSStr(B(_cz(0,_1g0.c,_1))));return _1gp;case 5:var _1gy=B(_1eM(_1fL,_)),_1gz=E(_1gy),_1gA=E(_1gz.a),_1gB=B(_1es(_1fb,_1gA,_)),_1gC=eval(E(_1ff)),_1gD=__app2(E(_1gC),E(E(_1gB).a),toJSStr(B(_cz(0,_1g0.a,_1)))),_1gE=B(_1es(_1fT,_1gA,_)),_1gF=__app2(E(_1gC),E(E(_1gE).a),toJSStr(B(_cz(0,_1g0.b,_1))));return _1gz;case 6:var _1gG=B(_1fg(_1g0.a,_)),_1gH=B(_1fg(_1g0.b,_)),_1gI=B(_1eM(_1fM,_)),_1gJ=E(_1gI),_1gK=E(_1gJ.a),_1gL=B(_1dz(_1fa,_1gK,_1gG,_)),_1gM=B(_1dz(_1f9,_1gK,_1gH,_));return _1gJ;case 7:return new F(function(){return _1eM(_1fN,_);});break;default:return new F(function(){return _1eM(_1fO,_);});}},_1gN=function(_1gO,_){var _1gP=E(_1gO);switch(_1gP._){case 0:return new F(function(){return _1eM(_1eW,_);});break;case 1:var _1gQ=B(_1gN(_1gP.f,_)),_1gR=B(_1gN(_1gP.g,_)),_1gS=B(_1fg(_1gP.c,_)),_1gT=B(_1eM(_1eF,_)),_1gU=E(_1gT),_1gV=E(_1gU.a),_1gW=B(_1es(_1eS,_1gV,_)),_1gX=eval(E(_1ff)),_1gY=__app2(E(_1gX),E(E(_1gW).a),toJSStr(B(_cz(0,_1gP.a,_1)))),_1gZ=B(_1es(_1eV,_1gV,_)),_1h0=__app2(E(_1gX),E(E(_1gZ).a),toJSStr(B(_cz(0,_1gP.b,_1)))),_1h1=B(_1dz(_1f3,_1gV,_1gS,_)),_1h2=B(_1es(_1eU,_1gV,_)),_1h3=__app2(E(_1gX),E(E(_1h2).a),toJSStr(B(_cz(0,_1gP.d,_1)))),_1h4=B(_1es(_1eT,_1gV,_)),_1h5=__app2(E(_1gX),E(E(_1h4).a),toJSStr(B(_cz(0,_1gP.e,_1)))),_1h6=B(_1dq(_1eY,_1gV,_1gQ,_)),_1h7=B(_1dq(_1eX,_1gV,_1gR,_));return _1gU;case 2:var _1h8=B(_1gN(_1gP.b,_)),_1h9=B(_1eM(_1eG,_)),_1ha=E(_1h9),_1hb=E(_1ha.a),_1hc=B(_1es(_1eS,_1hb,_)),_1hd=eval(E(_1ff)),_1he=__app2(E(_1hd),E(E(_1hc).a),toJSStr(B(_cz(0,_1gP.a,_1)))),_1hf=B(_1dq(_1f1,_1hb,_1h8,_));return _1ha;case 3:var _1hg=B(_1gN(_1gP.f,_)),_1hh=B(_1eM(_1eH,_)),_1hi=B(_1fg(_1gP.d,_)),_1hj=E(_1hh),_1hk=E(_1hj.a),_1hl=B(_1es(_1eR,_1hk,_)),_1hm=eval(E(_1ff)),_1hn=__app2(E(_1hm),E(E(_1hl).a),toJSStr(B(_cz(0,_1gP.a,_1)))),_1ho=B(_1es(_1eQ,_1hk,_)),_1hp=__app2(E(_1hm),E(E(_1ho).a),toJSStr(B(_cz(0,_1gP.b,_1)))),_1hq=B(_1es(_1f4,_1hk,_)),_1hr=__app2(E(_1hm),E(E(_1hq).a),toJSStr(B(_cz(0,_1gP.c,_1)))),_1hs=B(_1dz(_1f3,_1hk,_1hi,_)),_1ht=B(_1es(_1f2,_1hk,_)),_1hu=__app2(E(_1hm),E(E(_1ht).a),toJSStr(B(_cz(0,_1gP.e,_1)))),_1hv=B(_1dq(_1f1,_1hk,_1hg,_));return _1hj;case 4:var _1hw=B(_1gN(_1gP.a,_)),_1hx=B(_1gN(_1gP.b,_)),_1hy=B(_1eM(_1eI,_)),_1hz=E(_1hy),_1hA=E(_1hz.a),_1hB=B(_1dq(_1eY,_1hA,_1hw,_)),_1hC=B(_1dq(_1eX,_1hA,_1hx,_));return _1hz;case 5:var _1hD=B(_1fY(_1gP.a,_)),_1hE=B(_1gN(_1gP.b,_)),_1hF=B(_1gN(_1gP.c,_)),_1hG=B(_1eM(_1eJ,_)),_1hH=E(_1hG),_1hI=E(_1hH.a),_1hJ=B(_1ex(_1eZ,_1hI,_1hD,_)),_1hK=B(_1dq(_1eY,_1hI,_1hE,_)),_1hL=B(_1dq(_1eX,_1hI,_1hF,_));return _1hH;default:var _1hM=B(_1fY(_1gP.a,_)),_1hN=B(_1gN(_1gP.c,_)),_1hO=B(_1gN(_1gP.d,_)),_1hP=B(_1eM(_1eK,_)),_1hQ=E(_1hP),_1hR=E(_1hQ.a),_1hS=B(_1es(_1f0,_1hR,_)),_1hT=eval(E(_1ff)),_1hU=__app2(E(_1hT),E(E(_1hS).a),toJSStr(B(_cz(0,_1gP.b,_1)))),_1hV=B(_1ex(_1eZ,_1hR,_1hM,_)),_1hW=B(_1dq(_1eY,_1hR,_1hN,_)),_1hX=B(_1dq(_1eX,_1hR,_1hO,_));return _1hQ;}},_1hY=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_1hZ=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_1i0=new T(function(){return B(unCStr("base_contract"));}),_1i1=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_1i2=function(_1i3,_){var _1i4=__app0(E(_1hY)),_1i5=__app0(E(_1hZ)),_1i6=B(_106(B(_g4(_14q,_1i3))));if(!_1i6._){return E(_10e);}else{if(!E(_1i6.b)._){var _1i7=B(_1gN(_1i6.a,_)),_1i8=B(_1dq(_1i0,_1i5,_1i7,_)),_1i9=__app0(E(_1i1)),_1ia=eval(E(_Yo)),_1ib=__app1(E(_1ia),toJSStr(E(_14K))),_1ic=new T(function(){var _1id=B(_106(B(_g4(_yK,new T(function(){var _1ie=String(_1ib);return fromJSStr(_1ie);})))));if(!_1id._){return E(_eS);}else{if(!E(_1id.b)._){var _1if=E(_1id.a);return new T4(0,new T(function(){return B(_bH(_1if.a));}),new T(function(){return B(_8f(_1if.b));}),new T(function(){return B(_9V(_1if.c));}),new T(function(){return B(_4n(_1if.d));}));}else{return E(_eQ);}}});return new F(function(){return _14r(_1ic,_);});}else{return E(_10d);}}},_1ig=function(_){var _1ih=eval(E(_Yo)),_1ii=__app1(E(_1ih),toJSStr(E(_1ct)));return new F(function(){return _1i2(new T(function(){var _1ij=String(_1ii);return fromJSStr(_1ij);}),_);});},_1ik=new T(function(){return B(unCStr("contractOutput"));}),_1il=new T(function(){return B(unCStr("([], [], [], [])"));}),_1im=new T(function(){return B(unCStr("([], [])"));}),_1in=new T1(0,0),_1io=new T(function(){return B(_cz(0,_1in,_1));}),_1ip="(function (t, s) {document.getElementById(t).value = s})",_1iq=function(_1ir,_1is,_){var _1it=eval(E(_1ip)),_1iu=__app2(E(_1it),toJSStr(E(_1ir)),toJSStr(E(_1is)));return new F(function(){return _A6(_);});},_1iv=function(_){var _1iw=__app0(E(_1hY)),_1ix=B(_14M(_1ct,_1,_)),_1iy=B(_1iq(_Yr,_1io,_)),_1iz=B(_14M(_Yq,_1im,_)),_1iA=B(_14M(_14K,_1il,_));return new F(function(){return _14M(_1ik,_1,_);});},_1iB=new T1(0,1000),_1iC=new T1(2,_1iB),_1iD=new T1(0,3),_1iE=new T1(0,_1iD),_1iF=new T1(0,4),_1iG=new T1(0,_1iF),_1iH=new T2(1,_1iE,_1iG),_1iI=new T1(0,2),_1iJ=new T1(0,_1iI),_1iK=new T1(0,1),_1iL=new T1(0,_1iK),_1iM=new T2(1,_1iL,_1iJ),_1iN=new T2(1,_1iM,_1iH),_1iO=new T2(6,_1iN,_1iC),_1iP=new T1(0,20),_1iQ=new T1(0,5),_1iR=new T6(3,_1iI,_1iI,_1iQ,_1iJ,_1iP,_TR),_1iS=new T6(3,_1iK,_1iK,_1iQ,_1iL,_1iP,_TR),_1iT=new T2(4,_1iS,_1iR),_1iU=new T6(3,_1iD,_1iD,_1iQ,_1iE,_1iP,_TR),_1iV=new T6(3,_1iF,_1iF,_1iQ,_1iG,_1iP,_TR),_1iW=new T2(4,_1iU,_1iV),_1iX=new T2(4,_1iT,_1iW),_1iY=new T3(5,_1iO,_1iX,_TR),_1iZ=new T1(0,10),_1j0=new T4(6,_11a,_1iZ,_TR,_1iY),_1j1=new T1(0,_1j0),_1j2=new T2(1,_1j1,_1),_1j3=new T1(0,0),_1j4=new T1(2,_1j3),_1j5=new T3(3,_1iF,_1iF,_1j4),_1j6={_:1,a:_1iF,b:_1iF,c:_1j5,d:_1iZ,e:_1iP,f:_TR,g:_TR},_1j7=new T1(2,_1iK),_1j8=new T2(6,_1j5,_1j7),_1j9=new T2(5,_1iF,_1iF),_1ja=new T2(1,_1j9,_1j8),_1jb=new T4(6,_1ja,_1iZ,_1j6,_TR),_1jc=new T3(3,_1iD,_1iD,_1j4),_1jd={_:1,a:_1iD,b:_1iD,c:_1jc,d:_1iZ,e:_1iP,f:_TR,g:_TR},_1je=new T2(6,_1jc,_1j7),_1jf=new T2(5,_1iD,_1iD),_1jg=new T2(1,_1jf,_1je),_1jh=new T4(6,_1jg,_1iZ,_1jd,_TR),_1ji=new T2(4,_1jh,_1jb),_1jj=new T3(3,_1iI,_1iI,_1j4),_1jk={_:1,a:_1iI,b:_1iI,c:_1jj,d:_1iZ,e:_1iP,f:_TR,g:_TR},_1jl=new T2(6,_1jj,_1j7),_1jm=new T2(5,_1iI,_1iI),_1jn=new T2(1,_1jm,_1jl),_1jo=new T4(6,_1jn,_1iZ,_1jk,_TR),_1jp=new T3(3,_1iK,_1iK,_1j4),_1jq={_:1,a:_1iK,b:_1iK,c:_1jp,d:_1iZ,e:_1iP,f:_TR,g:_TR},_1jr=new T2(6,_1jp,_1j7),_1js=new T2(5,_1iK,_1iK),_1jt=new T2(1,_1js,_1jr),_1ju=new T4(6,_1jt,_1iZ,_1jq,_TR),_1jv=new T2(4,_1ju,_1jo),_1jw=new T2(4,_1jv,_1ji),_1jx=new T1(0,_1jw),_1jy=new T2(1,_1jx,_1j2),_1jz=new T(function(){return B(_1bJ(_1bD,_1ay,_1jy));}),_1jA=function(_){var _1jB=B(_1iv(_)),_1jC=B(_14M(_1ct,_1jz,_)),_1jD=eval(E(_Yo)),_1jE=__app1(E(_1jD),toJSStr(E(_1ct)));return new F(function(){return _1i2(new T(function(){var _1jF=String(_1jE);return fromJSStr(_1jF);}),_);});},_1jG=new T1(0,1),_1jH=new T1(3,_1jG),_1jI=new T1(6,_1jG),_1jJ=new T1(0,100),_1jK=new T1(2,_1jJ),_1jL=new T1(2,_1jK),_1jM=new T1(0,10),_1jN=new T1(6,_1jM),_1jO=new T1(0,200),_1jP=new T1(6,_1jO),_1jQ=new T1(0,20),_1jR=new T1(2,_1jQ),_1jS=new T1(0,2),_1jT=new T2(2,_1jG,_TR),_1jU=new T2(2,_1jS,_TR),_1jV=new T2(4,_1jT,_1jU),_1jW=new T6(3,_1jG,_1jS,_1jG,_1jR,_1jO,_1jV),_1jX=new T2(5,_1jG,_1jG),_1jY=new T4(6,_1jX,_1jJ,_1jV,_1jW),_1jZ={_:1,a:_1jS,b:_1jS,c:_1jR,d:_1jQ,e:_1jO,f:_1jY,g:_1jT},_1k0=new T1(0,_1jZ),_1k1=new T1(0,_TR),_1k2=new T2(1,_1k1,_1),_1k3=new T2(1,_1k0,_1k2),_1k4=new T2(1,_1jP,_1k3),_1k5=new T2(1,_1jN,_1k4),_1k6=new T2(1,_1jL,_1k5),_1k7=new T2(1,_1jI,_1k6),_1k8=new T2(1,_1jH,_1k7),_1k9=new T(function(){return B(_1bJ(_1bD,_1aC,_1k8));}),_1ka=function(_){var _1kb=B(_1iv(_)),_1kc=B(_14M(_1ct,_1k9,_)),_1kd=eval(E(_Yo)),_1ke=__app1(E(_1kd),toJSStr(E(_1ct)));return new F(function(){return _1i2(new T(function(){var _1kf=String(_1ke);return fromJSStr(_1kf);}),_);});},_1kg=new T1(0,1),_1kh=new T1(3,_1kg),_1ki=new T1(6,_1kg),_1kj=new T1(0,450),_1kk=new T1(2,_1kj),_1kl=new T1(2,_1kk),_1km=new T1(0,10),_1kn=new T1(6,_1km),_1ko=new T1(0,100),_1kp=new T1(6,_1ko),_1kq=new T1(0,90),_1kr=new T1(0,3),_1ks=new T1(0,0),_1kt=new T3(4,_1kr,_1kr,_1ks),_1ku=new T1(0,2),_1kv=new T3(4,_1ku,_1ku,_1ks),_1kw=new T2(1,_1kv,_1kt),_1kx=new T2(2,_1kv,_1kt),_1ky=new T3(4,_1kg,_1kg,_1ks),_1kz=new T2(1,_1ky,_1kx),_1kA=new T2(2,_1kz,_1kw),_1kB=new T3(4,_1kr,_1kr,_1kg),_1kC=new T3(4,_1ku,_1ku,_1kg),_1kD=new T2(1,_1kC,_1kB),_1kE=new T2(2,_1kC,_1kB),_1kF=new T3(4,_1kg,_1kg,_1kg),_1kG=new T2(1,_1kF,_1kE),_1kH=new T2(2,_1kG,_1kD),_1kI=new T2(2,_1kA,_1kH),_1kJ=new T2(2,_1kg,_TR),_1kK=new T1(0,_1kg),_1kL=new T6(3,_1kg,_1kg,_1ku,_1kK,_1ko,_1kJ),_1kM=new T3(5,_1kH,_1kL,_1kJ),_1kN=new T4(6,_1kI,_1kq,_1kM,_1kJ),_1kO=new T1(0,_1kN),_1kP=new T2(1,_1kO,_1k2),_1kQ=new T2(1,_1kp,_1kP),_1kR=new T2(1,_1kn,_1kQ),_1kS=new T2(1,_1kl,_1kR),_1kT=new T2(1,_1ki,_1kS),_1kU=new T2(1,_1kh,_1kT),_1kV=new T(function(){return B(_1bJ(_1bD,_1aC,_1kU));}),_1kW=function(_){var _1kX=B(_1iv(_)),_1kY=B(_14M(_1ct,_1kV,_)),_1kZ=eval(E(_Yo)),_1l0=__app1(E(_1kZ),toJSStr(E(_1ct)));return new F(function(){return _1i2(new T(function(){var _1l1=String(_1l0);return fromJSStr(_1l1);}),_);});},_1l2=new T(function(){return B(unCStr("NotRedeemed "));}),_1l3=function(_1l4,_1l5,_1l6){var _1l7=E(_1l5);switch(_1l7._){case 0:var _1l8=function(_1l9){return new F(function(){return _cz(11,_1l7.a,new T2(1,_cJ,new T(function(){return B(_cz(11,_1l7.b,_1l9));})));});};if(E(_1l4)<11){return new F(function(){return _ce(_1l2,new T(function(){return B(_1l8(_1l6));},1));});}else{var _1la=new T(function(){return B(_ce(_1l2,new T(function(){return B(_1l8(new T2(1,_cw,_1l6)));},1)));});return new T2(1,_cx,_1la);}break;case 1:return new F(function(){return _ce(_YN,_1l6);});break;default:return new F(function(){return _ce(_YS,_1l6);});}},_1lb=0,_1lc=function(_1ld,_1le,_1lf){var _1lg=new T(function(){var _1lh=function(_1li){var _1lj=E(_1le),_1lk=new T(function(){return B(A3(_dr,_c9,new T2(1,function(_1ll){return new F(function(){return _cz(0,_1lj.a,_1ll);});},new T2(1,function(_vz){return new F(function(){return _1l3(_1lb,_1lj.b,_vz);});},_1)),new T2(1,_cw,_1li)));});return new T2(1,_cx,_1lk);};return B(A3(_dr,_c9,new T2(1,function(_1lm){return new F(function(){return _cE(0,_1ld,_1lm);});},new T2(1,_1lh,_1)),new T2(1,_cw,_1lf)));});return new T2(0,_cx,_1lg);},_1ln=function(_1lo,_1lp){var _1lq=E(_1lo),_1lr=B(_1lc(_1lq.a,_1lq.b,_1lp));return new T2(1,_1lr.a,_1lr.b);},_1ls=function(_1lt,_1lu){return new F(function(){return _dQ(_1ln,_1lt,_1lu);});},_1lv=new T(function(){return B(unCStr("ChoiceMade "));}),_1lw=new T(function(){return B(unCStr("DuplicateRedeem "));}),_1lx=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_1ly=new T(function(){return B(unCStr("CommitRedeemed "));}),_1lz=new T(function(){return B(unCStr("SuccessfulCommit "));}),_1lA=new T(function(){return B(unCStr("FailedPay "));}),_1lB=new T(function(){return B(unCStr("ExpiredPay "));}),_1lC=new T(function(){return B(unCStr("SuccessfulPay "));}),_1lD=function(_1lE,_1lF,_1lG){var _1lH=E(_1lF);switch(_1lH._){case 0:var _1lI=function(_1lJ){var _1lK=new T(function(){var _1lL=new T(function(){return B(_cz(11,_1lH.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lH.d,_1lJ));}))));});return B(_cz(11,_1lH.b,new T2(1,_cJ,_1lL)));});return new F(function(){return _dg(11,_1lH.a,new T2(1,_cJ,_1lK));});};if(_1lE<11){return new F(function(){return _ce(_1lC,new T(function(){return B(_1lI(_1lG));},1));});}else{var _1lM=new T(function(){return B(_ce(_1lC,new T(function(){return B(_1lI(new T2(1,_cw,_1lG)));},1)));});return new T2(1,_cx,_1lM);}break;case 1:var _1lN=function(_1lO){var _1lP=new T(function(){var _1lQ=new T(function(){return B(_cz(11,_1lH.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lH.d,_1lO));}))));});return B(_cz(11,_1lH.b,new T2(1,_cJ,_1lQ)));});return new F(function(){return _dg(11,_1lH.a,new T2(1,_cJ,_1lP));});};if(_1lE<11){return new F(function(){return _ce(_1lB,new T(function(){return B(_1lN(_1lG));},1));});}else{var _1lR=new T(function(){return B(_ce(_1lB,new T(function(){return B(_1lN(new T2(1,_cw,_1lG)));},1)));});return new T2(1,_cx,_1lR);}break;case 2:var _1lS=function(_1lT){var _1lU=new T(function(){var _1lV=new T(function(){return B(_cz(11,_1lH.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lH.d,_1lT));}))));});return B(_cz(11,_1lH.b,new T2(1,_cJ,_1lV)));});return new F(function(){return _dg(11,_1lH.a,new T2(1,_cJ,_1lU));});};if(_1lE<11){return new F(function(){return _ce(_1lA,new T(function(){return B(_1lS(_1lG));},1));});}else{var _1lW=new T(function(){return B(_ce(_1lA,new T(function(){return B(_1lS(new T2(1,_cw,_1lG)));},1)));});return new T2(1,_cx,_1lW);}break;case 3:var _1lX=function(_1lY){var _1lZ=new T(function(){var _1m0=new T(function(){return B(_cz(11,_1lH.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lH.d,_1lY));}))));});return B(_cz(11,_1lH.b,new T2(1,_cJ,_1m0)));});return new F(function(){return _cE(11,_1lH.a,new T2(1,_cJ,_1lZ));});};if(_1lE<11){return new F(function(){return _ce(_1lz,new T(function(){return B(_1lX(_1lG));},1));});}else{var _1m1=new T(function(){return B(_ce(_1lz,new T(function(){return B(_1lX(new T2(1,_cw,_1lG)));},1)));});return new T2(1,_cx,_1m1);}break;case 4:var _1m2=function(_1m3){var _1m4=new T(function(){var _1m5=new T(function(){return B(_cz(11,_1lH.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lH.c,_1m3));}))));});return B(_cE(11,_1lH.a,new T2(1,_cJ,_1m5)));},1);return new F(function(){return _ce(_1ly,_1m4);});};if(_1lE<11){return new F(function(){return _1m2(_1lG);});}else{return new T2(1,_cx,new T(function(){return B(_1m2(new T2(1,_cw,_1lG)));}));}break;case 5:var _1m6=function(_1m7){var _1m8=new T(function(){var _1m9=new T(function(){return B(_cz(11,_1lH.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lH.c,_1m7));}))));});return B(_cE(11,_1lH.a,new T2(1,_cJ,_1m9)));},1);return new F(function(){return _ce(_1lx,_1m8);});};if(_1lE<11){return new F(function(){return _1m6(_1lG);});}else{return new T2(1,_cx,new T(function(){return B(_1m6(new T2(1,_cw,_1lG)));}));}break;case 6:var _1ma=function(_1mb){return new F(function(){return _cE(11,_1lH.a,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lH.b,_1mb));})));});};if(_1lE<11){return new F(function(){return _ce(_1lw,new T(function(){return B(_1ma(_1lG));},1));});}else{var _1mc=new T(function(){return B(_ce(_1lw,new T(function(){return B(_1ma(new T2(1,_cw,_1lG)));},1)));});return new T2(1,_cx,_1mc);}break;default:var _1md=function(_1me){var _1mf=new T(function(){var _1mg=new T(function(){return B(_cz(11,_1lH.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lH.c,_1me));}))));});return B(_e5(11,_1lH.a,new T2(1,_cJ,_1mg)));},1);return new F(function(){return _ce(_1lv,_1mf);});};if(_1lE<11){return new F(function(){return _1md(_1lG);});}else{return new T2(1,_cx,new T(function(){return B(_1md(new T2(1,_cw,_1lG)));}));}}},_1mh=new T(function(){return eval("(function (x) { alert(x) ; })");}),_1mi=function(_1mj,_1mk){var _1ml=E(_1mj),_1mm=E(_1mk);if(!_1mm._){var _1mn=_1mm.b,_1mo=_1mm.c,_1mp=_1mm.d;switch(B(_2(_1ml,_1mn))){case 0:return new F(function(){return _5q(_1mn,B(_1mi(_1ml,_1mo)),_1mp);});break;case 1:return new T4(0,_1mm.a,E(_1ml),E(_1mo),E(_1mp));default:return new F(function(){return _4G(_1mn,_1mo,B(_1mi(_1ml,_1mp)));});}}else{return new T4(0,1,E(_1ml),E(_4B),E(_4B));}},_1mq=function(_1mr,_1ms){while(1){var _1mt=E(_1mr),_1mu=E(_1ms);if(!_1mu._){switch(B(_2(_1mt,_1mu.b))){case 0:_1mr=_1mt;_1ms=_1mu.c;continue;case 1:return true;default:_1mr=_1mt;_1ms=_1mu.d;continue;}}else{return false;}}},_1mv=function(_1mw,_1mx,_1my){var _1mz=function(_1mA,_1mB){while(1){var _1mC=E(_1mA),_1mD=E(_1mB);if(!_1mD._){switch(B(A3(_I1,_1mw,_1mC,_1mD.b))){case 0:_1mA=_1mC;_1mB=_1mD.c;continue;case 1:return true;default:_1mA=_1mC;_1mB=_1mD.d;continue;}}else{return false;}}};return new F(function(){return _1mz(_1mx,_1my);});},_1mE=function(_1mF,_1mG,_1mH,_1mI){var _1mJ=E(_1mI);if(!_1mJ._){var _1mK=new T(function(){var _1mL=B(_1mE(_1mJ.a,_1mJ.b,_1mJ.c,_1mJ.d));return new T2(0,_1mL.a,_1mL.b);});return new T2(0,new T(function(){return E(E(_1mK).a);}),new T(function(){return B(_5q(_1mG,_1mH,E(_1mK).b));}));}else{return new T2(0,_1mG,_1mH);}},_1mM=function(_1mN,_1mO,_1mP,_1mQ){var _1mR=E(_1mP);if(!_1mR._){var _1mS=new T(function(){var _1mT=B(_1mM(_1mR.a,_1mR.b,_1mR.c,_1mR.d));return new T2(0,_1mT.a,_1mT.b);});return new T2(0,new T(function(){return E(E(_1mS).a);}),new T(function(){return B(_4G(_1mO,E(_1mS).b,_1mQ));}));}else{return new T2(0,_1mO,_1mQ);}},_1mU=function(_1mV,_1mW){var _1mX=E(_1mV);if(!_1mX._){var _1mY=_1mX.a,_1mZ=E(_1mW);if(!_1mZ._){var _1n0=_1mZ.a;if(_1mY<=_1n0){var _1n1=B(_1mM(_1n0,_1mZ.b,_1mZ.c,_1mZ.d));return new F(function(){return _5q(_1n1.a,_1mX,_1n1.b);});}else{var _1n2=B(_1mE(_1mY,_1mX.b,_1mX.c,_1mX.d));return new F(function(){return _4G(_1n2.a,_1n2.b,_1mZ);});}}else{return E(_1mX);}}else{return E(_1mW);}},_1n3=function(_1n4,_1n5,_1n6,_1n7,_1n8){var _1n9=E(_1n4);if(!_1n9._){var _1na=_1n9.a,_1nb=_1n9.b,_1nc=_1n9.c,_1nd=_1n9.d;if((imul(3,_1na)|0)>=_1n5){if((imul(3,_1n5)|0)>=_1na){return new F(function(){return _1mU(_1n9,new T4(0,_1n5,E(_1n6),E(_1n7),E(_1n8)));});}else{return new F(function(){return _4G(_1nb,_1nc,B(_1n3(_1nd,_1n5,_1n6,_1n7,_1n8)));});}}else{return new F(function(){return _5q(_1n6,B(_1ne(_1na,_1nb,_1nc,_1nd,_1n7)),_1n8);});}}else{return new T4(0,_1n5,E(_1n6),E(_1n7),E(_1n8));}},_1ne=function(_1nf,_1ng,_1nh,_1ni,_1nj){var _1nk=E(_1nj);if(!_1nk._){var _1nl=_1nk.a,_1nm=_1nk.b,_1nn=_1nk.c,_1no=_1nk.d;if((imul(3,_1nf)|0)>=_1nl){if((imul(3,_1nl)|0)>=_1nf){return new F(function(){return _1mU(new T4(0,_1nf,E(_1ng),E(_1nh),E(_1ni)),_1nk);});}else{return new F(function(){return _4G(_1ng,_1nh,B(_1n3(_1ni,_1nl,_1nm,_1nn,_1no)));});}}else{return new F(function(){return _5q(_1nm,B(_1ne(_1nf,_1ng,_1nh,_1ni,_1nn)),_1no);});}}else{return new T4(0,_1nf,E(_1ng),E(_1nh),E(_1ni));}},_1np=function(_1nq,_1nr){var _1ns=E(_1nq);if(!_1ns._){var _1nt=_1ns.a,_1nu=_1ns.b,_1nv=_1ns.c,_1nw=_1ns.d,_1nx=E(_1nr);if(!_1nx._){var _1ny=_1nx.a,_1nz=_1nx.b,_1nA=_1nx.c,_1nB=_1nx.d;if((imul(3,_1nt)|0)>=_1ny){if((imul(3,_1ny)|0)>=_1nt){return new F(function(){return _1mU(_1ns,_1nx);});}else{return new F(function(){return _4G(_1nu,_1nv,B(_1n3(_1nw,_1ny,_1nz,_1nA,_1nB)));});}}else{return new F(function(){return _5q(_1nz,B(_1ne(_1nt,_1nu,_1nv,_1nw,_1nA)),_1nB);});}}else{return E(_1ns);}}else{return E(_1nr);}},_1nC=function(_1nD,_1nE,_1nF,_1nG,_1nH){var _1nI=E(_1nH);if(!_1nI._){var _1nJ=E(_1nG);if(!_1nJ._){var _1nK=_1nJ.b,_1nL=new T1(1,E(_1nK)),_1nM=B(_1nC(_1nD,_1nL,_1nF,_1nJ.d,B(_Kc(_1nD,_1nL,_1nF,_1nI)))),_1nN=B(_1nC(_1nD,_1nE,_1nL,_1nJ.c,B(_Kc(_1nD,_1nE,_1nL,_1nI))));if(!B(_1mv(_1nD,_1nK,_1nI))){return new F(function(){return _1np(_1nN,_1nM);});}else{return new F(function(){return _6C(_1nK,_1nN,_1nM);});}}else{return new T0(1);}}else{return new T0(1);}},_1nO=function(_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ){var _1o0=new T1(1,E(_1nT)),_1o1=B(_1nC(_1nP,_1o0,_1nR,_1nV,B(_Kc(_1nP,_1o0,_1nR,new T4(0,_1nW,E(_1nX),E(_1nY),E(_1nZ)))))),_1o2=B(_1nC(_1nP,_1nQ,_1o0,_1nU,B(_Kc(_1nP,_1nQ,_1o0,new T4(0,_1nW,E(_1nX),E(_1nY),E(_1nZ))))));if(!B(_1mv(_1nP,_1nT,new T4(0,_1nW,E(_1nX),E(_1nY),E(_1nZ))))){return new F(function(){return _1np(_1o2,_1o1);});}else{return new F(function(){return _6C(_1nT,_1o2,_1o1);});}},_1o3=function(_1o4,_1o5,_1o6,_1o7){var _1o8=function(_1o9){var _1oa=E(_1o5);if(!_1oa._){var _1ob=E(_1o7);return (_1ob._==0)?(B(_1nO(_Gx,_I0,_I0,_1oa.a,_1oa.b,_1oa.c,_1oa.d,_1ob.a,_1ob.b,_1ob.c,_1ob.d))._==0)?false:true:true;}else{return true;}},_1oc=E(_1o4);if(!_1oc._){var _1od=E(_1o6);if(!_1od._){if(!B(_1nO(_ON,_I0,_I0,_1oc.a,_1oc.b,_1oc.c,_1oc.d,_1od.a,_1od.b,_1od.c,_1od.d))._){return false;}else{return new F(function(){return _1o8(_);});}}else{return new F(function(){return _1o8(_);});}}else{return new F(function(){return _1o8(_);});}},_1oe=function(_1of,_1og,_1oh,_1oi){return new T2(0,new T(function(){var _1oj=E(_1of);if(!_1oj._){var _1ok=E(_1oh);if(!_1ok._){return B(_KO(_ON,_I0,_I0,_1oj.a,_1oj.b,_1oj.c,_1oj.d,_1ok.a,_1ok.b,_1ok.c,_1ok.d));}else{return E(_1oj);}}else{return E(_1oh);}}),new T(function(){var _1ol=E(_1og);if(!_1ol._){var _1om=E(_1oi);if(!_1om._){return B(_KO(_Gx,_I0,_I0,_1ol.a,_1ol.b,_1ol.c,_1ol.d,_1om.a,_1om.b,_1om.c,_1om.d));}else{return E(_1ol);}}else{return E(_1oi);}}));},_1on=function(_1oo,_1op,_1oq){var _1or=E(_1oq);if(!_1or._){var _1os=_1or.c,_1ot=_1or.d,_1ou=E(_1or.b);switch(B(_2(_1oo,_1ou.a))){case 0:return new F(function(){return _5q(_1ou,B(_1on(_1oo,_1op,_1os)),_1ot);});break;case 1:switch(B(_2(_1op,_1ou.b))){case 0:return new F(function(){return _5q(_1ou,B(_1on(_1oo,_1op,_1os)),_1ot);});break;case 1:return new T4(0,_1or.a,E(new T2(0,_1oo,_1op)),E(_1os),E(_1ot));default:return new F(function(){return _4G(_1ou,_1os,B(_1on(_1oo,_1op,_1ot)));});}break;default:return new F(function(){return _4G(_1ou,_1os,B(_1on(_1oo,_1op,_1ot)));});}}else{return new T4(0,1,E(new T2(0,_1oo,_1op)),E(_4B),E(_4B));}},_1ov=function(_1ow,_1ox,_1oy){while(1){var _1oz=E(_1oy);if(!_1oz._){var _1oA=_1oz.c,_1oB=_1oz.d,_1oC=E(_1oz.b);switch(B(_2(_1ow,_1oC.a))){case 0:_1oy=_1oA;continue;case 1:switch(B(_2(_1ox,_1oC.b))){case 0:_1oy=_1oA;continue;case 1:return true;default:_1oy=_1oB;continue;}break;default:_1oy=_1oB;continue;}}else{return false;}}},_1oD=function(_1oE,_1oF,_1oG){var _1oH=E(_1oG);if(!_1oH._){return __Z;}else{var _1oI=E(_1oH.a),_1oJ=_1oI.b;return (!B(_1ov(_1oE,_1oF,_1oJ)))?new T1(1,new T2(0,_1oI.a,new T(function(){return B(_1on(_1oE,_1oF,_1oJ));}))):__Z;}},_1oK=function(_1oL,_1oM){var _1oN=E(_1oL);if(!_1oN._){return __Z;}else{var _1oO=E(_1oM);if(!_1oO._){return __Z;}else{var _1oP=E(_1oN.a),_1oQ=_1oP.a,_1oR=_1oP.b,_1oS=E(_1oO.a),_1oT=_1oS.a,_1oU=_1oS.b;return (!B(_1o3(_1oQ,_1oR,_1oT,_1oU)))?__Z:new T1(1,new T(function(){var _1oV=B(_1oe(_1oQ,_1oR,_1oT,_1oU));return new T2(0,_1oV.a,_1oV.b);}));}}},_1oW=new T2(0,_4B,_4B),_1oX=new T1(1,_1oW),_1oY=function(_1oZ){while(1){var _1p0=B((function(_1p1){var _1p2=E(_1p1);switch(_1p2._){case 0:return E(_1oX);case 1:var _1p3=_1p2.a,_1p4=B(_1oY(_1p2.f));if(!_1p4._){return __Z;}else{var _1p5=B(_1oY(_1p2.g));if(!_1p5._){return __Z;}else{var _1p6=E(_1p4.a),_1p7=_1p6.a,_1p8=_1p6.b,_1p9=E(_1p5.a),_1pa=_1p9.a,_1pb=_1p9.b;if(!B(_1o3(_1p7,_1p8,_1pa,_1pb))){return __Z;}else{var _1pc=B(_1oe(_1p7,_1p8,_1pa,_1pb)),_1pd=_1pc.a;return (!B(_1mq(_1p3,_1pd)))?new T1(1,new T2(0,new T(function(){return B(_1mi(_1p3,_1pd));}),_1pc.b)):__Z;}}}break;case 2:_1oZ=_1p2.b;return __continue;case 3:return new F(function(){return _1oD(_1p2.a,_1p2.c,B(_1oY(_1p2.f)));});break;case 4:return new F(function(){return _1oK(B(_1oY(_1p2.a)),new T(function(){return B(_1oY(_1p2.b));},1));});break;case 5:return new F(function(){return _1oK(B(_1oY(_1p2.b)),new T(function(){return B(_1oY(_1p2.c));},1));});break;default:return new F(function(){return _1oK(B(_1oY(_1p2.c)),new T(function(){return B(_1oY(_1p2.d));},1));});}})(_1oZ));if(_1p0!=__continue){return _1p0;}}},_1pe=new T(function(){return B(unCStr("Badly formed contract: Identifiers are not unique!"));}),_1pf=new T1(0,1),_1pg=new T(function(){return B(unAppCStr("[]",_1));}),_1ph=new T2(1,_dO,_1),_1pi=function(_1pj){var _1pk=E(_1pj);if(!_1pk._){return E(_1ph);}else{var _1pl=new T(function(){return B(_1lD(0,_1pk.a,new T(function(){return B(_1pi(_1pk.b));})));});return new T2(1,_c8,_1pl);}},_1pm=function(_){var _1pn=E(_14K),_1po=toJSStr(_1pn),_1pp=eval(E(_Yo)),_1pq=_1pp,_1pr=__app1(E(_1pq),_1po),_1ps=E(_Yq),_1pt=__app1(E(_1pq),toJSStr(_1ps)),_1pu=__app0(E(_Yp)),_1pv=new T(function(){var _1pw=B(_106(B(_g4(_14q,new T(function(){var _1px=String(_1pu);return fromJSStr(_1px);})))));if(!_1pw._){return E(_10e);}else{if(!E(_1pw.b)._){return E(_1pw.a);}else{return E(_10d);}}}),_1py=E(_Yr),_1pz=eval(E(_Yw)),_1pA=__app1(E(_1pz),toJSStr(_1py)),_1pB=new T(function(){var _1pC=B(_106(B(_g4(_Yv,new T(function(){var _1pD=String(_1pA);return fromJSStr(_1pD);})))));if(!_1pC._){return E(_Yu);}else{if(!E(_1pC.b)._){return E(_1pC.a);}else{return E(_Yt);}}});if(!B(_1oY(_1pv))._){var _1pE=__app1(E(_1mh),toJSStr(_1pe));return new F(function(){return _A6(_);});}else{var _1pF=new T(function(){var _1pG=B(_106(B(_g4(_103,new T(function(){var _1pH=String(_1pt);return fromJSStr(_1pH);})))));if(!_1pG._){return E(_Yy);}else{if(!E(_1pG.b)._){var _1pI=E(_1pG.a);return new T2(0,new T(function(){return B(_zV(_1pI.a));}),new T(function(){return B(_4n(_1pI.b));}));}else{return E(_Yx);}}}),_1pJ=new T(function(){var _1pK=B(_106(B(_g4(_yK,new T(function(){var _1pL=String(_1pr);return fromJSStr(_1pL);})))));if(!_1pK._){return E(_eS);}else{if(!E(_1pK.b)._){var _1pM=E(_1pK.a);return new T4(0,new T(function(){return B(_bH(_1pM.a));}),new T(function(){return B(_8f(_1pM.b));}),new T(function(){return B(_9V(_1pM.c));}),new T(function(){return B(_4n(_1pM.d));}));}else{return E(_eQ);}}}),_1pN=B(_XH(_1pJ,_1pF,_1pv,new T2(0,_104,_1pB))),_1pO=function(_,_1pP){var _1pQ=function(_,_1pR){var _1pS=E(_1pN.a),_1pT=new T(function(){var _1pU=new T(function(){return B(_c1(_1,_1pS.b));}),_1pV=new T(function(){return B(_c1(_1,_1pS.a));});return B(A3(_dr,_c9,new T2(1,function(_1pW){return new F(function(){return _1ls(_1pV,_1pW);});},new T2(1,function(_1pX){return new F(function(){return _er(_1pU,_1pX);});},_1)),_eu));}),_1pY=B(_14M(_1ps,new T2(1,_cx,_1pT),_)),_1pZ=B(_14M(_1pn,_1il,_)),_1q0=B(_1iq(_1py,B(_cz(0,B(_ji(_1pB,_1pf)),_1)),_)),_1q1=__app1(E(_1pq),toJSStr(E(_1ct))),_1q2=B(_1i2(new T(function(){var _1q3=String(_1q1);return fromJSStr(_1q3);}),_)),_1q4=__app1(E(_1pq),_1po),_1q5=new T(function(){var _1q6=B(_106(B(_g4(_yK,new T(function(){var _1q7=String(_1q4);return fromJSStr(_1q7);})))));if(!_1q6._){return E(_eS);}else{if(!E(_1q6.b)._){var _1q8=E(_1q6.a);return new T4(0,new T(function(){return B(_bH(_1q8.a));}),new T(function(){return B(_8f(_1q8.b));}),new T(function(){return B(_9V(_1q8.c));}),new T(function(){return B(_4n(_1q8.d));}));}else{return E(_eQ);}}});return new F(function(){return _14r(_1q5,_);});},_1q9=E(_1pN.b);switch(_1q9._){case 0:var _1qa=B(_14M(_1ct,_1co,_));return new F(function(){return _1pQ(_,_1qa);});break;case 1:var _1qb=B(_14M(_1ct,B(_1bJ(_1bD,_1aC,new T2(1,new T1(3,_1q9.a),new T2(1,new T1(6,_1q9.b),new T2(1,new T1(2,_1q9.c),new T2(1,new T1(6,_1q9.d),new T2(1,new T1(6,_1q9.e),new T2(1,new T1(0,_1q9.f),new T2(1,new T1(0,_1q9.g),_1))))))))),_));return new F(function(){return _1pQ(_,_1qb);});break;case 2:var _1qc=B(_14M(_1ct,B(_1bJ(_1bD,_1aB,new T2(1,new T1(3,_1q9.a),new T2(1,new T1(0,_1q9.b),_1)))),_));return new F(function(){return _1pQ(_,_1qc);});break;case 3:var _1qd=B(_14M(_1ct,B(_1bJ(_1bD,_1aA,new T2(1,new T1(5,_1q9.a),new T2(1,new T1(6,_1q9.b),new T2(1,new T1(6,_1q9.c),new T2(1,new T1(2,_1q9.d),new T2(1,new T1(6,_1q9.e),new T2(1,new T1(0,_1q9.f),_1)))))))),_));return new F(function(){return _1pQ(_,_1qd);});break;case 4:var _1qe=B(_14M(_1ct,B(_1bJ(_1bD,_1ay,new T2(1,new T1(0,_1q9.a),new T2(1,new T1(0,_1q9.b),_1)))),_));return new F(function(){return _1pQ(_,_1qe);});break;case 5:var _1qf=B(_14M(_1ct,B(_1bJ(_1bD,_1ax,new T2(1,new T1(1,_1q9.a),new T2(1,new T1(0,_1q9.b),new T2(1,new T1(0,_1q9.c),_1))))),_));return new F(function(){return _1pQ(_,_1qf);});break;default:var _1qg=B(_14M(_1ct,B(_1bJ(_1bD,_1aw,new T2(1,new T1(1,_1q9.a),new T2(1,new T1(6,_1q9.b),new T2(1,new T1(0,_1q9.c),new T2(1,new T1(0,_1q9.d),_1)))))),_));return new F(function(){return _1pQ(_,_1qg);});}},_1qh=E(_1pN.c);if(!_1qh._){var _1qi=B(_14M(_1ik,_1pg,_));return new F(function(){return _1pO(_,_1qi);});}else{var _1qj=new T(function(){return B(_1lD(0,_1qh.a,new T(function(){return B(_1pi(_1qh.b));})));}),_1qk=B(_14M(_1ik,new T2(1,_dP,_1qj),_));return new F(function(){return _1pO(_,_1qk);});}}},_1ql=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qm=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qn=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qo=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qp=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qq=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qr=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qs=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qt=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qu=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qv=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qw=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qx=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qy=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qz=function(_){return new F(function(){return __jsNull();});},_1qA=function(_1qB){var _1qC=B(A1(_1qB,_));return E(_1qC);},_1qD=new T(function(){return B(_1qA(_1qz));}),_1qE=new T(function(){return E(_1qD);}),_1qF=function(_){var _1qG=eval(E(_Yo)),_1qH=__app1(E(_1qG),toJSStr(E(_14K))),_1qI=new T(function(){var _1qJ=B(_106(B(_g4(_yK,new T(function(){var _1qK=String(_1qH);return fromJSStr(_1qK);})))));if(!_1qJ._){return E(_eS);}else{if(!E(_1qJ.b)._){var _1qL=E(_1qJ.a);return new T4(0,new T(function(){return B(_bH(_1qL.a));}),new T(function(){return B(_8f(_1qL.b));}),new T(function(){return B(_9V(_1qL.c));}),new T(function(){return B(_4n(_1qL.d));}));}else{return E(_eQ);}}});return new F(function(){return _14r(_1qI,_);});},_1qM=function(_){var _1qN=eval(E(_Yo)),_1qO=__app1(E(_1qN),toJSStr(E(_1ct))),_1qP=B(_1i2(new T(function(){var _1qQ=String(_1qO);return fromJSStr(_1qQ);}),_)),_1qR=__createJSFunc(0,function(_){var _1qS=B(_1iv(_));return _1qE;}),_1qT=__app2(E(_1qv),"clear_workspace",_1qR),_1qU=__createJSFunc(0,function(_){var _1qV=B(_1cu(_));return _1qE;}),_1qW=__app2(E(_1qu),"b2c",_1qU),_1qX=__createJSFunc(0,function(_){var _1qY=B(_1ig(_));return _1qE;}),_1qZ=__app2(E(_1qt),"c2b",_1qX),_1r0=function(_1r1){var _1r2=new T(function(){var _1r3=Number(E(_1r1));return jsTrunc(_1r3);}),_1r4=function(_1r5){var _1r6=new T(function(){var _1r7=Number(E(_1r5));return jsTrunc(_1r7);}),_1r8=function(_1r9){var _1ra=new T(function(){var _1rb=Number(E(_1r9));return jsTrunc(_1rb);}),_1rc=function(_1rd,_){var _1re=B(_15C(_1r2,_1r6,_1ra,new T(function(){var _1rf=Number(E(_1rd));return jsTrunc(_1rf);},1),_));return _1qE;};return E(_1rc);};return E(_1r8);};return E(_1r4);},_1rg=__createJSFunc(5,E(_1r0)),_1rh=__app2(E(_1qs),"commit",_1rg),_1ri=function(_1rj){var _1rk=new T(function(){var _1rl=Number(E(_1rj));return jsTrunc(_1rl);}),_1rm=function(_1rn){var _1ro=new T(function(){var _1rp=Number(E(_1rn));return jsTrunc(_1rp);}),_1rq=function(_1rr,_){var _1rs=B(_15j(_1rk,_1ro,new T(function(){var _1rt=Number(E(_1rr));return jsTrunc(_1rt);},1),_));return _1qE;};return E(_1rq);};return E(_1rm);},_1ru=__createJSFunc(4,E(_1ri)),_1rv=__app2(E(_1qr),"redeem",_1ru),_1rw=function(_1rx){var _1ry=new T(function(){var _1rz=Number(E(_1rx));return jsTrunc(_1rz);}),_1rA=function(_1rB){var _1rC=new T(function(){var _1rD=Number(E(_1rB));return jsTrunc(_1rD);}),_1rE=function(_1rF,_){var _1rG=B(_14R(_1ry,_1rC,new T(function(){var _1rH=Number(E(_1rF));return jsTrunc(_1rH);},1),_));return _1qE;};return E(_1rE);};return E(_1rA);},_1rI=__createJSFunc(4,E(_1rw)),_1rJ=__app2(E(_1qq),"claim",_1rI),_1rK=function(_1rL){var _1rM=new T(function(){var _1rN=Number(E(_1rL));return jsTrunc(_1rN);}),_1rO=function(_1rP){var _1rQ=new T(function(){var _1rR=Number(E(_1rP));return jsTrunc(_1rR);}),_1rS=function(_1rT,_){var _1rU=B(_170(_1rM,_1rQ,new T(function(){var _1rV=Number(E(_1rT));return jsTrunc(_1rV);},1),_));return _1qE;};return E(_1rS);};return E(_1rO);},_1rW=__createJSFunc(4,E(_1rK)),_1rX=__app2(E(_1qp),"choose",_1rW),_1rY=__createJSFunc(0,function(_){var _1rZ=B(_1pm(_));return _1qE;}),_1s0=__app2(E(_1qo),"execute",_1rY),_1s1=__createJSFunc(0,function(_){var _1s2=B(_1qF(_));return _1qE;}),_1s3=__app2(E(_1qn),"refreshActions",_1s1),_1s4=function(_1s5,_){var _1s6=B(A2(_16M,new T(function(){var _1s7=String(E(_1s5));return fromJSStr(_1s7);}),_));return _1qE;},_1s8=__createJSFunc(2,E(_1s4)),_1s9=__app2(E(_1qm),"addAction",_1s8),_1sa=function(_1sb){var _1sc=new T(function(){var _1sd=String(E(_1sb));return fromJSStr(_1sd);}),_1se=function(_1sf,_){var _1sg=B(A3(_17m,_1sc,new T(function(){var _1sh=Number(E(_1sf));return jsTrunc(_1sh);}),_));return _1qE;};return E(_1se);},_1si=__createJSFunc(3,E(_1sa)),_1sj=__app2(E(_1ql),"addActionWithNum",_1si),_1sk=__createJSFunc(0,function(_){var _1sl=B(_1ka(_));return _1qE;}),_1sm=__app2(E(_1qy),"depositIncentive",_1sk),_1sn=__createJSFunc(0,function(_){var _1so=B(_1jA(_));return _1qE;}),_1sp=__app2(E(_1qx),"crowdFunding",_1sn),_1sq=__createJSFunc(0,function(_){var _1sr=B(_1kW(_));return _1qE;}),_1ss=__app2(E(_1qw),"escrow",_1sq),_1st=__app1(E(_1qN),toJSStr(E(_14K))),_1su=new T(function(){var _1sv=B(_106(B(_g4(_yK,new T(function(){var _1sw=String(_1st);return fromJSStr(_1sw);})))));if(!_1sv._){return E(_eS);}else{if(!E(_1sv.b)._){var _1sx=E(_1sv.a);return new T4(0,new T(function(){return B(_bH(_1sx.a));}),new T(function(){return B(_8f(_1sx.b));}),new T(function(){return B(_9V(_1sx.c));}),new T(function(){return B(_4n(_1sx.d));}));}else{return E(_eQ);}}}),_1sy=B(_14r(_1su,_));return _bT;},_1sz=function(_){return new F(function(){return _1qM(_);});};
var hasteMain = function() {B(A(_1sz, [0]));};window.onload = hasteMain;