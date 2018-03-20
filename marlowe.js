"use strict";
var __haste_prog_id = '8afb0fca3d50c281a503c124273546bb6fe9db489ecf7b3f547b82d6febab607';
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

var _0=new T0(1),_1=__Z,_2=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_3=function(_4){return new F(function(){return err(_2);});},_5=new T(function(){return B(_3(_));}),_6=function(_7,_8,_9,_a){var _b=E(_9);if(!_b._){var _c=_b.a,_d=E(_a);if(!_d._){var _e=_d.a,_f=_d.b,_g=_d.c;if(_e<=(imul(3,_c)|0)){return new T5(0,(1+_c|0)+_e|0,E(_7),_8,E(_b),E(_d));}else{var _h=E(_d.d);if(!_h._){var _i=_h.a,_j=_h.b,_k=_h.c,_l=_h.d,_m=E(_d.e);if(!_m._){var _n=_m.a;if(_i>=(imul(2,_n)|0)){var _o=function(_p){var _q=E(_7),_r=E(_h.e);return (_r._==0)?new T5(0,(1+_c|0)+_e|0,E(_j),_k,E(new T5(0,(1+_c|0)+_p|0,E(_q),_8,E(_b),E(_l))),E(new T5(0,(1+_n|0)+_r.a|0,E(_f),_g,E(_r),E(_m)))):new T5(0,(1+_c|0)+_e|0,E(_j),_k,E(new T5(0,(1+_c|0)+_p|0,E(_q),_8,E(_b),E(_l))),E(new T5(0,1+_n|0,E(_f),_g,E(_0),E(_m))));},_s=E(_l);if(!_s._){return new F(function(){return _o(_s.a);});}else{return new F(function(){return _o(0);});}}else{return new T5(0,(1+_c|0)+_e|0,E(_f),_g,E(new T5(0,(1+_c|0)+_i|0,E(_7),_8,E(_b),E(_h))),E(_m));}}else{return E(_5);}}else{return E(_5);}}}else{return new T5(0,1+_c|0,E(_7),_8,E(_b),E(_0));}}else{var _t=E(_a);if(!_t._){var _u=_t.a,_v=_t.b,_w=_t.c,_x=_t.e,_y=E(_t.d);if(!_y._){var _z=_y.a,_A=_y.b,_B=_y.c,_C=_y.d,_D=E(_x);if(!_D._){var _E=_D.a;if(_z>=(imul(2,_E)|0)){var _F=function(_G){var _H=E(_7),_I=E(_y.e);return (_I._==0)?new T5(0,1+_u|0,E(_A),_B,E(new T5(0,1+_G|0,E(_H),_8,E(_0),E(_C))),E(new T5(0,(1+_E|0)+_I.a|0,E(_v),_w,E(_I),E(_D)))):new T5(0,1+_u|0,E(_A),_B,E(new T5(0,1+_G|0,E(_H),_8,E(_0),E(_C))),E(new T5(0,1+_E|0,E(_v),_w,E(_0),E(_D))));},_J=E(_C);if(!_J._){return new F(function(){return _F(_J.a);});}else{return new F(function(){return _F(0);});}}else{return new T5(0,1+_u|0,E(_v),_w,E(new T5(0,1+_z|0,E(_7),_8,E(_0),E(_y))),E(_D));}}else{return new T5(0,3,E(_A),_B,E(new T5(0,1,E(_7),_8,E(_0),E(_0))),E(new T5(0,1,E(_v),_w,E(_0),E(_0))));}}else{var _K=E(_x);return (_K._==0)?new T5(0,3,E(_v),_w,E(new T5(0,1,E(_7),_8,E(_0),E(_0))),E(_K)):new T5(0,2,E(_7),_8,E(_0),E(_t));}}else{return new T5(0,1,E(_7),_8,E(_0),E(_0));}}},_L=function(_M,_N){return new T5(0,1,E(_M),_N,E(_0),E(_0));},_O=function(_P,_Q,_R){var _S=E(_R);if(!_S._){return new F(function(){return _6(_S.b,_S.c,_S.d,B(_O(_P,_Q,_S.e)));});}else{return new F(function(){return _L(_P,_Q);});}},_T=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_U=function(_V){return new F(function(){return err(_T);});},_W=new T(function(){return B(_U(_));}),_X=function(_Y,_Z,_10,_11){var _12=E(_11);if(!_12._){var _13=_12.a,_14=E(_10);if(!_14._){var _15=_14.a,_16=_14.b,_17=_14.c;if(_15<=(imul(3,_13)|0)){return new T5(0,(1+_15|0)+_13|0,E(_Y),_Z,E(_14),E(_12));}else{var _18=E(_14.d);if(!_18._){var _19=_18.a,_1a=E(_14.e);if(!_1a._){var _1b=_1a.a,_1c=_1a.b,_1d=_1a.c,_1e=_1a.d;if(_1b>=(imul(2,_19)|0)){var _1f=function(_1g){var _1h=E(_1a.e);return (_1h._==0)?new T5(0,(1+_15|0)+_13|0,E(_1c),_1d,E(new T5(0,(1+_19|0)+_1g|0,E(_16),_17,E(_18),E(_1e))),E(new T5(0,(1+_13|0)+_1h.a|0,E(_Y),_Z,E(_1h),E(_12)))):new T5(0,(1+_15|0)+_13|0,E(_1c),_1d,E(new T5(0,(1+_19|0)+_1g|0,E(_16),_17,E(_18),E(_1e))),E(new T5(0,1+_13|0,E(_Y),_Z,E(_0),E(_12))));},_1i=E(_1e);if(!_1i._){return new F(function(){return _1f(_1i.a);});}else{return new F(function(){return _1f(0);});}}else{return new T5(0,(1+_15|0)+_13|0,E(_16),_17,E(_18),E(new T5(0,(1+_13|0)+_1b|0,E(_Y),_Z,E(_1a),E(_12))));}}else{return E(_W);}}else{return E(_W);}}}else{return new T5(0,1+_13|0,E(_Y),_Z,E(_0),E(_12));}}else{var _1j=E(_10);if(!_1j._){var _1k=_1j.a,_1l=_1j.b,_1m=_1j.c,_1n=_1j.e,_1o=E(_1j.d);if(!_1o._){var _1p=_1o.a,_1q=E(_1n);if(!_1q._){var _1r=_1q.a,_1s=_1q.b,_1t=_1q.c,_1u=_1q.d;if(_1r>=(imul(2,_1p)|0)){var _1v=function(_1w){var _1x=E(_1q.e);return (_1x._==0)?new T5(0,1+_1k|0,E(_1s),_1t,E(new T5(0,(1+_1p|0)+_1w|0,E(_1l),_1m,E(_1o),E(_1u))),E(new T5(0,1+_1x.a|0,E(_Y),_Z,E(_1x),E(_0)))):new T5(0,1+_1k|0,E(_1s),_1t,E(new T5(0,(1+_1p|0)+_1w|0,E(_1l),_1m,E(_1o),E(_1u))),E(new T5(0,1,E(_Y),_Z,E(_0),E(_0))));},_1y=E(_1u);if(!_1y._){return new F(function(){return _1v(_1y.a);});}else{return new F(function(){return _1v(0);});}}else{return new T5(0,1+_1k|0,E(_1l),_1m,E(_1o),E(new T5(0,1+_1r|0,E(_Y),_Z,E(_1q),E(_0))));}}else{return new T5(0,3,E(_1l),_1m,E(_1o),E(new T5(0,1,E(_Y),_Z,E(_0),E(_0))));}}else{var _1z=E(_1n);return (_1z._==0)?new T5(0,3,E(_1z.b),_1z.c,E(new T5(0,1,E(_1l),_1m,E(_0),E(_0))),E(new T5(0,1,E(_Y),_Z,E(_0),E(_0)))):new T5(0,2,E(_Y),_Z,E(_1j),E(_0));}}else{return new T5(0,1,E(_Y),_Z,E(_0),E(_0));}}},_1A=function(_1B,_1C,_1D){var _1E=E(_1D);if(!_1E._){return new F(function(){return _X(_1E.b,_1E.c,B(_1A(_1B,_1C,_1E.d)),_1E.e);});}else{return new F(function(){return _L(_1B,_1C);});}},_1F=function(_1G,_1H,_1I,_1J,_1K,_1L,_1M){return new F(function(){return _X(_1J,_1K,B(_1A(_1G,_1H,_1L)),_1M);});},_1N=function(_1O,_1P,_1Q,_1R,_1S,_1T,_1U,_1V){var _1W=E(_1Q);if(!_1W._){var _1X=_1W.a,_1Y=_1W.b,_1Z=_1W.c,_20=_1W.d,_21=_1W.e;if((imul(3,_1X)|0)>=_1R){if((imul(3,_1R)|0)>=_1X){return new T5(0,(_1X+_1R|0)+1|0,E(_1O),_1P,E(_1W),E(new T5(0,_1R,E(_1S),_1T,E(_1U),E(_1V))));}else{return new F(function(){return _6(_1Y,_1Z,_20,B(_1N(_1O,_1P,_21,_1R,_1S,_1T,_1U,_1V)));});}}else{return new F(function(){return _X(_1S,_1T,B(_22(_1O,_1P,_1X,_1Y,_1Z,_20,_21,_1U)),_1V);});}}else{return new F(function(){return _1F(_1O,_1P,_1R,_1S,_1T,_1U,_1V);});}},_22=function(_23,_24,_25,_26,_27,_28,_29,_2a){var _2b=E(_2a);if(!_2b._){var _2c=_2b.a,_2d=_2b.b,_2e=_2b.c,_2f=_2b.d,_2g=_2b.e;if((imul(3,_25)|0)>=_2c){if((imul(3,_2c)|0)>=_25){return new T5(0,(_25+_2c|0)+1|0,E(_23),_24,E(new T5(0,_25,E(_26),_27,E(_28),E(_29))),E(_2b));}else{return new F(function(){return _6(_26,_27,_28,B(_1N(_23,_24,_29,_2c,_2d,_2e,_2f,_2g)));});}}else{return new F(function(){return _X(_2d,_2e,B(_22(_23,_24,_25,_26,_27,_28,_29,_2f)),_2g);});}}else{return new F(function(){return _O(_23,_24,new T5(0,_25,E(_26),_27,E(_28),E(_29)));});}},_2h=function(_2i,_2j,_2k,_2l){var _2m=E(_2k);if(!_2m._){var _2n=_2m.a,_2o=_2m.b,_2p=_2m.c,_2q=_2m.d,_2r=_2m.e,_2s=E(_2l);if(!_2s._){var _2t=_2s.a,_2u=_2s.b,_2v=_2s.c,_2w=_2s.d,_2x=_2s.e;if((imul(3,_2n)|0)>=_2t){if((imul(3,_2t)|0)>=_2n){return new T5(0,(_2n+_2t|0)+1|0,E(_2i),_2j,E(_2m),E(_2s));}else{return new F(function(){return _6(_2o,_2p,_2q,B(_1N(_2i,_2j,_2r,_2t,_2u,_2v,_2w,_2x)));});}}else{return new F(function(){return _X(_2u,_2v,B(_22(_2i,_2j,_2n,_2o,_2p,_2q,_2r,_2w)),_2x);});}}else{return new F(function(){return _O(_2i,_2j,_2m);});}}else{return new F(function(){return _1A(_2i,_2j,_2l);});}},_2y=function(_2z,_2A,_2B,_2C,_2D){var _2E=E(_2z);if(_2E==1){var _2F=E(_2D);if(!_2F._){return new T3(0,new T5(0,1,E(new T2(0,_2A,_2B)),_2C,E(_0),E(_0)),_1,_1);}else{var _2G=E(E(_2F.a).a),_2H=E(_2A),_2I=E(_2G.a);return (_2H>=_2I)?(_2H!=_2I)?new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_1,_2F):(_2B<E(_2G.b))?new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_2F,_1):new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_1,_2F):new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_2F,_1);}}else{var _2J=B(_2y(_2E>>1,_2A,_2B,_2C,_2D)),_2K=_2J.a,_2L=_2J.c,_2M=E(_2J.b);if(!_2M._){return new T3(0,_2K,_1,_2L);}else{var _2N=E(_2M.a),_2O=_2N.a,_2P=_2N.b,_2Q=E(_2M.b);if(!_2Q._){return new T3(0,new T(function(){return B(_O(_2O,_2P,_2K));}),_1,_2L);}else{var _2R=_2Q.b,_2S=E(_2Q.a),_2T=_2S.b,_2U=E(_2O),_2V=E(_2S.a),_2W=_2V.b,_2X=E(_2U.a),_2Y=E(_2V.a);if(_2X>=_2Y){if(_2X!=_2Y){return new T3(0,_2K,_1,_2M);}else{var _2Z=E(_2W);if(E(_2U.b)<_2Z){var _30=B(_2y(_2E>>1,_2Y,_2Z,_2T,_2R));return new T3(0,new T(function(){return B(_2h(_2U,_2P,_2K,_30.a));}),_30.b,_30.c);}else{return new T3(0,_2K,_1,_2M);}}}else{var _31=B(_32(_2E>>1,_2Y,_2W,_2T,_2R));return new T3(0,new T(function(){return B(_2h(_2U,_2P,_2K,_31.a));}),_31.b,_31.c);}}}}},_32=function(_33,_34,_35,_36,_37){var _38=E(_33);if(_38==1){var _39=E(_37);if(!_39._){return new T3(0,new T5(0,1,E(new T2(0,_34,_35)),_36,E(_0),E(_0)),_1,_1);}else{var _3a=E(E(_39.a).a),_3b=E(_34),_3c=E(_3a.a);if(_3b>=_3c){if(_3b!=_3c){return new T3(0,new T5(0,1,E(new T2(0,_3b,_35)),_36,E(_0),E(_0)),_1,_39);}else{var _3d=E(_35);return (_3d<E(_3a.b))?new T3(0,new T5(0,1,E(new T2(0,_3b,_3d)),_36,E(_0),E(_0)),_39,_1):new T3(0,new T5(0,1,E(new T2(0,_3b,_3d)),_36,E(_0),E(_0)),_1,_39);}}else{return new T3(0,new T5(0,1,E(new T2(0,_3b,_35)),_36,E(_0),E(_0)),_39,_1);}}}else{var _3e=B(_32(_38>>1,_34,_35,_36,_37)),_3f=_3e.a,_3g=_3e.c,_3h=E(_3e.b);if(!_3h._){return new T3(0,_3f,_1,_3g);}else{var _3i=E(_3h.a),_3j=_3i.a,_3k=_3i.b,_3l=E(_3h.b);if(!_3l._){return new T3(0,new T(function(){return B(_O(_3j,_3k,_3f));}),_1,_3g);}else{var _3m=_3l.b,_3n=E(_3l.a),_3o=_3n.b,_3p=E(_3j),_3q=E(_3n.a),_3r=_3q.b,_3s=E(_3p.a),_3t=E(_3q.a);if(_3s>=_3t){if(_3s!=_3t){return new T3(0,_3f,_1,_3h);}else{var _3u=E(_3r);if(E(_3p.b)<_3u){var _3v=B(_2y(_38>>1,_3t,_3u,_3o,_3m));return new T3(0,new T(function(){return B(_2h(_3p,_3k,_3f,_3v.a));}),_3v.b,_3v.c);}else{return new T3(0,_3f,_1,_3h);}}}else{var _3w=B(_32(_38>>1,_3t,_3r,_3o,_3m));return new T3(0,new T(function(){return B(_2h(_3p,_3k,_3f,_3w.a));}),_3w.b,_3w.c);}}}}},_3x=function(_3y,_3z,_3A,_3B,_3C){var _3D=E(_3C);if(!_3D._){var _3E=_3D.c,_3F=_3D.d,_3G=_3D.e,_3H=E(_3D.b),_3I=E(_3H.a);if(_3y>=_3I){if(_3y!=_3I){return new F(function(){return _6(_3H,_3E,_3F,B(_3x(_3y,_,_3A,_3B,_3G)));});}else{var _3J=E(_3H.b);if(_3A>=_3J){if(_3A!=_3J){return new F(function(){return _6(_3H,_3E,_3F,B(_3x(_3y,_,_3A,_3B,_3G)));});}else{return new T5(0,_3D.a,E(new T2(0,_3y,_3A)),_3B,E(_3F),E(_3G));}}else{return new F(function(){return _X(_3H,_3E,B(_3x(_3y,_,_3A,_3B,_3F)),_3G);});}}}else{return new F(function(){return _X(_3H,_3E,B(_3x(_3y,_,_3A,_3B,_3F)),_3G);});}}else{return new T5(0,1,E(new T2(0,_3y,_3A)),_3B,E(_0),E(_0));}},_3K=function(_3L,_3M,_3N,_3O,_3P){var _3Q=E(_3P);if(!_3Q._){var _3R=_3Q.c,_3S=_3Q.d,_3T=_3Q.e,_3U=E(_3Q.b),_3V=E(_3U.a);if(_3L>=_3V){if(_3L!=_3V){return new F(function(){return _6(_3U,_3R,_3S,B(_3K(_3L,_,_3N,_3O,_3T)));});}else{var _3W=E(_3N),_3X=E(_3U.b);if(_3W>=_3X){if(_3W!=_3X){return new F(function(){return _6(_3U,_3R,_3S,B(_3x(_3L,_,_3W,_3O,_3T)));});}else{return new T5(0,_3Q.a,E(new T2(0,_3L,_3W)),_3O,E(_3S),E(_3T));}}else{return new F(function(){return _X(_3U,_3R,B(_3x(_3L,_,_3W,_3O,_3S)),_3T);});}}}else{return new F(function(){return _X(_3U,_3R,B(_3K(_3L,_,_3N,_3O,_3S)),_3T);});}}else{return new T5(0,1,E(new T2(0,_3L,_3N)),_3O,E(_0),E(_0));}},_3Y=function(_3Z,_40,_41,_42){var _43=E(_42);if(!_43._){var _44=_43.c,_45=_43.d,_46=_43.e,_47=E(_43.b),_48=E(_3Z),_49=E(_47.a);if(_48>=_49){if(_48!=_49){return new F(function(){return _6(_47,_44,_45,B(_3K(_48,_,_40,_41,_46)));});}else{var _4a=E(_40),_4b=E(_47.b);if(_4a>=_4b){if(_4a!=_4b){return new F(function(){return _6(_47,_44,_45,B(_3x(_48,_,_4a,_41,_46)));});}else{return new T5(0,_43.a,E(new T2(0,_48,_4a)),_41,E(_45),E(_46));}}else{return new F(function(){return _X(_47,_44,B(_3x(_48,_,_4a,_41,_45)),_46);});}}}else{return new F(function(){return _X(_47,_44,B(_3K(_48,_,_40,_41,_45)),_46);});}}else{return new T5(0,1,E(new T2(0,_3Z,_40)),_41,E(_0),E(_0));}},_4c=function(_4d,_4e){while(1){var _4f=E(_4e);if(!_4f._){return E(_4d);}else{var _4g=E(_4f.a),_4h=E(_4g.a),_4i=B(_3Y(_4h.a,_4h.b,_4g.b,_4d));_4d=_4i;_4e=_4f.b;continue;}}},_4j=function(_4k,_4l,_4m,_4n,_4o){return new F(function(){return _4c(B(_3Y(_4l,_4m,_4n,_4k)),_4o);});},_4p=function(_4q,_4r,_4s){var _4t=E(_4r),_4u=E(_4t.a);return new F(function(){return _4c(B(_3Y(_4u.a,_4u.b,_4t.b,_4q)),_4s);});},_4v=function(_4w,_4x,_4y){var _4z=E(_4y);if(!_4z._){return E(_4x);}else{var _4A=E(_4z.a),_4B=_4A.a,_4C=_4A.b,_4D=E(_4z.b);if(!_4D._){return new F(function(){return _O(_4B,_4C,_4x);});}else{var _4E=E(_4D.a),_4F=E(_4B),_4G=_4F.b,_4H=E(_4E.a),_4I=_4H.b,_4J=E(_4F.a),_4K=E(_4H.a),_4L=function(_4M){var _4N=B(_32(_4w,_4K,_4I,_4E.b,_4D.b)),_4O=_4N.a,_4P=E(_4N.c);if(!_4P._){return new F(function(){return _4v(_4w<<1,B(_2h(_4F,_4C,_4x,_4O)),_4N.b);});}else{return new F(function(){return _4p(B(_2h(_4F,_4C,_4x,_4O)),_4P.a,_4P.b);});}};if(_4J>=_4K){if(_4J!=_4K){return new F(function(){return _4j(_4x,_4J,_4G,_4C,_4D);});}else{var _4Q=E(_4G);if(_4Q<E(_4I)){return new F(function(){return _4L(_);});}else{return new F(function(){return _4j(_4x,_4J,_4Q,_4C,_4D);});}}}else{return new F(function(){return _4L(_);});}}}},_4R=function(_4S,_4T,_4U,_4V,_4W,_4X){var _4Y=E(_4X);if(!_4Y._){return new F(function(){return _O(new T2(0,_4U,_4V),_4W,_4T);});}else{var _4Z=E(_4Y.a),_50=E(_4Z.a),_51=_50.b,_52=E(_4U),_53=E(_50.a),_54=function(_55){var _56=B(_32(_4S,_53,_51,_4Z.b,_4Y.b)),_57=_56.a,_58=E(_56.c);if(!_58._){return new F(function(){return _4v(_4S<<1,B(_2h(new T2(0,_52,_4V),_4W,_4T,_57)),_56.b);});}else{return new F(function(){return _4p(B(_2h(new T2(0,_52,_4V),_4W,_4T,_57)),_58.a,_58.b);});}};if(_52>=_53){if(_52!=_53){return new F(function(){return _4j(_4T,_52,_4V,_4W,_4Y);});}else{if(_4V<E(_51)){return new F(function(){return _54(_);});}else{return new F(function(){return _4j(_4T,_52,_4V,_4W,_4Y);});}}}else{return new F(function(){return _54(_);});}}},_59=function(_5a,_5b,_5c,_5d,_5e,_5f){var _5g=E(_5f);if(!_5g._){return new F(function(){return _O(new T2(0,_5c,_5d),_5e,_5b);});}else{var _5h=E(_5g.a),_5i=E(_5h.a),_5j=_5i.b,_5k=E(_5c),_5l=E(_5i.a),_5m=function(_5n){var _5o=B(_32(_5a,_5l,_5j,_5h.b,_5g.b)),_5p=_5o.a,_5q=E(_5o.c);if(!_5q._){return new F(function(){return _4v(_5a<<1,B(_2h(new T2(0,_5k,_5d),_5e,_5b,_5p)),_5o.b);});}else{return new F(function(){return _4p(B(_2h(new T2(0,_5k,_5d),_5e,_5b,_5p)),_5q.a,_5q.b);});}};if(_5k>=_5l){if(_5k!=_5l){return new F(function(){return _4j(_5b,_5k,_5d,_5e,_5g);});}else{var _5r=E(_5d);if(_5r<E(_5j)){return new F(function(){return _5m(_);});}else{return new F(function(){return _4j(_5b,_5k,_5r,_5e,_5g);});}}}else{return new F(function(){return _5m(_);});}}},_5s=function(_5t){var _5u=E(_5t);if(!_5u._){return new T0(1);}else{var _5v=E(_5u.a),_5w=_5v.a,_5x=_5v.b,_5y=E(_5u.b);if(!_5y._){return new T5(0,1,E(_5w),_5x,E(_0),E(_0));}else{var _5z=_5y.b,_5A=E(_5y.a),_5B=_5A.b,_5C=E(_5w),_5D=E(_5A.a),_5E=_5D.b,_5F=E(_5C.a),_5G=E(_5D.a);if(_5F>=_5G){if(_5F!=_5G){return new F(function(){return _4j(new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5E,_5B,_5z);});}else{var _5H=E(_5E);if(E(_5C.b)<_5H){return new F(function(){return _4R(1,new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5H,_5B,_5z);});}else{return new F(function(){return _4j(new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5H,_5B,_5z);});}}}else{return new F(function(){return _59(1,new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5E,_5B,_5z);});}}}},_5I=new T0(1),_5J=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_5K=function(_5L){return new F(function(){return err(_5J);});},_5M=new T(function(){return B(_5K(_));}),_5N=function(_5O,_5P,_5Q){var _5R=E(_5P);if(!_5R._){var _5S=_5R.a,_5T=E(_5Q);if(!_5T._){var _5U=_5T.a,_5V=_5T.b;if(_5U<=(imul(3,_5S)|0)){return new T4(0,(1+_5S|0)+_5U|0,E(_5O),E(_5R),E(_5T));}else{var _5W=E(_5T.c);if(!_5W._){var _5X=_5W.a,_5Y=_5W.b,_5Z=_5W.c,_60=E(_5T.d);if(!_60._){var _61=_60.a;if(_5X>=(imul(2,_61)|0)){var _62=function(_63){var _64=E(_5O),_65=E(_5W.d);return (_65._==0)?new T4(0,(1+_5S|0)+_5U|0,E(_5Y),E(new T4(0,(1+_5S|0)+_63|0,E(_64),E(_5R),E(_5Z))),E(new T4(0,(1+_61|0)+_65.a|0,E(_5V),E(_65),E(_60)))):new T4(0,(1+_5S|0)+_5U|0,E(_5Y),E(new T4(0,(1+_5S|0)+_63|0,E(_64),E(_5R),E(_5Z))),E(new T4(0,1+_61|0,E(_5V),E(_5I),E(_60))));},_66=E(_5Z);if(!_66._){return new F(function(){return _62(_66.a);});}else{return new F(function(){return _62(0);});}}else{return new T4(0,(1+_5S|0)+_5U|0,E(_5V),E(new T4(0,(1+_5S|0)+_5X|0,E(_5O),E(_5R),E(_5W))),E(_60));}}else{return E(_5M);}}else{return E(_5M);}}}else{return new T4(0,1+_5S|0,E(_5O),E(_5R),E(_5I));}}else{var _67=E(_5Q);if(!_67._){var _68=_67.a,_69=_67.b,_6a=_67.d,_6b=E(_67.c);if(!_6b._){var _6c=_6b.a,_6d=_6b.b,_6e=_6b.c,_6f=E(_6a);if(!_6f._){var _6g=_6f.a;if(_6c>=(imul(2,_6g)|0)){var _6h=function(_6i){var _6j=E(_5O),_6k=E(_6b.d);return (_6k._==0)?new T4(0,1+_68|0,E(_6d),E(new T4(0,1+_6i|0,E(_6j),E(_5I),E(_6e))),E(new T4(0,(1+_6g|0)+_6k.a|0,E(_69),E(_6k),E(_6f)))):new T4(0,1+_68|0,E(_6d),E(new T4(0,1+_6i|0,E(_6j),E(_5I),E(_6e))),E(new T4(0,1+_6g|0,E(_69),E(_5I),E(_6f))));},_6l=E(_6e);if(!_6l._){return new F(function(){return _6h(_6l.a);});}else{return new F(function(){return _6h(0);});}}else{return new T4(0,1+_68|0,E(_69),E(new T4(0,1+_6c|0,E(_5O),E(_5I),E(_6b))),E(_6f));}}else{return new T4(0,3,E(_6d),E(new T4(0,1,E(_5O),E(_5I),E(_5I))),E(new T4(0,1,E(_69),E(_5I),E(_5I))));}}else{var _6m=E(_6a);return (_6m._==0)?new T4(0,3,E(_69),E(new T4(0,1,E(_5O),E(_5I),E(_5I))),E(_6m)):new T4(0,2,E(_5O),E(_5I),E(_67));}}else{return new T4(0,1,E(_5O),E(_5I),E(_5I));}}},_6n=function(_6o){return new T4(0,1,E(_6o),E(_5I),E(_5I));},_6p=function(_6q,_6r){var _6s=E(_6r);if(!_6s._){return new F(function(){return _5N(_6s.b,_6s.c,B(_6p(_6q,_6s.d)));});}else{return new F(function(){return _6n(_6q);});}},_6t=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_6u=function(_6v){return new F(function(){return err(_6t);});},_6w=new T(function(){return B(_6u(_));}),_6x=function(_6y,_6z,_6A){var _6B=E(_6A);if(!_6B._){var _6C=_6B.a,_6D=E(_6z);if(!_6D._){var _6E=_6D.a,_6F=_6D.b;if(_6E<=(imul(3,_6C)|0)){return new T4(0,(1+_6E|0)+_6C|0,E(_6y),E(_6D),E(_6B));}else{var _6G=E(_6D.c);if(!_6G._){var _6H=_6G.a,_6I=E(_6D.d);if(!_6I._){var _6J=_6I.a,_6K=_6I.b,_6L=_6I.c;if(_6J>=(imul(2,_6H)|0)){var _6M=function(_6N){var _6O=E(_6I.d);return (_6O._==0)?new T4(0,(1+_6E|0)+_6C|0,E(_6K),E(new T4(0,(1+_6H|0)+_6N|0,E(_6F),E(_6G),E(_6L))),E(new T4(0,(1+_6C|0)+_6O.a|0,E(_6y),E(_6O),E(_6B)))):new T4(0,(1+_6E|0)+_6C|0,E(_6K),E(new T4(0,(1+_6H|0)+_6N|0,E(_6F),E(_6G),E(_6L))),E(new T4(0,1+_6C|0,E(_6y),E(_5I),E(_6B))));},_6P=E(_6L);if(!_6P._){return new F(function(){return _6M(_6P.a);});}else{return new F(function(){return _6M(0);});}}else{return new T4(0,(1+_6E|0)+_6C|0,E(_6F),E(_6G),E(new T4(0,(1+_6C|0)+_6J|0,E(_6y),E(_6I),E(_6B))));}}else{return E(_6w);}}else{return E(_6w);}}}else{return new T4(0,1+_6C|0,E(_6y),E(_5I),E(_6B));}}else{var _6Q=E(_6z);if(!_6Q._){var _6R=_6Q.a,_6S=_6Q.b,_6T=_6Q.d,_6U=E(_6Q.c);if(!_6U._){var _6V=_6U.a,_6W=E(_6T);if(!_6W._){var _6X=_6W.a,_6Y=_6W.b,_6Z=_6W.c;if(_6X>=(imul(2,_6V)|0)){var _70=function(_71){var _72=E(_6W.d);return (_72._==0)?new T4(0,1+_6R|0,E(_6Y),E(new T4(0,(1+_6V|0)+_71|0,E(_6S),E(_6U),E(_6Z))),E(new T4(0,1+_72.a|0,E(_6y),E(_72),E(_5I)))):new T4(0,1+_6R|0,E(_6Y),E(new T4(0,(1+_6V|0)+_71|0,E(_6S),E(_6U),E(_6Z))),E(new T4(0,1,E(_6y),E(_5I),E(_5I))));},_73=E(_6Z);if(!_73._){return new F(function(){return _70(_73.a);});}else{return new F(function(){return _70(0);});}}else{return new T4(0,1+_6R|0,E(_6S),E(_6U),E(new T4(0,1+_6X|0,E(_6y),E(_6W),E(_5I))));}}else{return new T4(0,3,E(_6S),E(_6U),E(new T4(0,1,E(_6y),E(_5I),E(_5I))));}}else{var _74=E(_6T);return (_74._==0)?new T4(0,3,E(_74.b),E(new T4(0,1,E(_6S),E(_5I),E(_5I))),E(new T4(0,1,E(_6y),E(_5I),E(_5I)))):new T4(0,2,E(_6y),E(_6Q),E(_5I));}}else{return new T4(0,1,E(_6y),E(_5I),E(_5I));}}},_75=function(_76,_77){var _78=E(_77);if(!_78._){return new F(function(){return _6x(_78.b,B(_75(_76,_78.c)),_78.d);});}else{return new F(function(){return _6n(_76);});}},_79=function(_7a,_7b,_7c,_7d,_7e){return new F(function(){return _5N(_7c,_7d,B(_6p(_7a,_7e)));});},_7f=function(_7g,_7h,_7i,_7j,_7k){return new F(function(){return _6x(_7i,B(_75(_7g,_7j)),_7k);});},_7l=function(_7m,_7n,_7o,_7p,_7q,_7r){var _7s=E(_7n);if(!_7s._){var _7t=_7s.a,_7u=_7s.b,_7v=_7s.c,_7w=_7s.d;if((imul(3,_7t)|0)>=_7o){if((imul(3,_7o)|0)>=_7t){return new T4(0,(_7t+_7o|0)+1|0,E(_7m),E(_7s),E(new T4(0,_7o,E(_7p),E(_7q),E(_7r))));}else{return new F(function(){return _5N(_7u,_7v,B(_7l(_7m,_7w,_7o,_7p,_7q,_7r)));});}}else{return new F(function(){return _6x(_7p,B(_7x(_7m,_7t,_7u,_7v,_7w,_7q)),_7r);});}}else{return new F(function(){return _7f(_7m,_7o,_7p,_7q,_7r);});}},_7x=function(_7y,_7z,_7A,_7B,_7C,_7D){var _7E=E(_7D);if(!_7E._){var _7F=_7E.a,_7G=_7E.b,_7H=_7E.c,_7I=_7E.d;if((imul(3,_7z)|0)>=_7F){if((imul(3,_7F)|0)>=_7z){return new T4(0,(_7z+_7F|0)+1|0,E(_7y),E(new T4(0,_7z,E(_7A),E(_7B),E(_7C))),E(_7E));}else{return new F(function(){return _5N(_7A,_7B,B(_7l(_7y,_7C,_7F,_7G,_7H,_7I)));});}}else{return new F(function(){return _6x(_7G,B(_7x(_7y,_7z,_7A,_7B,_7C,_7H)),_7I);});}}else{return new F(function(){return _79(_7y,_7z,_7A,_7B,_7C);});}},_7J=function(_7K,_7L,_7M){var _7N=E(_7L);if(!_7N._){var _7O=_7N.a,_7P=_7N.b,_7Q=_7N.c,_7R=_7N.d,_7S=E(_7M);if(!_7S._){var _7T=_7S.a,_7U=_7S.b,_7V=_7S.c,_7W=_7S.d;if((imul(3,_7O)|0)>=_7T){if((imul(3,_7T)|0)>=_7O){return new T4(0,(_7O+_7T|0)+1|0,E(_7K),E(_7N),E(_7S));}else{return new F(function(){return _5N(_7P,_7Q,B(_7l(_7K,_7R,_7T,_7U,_7V,_7W)));});}}else{return new F(function(){return _6x(_7U,B(_7x(_7K,_7O,_7P,_7Q,_7R,_7V)),_7W);});}}else{return new F(function(){return _79(_7K,_7O,_7P,_7Q,_7R);});}}else{return new F(function(){return _75(_7K,_7M);});}},_7X=function(_7Y,_7Z,_80,_81,_82){var _83=E(_7Y);if(_83==1){var _84=E(_82);if(!_84._){return new T3(0,new T4(0,1,E(new T3(0,_7Z,_80,_81)),E(_5I),E(_5I)),_1,_1);}else{var _85=E(_7Z),_86=E(_84.a),_87=E(_86.a);if(_85>=_87){if(_85!=_87){return new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_1,_84);}else{var _88=E(_86.b);return (_80>=_88)?(_80!=_88)?new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_1,_84):(_81<E(_86.c))?new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_84,_1):new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_1,_84):new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_84,_1);}}else{return new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_84,_1);}}}else{var _89=B(_7X(_83>>1,_7Z,_80,_81,_82)),_8a=_89.a,_8b=_89.c,_8c=E(_89.b);if(!_8c._){return new T3(0,_8a,_1,_8b);}else{var _8d=_8c.a,_8e=E(_8c.b);if(!_8e._){return new T3(0,new T(function(){return B(_6p(_8d,_8a));}),_1,_8b);}else{var _8f=_8e.b,_8g=E(_8d),_8h=E(_8g.a),_8i=E(_8e.a),_8j=_8i.b,_8k=_8i.c,_8l=E(_8i.a);if(_8h>=_8l){if(_8h!=_8l){return new T3(0,_8a,_1,_8c);}else{var _8m=E(_8g.b),_8n=E(_8j);if(_8m>=_8n){if(_8m!=_8n){return new T3(0,_8a,_1,_8c);}else{var _8o=E(_8k);if(E(_8g.c)<_8o){var _8p=B(_7X(_83>>1,_8l,_8n,_8o,_8f));return new T3(0,new T(function(){return B(_7J(_8g,_8a,_8p.a));}),_8p.b,_8p.c);}else{return new T3(0,_8a,_1,_8c);}}}else{var _8q=B(_8r(_83>>1,_8l,_8n,_8k,_8f));return new T3(0,new T(function(){return B(_7J(_8g,_8a,_8q.a));}),_8q.b,_8q.c);}}}else{var _8s=B(_8t(_83>>1,_8l,_8j,_8k,_8f));return new T3(0,new T(function(){return B(_7J(_8g,_8a,_8s.a));}),_8s.b,_8s.c);}}}}},_8r=function(_8u,_8v,_8w,_8x,_8y){var _8z=E(_8u);if(_8z==1){var _8A=E(_8y);if(!_8A._){return new T3(0,new T4(0,1,E(new T3(0,_8v,_8w,_8x)),E(_5I),E(_5I)),_1,_1);}else{var _8B=E(_8v),_8C=E(_8A.a),_8D=E(_8C.a);if(_8B>=_8D){if(_8B!=_8D){return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_1,_8A);}else{var _8E=E(_8C.b);if(_8w>=_8E){if(_8w!=_8E){return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_1,_8A);}else{var _8F=E(_8x);return (_8F<E(_8C.c))?new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8F)),E(_5I),E(_5I)),_8A,_1):new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8F)),E(_5I),E(_5I)),_1,_8A);}}else{return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_8A,_1);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_8A,_1);}}}else{var _8G=B(_8r(_8z>>1,_8v,_8w,_8x,_8y)),_8H=_8G.a,_8I=_8G.c,_8J=E(_8G.b);if(!_8J._){return new T3(0,_8H,_1,_8I);}else{var _8K=_8J.a,_8L=E(_8J.b);if(!_8L._){return new T3(0,new T(function(){return B(_6p(_8K,_8H));}),_1,_8I);}else{var _8M=_8L.b,_8N=E(_8K),_8O=E(_8N.a),_8P=E(_8L.a),_8Q=_8P.b,_8R=_8P.c,_8S=E(_8P.a);if(_8O>=_8S){if(_8O!=_8S){return new T3(0,_8H,_1,_8J);}else{var _8T=E(_8N.b),_8U=E(_8Q);if(_8T>=_8U){if(_8T!=_8U){return new T3(0,_8H,_1,_8J);}else{var _8V=E(_8R);if(E(_8N.c)<_8V){var _8W=B(_7X(_8z>>1,_8S,_8U,_8V,_8M));return new T3(0,new T(function(){return B(_7J(_8N,_8H,_8W.a));}),_8W.b,_8W.c);}else{return new T3(0,_8H,_1,_8J);}}}else{var _8X=B(_8r(_8z>>1,_8S,_8U,_8R,_8M));return new T3(0,new T(function(){return B(_7J(_8N,_8H,_8X.a));}),_8X.b,_8X.c);}}}else{var _8Y=B(_8t(_8z>>1,_8S,_8Q,_8R,_8M));return new T3(0,new T(function(){return B(_7J(_8N,_8H,_8Y.a));}),_8Y.b,_8Y.c);}}}}},_8t=function(_8Z,_90,_91,_92,_93){var _94=E(_8Z);if(_94==1){var _95=E(_93);if(!_95._){return new T3(0,new T4(0,1,E(new T3(0,_90,_91,_92)),E(_5I),E(_5I)),_1,_1);}else{var _96=E(_90),_97=E(_95.a),_98=E(_97.a);if(_96>=_98){if(_96!=_98){return new T3(0,new T4(0,1,E(new T3(0,_96,_91,_92)),E(_5I),E(_5I)),_1,_95);}else{var _99=E(_91),_9a=E(_97.b);if(_99>=_9a){if(_99!=_9a){return new T3(0,new T4(0,1,E(new T3(0,_96,_99,_92)),E(_5I),E(_5I)),_1,_95);}else{var _9b=E(_92);return (_9b<E(_97.c))?new T3(0,new T4(0,1,E(new T3(0,_96,_99,_9b)),E(_5I),E(_5I)),_95,_1):new T3(0,new T4(0,1,E(new T3(0,_96,_99,_9b)),E(_5I),E(_5I)),_1,_95);}}else{return new T3(0,new T4(0,1,E(new T3(0,_96,_99,_92)),E(_5I),E(_5I)),_95,_1);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_96,_91,_92)),E(_5I),E(_5I)),_95,_1);}}}else{var _9c=B(_8t(_94>>1,_90,_91,_92,_93)),_9d=_9c.a,_9e=_9c.c,_9f=E(_9c.b);if(!_9f._){return new T3(0,_9d,_1,_9e);}else{var _9g=_9f.a,_9h=E(_9f.b);if(!_9h._){return new T3(0,new T(function(){return B(_6p(_9g,_9d));}),_1,_9e);}else{var _9i=_9h.b,_9j=E(_9g),_9k=E(_9j.a),_9l=E(_9h.a),_9m=_9l.b,_9n=_9l.c,_9o=E(_9l.a);if(_9k>=_9o){if(_9k!=_9o){return new T3(0,_9d,_1,_9f);}else{var _9p=E(_9j.b),_9q=E(_9m);if(_9p>=_9q){if(_9p!=_9q){return new T3(0,_9d,_1,_9f);}else{var _9r=E(_9n);if(E(_9j.c)<_9r){var _9s=B(_7X(_94>>1,_9o,_9q,_9r,_9i));return new T3(0,new T(function(){return B(_7J(_9j,_9d,_9s.a));}),_9s.b,_9s.c);}else{return new T3(0,_9d,_1,_9f);}}}else{var _9t=B(_8r(_94>>1,_9o,_9q,_9n,_9i));return new T3(0,new T(function(){return B(_7J(_9j,_9d,_9t.a));}),_9t.b,_9t.c);}}}else{var _9u=B(_8t(_94>>1,_9o,_9m,_9n,_9i));return new T3(0,new T(function(){return B(_7J(_9j,_9d,_9u.a));}),_9u.b,_9u.c);}}}}},_9v=function(_9w,_9x,_9y,_9z,_9A){var _9B=E(_9A);if(!_9B._){var _9C=_9B.c,_9D=_9B.d,_9E=E(_9B.b),_9F=E(_9E.a);if(_9w>=_9F){if(_9w!=_9F){return new F(function(){return _5N(_9E,_9C,B(_9v(_9w,_,_9y,_9z,_9D)));});}else{var _9G=E(_9E.b);if(_9y>=_9G){if(_9y!=_9G){return new F(function(){return _5N(_9E,_9C,B(_9v(_9w,_,_9y,_9z,_9D)));});}else{var _9H=E(_9E.c);if(_9z>=_9H){if(_9z!=_9H){return new F(function(){return _5N(_9E,_9C,B(_9v(_9w,_,_9y,_9z,_9D)));});}else{return new T4(0,_9B.a,E(new T3(0,_9w,_9y,_9z)),E(_9C),E(_9D));}}else{return new F(function(){return _6x(_9E,B(_9v(_9w,_,_9y,_9z,_9C)),_9D);});}}}else{return new F(function(){return _6x(_9E,B(_9v(_9w,_,_9y,_9z,_9C)),_9D);});}}}else{return new F(function(){return _6x(_9E,B(_9v(_9w,_,_9y,_9z,_9C)),_9D);});}}else{return new T4(0,1,E(new T3(0,_9w,_9y,_9z)),E(_5I),E(_5I));}},_9I=function(_9J,_9K,_9L,_9M,_9N){var _9O=E(_9N);if(!_9O._){var _9P=_9O.c,_9Q=_9O.d,_9R=E(_9O.b),_9S=E(_9R.a);if(_9J>=_9S){if(_9J!=_9S){return new F(function(){return _5N(_9R,_9P,B(_9I(_9J,_,_9L,_9M,_9Q)));});}else{var _9T=E(_9R.b);if(_9L>=_9T){if(_9L!=_9T){return new F(function(){return _5N(_9R,_9P,B(_9I(_9J,_,_9L,_9M,_9Q)));});}else{var _9U=E(_9M),_9V=E(_9R.c);if(_9U>=_9V){if(_9U!=_9V){return new F(function(){return _5N(_9R,_9P,B(_9v(_9J,_,_9L,_9U,_9Q)));});}else{return new T4(0,_9O.a,E(new T3(0,_9J,_9L,_9U)),E(_9P),E(_9Q));}}else{return new F(function(){return _6x(_9R,B(_9v(_9J,_,_9L,_9U,_9P)),_9Q);});}}}else{return new F(function(){return _6x(_9R,B(_9I(_9J,_,_9L,_9M,_9P)),_9Q);});}}}else{return new F(function(){return _6x(_9R,B(_9I(_9J,_,_9L,_9M,_9P)),_9Q);});}}else{return new T4(0,1,E(new T3(0,_9J,_9L,_9M)),E(_5I),E(_5I));}},_9W=function(_9X,_9Y,_9Z,_a0,_a1){var _a2=E(_a1);if(!_a2._){var _a3=_a2.c,_a4=_a2.d,_a5=E(_a2.b),_a6=E(_a5.a);if(_9X>=_a6){if(_9X!=_a6){return new F(function(){return _5N(_a5,_a3,B(_9W(_9X,_,_9Z,_a0,_a4)));});}else{var _a7=E(_9Z),_a8=E(_a5.b);if(_a7>=_a8){if(_a7!=_a8){return new F(function(){return _5N(_a5,_a3,B(_9I(_9X,_,_a7,_a0,_a4)));});}else{var _a9=E(_a0),_aa=E(_a5.c);if(_a9>=_aa){if(_a9!=_aa){return new F(function(){return _5N(_a5,_a3,B(_9v(_9X,_,_a7,_a9,_a4)));});}else{return new T4(0,_a2.a,E(new T3(0,_9X,_a7,_a9)),E(_a3),E(_a4));}}else{return new F(function(){return _6x(_a5,B(_9v(_9X,_,_a7,_a9,_a3)),_a4);});}}}else{return new F(function(){return _6x(_a5,B(_9I(_9X,_,_a7,_a0,_a3)),_a4);});}}}else{return new F(function(){return _6x(_a5,B(_9W(_9X,_,_9Z,_a0,_a3)),_a4);});}}else{return new T4(0,1,E(new T3(0,_9X,_9Z,_a0)),E(_5I),E(_5I));}},_ab=function(_ac,_ad,_ae,_af){var _ag=E(_af);if(!_ag._){var _ah=_ag.c,_ai=_ag.d,_aj=E(_ag.b),_ak=E(_ac),_al=E(_aj.a);if(_ak>=_al){if(_ak!=_al){return new F(function(){return _5N(_aj,_ah,B(_9W(_ak,_,_ad,_ae,_ai)));});}else{var _am=E(_ad),_an=E(_aj.b);if(_am>=_an){if(_am!=_an){return new F(function(){return _5N(_aj,_ah,B(_9I(_ak,_,_am,_ae,_ai)));});}else{var _ao=E(_ae),_ap=E(_aj.c);if(_ao>=_ap){if(_ao!=_ap){return new F(function(){return _5N(_aj,_ah,B(_9v(_ak,_,_am,_ao,_ai)));});}else{return new T4(0,_ag.a,E(new T3(0,_ak,_am,_ao)),E(_ah),E(_ai));}}else{return new F(function(){return _6x(_aj,B(_9v(_ak,_,_am,_ao,_ah)),_ai);});}}}else{return new F(function(){return _6x(_aj,B(_9I(_ak,_,_am,_ae,_ah)),_ai);});}}}else{return new F(function(){return _6x(_aj,B(_9W(_ak,_,_ad,_ae,_ah)),_ai);});}}else{return new T4(0,1,E(new T3(0,_ac,_ad,_ae)),E(_5I),E(_5I));}},_aq=function(_ar,_as){while(1){var _at=E(_as);if(!_at._){return E(_ar);}else{var _au=E(_at.a),_av=B(_ab(_au.a,_au.b,_au.c,_ar));_ar=_av;_as=_at.b;continue;}}},_aw=function(_ax,_ay,_az,_aA,_aB){return new F(function(){return _aq(B(_ab(_ay,_az,_aA,_ax)),_aB);});},_aC=function(_aD,_aE,_aF){var _aG=E(_aE);return new F(function(){return _aq(B(_ab(_aG.a,_aG.b,_aG.c,_aD)),_aF);});},_aH=function(_aI,_aJ,_aK){var _aL=E(_aK);if(!_aL._){return E(_aJ);}else{var _aM=_aL.a,_aN=E(_aL.b);if(!_aN._){return new F(function(){return _6p(_aM,_aJ);});}else{var _aO=E(_aM),_aP=_aO.b,_aQ=_aO.c,_aR=E(_aO.a),_aS=E(_aN.a),_aT=_aS.b,_aU=_aS.c,_aV=E(_aS.a),_aW=function(_aX){var _aY=B(_8t(_aI,_aV,_aT,_aU,_aN.b)),_aZ=_aY.a,_b0=E(_aY.c);if(!_b0._){return new F(function(){return _aH(_aI<<1,B(_7J(_aO,_aJ,_aZ)),_aY.b);});}else{return new F(function(){return _aC(B(_7J(_aO,_aJ,_aZ)),_b0.a,_b0.b);});}};if(_aR>=_aV){if(_aR!=_aV){return new F(function(){return _aw(_aJ,_aR,_aP,_aQ,_aN);});}else{var _b1=E(_aP),_b2=E(_aT);if(_b1>=_b2){if(_b1!=_b2){return new F(function(){return _aw(_aJ,_aR,_b1,_aQ,_aN);});}else{var _b3=E(_aQ);if(_b3<E(_aU)){return new F(function(){return _aW(_);});}else{return new F(function(){return _aw(_aJ,_aR,_b1,_b3,_aN);});}}}else{return new F(function(){return _aW(_);});}}}else{return new F(function(){return _aW(_);});}}}},_b4=function(_b5,_b6,_b7,_b8,_b9,_ba){var _bb=E(_ba);if(!_bb._){return new F(function(){return _6p(new T3(0,_b7,_b8,_b9),_b6);});}else{var _bc=E(_b7),_bd=E(_bb.a),_be=_bd.b,_bf=_bd.c,_bg=E(_bd.a),_bh=function(_bi){var _bj=B(_8t(_b5,_bg,_be,_bf,_bb.b)),_bk=_bj.a,_bl=E(_bj.c);if(!_bl._){return new F(function(){return _aH(_b5<<1,B(_7J(new T3(0,_bc,_b8,_b9),_b6,_bk)),_bj.b);});}else{return new F(function(){return _aC(B(_7J(new T3(0,_bc,_b8,_b9),_b6,_bk)),_bl.a,_bl.b);});}};if(_bc>=_bg){if(_bc!=_bg){return new F(function(){return _aw(_b6,_bc,_b8,_b9,_bb);});}else{var _bm=E(_be);if(_b8>=_bm){if(_b8!=_bm){return new F(function(){return _aw(_b6,_bc,_b8,_b9,_bb);});}else{var _bn=E(_b9);if(_bn<E(_bf)){return new F(function(){return _bh(_);});}else{return new F(function(){return _aw(_b6,_bc,_b8,_bn,_bb);});}}}else{return new F(function(){return _bh(_);});}}}else{return new F(function(){return _bh(_);});}}},_bo=function(_bp,_bq,_br,_bs,_bt,_bu){var _bv=E(_bu);if(!_bv._){return new F(function(){return _6p(new T3(0,_br,_bs,_bt),_bq);});}else{var _bw=E(_br),_bx=E(_bv.a),_by=_bx.b,_bz=_bx.c,_bA=E(_bx.a),_bB=function(_bC){var _bD=B(_8t(_bp,_bA,_by,_bz,_bv.b)),_bE=_bD.a,_bF=E(_bD.c);if(!_bF._){return new F(function(){return _aH(_bp<<1,B(_7J(new T3(0,_bw,_bs,_bt),_bq,_bE)),_bD.b);});}else{return new F(function(){return _aC(B(_7J(new T3(0,_bw,_bs,_bt),_bq,_bE)),_bF.a,_bF.b);});}};if(_bw>=_bA){if(_bw!=_bA){return new F(function(){return _aw(_bq,_bw,_bs,_bt,_bv);});}else{var _bG=E(_by);if(_bs>=_bG){if(_bs!=_bG){return new F(function(){return _aw(_bq,_bw,_bs,_bt,_bv);});}else{if(_bt<E(_bz)){return new F(function(){return _bB(_);});}else{return new F(function(){return _aw(_bq,_bw,_bs,_bt,_bv);});}}}else{return new F(function(){return _bB(_);});}}}else{return new F(function(){return _bB(_);});}}},_bH=function(_bI,_bJ,_bK,_bL,_bM,_bN){var _bO=E(_bN);if(!_bO._){return new F(function(){return _6p(new T3(0,_bK,_bL,_bM),_bJ);});}else{var _bP=E(_bK),_bQ=E(_bO.a),_bR=_bQ.b,_bS=_bQ.c,_bT=E(_bQ.a),_bU=function(_bV){var _bW=B(_8t(_bI,_bT,_bR,_bS,_bO.b)),_bX=_bW.a,_bY=E(_bW.c);if(!_bY._){return new F(function(){return _aH(_bI<<1,B(_7J(new T3(0,_bP,_bL,_bM),_bJ,_bX)),_bW.b);});}else{return new F(function(){return _aC(B(_7J(new T3(0,_bP,_bL,_bM),_bJ,_bX)),_bY.a,_bY.b);});}};if(_bP>=_bT){if(_bP!=_bT){return new F(function(){return _aw(_bJ,_bP,_bL,_bM,_bO);});}else{var _bZ=E(_bL),_c0=E(_bR);if(_bZ>=_c0){if(_bZ!=_c0){return new F(function(){return _aw(_bJ,_bP,_bZ,_bM,_bO);});}else{var _c1=E(_bM);if(_c1<E(_bS)){return new F(function(){return _bU(_);});}else{return new F(function(){return _aw(_bJ,_bP,_bZ,_c1,_bO);});}}}else{return new F(function(){return _bU(_);});}}}else{return new F(function(){return _bU(_);});}}},_c2=function(_c3){var _c4=E(_c3);if(!_c4._){return new T0(1);}else{var _c5=_c4.a,_c6=E(_c4.b);if(!_c6._){return new T4(0,1,E(_c5),E(_5I),E(_5I));}else{var _c7=_c6.b,_c8=E(_c5),_c9=E(_c8.a),_ca=E(_c6.a),_cb=_ca.b,_cc=_ca.c,_cd=E(_ca.a);if(_c9>=_cd){if(_c9!=_cd){return new F(function(){return _aw(new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cb,_cc,_c7);});}else{var _ce=E(_c8.b),_cf=E(_cb);if(_ce>=_cf){if(_ce!=_cf){return new F(function(){return _aw(new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cc,_c7);});}else{var _cg=E(_cc);if(E(_c8.c)<_cg){return new F(function(){return _bo(1,new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cg,_c7);});}else{return new F(function(){return _aw(new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cg,_c7);});}}}else{return new F(function(){return _b4(1,new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cc,_c7);});}}}else{return new F(function(){return _bH(1,new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cb,_cc,_c7);});}}}},_ch=function(_ci,_cj,_ck,_cl,_cm){var _cn=E(_ci);if(_cn==1){var _co=E(_cm);if(!_co._){return new T3(0,new T5(0,1,E(new T2(0,_cj,_ck)),_cl,E(_0),E(_0)),_1,_1);}else{var _cp=E(E(_co.a).a),_cq=E(_cj),_cr=E(_cp.a);return (_cq>=_cr)?(_cq!=_cr)?new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_1,_co):(_ck<E(_cp.b))?new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_co,_1):new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_1,_co):new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_co,_1);}}else{var _cs=B(_ch(_cn>>1,_cj,_ck,_cl,_cm)),_ct=_cs.a,_cu=_cs.c,_cv=E(_cs.b);if(!_cv._){return new T3(0,_ct,_1,_cu);}else{var _cw=E(_cv.a),_cx=_cw.a,_cy=_cw.b,_cz=E(_cv.b);if(!_cz._){return new T3(0,new T(function(){return B(_O(_cx,_cy,_ct));}),_1,_cu);}else{var _cA=_cz.b,_cB=E(_cz.a),_cC=_cB.b,_cD=E(_cx),_cE=E(_cB.a),_cF=_cE.b,_cG=E(_cD.a),_cH=E(_cE.a);if(_cG>=_cH){if(_cG!=_cH){return new T3(0,_ct,_1,_cv);}else{var _cI=E(_cF);if(E(_cD.b)<_cI){var _cJ=B(_ch(_cn>>1,_cH,_cI,_cC,_cA));return new T3(0,new T(function(){return B(_2h(_cD,_cy,_ct,_cJ.a));}),_cJ.b,_cJ.c);}else{return new T3(0,_ct,_1,_cv);}}}else{var _cK=B(_cL(_cn>>1,_cH,_cF,_cC,_cA));return new T3(0,new T(function(){return B(_2h(_cD,_cy,_ct,_cK.a));}),_cK.b,_cK.c);}}}}},_cL=function(_cM,_cN,_cO,_cP,_cQ){var _cR=E(_cM);if(_cR==1){var _cS=E(_cQ);if(!_cS._){return new T3(0,new T5(0,1,E(new T2(0,_cN,_cO)),_cP,E(_0),E(_0)),_1,_1);}else{var _cT=E(E(_cS.a).a),_cU=E(_cN),_cV=E(_cT.a);if(_cU>=_cV){if(_cU!=_cV){return new T3(0,new T5(0,1,E(new T2(0,_cU,_cO)),_cP,E(_0),E(_0)),_1,_cS);}else{var _cW=E(_cO);return (_cW<E(_cT.b))?new T3(0,new T5(0,1,E(new T2(0,_cU,_cW)),_cP,E(_0),E(_0)),_cS,_1):new T3(0,new T5(0,1,E(new T2(0,_cU,_cW)),_cP,E(_0),E(_0)),_1,_cS);}}else{return new T3(0,new T5(0,1,E(new T2(0,_cU,_cO)),_cP,E(_0),E(_0)),_cS,_1);}}}else{var _cX=B(_cL(_cR>>1,_cN,_cO,_cP,_cQ)),_cY=_cX.a,_cZ=_cX.c,_d0=E(_cX.b);if(!_d0._){return new T3(0,_cY,_1,_cZ);}else{var _d1=E(_d0.a),_d2=_d1.a,_d3=_d1.b,_d4=E(_d0.b);if(!_d4._){return new T3(0,new T(function(){return B(_O(_d2,_d3,_cY));}),_1,_cZ);}else{var _d5=_d4.b,_d6=E(_d4.a),_d7=_d6.b,_d8=E(_d2),_d9=E(_d6.a),_da=_d9.b,_db=E(_d8.a),_dc=E(_d9.a);if(_db>=_dc){if(_db!=_dc){return new T3(0,_cY,_1,_d0);}else{var _dd=E(_da);if(E(_d8.b)<_dd){var _de=B(_ch(_cR>>1,_dc,_dd,_d7,_d5));return new T3(0,new T(function(){return B(_2h(_d8,_d3,_cY,_de.a));}),_de.b,_de.c);}else{return new T3(0,_cY,_1,_d0);}}}else{var _df=B(_cL(_cR>>1,_dc,_da,_d7,_d5));return new T3(0,new T(function(){return B(_2h(_d8,_d3,_cY,_df.a));}),_df.b,_df.c);}}}}},_dg=function(_dh,_di,_dj,_dk,_dl){var _dm=E(_dl);if(!_dm._){var _dn=_dm.c,_do=_dm.d,_dp=_dm.e,_dq=E(_dm.b),_dr=E(_dq.a);if(_dh>=_dr){if(_dh!=_dr){return new F(function(){return _6(_dq,_dn,_do,B(_dg(_dh,_,_dj,_dk,_dp)));});}else{var _ds=E(_dq.b);if(_dj>=_ds){if(_dj!=_ds){return new F(function(){return _6(_dq,_dn,_do,B(_dg(_dh,_,_dj,_dk,_dp)));});}else{return new T5(0,_dm.a,E(new T2(0,_dh,_dj)),_dk,E(_do),E(_dp));}}else{return new F(function(){return _X(_dq,_dn,B(_dg(_dh,_,_dj,_dk,_do)),_dp);});}}}else{return new F(function(){return _X(_dq,_dn,B(_dg(_dh,_,_dj,_dk,_do)),_dp);});}}else{return new T5(0,1,E(new T2(0,_dh,_dj)),_dk,E(_0),E(_0));}},_dt=function(_du,_dv,_dw,_dx,_dy){var _dz=E(_dy);if(!_dz._){var _dA=_dz.c,_dB=_dz.d,_dC=_dz.e,_dD=E(_dz.b),_dE=E(_dD.a);if(_du>=_dE){if(_du!=_dE){return new F(function(){return _6(_dD,_dA,_dB,B(_dt(_du,_,_dw,_dx,_dC)));});}else{var _dF=E(_dw),_dG=E(_dD.b);if(_dF>=_dG){if(_dF!=_dG){return new F(function(){return _6(_dD,_dA,_dB,B(_dg(_du,_,_dF,_dx,_dC)));});}else{return new T5(0,_dz.a,E(new T2(0,_du,_dF)),_dx,E(_dB),E(_dC));}}else{return new F(function(){return _X(_dD,_dA,B(_dg(_du,_,_dF,_dx,_dB)),_dC);});}}}else{return new F(function(){return _X(_dD,_dA,B(_dt(_du,_,_dw,_dx,_dB)),_dC);});}}else{return new T5(0,1,E(new T2(0,_du,_dw)),_dx,E(_0),E(_0));}},_dH=function(_dI,_dJ,_dK,_dL){var _dM=E(_dL);if(!_dM._){var _dN=_dM.c,_dO=_dM.d,_dP=_dM.e,_dQ=E(_dM.b),_dR=E(_dI),_dS=E(_dQ.a);if(_dR>=_dS){if(_dR!=_dS){return new F(function(){return _6(_dQ,_dN,_dO,B(_dt(_dR,_,_dJ,_dK,_dP)));});}else{var _dT=E(_dJ),_dU=E(_dQ.b);if(_dT>=_dU){if(_dT!=_dU){return new F(function(){return _6(_dQ,_dN,_dO,B(_dg(_dR,_,_dT,_dK,_dP)));});}else{return new T5(0,_dM.a,E(new T2(0,_dR,_dT)),_dK,E(_dO),E(_dP));}}else{return new F(function(){return _X(_dQ,_dN,B(_dg(_dR,_,_dT,_dK,_dO)),_dP);});}}}else{return new F(function(){return _X(_dQ,_dN,B(_dt(_dR,_,_dJ,_dK,_dO)),_dP);});}}else{return new T5(0,1,E(new T2(0,_dI,_dJ)),_dK,E(_0),E(_0));}},_dV=function(_dW,_dX){while(1){var _dY=E(_dX);if(!_dY._){return E(_dW);}else{var _dZ=E(_dY.a),_e0=E(_dZ.a),_e1=B(_dH(_e0.a,_e0.b,_dZ.b,_dW));_dW=_e1;_dX=_dY.b;continue;}}},_e2=function(_e3,_e4,_e5,_e6,_e7){return new F(function(){return _dV(B(_dH(_e4,_e5,_e6,_e3)),_e7);});},_e8=function(_e9,_ea,_eb){var _ec=E(_ea),_ed=E(_ec.a);return new F(function(){return _dV(B(_dH(_ed.a,_ed.b,_ec.b,_e9)),_eb);});},_ee=function(_ef,_eg,_eh){var _ei=E(_eh);if(!_ei._){return E(_eg);}else{var _ej=E(_ei.a),_ek=_ej.a,_el=_ej.b,_em=E(_ei.b);if(!_em._){return new F(function(){return _O(_ek,_el,_eg);});}else{var _en=E(_em.a),_eo=E(_ek),_ep=_eo.b,_eq=E(_en.a),_er=_eq.b,_es=E(_eo.a),_et=E(_eq.a),_eu=function(_ev){var _ew=B(_cL(_ef,_et,_er,_en.b,_em.b)),_ex=_ew.a,_ey=E(_ew.c);if(!_ey._){return new F(function(){return _ee(_ef<<1,B(_2h(_eo,_el,_eg,_ex)),_ew.b);});}else{return new F(function(){return _e8(B(_2h(_eo,_el,_eg,_ex)),_ey.a,_ey.b);});}};if(_es>=_et){if(_es!=_et){return new F(function(){return _e2(_eg,_es,_ep,_el,_em);});}else{var _ez=E(_ep);if(_ez<E(_er)){return new F(function(){return _eu(_);});}else{return new F(function(){return _e2(_eg,_es,_ez,_el,_em);});}}}else{return new F(function(){return _eu(_);});}}}},_eA=function(_eB,_eC,_eD,_eE,_eF,_eG){var _eH=E(_eG);if(!_eH._){return new F(function(){return _O(new T2(0,_eD,_eE),_eF,_eC);});}else{var _eI=E(_eH.a),_eJ=E(_eI.a),_eK=_eJ.b,_eL=E(_eD),_eM=E(_eJ.a),_eN=function(_eO){var _eP=B(_cL(_eB,_eM,_eK,_eI.b,_eH.b)),_eQ=_eP.a,_eR=E(_eP.c);if(!_eR._){return new F(function(){return _ee(_eB<<1,B(_2h(new T2(0,_eL,_eE),_eF,_eC,_eQ)),_eP.b);});}else{return new F(function(){return _e8(B(_2h(new T2(0,_eL,_eE),_eF,_eC,_eQ)),_eR.a,_eR.b);});}};if(_eL>=_eM){if(_eL!=_eM){return new F(function(){return _e2(_eC,_eL,_eE,_eF,_eH);});}else{var _eS=E(_eE);if(_eS<E(_eK)){return new F(function(){return _eN(_);});}else{return new F(function(){return _e2(_eC,_eL,_eS,_eF,_eH);});}}}else{return new F(function(){return _eN(_);});}}},_eT=function(_eU,_eV,_eW,_eX,_eY,_eZ){var _f0=E(_eZ);if(!_f0._){return new F(function(){return _O(new T2(0,_eW,_eX),_eY,_eV);});}else{var _f1=E(_f0.a),_f2=E(_f1.a),_f3=_f2.b,_f4=E(_eW),_f5=E(_f2.a),_f6=function(_f7){var _f8=B(_cL(_eU,_f5,_f3,_f1.b,_f0.b)),_f9=_f8.a,_fa=E(_f8.c);if(!_fa._){return new F(function(){return _ee(_eU<<1,B(_2h(new T2(0,_f4,_eX),_eY,_eV,_f9)),_f8.b);});}else{return new F(function(){return _e8(B(_2h(new T2(0,_f4,_eX),_eY,_eV,_f9)),_fa.a,_fa.b);});}};if(_f4>=_f5){if(_f4!=_f5){return new F(function(){return _e2(_eV,_f4,_eX,_eY,_f0);});}else{if(_eX<E(_f3)){return new F(function(){return _f6(_);});}else{return new F(function(){return _e2(_eV,_f4,_eX,_eY,_f0);});}}}else{return new F(function(){return _f6(_);});}}},_fb=function(_fc){var _fd=E(_fc);if(!_fd._){return new T0(1);}else{var _fe=E(_fd.a),_ff=_fe.a,_fg=_fe.b,_fh=E(_fd.b);if(!_fh._){return new T5(0,1,E(_ff),_fg,E(_0),E(_0));}else{var _fi=_fh.b,_fj=E(_fh.a),_fk=_fj.b,_fl=E(_ff),_fm=E(_fj.a),_fn=_fm.b,_fo=E(_fl.a),_fp=E(_fm.a);if(_fo>=_fp){if(_fo!=_fp){return new F(function(){return _e2(new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fn,_fk,_fi);});}else{var _fq=E(_fn);if(E(_fl.b)<_fq){return new F(function(){return _eT(1,new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fq,_fk,_fi);});}else{return new F(function(){return _e2(new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fq,_fk,_fi);});}}}else{return new F(function(){return _eA(1,new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fn,_fk,_fi);});}}}},_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=E(_fw);if(!_fx._){var _fy=_fx.c,_fz=_fx.d,_fA=E(_fx.b),_fB=E(_fs),_fC=E(_fA.a);if(_fB>=_fC){if(_fB!=_fC){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_ft,_fu,_fv,_fz)));});}else{var _fD=E(_ft),_fE=E(_fA.b);if(_fD>=_fE){if(_fD!=_fE){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_fD,_fu,_fv,_fz)));});}else{var _fF=E(_fu),_fG=E(_fA.c);if(_fF>=_fG){if(_fF!=_fG){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_fD,_fF,_fv,_fz)));});}else{var _fH=E(_fv),_fI=E(_fA.d);if(_fH>=_fI){if(_fH!=_fI){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_fD,_fF,_fH,_fz)));});}else{return new T4(0,_fx.a,E(new T4(0,_fB,_fD,_fF,_fH)),E(_fy),E(_fz));}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_fD,_fF,_fH,_fy)),_fz);});}}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_fD,_fF,_fv,_fy)),_fz);});}}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_fD,_fu,_fv,_fy)),_fz);});}}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_ft,_fu,_fv,_fy)),_fz);});}}else{return new T4(0,1,E(new T4(0,_fs,_ft,_fu,_fv)),E(_5I),E(_5I));}},_fJ=function(_fK,_fL){while(1){var _fM=E(_fL);if(!_fM._){return E(_fK);}else{var _fN=E(_fM.a),_fO=B(_fr(_fN.a,_fN.b,_fN.c,_fN.d,_fK));_fK=_fO;_fL=_fM.b;continue;}}},_fP=function(_fQ,_fR,_fS,_fT,_fU,_fV){return new F(function(){return _fJ(B(_fr(_fR,_fS,_fT,_fU,_fQ)),_fV);});},_fW=function(_fX,_fY){var _fZ=E(_fY);if(!_fZ._){return new T3(0,_5I,_1,_1);}else{var _g0=_fZ.a,_g1=E(_fX);if(_g1==1){var _g2=E(_fZ.b);if(!_g2._){return new T3(0,new T(function(){return new T4(0,1,E(_g0),E(_5I),E(_5I));}),_1,_1);}else{var _g3=E(_g0),_g4=E(_g3.a),_g5=E(_g2.a),_g6=E(_g5.a);if(_g4>=_g6){if(_g4!=_g6){return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2);}else{var _g7=E(_g3.b),_g8=E(_g5.b);if(_g7>=_g8){if(_g7!=_g8){return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2);}else{var _g9=E(_g3.c),_ga=E(_g5.c);return (_g9>=_ga)?(_g9!=_ga)?new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2):(E(_g3.d)<E(_g5.d))?new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1):new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2):new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1);}}else{return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1);}}}else{return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1);}}}else{var _gb=B(_fW(_g1>>1,_fZ)),_gc=_gb.a,_gd=_gb.c,_ge=E(_gb.b);if(!_ge._){return new T3(0,_gc,_1,_gd);}else{var _gf=_ge.a,_gg=E(_ge.b);if(!_gg._){return new T3(0,new T(function(){return B(_6p(_gf,_gc));}),_1,_gd);}else{var _gh=E(_gf),_gi=E(_gh.a),_gj=E(_gg.a),_gk=E(_gj.a);if(_gi>=_gk){if(_gi!=_gk){return new T3(0,_gc,_1,_ge);}else{var _gl=E(_gh.b),_gm=E(_gj.b);if(_gl>=_gm){if(_gl!=_gm){return new T3(0,_gc,_1,_ge);}else{var _gn=E(_gh.c),_go=E(_gj.c);if(_gn>=_go){if(_gn!=_go){return new T3(0,_gc,_1,_ge);}else{if(E(_gh.d)<E(_gj.d)){var _gp=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gp.a));}),_gp.b,_gp.c);}else{return new T3(0,_gc,_1,_ge);}}}else{var _gq=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gq.a));}),_gq.b,_gq.c);}}}else{var _gr=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gr.a));}),_gr.b,_gr.c);}}}else{var _gs=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gs.a));}),_gs.b,_gs.c);}}}}}},_gt=function(_gu,_gv,_gw){var _gx=E(_gw);if(!_gx._){return E(_gv);}else{var _gy=_gx.a,_gz=E(_gx.b);if(!_gz._){return new F(function(){return _6p(_gy,_gv);});}else{var _gA=E(_gy),_gB=_gA.b,_gC=_gA.c,_gD=_gA.d,_gE=E(_gA.a),_gF=E(_gz.a),_gG=E(_gF.a),_gH=function(_gI){var _gJ=B(_fW(_gu,_gz)),_gK=_gJ.a,_gL=E(_gJ.c);if(!_gL._){return new F(function(){return _gt(_gu<<1,B(_7J(_gA,_gv,_gK)),_gJ.b);});}else{return new F(function(){return _fJ(B(_7J(_gA,_gv,_gK)),_gL);});}};if(_gE>=_gG){if(_gE!=_gG){return new F(function(){return _fP(_gv,_gE,_gB,_gC,_gD,_gz);});}else{var _gM=E(_gB),_gN=E(_gF.b);if(_gM>=_gN){if(_gM!=_gN){return new F(function(){return _fP(_gv,_gE,_gM,_gC,_gD,_gz);});}else{var _gO=E(_gC),_gP=E(_gF.c);if(_gO>=_gP){if(_gO!=_gP){return new F(function(){return _fP(_gv,_gE,_gM,_gO,_gD,_gz);});}else{var _gQ=E(_gD);if(_gQ<E(_gF.d)){return new F(function(){return _gH(_);});}else{return new F(function(){return _fP(_gv,_gE,_gM,_gO,_gQ,_gz);});}}}else{return new F(function(){return _gH(_);});}}}else{return new F(function(){return _gH(_);});}}}else{return new F(function(){return _gH(_);});}}}},_gR=function(_gS){var _gT=E(_gS);if(!_gT._){return new T0(1);}else{var _gU=_gT.a,_gV=E(_gT.b);if(!_gV._){return new T4(0,1,E(_gU),E(_5I),E(_5I));}else{var _gW=_gV.b,_gX=E(_gU),_gY=E(_gX.a),_gZ=E(_gV.a),_h0=_gZ.b,_h1=_gZ.c,_h2=_gZ.d,_h3=E(_gZ.a);if(_gY>=_h3){if(_gY!=_h3){return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h0,_h1,_h2,_gW);});}else{var _h4=E(_gX.b),_h5=E(_h0);if(_h4>=_h5){if(_h4!=_h5){return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h5,_h1,_h2,_gW);});}else{var _h6=E(_gX.c),_h7=E(_h1);if(_h6>=_h7){if(_h6!=_h7){return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h5,_h7,_h2,_gW);});}else{var _h8=E(_h2);if(E(_gX.d)<_h8){return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}else{return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h5,_h7,_h8,_gW);});}}}else{return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}}}else{return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}}}else{return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}}}},_h9=0,_ha=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_hb=new T(function(){return B(err(_ha));}),_hc=function(_hd,_he){while(1){var _hf=B((function(_hg,_hh){var _hi=E(_hh);if(!_hi._){_hd=new T2(1,new T2(0,_hi.b,_hi.c),new T(function(){return B(_hc(_hg,_hi.e));}));_he=_hi.d;return __continue;}else{return E(_hg);}})(_hd,_he));if(_hf!=__continue){return _hf;}}},_hj=44,_hk=function(_hl,_hm,_hn){return new F(function(){return A1(_hl,new T2(1,_hj,new T(function(){return B(A1(_hm,_hn));})));});},_ho=new T(function(){return B(unCStr("CC "));}),_hp=new T(function(){return B(unCStr("IdentCC "));}),_hq=function(_hr,_hs){var _ht=E(_hr);return (_ht._==0)?E(_hs):new T2(1,_ht.a,new T(function(){return B(_hq(_ht.b,_hs));}));},_hu=function(_hv,_hw){var _hx=jsShowI(_hv);return new F(function(){return _hq(fromJSStr(_hx),_hw);});},_hy=41,_hz=40,_hA=function(_hB,_hC,_hD){if(_hC>=0){return new F(function(){return _hu(_hC,_hD);});}else{if(_hB<=6){return new F(function(){return _hu(_hC,_hD);});}else{return new T2(1,_hz,new T(function(){var _hE=jsShowI(_hC);return B(_hq(fromJSStr(_hE),new T2(1,_hy,_hD)));}));}}},_hF=function(_hG,_hH,_hI){if(_hG<11){return new F(function(){return _hq(_hp,new T(function(){return B(_hA(11,E(_hH),_hI));},1));});}else{var _hJ=new T(function(){return B(_hq(_hp,new T(function(){return B(_hA(11,E(_hH),new T2(1,_hy,_hI)));},1)));});return new T2(1,_hz,_hJ);}},_hK=32,_hL=function(_hM,_hN,_hO,_hP,_hQ,_hR){var _hS=function(_hT){var _hU=new T(function(){var _hV=new T(function(){return B(_hA(11,E(_hP),new T2(1,_hK,new T(function(){return B(_hA(11,E(_hQ),_hT));}))));});return B(_hA(11,E(_hO),new T2(1,_hK,_hV)));});return new F(function(){return _hF(11,_hN,new T2(1,_hK,_hU));});};if(_hM<11){return new F(function(){return _hq(_ho,new T(function(){return B(_hS(_hR));},1));});}else{var _hW=new T(function(){return B(_hq(_ho,new T(function(){return B(_hS(new T2(1,_hy,_hR)));},1)));});return new T2(1,_hz,_hW);}},_hX=function(_hY,_hZ){var _i0=E(_hY);return new F(function(){return _hL(0,_i0.a,_i0.b,_i0.c,_i0.d,_hZ);});},_i1=new T(function(){return B(unCStr("RC "));}),_i2=function(_i3,_i4,_i5,_i6,_i7){var _i8=function(_i9){var _ia=new T(function(){var _ib=new T(function(){return B(_hA(11,E(_i5),new T2(1,_hK,new T(function(){return B(_hA(11,E(_i6),_i9));}))));});return B(_hF(11,_i4,new T2(1,_hK,_ib)));},1);return new F(function(){return _hq(_i1,_ia);});};if(_i3<11){return new F(function(){return _i8(_i7);});}else{return new T2(1,_hz,new T(function(){return B(_i8(new T2(1,_hy,_i7)));}));}},_ic=function(_id,_ie){var _if=E(_id);return new F(function(){return _i2(0,_if.a,_if.b,_if.c,_ie);});},_ig=new T(function(){return B(unCStr("IdentPay "));}),_ih=function(_ii,_ij,_ik){if(_ii<11){return new F(function(){return _hq(_ig,new T(function(){return B(_hA(11,E(_ij),_ik));},1));});}else{var _il=new T(function(){return B(_hq(_ig,new T(function(){return B(_hA(11,E(_ij),new T2(1,_hy,_ik)));},1)));});return new T2(1,_hz,_il);}},_im=new T(function(){return B(unCStr(": empty list"));}),_in=new T(function(){return B(unCStr("Prelude."));}),_io=function(_ip){return new F(function(){return err(B(_hq(_in,new T(function(){return B(_hq(_ip,_im));},1))));});},_iq=new T(function(){return B(unCStr("foldr1"));}),_ir=new T(function(){return B(_io(_iq));}),_is=function(_it,_iu){var _iv=E(_iu);if(!_iv._){return E(_ir);}else{var _iw=_iv.a,_ix=E(_iv.b);if(!_ix._){return E(_iw);}else{return new F(function(){return A2(_it,_iw,new T(function(){return B(_is(_it,_ix));}));});}}},_iy=function(_iz,_iA,_iB){var _iC=new T(function(){var _iD=function(_iE){var _iF=E(_iz),_iG=new T(function(){return B(A3(_is,_hk,new T2(1,function(_iH){return new F(function(){return _ih(0,_iF.a,_iH);});},new T2(1,function(_iI){return new F(function(){return _hA(0,E(_iF.b),_iI);});},_1)),new T2(1,_hy,_iE)));});return new T2(1,_hz,_iG);};return B(A3(_is,_hk,new T2(1,_iD,new T2(1,function(_iJ){return new F(function(){return _hA(0,E(_iA),_iJ);});},_1)),new T2(1,_hy,_iB)));});return new T2(0,_hz,_iC);},_iK=function(_iL,_iM){var _iN=E(_iL),_iO=B(_iy(_iN.a,_iN.b,_iM));return new T2(1,_iO.a,_iO.b);},_iP=93,_iQ=91,_iR=function(_iS,_iT,_iU){var _iV=E(_iT);if(!_iV._){return new F(function(){return unAppCStr("[]",_iU);});}else{var _iW=new T(function(){var _iX=new T(function(){var _iY=function(_iZ){var _j0=E(_iZ);if(!_j0._){return E(new T2(1,_iP,_iU));}else{var _j1=new T(function(){return B(A2(_iS,_j0.a,new T(function(){return B(_iY(_j0.b));})));});return new T2(1,_hj,_j1);}};return B(_iY(_iV.b));});return B(A2(_iS,_iV.a,_iX));});return new T2(1,_iQ,_iW);}},_j2=function(_j3,_j4){return new F(function(){return _iR(_iK,_j3,_j4);});},_j5=new T(function(){return B(unCStr("IdentChoice "));}),_j6=function(_j7,_j8,_j9){if(_j7<11){return new F(function(){return _hq(_j5,new T(function(){return B(_hA(11,E(_j8),_j9));},1));});}else{var _ja=new T(function(){return B(_hq(_j5,new T(function(){return B(_hA(11,E(_j8),new T2(1,_hy,_j9)));},1)));});return new T2(1,_hz,_ja);}},_jb=function(_jc,_jd,_je){var _jf=new T(function(){var _jg=function(_jh){var _ji=E(_jc),_jj=new T(function(){return B(A3(_is,_hk,new T2(1,function(_jk){return new F(function(){return _j6(0,_ji.a,_jk);});},new T2(1,function(_jl){return new F(function(){return _hA(0,E(_ji.b),_jl);});},_1)),new T2(1,_hy,_jh)));});return new T2(1,_hz,_jj);};return B(A3(_is,_hk,new T2(1,_jg,new T2(1,function(_jm){return new F(function(){return _hA(0,E(_jd),_jm);});},_1)),new T2(1,_hy,_je)));});return new T2(0,_hz,_jf);},_jn=function(_jo,_jp){var _jq=E(_jo),_jr=B(_jb(_jq.a,_jq.b,_jp));return new T2(1,_jr.a,_jr.b);},_js=function(_jt,_ju){return new F(function(){return _iR(_jn,_jt,_ju);});},_jv=new T2(1,_hy,_1),_jw=function(_jx,_jy){while(1){var _jz=B((function(_jA,_jB){var _jC=E(_jB);if(!_jC._){_jx=new T2(1,_jC.b,new T(function(){return B(_jw(_jA,_jC.d));}));_jy=_jC.c;return __continue;}else{return E(_jA);}})(_jx,_jy));if(_jz!=__continue){return _jz;}}},_jD=function(_jE,_jF,_jG,_jH){var _jI=new T(function(){var _jJ=new T(function(){return B(_hc(_1,_jH));}),_jK=new T(function(){return B(_hc(_1,_jG));}),_jL=new T(function(){return B(_jw(_1,_jF));}),_jM=new T(function(){return B(_jw(_1,_jE));});return B(A3(_is,_hk,new T2(1,function(_jN){return new F(function(){return _iR(_hX,_jM,_jN);});},new T2(1,function(_jO){return new F(function(){return _iR(_ic,_jL,_jO);});},new T2(1,function(_jP){return new F(function(){return _j2(_jK,_jP);});},new T2(1,function(_jQ){return new F(function(){return _js(_jJ,_jQ);});},_1)))),_jv));});return new T2(0,_hz,_jI);},_jR=new T(function(){return B(err(_ha));}),_jS=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jT=new T(function(){return B(err(_jS));}),_jU=new T0(2),_jV=function(_jW){return new T2(3,_jW,_jU);},_jX=new T(function(){return B(unCStr("base"));}),_jY=new T(function(){return B(unCStr("Control.Exception.Base"));}),_jZ=new T(function(){return B(unCStr("PatternMatchFail"));}),_k0=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_jX,_jY,_jZ),_k1=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_k0,_1,_1),_k2=function(_k3){return E(_k1);},_k4=function(_k5){return E(E(_k5).a);},_k6=function(_k7,_k8,_k9){var _ka=B(A1(_k7,_)),_kb=B(A1(_k8,_)),_kc=hs_eqWord64(_ka.a,_kb.a);if(!_kc){return __Z;}else{var _kd=hs_eqWord64(_ka.b,_kb.b);return (!_kd)?__Z:new T1(1,_k9);}},_ke=function(_kf){var _kg=E(_kf);return new F(function(){return _k6(B(_k4(_kg.a)),_k2,_kg.b);});},_kh=function(_ki){return E(E(_ki).a);},_kj=function(_kk){return new T2(0,_kl,_kk);},_km=function(_kn,_ko){return new F(function(){return _hq(E(_kn).a,_ko);});},_kp=function(_kq,_kr){return new F(function(){return _iR(_km,_kq,_kr);});},_ks=function(_kt,_ku,_kv){return new F(function(){return _hq(E(_ku).a,_kv);});},_kw=new T3(0,_ks,_kh,_kp),_kl=new T(function(){return new T5(0,_k2,_kw,_kj,_ke,_kh);}),_kx=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_ky=function(_kz){return E(E(_kz).c);},_kA=function(_kB,_kC){return new F(function(){return die(new T(function(){return B(A2(_ky,_kC,_kB));}));});},_kD=function(_kE,_kF){return new F(function(){return _kA(_kE,_kF);});},_kG=function(_kH,_kI){var _kJ=E(_kI);if(!_kJ._){return new T2(0,_1,_1);}else{var _kK=_kJ.a;if(!B(A1(_kH,_kK))){return new T2(0,_1,_kJ);}else{var _kL=new T(function(){var _kM=B(_kG(_kH,_kJ.b));return new T2(0,_kM.a,_kM.b);});return new T2(0,new T2(1,_kK,new T(function(){return E(E(_kL).a);})),new T(function(){return E(E(_kL).b);}));}}},_kN=32,_kO=new T(function(){return B(unCStr("\n"));}),_kP=function(_kQ){return (E(_kQ)==124)?false:true;},_kR=function(_kS,_kT){var _kU=B(_kG(_kP,B(unCStr(_kS)))),_kV=_kU.a,_kW=function(_kX,_kY){var _kZ=new T(function(){var _l0=new T(function(){return B(_hq(_kT,new T(function(){return B(_hq(_kY,_kO));},1)));});return B(unAppCStr(": ",_l0));},1);return new F(function(){return _hq(_kX,_kZ);});},_l1=E(_kU.b);if(!_l1._){return new F(function(){return _kW(_kV,_1);});}else{if(E(_l1.a)==124){return new F(function(){return _kW(_kV,new T2(1,_kN,_l1.b));});}else{return new F(function(){return _kW(_kV,_1);});}}},_l2=function(_l3){return new F(function(){return _kD(new T1(0,new T(function(){return B(_kR(_l3,_kx));})),_kl);});},_l4=new T(function(){return B(_l2("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_l5=function(_l6,_l7){while(1){var _l8=B((function(_l9,_la){var _lb=E(_l9);switch(_lb._){case 0:var _lc=E(_la);if(!_lc._){return __Z;}else{_l6=B(A1(_lb.a,_lc.a));_l7=_lc.b;return __continue;}break;case 1:var _ld=B(A1(_lb.a,_la)),_le=_la;_l6=_ld;_l7=_le;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_lb.a,_la),new T(function(){return B(_l5(_lb.b,_la));}));default:return E(_lb.a);}})(_l6,_l7));if(_l8!=__continue){return _l8;}}},_lf=function(_lg,_lh){var _li=function(_lj){var _lk=E(_lh);if(_lk._==3){return new T2(3,_lk.a,new T(function(){return B(_lf(_lg,_lk.b));}));}else{var _ll=E(_lg);if(_ll._==2){return E(_lk);}else{var _lm=E(_lk);if(_lm._==2){return E(_ll);}else{var _ln=function(_lo){var _lp=E(_lm);if(_lp._==4){var _lq=function(_lr){return new T1(4,new T(function(){return B(_hq(B(_l5(_ll,_lr)),_lp.a));}));};return new T1(1,_lq);}else{var _ls=E(_ll);if(_ls._==1){var _lt=_ls.a,_lu=E(_lp);if(!_lu._){return new T1(1,function(_lv){return new F(function(){return _lf(B(A1(_lt,_lv)),_lu);});});}else{var _lw=function(_lx){return new F(function(){return _lf(B(A1(_lt,_lx)),new T(function(){return B(A1(_lu.a,_lx));}));});};return new T1(1,_lw);}}else{var _ly=E(_lp);if(!_ly._){return E(_l4);}else{var _lz=function(_lA){return new F(function(){return _lf(_ls,new T(function(){return B(A1(_ly.a,_lA));}));});};return new T1(1,_lz);}}}},_lB=E(_ll);switch(_lB._){case 1:var _lC=E(_lm);if(_lC._==4){var _lD=function(_lE){return new T1(4,new T(function(){return B(_hq(B(_l5(B(A1(_lB.a,_lE)),_lE)),_lC.a));}));};return new T1(1,_lD);}else{return new F(function(){return _ln(_);});}break;case 4:var _lF=_lB.a,_lG=E(_lm);switch(_lG._){case 0:var _lH=function(_lI){var _lJ=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(_lG,_lI));},1)));});return new T1(4,_lJ);};return new T1(1,_lH);case 1:var _lK=function(_lL){var _lM=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(B(A1(_lG.a,_lL)),_lL));},1)));});return new T1(4,_lM);};return new T1(1,_lK);default:return new T1(4,new T(function(){return B(_hq(_lF,_lG.a));}));}break;default:return new F(function(){return _ln(_);});}}}}},_lN=E(_lg);switch(_lN._){case 0:var _lO=E(_lh);if(!_lO._){var _lP=function(_lQ){return new F(function(){return _lf(B(A1(_lN.a,_lQ)),new T(function(){return B(A1(_lO.a,_lQ));}));});};return new T1(0,_lP);}else{return new F(function(){return _li(_);});}break;case 3:return new T2(3,_lN.a,new T(function(){return B(_lf(_lN.b,_lh));}));default:return new F(function(){return _li(_);});}},_lR=new T(function(){return B(unCStr("("));}),_lS=new T(function(){return B(unCStr(")"));}),_lT=function(_lU,_lV){while(1){var _lW=E(_lU);if(!_lW._){return (E(_lV)._==0)?true:false;}else{var _lX=E(_lV);if(!_lX._){return false;}else{if(E(_lW.a)!=E(_lX.a)){return false;}else{_lU=_lW.b;_lV=_lX.b;continue;}}}}},_lY=function(_lZ,_m0){return E(_lZ)!=E(_m0);},_m1=function(_m2,_m3){return E(_m2)==E(_m3);},_m4=new T2(0,_m1,_lY),_m5=function(_m6,_m7){while(1){var _m8=E(_m6);if(!_m8._){return (E(_m7)._==0)?true:false;}else{var _m9=E(_m7);if(!_m9._){return false;}else{if(E(_m8.a)!=E(_m9.a)){return false;}else{_m6=_m8.b;_m7=_m9.b;continue;}}}}},_ma=function(_mb,_mc){return (!B(_m5(_mb,_mc)))?true:false;},_md=new T2(0,_m5,_ma),_me=function(_mf,_mg){var _mh=E(_mf);switch(_mh._){case 0:return new T1(0,function(_mi){return new F(function(){return _me(B(A1(_mh.a,_mi)),_mg);});});case 1:return new T1(1,function(_mj){return new F(function(){return _me(B(A1(_mh.a,_mj)),_mg);});});case 2:return new T0(2);case 3:return new F(function(){return _lf(B(A1(_mg,_mh.a)),new T(function(){return B(_me(_mh.b,_mg));}));});break;default:var _mk=function(_ml){var _mm=E(_ml);if(!_mm._){return __Z;}else{var _mn=E(_mm.a);return new F(function(){return _hq(B(_l5(B(A1(_mg,_mn.a)),_mn.b)),new T(function(){return B(_mk(_mm.b));},1));});}},_mo=B(_mk(_mh.a));return (_mo._==0)?new T0(2):new T1(4,_mo);}},_mp=function(_mq,_mr){var _ms=E(_mq);if(!_ms){return new F(function(){return A1(_mr,_h9);});}else{var _mt=new T(function(){return B(_mp(_ms-1|0,_mr));});return new T1(0,function(_mu){return E(_mt);});}},_mv=function(_mw,_mx,_my){var _mz=new T(function(){return B(A1(_mw,_jV));}),_mA=function(_mB,_mC,_mD,_mE){while(1){var _mF=B((function(_mG,_mH,_mI,_mJ){var _mK=E(_mG);switch(_mK._){case 0:var _mL=E(_mH);if(!_mL._){return new F(function(){return A1(_mx,_mJ);});}else{var _mM=_mI+1|0,_mN=_mJ;_mB=B(A1(_mK.a,_mL.a));_mC=_mL.b;_mD=_mM;_mE=_mN;return __continue;}break;case 1:var _mO=B(A1(_mK.a,_mH)),_mP=_mH,_mM=_mI,_mN=_mJ;_mB=_mO;_mC=_mP;_mD=_mM;_mE=_mN;return __continue;case 2:return new F(function(){return A1(_mx,_mJ);});break;case 3:var _mQ=new T(function(){return B(_me(_mK,_mJ));});return new F(function(){return _mp(_mI,function(_mR){return E(_mQ);});});break;default:return new F(function(){return _me(_mK,_mJ);});}})(_mB,_mC,_mD,_mE));if(_mF!=__continue){return _mF;}}};return function(_mS){return new F(function(){return _mA(_mz,_mS,0,_my);});};},_mT=function(_mU){return new F(function(){return A1(_mU,_1);});},_mV=function(_mW,_mX){var _mY=function(_mZ){var _n0=E(_mZ);if(!_n0._){return E(_mT);}else{var _n1=_n0.a;if(!B(A1(_mW,_n1))){return E(_mT);}else{var _n2=new T(function(){return B(_mY(_n0.b));}),_n3=function(_n4){var _n5=new T(function(){return B(A1(_n2,function(_n6){return new F(function(){return A1(_n4,new T2(1,_n1,_n6));});}));});return new T1(0,function(_n7){return E(_n5);});};return E(_n3);}}};return function(_n8){return new F(function(){return A2(_mY,_n8,_mX);});};},_n9=new T0(6),_na=function(_nb){return E(_nb);},_nc=new T(function(){return B(unCStr("valDig: Bad base"));}),_nd=new T(function(){return B(err(_nc));}),_ne=function(_nf,_ng){var _nh=function(_ni,_nj){var _nk=E(_ni);if(!_nk._){var _nl=new T(function(){return B(A1(_nj,_1));});return function(_nm){return new F(function(){return A1(_nm,_nl);});};}else{var _nn=E(_nk.a),_no=function(_np){var _nq=new T(function(){return B(_nh(_nk.b,function(_nr){return new F(function(){return A1(_nj,new T2(1,_np,_nr));});}));}),_ns=function(_nt){var _nu=new T(function(){return B(A1(_nq,_nt));});return new T1(0,function(_nv){return E(_nu);});};return E(_ns);};switch(E(_nf)){case 8:if(48>_nn){var _nw=new T(function(){return B(A1(_nj,_1));});return function(_nx){return new F(function(){return A1(_nx,_nw);});};}else{if(_nn>55){var _ny=new T(function(){return B(A1(_nj,_1));});return function(_nz){return new F(function(){return A1(_nz,_ny);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 10:if(48>_nn){var _nA=new T(function(){return B(A1(_nj,_1));});return function(_nB){return new F(function(){return A1(_nB,_nA);});};}else{if(_nn>57){var _nC=new T(function(){return B(A1(_nj,_1));});return function(_nD){return new F(function(){return A1(_nD,_nC);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 16:if(48>_nn){if(97>_nn){if(65>_nn){var _nE=new T(function(){return B(A1(_nj,_1));});return function(_nF){return new F(function(){return A1(_nF,_nE);});};}else{if(_nn>70){var _nG=new T(function(){return B(A1(_nj,_1));});return function(_nH){return new F(function(){return A1(_nH,_nG);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nI=new T(function(){return B(A1(_nj,_1));});return function(_nJ){return new F(function(){return A1(_nJ,_nI);});};}else{if(_nn>70){var _nK=new T(function(){return B(A1(_nj,_1));});return function(_nL){return new F(function(){return A1(_nL,_nK);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{if(_nn>57){if(97>_nn){if(65>_nn){var _nM=new T(function(){return B(A1(_nj,_1));});return function(_nN){return new F(function(){return A1(_nN,_nM);});};}else{if(_nn>70){var _nO=new T(function(){return B(A1(_nj,_1));});return function(_nP){return new F(function(){return A1(_nP,_nO);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nQ=new T(function(){return B(A1(_nj,_1));});return function(_nR){return new F(function(){return A1(_nR,_nQ);});};}else{if(_nn>70){var _nS=new T(function(){return B(A1(_nj,_1));});return function(_nT){return new F(function(){return A1(_nT,_nS);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{return new F(function(){return _no(_nn-48|0);});}}break;default:return E(_nd);}}},_nU=function(_nV){var _nW=E(_nV);if(!_nW._){return new T0(2);}else{return new F(function(){return A1(_ng,_nW);});}};return function(_nX){return new F(function(){return A3(_nh,_nX,_na,_nU);});};},_nY=16,_nZ=8,_o0=function(_o1){var _o2=function(_o3){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nZ,_o3)));});},_o4=function(_o5){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nY,_o5)));});},_o6=function(_o7){switch(E(_o7)){case 79:return new T1(1,B(_ne(_nZ,_o2)));case 88:return new T1(1,B(_ne(_nY,_o4)));case 111:return new T1(1,B(_ne(_nZ,_o2)));case 120:return new T1(1,B(_ne(_nY,_o4)));default:return new T0(2);}};return function(_o8){return (E(_o8)==48)?E(new T1(0,_o6)):new T0(2);};},_o9=function(_oa){return new T1(0,B(_o0(_oa)));},_ob=__Z,_oc=function(_od){return new F(function(){return A1(_od,_ob);});},_oe=function(_of){return new F(function(){return A1(_of,_ob);});},_og=10,_oh=new T1(0,1),_oi=new T1(0,2147483647),_oj=function(_ok,_ol){while(1){var _om=E(_ok);if(!_om._){var _on=_om.a,_oo=E(_ol);if(!_oo._){var _op=_oo.a,_oq=addC(_on,_op);if(!E(_oq.b)){return new T1(0,_oq.a);}else{_ok=new T1(1,I_fromInt(_on));_ol=new T1(1,I_fromInt(_op));continue;}}else{_ok=new T1(1,I_fromInt(_on));_ol=_oo;continue;}}else{var _or=E(_ol);if(!_or._){_ok=_om;_ol=new T1(1,I_fromInt(_or.a));continue;}else{return new T1(1,I_add(_om.a,_or.a));}}}},_os=new T(function(){return B(_oj(_oi,_oh));}),_ot=function(_ou){var _ov=E(_ou);if(!_ov._){var _ow=E(_ov.a);return (_ow==( -2147483648))?E(_os):new T1(0, -_ow);}else{return new T1(1,I_negate(_ov.a));}},_ox=new T1(0,10),_oy=function(_oz,_oA){while(1){var _oB=E(_oz);if(!_oB._){return E(_oA);}else{var _oC=_oA+1|0;_oz=_oB.b;_oA=_oC;continue;}}},_oD=function(_oE,_oF){var _oG=E(_oF);return (_oG._==0)?__Z:new T2(1,new T(function(){return B(A1(_oE,_oG.a));}),new T(function(){return B(_oD(_oE,_oG.b));}));},_oH=function(_oI){return new T1(0,_oI);},_oJ=function(_oK){return new F(function(){return _oH(E(_oK));});},_oL=new T(function(){return B(unCStr("this should not happen"));}),_oM=new T(function(){return B(err(_oL));}),_oN=function(_oO,_oP){while(1){var _oQ=E(_oO);if(!_oQ._){var _oR=_oQ.a,_oS=E(_oP);if(!_oS._){var _oT=_oS.a;if(!(imul(_oR,_oT)|0)){return new T1(0,imul(_oR,_oT)|0);}else{_oO=new T1(1,I_fromInt(_oR));_oP=new T1(1,I_fromInt(_oT));continue;}}else{_oO=new T1(1,I_fromInt(_oR));_oP=_oS;continue;}}else{var _oU=E(_oP);if(!_oU._){_oO=_oQ;_oP=new T1(1,I_fromInt(_oU.a));continue;}else{return new T1(1,I_mul(_oQ.a,_oU.a));}}}},_oV=function(_oW,_oX){var _oY=E(_oX);if(!_oY._){return __Z;}else{var _oZ=E(_oY.b);return (_oZ._==0)?E(_oM):new T2(1,B(_oj(B(_oN(_oY.a,_oW)),_oZ.a)),new T(function(){return B(_oV(_oW,_oZ.b));}));}},_p0=new T1(0,0),_p1=function(_p2,_p3,_p4){while(1){var _p5=B((function(_p6,_p7,_p8){var _p9=E(_p8);if(!_p9._){return E(_p0);}else{if(!E(_p9.b)._){return E(_p9.a);}else{var _pa=E(_p7);if(_pa<=40){var _pb=function(_pc,_pd){while(1){var _pe=E(_pd);if(!_pe._){return E(_pc);}else{var _pf=B(_oj(B(_oN(_pc,_p6)),_pe.a));_pc=_pf;_pd=_pe.b;continue;}}};return new F(function(){return _pb(_p0,_p9);});}else{var _pg=B(_oN(_p6,_p6));if(!(_pa%2)){var _ph=B(_oV(_p6,_p9));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}else{var _ph=B(_oV(_p6,new T2(1,_p0,_p9)));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}}}}})(_p2,_p3,_p4));if(_p5!=__continue){return _p5;}}},_pi=function(_pj,_pk){return new F(function(){return _p1(_pj,new T(function(){return B(_oy(_pk,0));},1),B(_oD(_oJ,_pk)));});},_pl=function(_pm){var _pn=new T(function(){var _po=new T(function(){var _pp=function(_pq){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pq));})));});};return new T1(1,B(_ne(_og,_pp)));}),_pr=function(_ps){if(E(_ps)==43){var _pt=function(_pu){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pu));})));});};return new T1(1,B(_ne(_og,_pt)));}else{return new T0(2);}},_pv=function(_pw){if(E(_pw)==45){var _px=function(_py){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_ot(B(_pi(_ox,_py))));})));});};return new T1(1,B(_ne(_og,_px)));}else{return new T0(2);}};return B(_lf(B(_lf(new T1(0,_pv),new T1(0,_pr))),_po));});return new F(function(){return _lf(new T1(0,function(_pz){return (E(_pz)==101)?E(_pn):new T0(2);}),new T1(0,function(_pA){return (E(_pA)==69)?E(_pn):new T0(2);}));});},_pB=function(_pC){var _pD=function(_pE){return new F(function(){return A1(_pC,new T1(1,_pE));});};return function(_pF){return (E(_pF)==46)?new T1(1,B(_ne(_og,_pD))):new T0(2);};},_pG=function(_pH){return new T1(0,B(_pB(_pH)));},_pI=function(_pJ){var _pK=function(_pL){var _pM=function(_pN){return new T1(1,B(_mv(_pl,_oc,function(_pO){return new F(function(){return A1(_pJ,new T1(5,new T3(1,_pL,_pN,_pO)));});})));};return new T1(1,B(_mv(_pG,_oe,_pM)));};return new F(function(){return _ne(_og,_pK);});},_pP=function(_pQ){return new T1(1,B(_pI(_pQ)));},_pR=function(_pS){return E(E(_pS).a);},_pT=function(_pU,_pV,_pW){while(1){var _pX=E(_pW);if(!_pX._){return false;}else{if(!B(A3(_pR,_pU,_pV,_pX.a))){_pW=_pX.b;continue;}else{return true;}}}},_pY=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_pZ=function(_q0){return new F(function(){return _pT(_m4,_q0,_pY);});},_q1=false,_q2=true,_q3=function(_q4){var _q5=new T(function(){return B(A1(_q4,_nZ));}),_q6=new T(function(){return B(A1(_q4,_nY));});return function(_q7){switch(E(_q7)){case 79:return E(_q5);case 88:return E(_q6);case 111:return E(_q5);case 120:return E(_q6);default:return new T0(2);}};},_q8=function(_q9){return new T1(0,B(_q3(_q9)));},_qa=function(_qb){return new F(function(){return A1(_qb,_og);});},_qc=function(_qd){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_hA(9,_qd,_1));}))));});},_qe=function(_qf){var _qg=E(_qf);if(!_qg._){return E(_qg.a);}else{return new F(function(){return I_toInt(_qg.a);});}},_qh=function(_qi,_qj){var _qk=E(_qi);if(!_qk._){var _ql=_qk.a,_qm=E(_qj);return (_qm._==0)?_ql<=_qm.a:I_compareInt(_qm.a,_ql)>=0;}else{var _qn=_qk.a,_qo=E(_qj);return (_qo._==0)?I_compareInt(_qn,_qo.a)<=0:I_compare(_qn,_qo.a)<=0;}},_qp=function(_qq){return new T0(2);},_qr=function(_qs){var _qt=E(_qs);if(!_qt._){return E(_qp);}else{var _qu=_qt.a,_qv=E(_qt.b);if(!_qv._){return E(_qu);}else{var _qw=new T(function(){return B(_qr(_qv));}),_qx=function(_qy){return new F(function(){return _lf(B(A1(_qu,_qy)),new T(function(){return B(A1(_qw,_qy));}));});};return E(_qx);}}},_qz=function(_qA,_qB){var _qC=function(_qD,_qE,_qF){var _qG=E(_qD);if(!_qG._){return new F(function(){return A1(_qF,_qA);});}else{var _qH=E(_qE);if(!_qH._){return new T0(2);}else{if(E(_qG.a)!=E(_qH.a)){return new T0(2);}else{var _qI=new T(function(){return B(_qC(_qG.b,_qH.b,_qF));});return new T1(0,function(_qJ){return E(_qI);});}}}};return function(_qK){return new F(function(){return _qC(_qA,_qK,_qB);});};},_qL=new T(function(){return B(unCStr("SO"));}),_qM=14,_qN=function(_qO){var _qP=new T(function(){return B(A1(_qO,_qM));});return new T1(1,B(_qz(_qL,function(_qQ){return E(_qP);})));},_qR=new T(function(){return B(unCStr("SOH"));}),_qS=1,_qT=function(_qU){var _qV=new T(function(){return B(A1(_qU,_qS));});return new T1(1,B(_qz(_qR,function(_qW){return E(_qV);})));},_qX=function(_qY){return new T1(1,B(_mv(_qT,_qN,_qY)));},_qZ=new T(function(){return B(unCStr("NUL"));}),_r0=0,_r1=function(_r2){var _r3=new T(function(){return B(A1(_r2,_r0));});return new T1(1,B(_qz(_qZ,function(_r4){return E(_r3);})));},_r5=new T(function(){return B(unCStr("STX"));}),_r6=2,_r7=function(_r8){var _r9=new T(function(){return B(A1(_r8,_r6));});return new T1(1,B(_qz(_r5,function(_ra){return E(_r9);})));},_rb=new T(function(){return B(unCStr("ETX"));}),_rc=3,_rd=function(_re){var _rf=new T(function(){return B(A1(_re,_rc));});return new T1(1,B(_qz(_rb,function(_rg){return E(_rf);})));},_rh=new T(function(){return B(unCStr("EOT"));}),_ri=4,_rj=function(_rk){var _rl=new T(function(){return B(A1(_rk,_ri));});return new T1(1,B(_qz(_rh,function(_rm){return E(_rl);})));},_rn=new T(function(){return B(unCStr("ENQ"));}),_ro=5,_rp=function(_rq){var _rr=new T(function(){return B(A1(_rq,_ro));});return new T1(1,B(_qz(_rn,function(_rs){return E(_rr);})));},_rt=new T(function(){return B(unCStr("ACK"));}),_ru=6,_rv=function(_rw){var _rx=new T(function(){return B(A1(_rw,_ru));});return new T1(1,B(_qz(_rt,function(_ry){return E(_rx);})));},_rz=new T(function(){return B(unCStr("BEL"));}),_rA=7,_rB=function(_rC){var _rD=new T(function(){return B(A1(_rC,_rA));});return new T1(1,B(_qz(_rz,function(_rE){return E(_rD);})));},_rF=new T(function(){return B(unCStr("BS"));}),_rG=8,_rH=function(_rI){var _rJ=new T(function(){return B(A1(_rI,_rG));});return new T1(1,B(_qz(_rF,function(_rK){return E(_rJ);})));},_rL=new T(function(){return B(unCStr("HT"));}),_rM=9,_rN=function(_rO){var _rP=new T(function(){return B(A1(_rO,_rM));});return new T1(1,B(_qz(_rL,function(_rQ){return E(_rP);})));},_rR=new T(function(){return B(unCStr("LF"));}),_rS=10,_rT=function(_rU){var _rV=new T(function(){return B(A1(_rU,_rS));});return new T1(1,B(_qz(_rR,function(_rW){return E(_rV);})));},_rX=new T(function(){return B(unCStr("VT"));}),_rY=11,_rZ=function(_s0){var _s1=new T(function(){return B(A1(_s0,_rY));});return new T1(1,B(_qz(_rX,function(_s2){return E(_s1);})));},_s3=new T(function(){return B(unCStr("FF"));}),_s4=12,_s5=function(_s6){var _s7=new T(function(){return B(A1(_s6,_s4));});return new T1(1,B(_qz(_s3,function(_s8){return E(_s7);})));},_s9=new T(function(){return B(unCStr("CR"));}),_sa=13,_sb=function(_sc){var _sd=new T(function(){return B(A1(_sc,_sa));});return new T1(1,B(_qz(_s9,function(_se){return E(_sd);})));},_sf=new T(function(){return B(unCStr("SI"));}),_sg=15,_sh=function(_si){var _sj=new T(function(){return B(A1(_si,_sg));});return new T1(1,B(_qz(_sf,function(_sk){return E(_sj);})));},_sl=new T(function(){return B(unCStr("DLE"));}),_sm=16,_sn=function(_so){var _sp=new T(function(){return B(A1(_so,_sm));});return new T1(1,B(_qz(_sl,function(_sq){return E(_sp);})));},_sr=new T(function(){return B(unCStr("DC1"));}),_ss=17,_st=function(_su){var _sv=new T(function(){return B(A1(_su,_ss));});return new T1(1,B(_qz(_sr,function(_sw){return E(_sv);})));},_sx=new T(function(){return B(unCStr("DC2"));}),_sy=18,_sz=function(_sA){var _sB=new T(function(){return B(A1(_sA,_sy));});return new T1(1,B(_qz(_sx,function(_sC){return E(_sB);})));},_sD=new T(function(){return B(unCStr("DC3"));}),_sE=19,_sF=function(_sG){var _sH=new T(function(){return B(A1(_sG,_sE));});return new T1(1,B(_qz(_sD,function(_sI){return E(_sH);})));},_sJ=new T(function(){return B(unCStr("DC4"));}),_sK=20,_sL=function(_sM){var _sN=new T(function(){return B(A1(_sM,_sK));});return new T1(1,B(_qz(_sJ,function(_sO){return E(_sN);})));},_sP=new T(function(){return B(unCStr("NAK"));}),_sQ=21,_sR=function(_sS){var _sT=new T(function(){return B(A1(_sS,_sQ));});return new T1(1,B(_qz(_sP,function(_sU){return E(_sT);})));},_sV=new T(function(){return B(unCStr("SYN"));}),_sW=22,_sX=function(_sY){var _sZ=new T(function(){return B(A1(_sY,_sW));});return new T1(1,B(_qz(_sV,function(_t0){return E(_sZ);})));},_t1=new T(function(){return B(unCStr("ETB"));}),_t2=23,_t3=function(_t4){var _t5=new T(function(){return B(A1(_t4,_t2));});return new T1(1,B(_qz(_t1,function(_t6){return E(_t5);})));},_t7=new T(function(){return B(unCStr("CAN"));}),_t8=24,_t9=function(_ta){var _tb=new T(function(){return B(A1(_ta,_t8));});return new T1(1,B(_qz(_t7,function(_tc){return E(_tb);})));},_td=new T(function(){return B(unCStr("EM"));}),_te=25,_tf=function(_tg){var _th=new T(function(){return B(A1(_tg,_te));});return new T1(1,B(_qz(_td,function(_ti){return E(_th);})));},_tj=new T(function(){return B(unCStr("SUB"));}),_tk=26,_tl=function(_tm){var _tn=new T(function(){return B(A1(_tm,_tk));});return new T1(1,B(_qz(_tj,function(_to){return E(_tn);})));},_tp=new T(function(){return B(unCStr("ESC"));}),_tq=27,_tr=function(_ts){var _tt=new T(function(){return B(A1(_ts,_tq));});return new T1(1,B(_qz(_tp,function(_tu){return E(_tt);})));},_tv=new T(function(){return B(unCStr("FS"));}),_tw=28,_tx=function(_ty){var _tz=new T(function(){return B(A1(_ty,_tw));});return new T1(1,B(_qz(_tv,function(_tA){return E(_tz);})));},_tB=new T(function(){return B(unCStr("GS"));}),_tC=29,_tD=function(_tE){var _tF=new T(function(){return B(A1(_tE,_tC));});return new T1(1,B(_qz(_tB,function(_tG){return E(_tF);})));},_tH=new T(function(){return B(unCStr("RS"));}),_tI=30,_tJ=function(_tK){var _tL=new T(function(){return B(A1(_tK,_tI));});return new T1(1,B(_qz(_tH,function(_tM){return E(_tL);})));},_tN=new T(function(){return B(unCStr("US"));}),_tO=31,_tP=function(_tQ){var _tR=new T(function(){return B(A1(_tQ,_tO));});return new T1(1,B(_qz(_tN,function(_tS){return E(_tR);})));},_tT=new T(function(){return B(unCStr("SP"));}),_tU=32,_tV=function(_tW){var _tX=new T(function(){return B(A1(_tW,_tU));});return new T1(1,B(_qz(_tT,function(_tY){return E(_tX);})));},_tZ=new T(function(){return B(unCStr("DEL"));}),_u0=127,_u1=function(_u2){var _u3=new T(function(){return B(A1(_u2,_u0));});return new T1(1,B(_qz(_tZ,function(_u4){return E(_u3);})));},_u5=new T2(1,_u1,_1),_u6=new T2(1,_tV,_u5),_u7=new T2(1,_tP,_u6),_u8=new T2(1,_tJ,_u7),_u9=new T2(1,_tD,_u8),_ua=new T2(1,_tx,_u9),_ub=new T2(1,_tr,_ua),_uc=new T2(1,_tl,_ub),_ud=new T2(1,_tf,_uc),_ue=new T2(1,_t9,_ud),_uf=new T2(1,_t3,_ue),_ug=new T2(1,_sX,_uf),_uh=new T2(1,_sR,_ug),_ui=new T2(1,_sL,_uh),_uj=new T2(1,_sF,_ui),_uk=new T2(1,_sz,_uj),_ul=new T2(1,_st,_uk),_um=new T2(1,_sn,_ul),_un=new T2(1,_sh,_um),_uo=new T2(1,_sb,_un),_up=new T2(1,_s5,_uo),_uq=new T2(1,_rZ,_up),_ur=new T2(1,_rT,_uq),_us=new T2(1,_rN,_ur),_ut=new T2(1,_rH,_us),_uu=new T2(1,_rB,_ut),_uv=new T2(1,_rv,_uu),_uw=new T2(1,_rp,_uv),_ux=new T2(1,_rj,_uw),_uy=new T2(1,_rd,_ux),_uz=new T2(1,_r7,_uy),_uA=new T2(1,_r1,_uz),_uB=new T2(1,_qX,_uA),_uC=new T(function(){return B(_qr(_uB));}),_uD=34,_uE=new T1(0,1114111),_uF=92,_uG=39,_uH=function(_uI){var _uJ=new T(function(){return B(A1(_uI,_rA));}),_uK=new T(function(){return B(A1(_uI,_rG));}),_uL=new T(function(){return B(A1(_uI,_rM));}),_uM=new T(function(){return B(A1(_uI,_rS));}),_uN=new T(function(){return B(A1(_uI,_rY));}),_uO=new T(function(){return B(A1(_uI,_s4));}),_uP=new T(function(){return B(A1(_uI,_sa));}),_uQ=new T(function(){return B(A1(_uI,_uF));}),_uR=new T(function(){return B(A1(_uI,_uG));}),_uS=new T(function(){return B(A1(_uI,_uD));}),_uT=new T(function(){var _uU=function(_uV){var _uW=new T(function(){return B(_oH(E(_uV)));}),_uX=function(_uY){var _uZ=B(_pi(_uW,_uY));if(!B(_qh(_uZ,_uE))){return new T0(2);}else{return new F(function(){return A1(_uI,new T(function(){var _v0=B(_qe(_uZ));if(_v0>>>0>1114111){return B(_qc(_v0));}else{return _v0;}}));});}};return new T1(1,B(_ne(_uV,_uX)));},_v1=new T(function(){var _v2=new T(function(){return B(A1(_uI,_tO));}),_v3=new T(function(){return B(A1(_uI,_tI));}),_v4=new T(function(){return B(A1(_uI,_tC));}),_v5=new T(function(){return B(A1(_uI,_tw));}),_v6=new T(function(){return B(A1(_uI,_tq));}),_v7=new T(function(){return B(A1(_uI,_tk));}),_v8=new T(function(){return B(A1(_uI,_te));}),_v9=new T(function(){return B(A1(_uI,_t8));}),_va=new T(function(){return B(A1(_uI,_t2));}),_vb=new T(function(){return B(A1(_uI,_sW));}),_vc=new T(function(){return B(A1(_uI,_sQ));}),_vd=new T(function(){return B(A1(_uI,_sK));}),_ve=new T(function(){return B(A1(_uI,_sE));}),_vf=new T(function(){return B(A1(_uI,_sy));}),_vg=new T(function(){return B(A1(_uI,_ss));}),_vh=new T(function(){return B(A1(_uI,_sm));}),_vi=new T(function(){return B(A1(_uI,_sg));}),_vj=new T(function(){return B(A1(_uI,_qM));}),_vk=new T(function(){return B(A1(_uI,_ru));}),_vl=new T(function(){return B(A1(_uI,_ro));}),_vm=new T(function(){return B(A1(_uI,_ri));}),_vn=new T(function(){return B(A1(_uI,_rc));}),_vo=new T(function(){return B(A1(_uI,_r6));}),_vp=new T(function(){return B(A1(_uI,_qS));}),_vq=new T(function(){return B(A1(_uI,_r0));}),_vr=function(_vs){switch(E(_vs)){case 64:return E(_vq);case 65:return E(_vp);case 66:return E(_vo);case 67:return E(_vn);case 68:return E(_vm);case 69:return E(_vl);case 70:return E(_vk);case 71:return E(_uJ);case 72:return E(_uK);case 73:return E(_uL);case 74:return E(_uM);case 75:return E(_uN);case 76:return E(_uO);case 77:return E(_uP);case 78:return E(_vj);case 79:return E(_vi);case 80:return E(_vh);case 81:return E(_vg);case 82:return E(_vf);case 83:return E(_ve);case 84:return E(_vd);case 85:return E(_vc);case 86:return E(_vb);case 87:return E(_va);case 88:return E(_v9);case 89:return E(_v8);case 90:return E(_v7);case 91:return E(_v6);case 92:return E(_v5);case 93:return E(_v4);case 94:return E(_v3);case 95:return E(_v2);default:return new T0(2);}};return B(_lf(new T1(0,function(_vt){return (E(_vt)==94)?E(new T1(0,_vr)):new T0(2);}),new T(function(){return B(A1(_uC,_uI));})));});return B(_lf(new T1(1,B(_mv(_q8,_qa,_uU))),_v1));});return new F(function(){return _lf(new T1(0,function(_vu){switch(E(_vu)){case 34:return E(_uS);case 39:return E(_uR);case 92:return E(_uQ);case 97:return E(_uJ);case 98:return E(_uK);case 102:return E(_uO);case 110:return E(_uM);case 114:return E(_uP);case 116:return E(_uL);case 118:return E(_uN);default:return new T0(2);}}),_uT);});},_vv=function(_vw){return new F(function(){return A1(_vw,_h9);});},_vx=function(_vy){var _vz=E(_vy);if(!_vz._){return E(_vv);}else{var _vA=E(_vz.a),_vB=_vA>>>0,_vC=new T(function(){return B(_vx(_vz.b));});if(_vB>887){var _vD=u_iswspace(_vA);if(!E(_vD)){return E(_vv);}else{var _vE=function(_vF){var _vG=new T(function(){return B(A1(_vC,_vF));});return new T1(0,function(_vH){return E(_vG);});};return E(_vE);}}else{var _vI=E(_vB);if(_vI==32){var _vJ=function(_vK){var _vL=new T(function(){return B(A1(_vC,_vK));});return new T1(0,function(_vM){return E(_vL);});};return E(_vJ);}else{if(_vI-9>>>0>4){if(E(_vI)==160){var _vN=function(_vO){var _vP=new T(function(){return B(A1(_vC,_vO));});return new T1(0,function(_vQ){return E(_vP);});};return E(_vN);}else{return E(_vv);}}else{var _vR=function(_vS){var _vT=new T(function(){return B(A1(_vC,_vS));});return new T1(0,function(_vU){return E(_vT);});};return E(_vR);}}}}},_vV=function(_vW){var _vX=new T(function(){return B(_vV(_vW));}),_vY=function(_vZ){return (E(_vZ)==92)?E(_vX):new T0(2);},_w0=function(_w1){return E(new T1(0,_vY));},_w2=new T1(1,function(_w3){return new F(function(){return A2(_vx,_w3,_w0);});}),_w4=new T(function(){return B(_uH(function(_w5){return new F(function(){return A1(_vW,new T2(0,_w5,_q2));});}));}),_w6=function(_w7){var _w8=E(_w7);if(_w8==38){return E(_vX);}else{var _w9=_w8>>>0;if(_w9>887){var _wa=u_iswspace(_w8);return (E(_wa)==0)?new T0(2):E(_w2);}else{var _wb=E(_w9);return (_wb==32)?E(_w2):(_wb-9>>>0>4)?(E(_wb)==160)?E(_w2):new T0(2):E(_w2);}}};return new F(function(){return _lf(new T1(0,function(_wc){return (E(_wc)==92)?E(new T1(0,_w6)):new T0(2);}),new T1(0,function(_wd){var _we=E(_wd);if(E(_we)==92){return E(_w4);}else{return new F(function(){return A1(_vW,new T2(0,_we,_q1));});}}));});},_wf=function(_wg,_wh){var _wi=new T(function(){return B(A1(_wh,new T1(1,new T(function(){return B(A1(_wg,_1));}))));}),_wj=function(_wk){var _wl=E(_wk),_wm=E(_wl.a);if(E(_wm)==34){if(!E(_wl.b)){return E(_wi);}else{return new F(function(){return _wf(function(_wn){return new F(function(){return A1(_wg,new T2(1,_wm,_wn));});},_wh);});}}else{return new F(function(){return _wf(function(_wo){return new F(function(){return A1(_wg,new T2(1,_wm,_wo));});},_wh);});}};return new F(function(){return _vV(_wj);});},_wp=new T(function(){return B(unCStr("_\'"));}),_wq=function(_wr){var _ws=u_iswalnum(_wr);if(!E(_ws)){return new F(function(){return _pT(_m4,_wr,_wp);});}else{return true;}},_wt=function(_wu){return new F(function(){return _wq(E(_wu));});},_wv=new T(function(){return B(unCStr(",;()[]{}`"));}),_ww=new T(function(){return B(unCStr("=>"));}),_wx=new T2(1,_ww,_1),_wy=new T(function(){return B(unCStr("~"));}),_wz=new T2(1,_wy,_wx),_wA=new T(function(){return B(unCStr("@"));}),_wB=new T2(1,_wA,_wz),_wC=new T(function(){return B(unCStr("->"));}),_wD=new T2(1,_wC,_wB),_wE=new T(function(){return B(unCStr("<-"));}),_wF=new T2(1,_wE,_wD),_wG=new T(function(){return B(unCStr("|"));}),_wH=new T2(1,_wG,_wF),_wI=new T(function(){return B(unCStr("\\"));}),_wJ=new T2(1,_wI,_wH),_wK=new T(function(){return B(unCStr("="));}),_wL=new T2(1,_wK,_wJ),_wM=new T(function(){return B(unCStr("::"));}),_wN=new T2(1,_wM,_wL),_wO=new T(function(){return B(unCStr(".."));}),_wP=new T2(1,_wO,_wN),_wQ=function(_wR){var _wS=new T(function(){return B(A1(_wR,_n9));}),_wT=new T(function(){var _wU=new T(function(){var _wV=function(_wW){var _wX=new T(function(){return B(A1(_wR,new T1(0,_wW)));});return new T1(0,function(_wY){return (E(_wY)==39)?E(_wX):new T0(2);});};return B(_uH(_wV));}),_wZ=function(_x0){var _x1=E(_x0);switch(E(_x1)){case 39:return new T0(2);case 92:return E(_wU);default:var _x2=new T(function(){return B(A1(_wR,new T1(0,_x1)));});return new T1(0,function(_x3){return (E(_x3)==39)?E(_x2):new T0(2);});}},_x4=new T(function(){var _x5=new T(function(){return B(_wf(_na,_wR));}),_x6=new T(function(){var _x7=new T(function(){var _x8=new T(function(){var _x9=function(_xa){var _xb=E(_xa),_xc=u_iswalpha(_xb);return (E(_xc)==0)?(E(_xb)==95)?new T1(1,B(_mV(_wt,function(_xd){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xd)));});}))):new T0(2):new T1(1,B(_mV(_wt,function(_xe){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xe)));});})));};return B(_lf(new T1(0,_x9),new T(function(){return new T1(1,B(_mv(_o9,_pP,_wR)));})));}),_xf=function(_xg){return (!B(_pT(_m4,_xg,_pY)))?new T0(2):new T1(1,B(_mV(_pZ,function(_xh){var _xi=new T2(1,_xg,_xh);if(!B(_pT(_md,_xi,_wP))){return new F(function(){return A1(_wR,new T1(4,_xi));});}else{return new F(function(){return A1(_wR,new T1(2,_xi));});}})));};return B(_lf(new T1(0,_xf),_x8));});return B(_lf(new T1(0,function(_xj){if(!B(_pT(_m4,_xj,_wv))){return new T0(2);}else{return new F(function(){return A1(_wR,new T1(2,new T2(1,_xj,_1)));});}}),_x7));});return B(_lf(new T1(0,function(_xk){return (E(_xk)==34)?E(_x5):new T0(2);}),_x6));});return B(_lf(new T1(0,function(_xl){return (E(_xl)==39)?E(new T1(0,_wZ)):new T0(2);}),_x4));});return new F(function(){return _lf(new T1(1,function(_xm){return (E(_xm)._==0)?E(_wS):new T0(2);}),_wT);});},_xn=0,_xo=function(_xp,_xq){var _xr=new T(function(){var _xs=new T(function(){var _xt=function(_xu){var _xv=new T(function(){var _xw=new T(function(){return B(A1(_xq,_xu));});return B(_wQ(function(_xx){var _xy=E(_xx);return (_xy._==2)?(!B(_lT(_xy.a,_lS)))?new T0(2):E(_xw):new T0(2);}));}),_xz=function(_xA){return E(_xv);};return new T1(1,function(_xB){return new F(function(){return A2(_vx,_xB,_xz);});});};return B(A2(_xp,_xn,_xt));});return B(_wQ(function(_xC){var _xD=E(_xC);return (_xD._==2)?(!B(_lT(_xD.a,_lR)))?new T0(2):E(_xs):new T0(2);}));}),_xE=function(_xF){return E(_xr);};return function(_xG){return new F(function(){return A2(_vx,_xG,_xE);});};},_xH=function(_xI,_xJ){var _xK=function(_xL){var _xM=new T(function(){return B(A1(_xI,_xL));}),_xN=function(_xO){return new F(function(){return _lf(B(A1(_xM,_xO)),new T(function(){return new T1(1,B(_xo(_xK,_xO)));}));});};return E(_xN);},_xP=new T(function(){return B(A1(_xI,_xJ));}),_xQ=function(_xR){return new F(function(){return _lf(B(A1(_xP,_xR)),new T(function(){return new T1(1,B(_xo(_xK,_xR)));}));});};return E(_xQ);},_xS=function(_xT,_xU){var _xV=function(_xW,_xX){var _xY=function(_xZ){return new F(function(){return A1(_xX,new T(function(){return  -E(_xZ);}));});},_y0=new T(function(){return B(_wQ(function(_y1){return new F(function(){return A3(_xT,_y1,_xW,_xY);});}));}),_y2=function(_y3){return E(_y0);},_y4=function(_y5){return new F(function(){return A2(_vx,_y5,_y2);});},_y6=new T(function(){return B(_wQ(function(_y7){var _y8=E(_y7);if(_y8._==4){var _y9=E(_y8.a);if(!_y9._){return new F(function(){return A3(_xT,_y8,_xW,_xX);});}else{if(E(_y9.a)==45){if(!E(_y9.b)._){return E(new T1(1,_y4));}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}));}),_ya=function(_yb){return E(_y6);};return new T1(1,function(_yc){return new F(function(){return A2(_vx,_yc,_ya);});});};return new F(function(){return _xH(_xV,_xU);});},_yd=function(_ye){var _yf=E(_ye);if(!_yf._){var _yg=_yf.b,_yh=new T(function(){return B(_p1(new T(function(){return B(_oH(E(_yf.a)));}),new T(function(){return B(_oy(_yg,0));},1),B(_oD(_oJ,_yg))));});return new T1(1,_yh);}else{return (E(_yf.b)._==0)?(E(_yf.c)._==0)?new T1(1,new T(function(){return B(_pi(_ox,_yf.a));})):__Z:__Z;}},_yi=function(_yj,_yk){return new T0(2);},_yl=function(_ym){var _yn=E(_ym);if(_yn._==5){var _yo=B(_yd(_yn.a));if(!_yo._){return E(_yi);}else{var _yp=new T(function(){return B(_qe(_yo.a));});return function(_yq,_yr){return new F(function(){return A1(_yr,_yp);});};}}else{return E(_yi);}},_ys=function(_yt){return new F(function(){return _xS(_yl,_yt);});},_yu=new T(function(){return B(unCStr("["));}),_yv=function(_yw,_yx){var _yy=function(_yz,_yA){var _yB=new T(function(){return B(A1(_yA,_1));}),_yC=new T(function(){var _yD=function(_yE){return new F(function(){return _yy(_q2,function(_yF){return new F(function(){return A1(_yA,new T2(1,_yE,_yF));});});});};return B(A2(_yw,_xn,_yD));}),_yG=new T(function(){return B(_wQ(function(_yH){var _yI=E(_yH);if(_yI._==2){var _yJ=E(_yI.a);if(!_yJ._){return new T0(2);}else{var _yK=_yJ.b;switch(E(_yJ.a)){case 44:return (E(_yK)._==0)?(!E(_yz))?new T0(2):E(_yC):new T0(2);case 93:return (E(_yK)._==0)?E(_yB):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_yL=function(_yM){return E(_yG);};return new T1(1,function(_yN){return new F(function(){return A2(_vx,_yN,_yL);});});},_yO=function(_yP,_yQ){return new F(function(){return _yR(_yQ);});},_yR=function(_yS){var _yT=new T(function(){var _yU=new T(function(){var _yV=new T(function(){var _yW=function(_yX){return new F(function(){return _yy(_q2,function(_yY){return new F(function(){return A1(_yS,new T2(1,_yX,_yY));});});});};return B(A2(_yw,_xn,_yW));});return B(_lf(B(_yy(_q1,_yS)),_yV));});return B(_wQ(function(_yZ){var _z0=E(_yZ);return (_z0._==2)?(!B(_lT(_z0.a,_yu)))?new T0(2):E(_yU):new T0(2);}));}),_z1=function(_z2){return E(_yT);};return new F(function(){return _lf(new T1(1,function(_z3){return new F(function(){return A2(_vx,_z3,_z1);});}),new T(function(){return new T1(1,B(_xo(_yO,_yS)));}));});};return new F(function(){return _yR(_yx);});},_z4=function(_z5,_z6){return new F(function(){return _yv(_ys,_z6);});},_z7=new T(function(){return B(_yv(_ys,_jV));}),_z8=function(_yt){return new F(function(){return _l5(_z7,_yt);});},_z9=function(_za){var _zb=new T(function(){return B(A3(_xS,_yl,_za,_jV));});return function(_zc){return new F(function(){return _l5(_zb,_zc);});};},_zd=new T4(0,_z9,_z8,_ys,_z4),_ze=11,_zf=new T(function(){return B(unCStr("IdentChoice"));}),_zg=function(_zh,_zi){if(_zh>10){return new T0(2);}else{var _zj=new T(function(){var _zk=new T(function(){return B(A3(_xS,_yl,_ze,function(_zl){return new F(function(){return A1(_zi,_zl);});}));});return B(_wQ(function(_zm){var _zn=E(_zm);return (_zn._==3)?(!B(_lT(_zn.a,_zf)))?new T0(2):E(_zk):new T0(2);}));}),_zo=function(_zp){return E(_zj);};return new T1(1,function(_zq){return new F(function(){return A2(_vx,_zq,_zo);});});}},_zr=function(_zs,_zt){return new F(function(){return _zg(E(_zs),_zt);});},_zu=function(_zv){return new F(function(){return _xH(_zr,_zv);});},_zw=function(_zx,_zy){return new F(function(){return _yv(_zu,_zy);});},_zz=new T(function(){return B(_yv(_zu,_jV));}),_zA=function(_zv){return new F(function(){return _l5(_zz,_zv);});},_zB=function(_zC){var _zD=new T(function(){return B(A3(_xH,_zr,_zC,_jV));});return function(_zc){return new F(function(){return _l5(_zD,_zc);});};},_zE=new T4(0,_zB,_zA,_zu,_zw),_zF=new T(function(){return B(unCStr(","));}),_zG=function(_zH){return E(E(_zH).c);},_zI=function(_zJ,_zK,_zL){var _zM=new T(function(){return B(_zG(_zK));}),_zN=new T(function(){return B(A2(_zG,_zJ,_zL));}),_zO=function(_zP){var _zQ=function(_zR){var _zS=new T(function(){var _zT=new T(function(){return B(A2(_zM,_zL,function(_zU){return new F(function(){return A1(_zP,new T2(0,_zR,_zU));});}));});return B(_wQ(function(_zV){var _zW=E(_zV);return (_zW._==2)?(!B(_lT(_zW.a,_zF)))?new T0(2):E(_zT):new T0(2);}));}),_zX=function(_zY){return E(_zS);};return new T1(1,function(_zZ){return new F(function(){return A2(_vx,_zZ,_zX);});});};return new F(function(){return A1(_zN,_zQ);});};return E(_zO);},_A0=function(_A1,_A2,_A3){var _A4=function(_yt){return new F(function(){return _zI(_A1,_A2,_yt);});},_A5=function(_A6,_A7){return new F(function(){return _A8(_A7);});},_A8=function(_A9){return new F(function(){return _lf(new T1(1,B(_xo(_A4,_A9))),new T(function(){return new T1(1,B(_xo(_A5,_A9)));}));});};return new F(function(){return _A8(_A3);});},_Aa=function(_Ab,_Ac){return new F(function(){return _A0(_zE,_zd,_Ac);});},_Ad=new T(function(){return B(_yv(_Aa,_jV));}),_Ae=function(_zv){return new F(function(){return _l5(_Ad,_zv);});},_Af=new T(function(){return B(_A0(_zE,_zd,_jV));}),_Ag=function(_zv){return new F(function(){return _l5(_Af,_zv);});},_Ah=function(_Ai,_zv){return new F(function(){return _Ag(_zv);});},_Aj=function(_Ak,_Al){return new F(function(){return _yv(_Aa,_Al);});},_Am=new T4(0,_Ah,_Ae,_Aa,_Aj),_An=function(_Ao,_Ap){return new F(function(){return _A0(_Am,_zd,_Ap);});},_Aq=function(_Ar,_As){return new F(function(){return _yv(_An,_As);});},_At=new T(function(){return B(_yv(_Aq,_jV));}),_Au=function(_Av){return new F(function(){return _l5(_At,_Av);});},_Aw=function(_Ax){return new F(function(){return _yv(_Aq,_Ax);});},_Ay=function(_Az,_AA){return new F(function(){return _Aw(_AA);});},_AB=new T(function(){return B(_yv(_An,_jV));}),_AC=function(_Av){return new F(function(){return _l5(_AB,_Av);});},_AD=function(_AE,_Av){return new F(function(){return _AC(_Av);});},_AF=new T4(0,_AD,_Au,_Aq,_Ay),_AG=new T(function(){return B(unCStr("IdentPay"));}),_AH=function(_AI,_AJ){if(_AI>10){return new T0(2);}else{var _AK=new T(function(){var _AL=new T(function(){return B(A3(_xS,_yl,_ze,function(_AM){return new F(function(){return A1(_AJ,_AM);});}));});return B(_wQ(function(_AN){var _AO=E(_AN);return (_AO._==3)?(!B(_lT(_AO.a,_AG)))?new T0(2):E(_AL):new T0(2);}));}),_AP=function(_AQ){return E(_AK);};return new T1(1,function(_AR){return new F(function(){return A2(_vx,_AR,_AP);});});}},_AS=function(_AT,_AU){return new F(function(){return _AH(E(_AT),_AU);});},_AV=function(_zv){return new F(function(){return _xH(_AS,_zv);});},_AW=function(_AX,_AY){return new F(function(){return _yv(_AV,_AY);});},_AZ=new T(function(){return B(_yv(_AV,_jV));}),_B0=function(_zv){return new F(function(){return _l5(_AZ,_zv);});},_B1=function(_B2){var _B3=new T(function(){return B(A3(_xH,_AS,_B2,_jV));});return function(_zc){return new F(function(){return _l5(_B3,_zc);});};},_B4=new T4(0,_B1,_B0,_AV,_AW),_B5=function(_B6,_B7){return new F(function(){return _A0(_B4,_zd,_B7);});},_B8=new T(function(){return B(_yv(_B5,_jV));}),_B9=function(_zv){return new F(function(){return _l5(_B8,_zv);});},_Ba=new T(function(){return B(_A0(_B4,_zd,_jV));}),_Bb=function(_zv){return new F(function(){return _l5(_Ba,_zv);});},_Bc=function(_Bd,_zv){return new F(function(){return _Bb(_zv);});},_Be=function(_Bf,_Bg){return new F(function(){return _yv(_B5,_Bg);});},_Bh=new T4(0,_Bc,_B9,_B5,_Be),_Bi=function(_Bj,_Bk){return new F(function(){return _A0(_Bh,_zd,_Bk);});},_Bl=function(_Bm,_Bn){return new F(function(){return _yv(_Bi,_Bn);});},_Bo=new T(function(){return B(_yv(_Bl,_jV));}),_Bp=function(_Av){return new F(function(){return _l5(_Bo,_Av);});},_Bq=function(_Br){return new F(function(){return _yv(_Bl,_Br);});},_Bs=function(_Bt,_Bu){return new F(function(){return _Bq(_Bu);});},_Bv=new T(function(){return B(_yv(_Bi,_jV));}),_Bw=function(_Av){return new F(function(){return _l5(_Bv,_Av);});},_Bx=function(_By,_Av){return new F(function(){return _Bw(_Av);});},_Bz=new T4(0,_Bx,_Bp,_Bl,_Bs),_BA=new T(function(){return B(unCStr("IdentCC"));}),_BB=function(_BC,_BD){if(_BC>10){return new T0(2);}else{var _BE=new T(function(){var _BF=new T(function(){return B(A3(_xS,_yl,_ze,function(_BG){return new F(function(){return A1(_BD,_BG);});}));});return B(_wQ(function(_BH){var _BI=E(_BH);return (_BI._==3)?(!B(_lT(_BI.a,_BA)))?new T0(2):E(_BF):new T0(2);}));}),_BJ=function(_BK){return E(_BE);};return new T1(1,function(_BL){return new F(function(){return A2(_vx,_BL,_BJ);});});}},_BM=function(_BN,_BO){return new F(function(){return _BB(E(_BN),_BO);});},_BP=new T(function(){return B(unCStr("RC"));}),_BQ=function(_BR,_BS){if(_BR>10){return new T0(2);}else{var _BT=new T(function(){var _BU=new T(function(){var _BV=function(_BW){var _BX=function(_BY){return new F(function(){return A3(_xS,_yl,_ze,function(_BZ){return new F(function(){return A1(_BS,new T3(0,_BW,_BY,_BZ));});});});};return new F(function(){return A3(_xS,_yl,_ze,_BX);});};return B(A3(_xH,_BM,_ze,_BV));});return B(_wQ(function(_C0){var _C1=E(_C0);return (_C1._==3)?(!B(_lT(_C1.a,_BP)))?new T0(2):E(_BU):new T0(2);}));}),_C2=function(_C3){return E(_BT);};return new T1(1,function(_C4){return new F(function(){return A2(_vx,_C4,_C2);});});}},_C5=function(_C6,_C7){return new F(function(){return _BQ(E(_C6),_C7);});},_C8=function(_zv){return new F(function(){return _xH(_C5,_zv);});},_C9=function(_Ca,_Cb){return new F(function(){return _yv(_C8,_Cb);});},_Cc=new T(function(){return B(_yv(_C9,_jV));}),_Cd=function(_Av){return new F(function(){return _l5(_Cc,_Av);});},_Ce=new T(function(){return B(_yv(_C8,_jV));}),_Cf=function(_Av){return new F(function(){return _l5(_Ce,_Av);});},_Cg=function(_Ch,_Av){return new F(function(){return _Cf(_Av);});},_Ci=function(_Cj,_Ck){return new F(function(){return _yv(_C9,_Ck);});},_Cl=new T4(0,_Cg,_Cd,_C9,_Ci),_Cm=new T(function(){return B(unCStr("CC"));}),_Cn=function(_Co,_Cp){if(_Co>10){return new T0(2);}else{var _Cq=new T(function(){var _Cr=new T(function(){var _Cs=function(_Ct){var _Cu=function(_Cv){var _Cw=function(_Cx){return new F(function(){return A3(_xS,_yl,_ze,function(_Cy){return new F(function(){return A1(_Cp,new T4(0,_Ct,_Cv,_Cx,_Cy));});});});};return new F(function(){return A3(_xS,_yl,_ze,_Cw);});};return new F(function(){return A3(_xS,_yl,_ze,_Cu);});};return B(A3(_xH,_BM,_ze,_Cs));});return B(_wQ(function(_Cz){var _CA=E(_Cz);return (_CA._==3)?(!B(_lT(_CA.a,_Cm)))?new T0(2):E(_Cr):new T0(2);}));}),_CB=function(_CC){return E(_Cq);};return new T1(1,function(_CD){return new F(function(){return A2(_vx,_CD,_CB);});});}},_CE=function(_CF,_CG){return new F(function(){return _Cn(E(_CF),_CG);});},_CH=function(_zv){return new F(function(){return _xH(_CE,_zv);});},_CI=function(_CJ,_CK){return new F(function(){return _yv(_CH,_CK);});},_CL=new T(function(){return B(_yv(_CI,_jV));}),_CM=function(_Av){return new F(function(){return _l5(_CL,_Av);});},_CN=new T(function(){return B(_yv(_CH,_jV));}),_CO=function(_Av){return new F(function(){return _l5(_CN,_Av);});},_CP=function(_CQ,_Av){return new F(function(){return _CO(_Av);});},_CR=function(_CS,_CT){return new F(function(){return _yv(_CI,_CT);});},_CU=new T4(0,_CP,_CM,_CI,_CR),_CV=function(_CW,_CX,_CY,_CZ,_D0){var _D1=new T(function(){return B(_zI(_CW,_CX,_D0));}),_D2=new T(function(){return B(_zG(_CZ));}),_D3=function(_D4){var _D5=function(_D6){var _D7=E(_D6),_D8=new T(function(){var _D9=new T(function(){var _Da=function(_Db){var _Dc=new T(function(){var _Dd=new T(function(){return B(A2(_D2,_D0,function(_De){return new F(function(){return A1(_D4,new T4(0,_D7.a,_D7.b,_Db,_De));});}));});return B(_wQ(function(_Df){var _Dg=E(_Df);return (_Dg._==2)?(!B(_lT(_Dg.a,_zF)))?new T0(2):E(_Dd):new T0(2);}));}),_Dh=function(_Di){return E(_Dc);};return new T1(1,function(_Dj){return new F(function(){return A2(_vx,_Dj,_Dh);});});};return B(A3(_zG,_CY,_D0,_Da));});return B(_wQ(function(_Dk){var _Dl=E(_Dk);return (_Dl._==2)?(!B(_lT(_Dl.a,_zF)))?new T0(2):E(_D9):new T0(2);}));}),_Dm=function(_Dn){return E(_D8);};return new T1(1,function(_Do){return new F(function(){return A2(_vx,_Do,_Dm);});});};return new F(function(){return A1(_D1,_D5);});};return E(_D3);},_Dp=function(_Dq,_Dr,_Ds,_Dt,_Du){var _Dv=function(_yt){return new F(function(){return _CV(_Dq,_Dr,_Ds,_Dt,_yt);});},_Dw=function(_Dx,_Dy){return new F(function(){return _Dz(_Dy);});},_Dz=function(_DA){return new F(function(){return _lf(new T1(1,B(_xo(_Dv,_DA))),new T(function(){return new T1(1,B(_xo(_Dw,_DA)));}));});};return new F(function(){return _Dz(_Du);});},_DB=function(_DC){var _DD=function(_DE){return E(new T2(3,_DC,_jU));};return new T1(1,function(_DF){return new F(function(){return A2(_vx,_DF,_DD);});});},_DG=new T(function(){return B(_Dp(_CU,_Cl,_Bz,_AF,_DB));}),_DH=function(_DI,_DJ,_DK,_DL){var _DM=E(_DI);if(_DM==1){var _DN=E(_DL);if(!_DN._){return new T3(0,new T(function(){var _DO=E(_DJ);return new T5(0,1,E(_DO),_DK,E(_0),E(_0));}),_1,_1);}else{var _DP=E(_DJ);return (_DP<E(E(_DN.a).a))?new T3(0,new T5(0,1,E(_DP),_DK,E(_0),E(_0)),_DN,_1):new T3(0,new T5(0,1,E(_DP),_DK,E(_0),E(_0)),_1,_DN);}}else{var _DQ=B(_DH(_DM>>1,_DJ,_DK,_DL)),_DR=_DQ.a,_DS=_DQ.c,_DT=E(_DQ.b);if(!_DT._){return new T3(0,_DR,_1,_DS);}else{var _DU=E(_DT.a),_DV=_DU.a,_DW=_DU.b,_DX=E(_DT.b);if(!_DX._){return new T3(0,new T(function(){return B(_O(_DV,_DW,_DR));}),_1,_DS);}else{var _DY=E(_DX.a),_DZ=E(_DV),_E0=E(_DY.a);if(_DZ<_E0){var _E1=B(_DH(_DM>>1,_E0,_DY.b,_DX.b));return new T3(0,new T(function(){return B(_2h(_DZ,_DW,_DR,_E1.a));}),_E1.b,_E1.c);}else{return new T3(0,_DR,_1,_DT);}}}}},_E2=function(_E3,_E4,_E5){var _E6=E(_E5);if(!_E6._){var _E7=_E6.c,_E8=_E6.d,_E9=_E6.e,_Ea=E(_E6.b);if(_E3>=_Ea){if(_E3!=_Ea){return new F(function(){return _6(_Ea,_E7,_E8,B(_E2(_E3,_E4,_E9)));});}else{return new T5(0,_E6.a,E(_E3),_E4,E(_E8),E(_E9));}}else{return new F(function(){return _X(_Ea,_E7,B(_E2(_E3,_E4,_E8)),_E9);});}}else{return new T5(0,1,E(_E3),_E4,E(_0),E(_0));}},_Eb=function(_Ec,_Ed){while(1){var _Ee=E(_Ed);if(!_Ee._){return E(_Ec);}else{var _Ef=E(_Ee.a),_Eg=B(_E2(E(_Ef.a),_Ef.b,_Ec));_Ec=_Eg;_Ed=_Ee.b;continue;}}},_Eh=function(_Ei,_Ej,_Ek,_El){return new F(function(){return _Eb(B(_E2(E(_Ej),_Ek,_Ei)),_El);});},_Em=function(_En,_Eo,_Ep){var _Eq=E(_Eo);return new F(function(){return _Eb(B(_E2(E(_Eq.a),_Eq.b,_En)),_Ep);});},_Er=function(_Es,_Et,_Eu){while(1){var _Ev=E(_Eu);if(!_Ev._){return E(_Et);}else{var _Ew=E(_Ev.a),_Ex=_Ew.a,_Ey=_Ew.b,_Ez=E(_Ev.b);if(!_Ez._){return new F(function(){return _O(_Ex,_Ey,_Et);});}else{var _EA=E(_Ez.a),_EB=E(_Ex),_EC=E(_EA.a);if(_EB<_EC){var _ED=B(_DH(_Es,_EC,_EA.b,_Ez.b)),_EE=_ED.a,_EF=E(_ED.c);if(!_EF._){var _EG=_Es<<1,_EH=B(_2h(_EB,_Ey,_Et,_EE));_Es=_EG;_Et=_EH;_Eu=_ED.b;continue;}else{return new F(function(){return _Em(B(_2h(_EB,_Ey,_Et,_EE)),_EF.a,_EF.b);});}}else{return new F(function(){return _Eh(_Et,_EB,_Ey,_Ez);});}}}}},_EI=function(_EJ,_EK,_EL,_EM,_EN){var _EO=E(_EN);if(!_EO._){return new F(function(){return _O(_EL,_EM,_EK);});}else{var _EP=E(_EO.a),_EQ=E(_EL),_ER=E(_EP.a);if(_EQ<_ER){var _ES=B(_DH(_EJ,_ER,_EP.b,_EO.b)),_ET=_ES.a,_EU=E(_ES.c);if(!_EU._){return new F(function(){return _Er(_EJ<<1,B(_2h(_EQ,_EM,_EK,_ET)),_ES.b);});}else{return new F(function(){return _Em(B(_2h(_EQ,_EM,_EK,_ET)),_EU.a,_EU.b);});}}else{return new F(function(){return _Eh(_EK,_EQ,_EM,_EO);});}}},_EV=function(_EW){var _EX=E(_EW);if(!_EX._){return new T0(1);}else{var _EY=E(_EX.a),_EZ=_EY.a,_F0=_EY.b,_F1=E(_EX.b);if(!_F1._){var _F2=E(_EZ);return new T5(0,1,E(_F2),_F0,E(_0),E(_0));}else{var _F3=_F1.b,_F4=E(_F1.a),_F5=_F4.b,_F6=E(_EZ),_F7=E(_F4.a);if(_F6<_F7){return new F(function(){return _EI(1,new T5(0,1,E(_F6),_F0,E(_0),E(_0)),_F7,_F5,_F3);});}else{return new F(function(){return _Eh(new T5(0,1,E(_F6),_F0,E(_0),E(_0)),_F7,_F5,_F3);});}}}},_F8=function(_){return _h9;},_F9=new T(function(){return B(unCStr(": Choose"));}),_Fa=new T(function(){return eval("(function (x, y, z) {var r = document.getElementById(\'actions\').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x + \' \')); var input = document.createElement(\'input\'); input.type = \'number\'; var ch = \'ibox\' + r.childNodes.length; input.id = ch; input.value = 0; input.style.setProperty(\'width\', \'5em\'); c1.appendChild(input); c1.appendChild(document.createTextNode(\' \' + y)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addActionWithNum(z, document.getElementById(ch).value);};})");}),_Fb=function(_Fc,_Fd,_){var _Fe=new T(function(){return B(A3(_is,_hk,new T2(1,function(_Ff){return new F(function(){return _j6(0,_Fc,_Ff);});},new T2(1,function(_Fg){return new F(function(){return _hA(0,E(_Fd),_Fg);});},_1)),_jv));}),_Fh=__app3(E(_Fa),toJSStr(B(unAppCStr("P",new T(function(){return B(_hq(B(_hA(0,E(_Fd),_1)),_F9));})))),toJSStr(B(unAppCStr("for choice with id ",new T(function(){return B(_hA(0,E(_Fc),_1));})))),toJSStr(new T2(1,_hz,_Fe)));return new F(function(){return _F8(_);});},_Fi=function(_Fj,_Fk,_){while(1){var _Fl=B((function(_Fm,_Fn,_){var _Fo=E(_Fn);if(!_Fo._){var _Fp=E(_Fo.b);_Fj=function(_){var _Fq=B(_Fb(_Fp.a,_Fp.b,_));return new F(function(){return _Fi(_Fm,_Fo.e,_);});};_Fk=_Fo.d;return __continue;}else{return new F(function(){return A1(_Fm,_);});}})(_Fj,_Fk,_));if(_Fl!=__continue){return _Fl;}}},_Fr=new T(function(){return B(unCStr("SIP "));}),_Fs=new T(function(){return B(unCStr("SIRC "));}),_Ft=new T(function(){return B(unCStr("SICC "));}),_Fu=function(_Fv,_Fw,_Fx){var _Fy=E(_Fw);switch(_Fy._){case 0:var _Fz=function(_FA){var _FB=new T(function(){var _FC=new T(function(){return B(_hA(11,E(_Fy.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.d),_FA));}))));});return B(_hA(11,E(_Fy.b),new T2(1,_hK,_FC)));});return new F(function(){return _hF(11,_Fy.a,new T2(1,_hK,_FB));});};if(_Fv<11){return new F(function(){return _hq(_Ft,new T(function(){return B(_Fz(_Fx));},1));});}else{var _FD=new T(function(){return B(_hq(_Ft,new T(function(){return B(_Fz(new T2(1,_hy,_Fx)));},1)));});return new T2(1,_hz,_FD);}break;case 1:var _FE=function(_FF){var _FG=new T(function(){var _FH=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FF));}))));});return B(_hF(11,_Fy.a,new T2(1,_hK,_FH)));},1);return new F(function(){return _hq(_Fs,_FG);});};if(_Fv<11){return new F(function(){return _FE(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FE(new T2(1,_hy,_Fx)));}));}break;default:var _FI=function(_FJ){var _FK=new T(function(){var _FL=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FJ));}))));});return B(_ih(11,_Fy.a,new T2(1,_hK,_FL)));},1);return new F(function(){return _hq(_Fr,_FK);});};if(_Fv<11){return new F(function(){return _FI(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FI(new T2(1,_hy,_Fx)));}));}}},_FM=new T(function(){return B(unCStr(" ADA"));}),_FN=new T(function(){return eval("(function (x, y) {var r = document.getElementById(\'actions\').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addAction(y);};})");}),_FO=function(_FP,_FQ,_FR,_){var _FS=new T(function(){var _FT=new T(function(){var _FU=new T(function(){var _FV=new T(function(){return B(unAppCStr(") of ",new T(function(){return B(_hq(B(_hA(0,E(_FR),_1)),_FM));})));},1);return B(_hq(B(_hA(0,E(_FP),_1)),_FV));});return B(unAppCStr(": Claim payment (with id: ",_FU));},1);return B(_hq(B(_hA(0,E(_FQ),_1)),_FT));}),_FW=__app2(E(_FN),toJSStr(B(unAppCStr("P",_FS))),toJSStr(B(_Fu(0,new T3(2,_FP,_FQ,_FR),_1))));return new F(function(){return _F8(_);});},_FX=function(_FY,_FZ,_){while(1){var _G0=B((function(_G1,_G2,_){var _G3=E(_G2);if(!_G3._){var _G4=E(_G3.b);_FY=function(_){var _G5=B(_FO(_G4.a,_G4.b,_G3.c,_));return new F(function(){return _FX(_G1,_G3.e,_);});};_FZ=_G3.d;return __continue;}else{return new F(function(){return A1(_G1,_);});}})(_FY,_FZ,_));if(_G0!=__continue){return _G0;}}},_G6=new T(function(){return B(unCStr(")"));}),_G7=function(_G8,_G9,_Ga,_){var _Gb=new T(function(){var _Gc=new T(function(){var _Gd=new T(function(){var _Ge=new T(function(){return B(unAppCStr(" ADA from commit (with id: ",new T(function(){return B(_hq(B(_hA(0,E(_G8),_1)),_G6));})));},1);return B(_hq(B(_hA(0,E(_Ga),_1)),_Ge));});return B(unAppCStr(": Redeem ",_Gd));},1);return B(_hq(B(_hA(0,E(_G9),_1)),_Gc));}),_Gf=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gb))),toJSStr(B(_Fu(0,new T3(1,_G8,_G9,_Ga),_1))));return new F(function(){return _F8(_);});},_Gg=function(_Gh,_Gi,_){while(1){var _Gj=B((function(_Gk,_Gl,_){var _Gm=E(_Gl);if(!_Gm._){var _Gn=E(_Gm.b);_Gh=function(_){var _Go=B(_G7(_Gn.a,_Gn.b,_Gn.c,_));return new F(function(){return _Gg(_Gk,_Gm.d,_);});};_Gi=_Gm.c;return __continue;}else{return new F(function(){return A1(_Gk,_);});}})(_Gh,_Gi,_));if(_Gj!=__continue){return _Gj;}}},_Gp=function(_){return _h9;},_Gq=function(_Gr,_Gs,_Gt,_Gu,_){var _Gv=new T(function(){var _Gw=new T(function(){var _Gx=new T(function(){var _Gy=new T(function(){var _Gz=new T(function(){var _GA=new T(function(){return B(unAppCStr(" ADA expiring on: ",new T(function(){return B(_hA(0,E(_Gu),_1));})));},1);return B(_hq(B(_hA(0,E(_Gt),_1)),_GA));});return B(unAppCStr(") of ",_Gz));},1);return B(_hq(B(_hA(0,E(_Gr),_1)),_Gy));});return B(unAppCStr(": Make commit (with id: ",_Gx));},1);return B(_hq(B(_hA(0,E(_Gs),_1)),_Gw));}),_GB=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gv))),toJSStr(B(_Fu(0,new T4(0,_Gr,_Gs,_Gt,_Gu),_1))));return new F(function(){return _F8(_);});},_GC=function(_GD,_GE,_){while(1){var _GF=B((function(_GG,_GH,_){var _GI=E(_GH);if(!_GI._){var _GJ=E(_GI.b);_GD=function(_){var _GK=B(_Gq(_GJ.a,_GJ.b,_GJ.c,_GJ.d,_));return new F(function(){return _GC(_GG,_GI.d,_);});};_GE=_GI.c;return __continue;}else{return new F(function(){return A1(_GG,_);});}})(_GD,_GE,_));if(_GF!=__continue){return _GF;}}},_GL=function(_GM,_GN,_GO,_GP,_){var _GQ=B(_GC(_Gp,_GM,_)),_GR=B(_Gg(_Gp,_GN,_)),_GS=B(_FX(_Gp,_GO,_));return new F(function(){return _Fi(_Gp,_GP,_);});},_GT=function(_GU,_GV){return E(_GU)==E(_GV);},_GW=function(_GX,_GY){while(1){var _GZ=E(_GX);switch(_GZ._){case 0:var _H0=E(_GY);if(!_H0._){return new F(function(){return _GT(_GZ.a,_H0.a);});}else{return false;}break;case 1:var _H1=E(_GY);if(_H1._==1){if(!B(_GW(_GZ.a,_H1.a))){return false;}else{_GX=_GZ.b;_GY=_H1.b;continue;}}else{return false;}break;case 2:var _H2=E(_GY);if(_H2._==2){return new F(function(){return _GT(_GZ.a,_H2.a);});}else{return false;}break;default:var _H3=E(_GY);if(_H3._==3){if(E(_GZ.a)!=E(_H3.a)){return false;}else{if(E(_GZ.b)!=E(_H3.b)){return false;}else{_GX=_GZ.c;_GY=_H3.c;continue;}}}else{return false;}}}},_H4=function(_H5,_H6){while(1){var _H7=E(_H5);switch(_H7._){case 0:var _H8=E(_H6);if(!_H8._){return new F(function(){return _GT(_H7.a,_H8.a);});}else{return false;}break;case 1:var _H9=E(_H6);if(_H9._==1){if(!B(_H4(_H7.a,_H9.a))){return false;}else{_H5=_H7.b;_H6=_H9.b;continue;}}else{return false;}break;case 2:var _Ha=E(_H6);if(_Ha._==2){if(!B(_H4(_H7.a,_Ha.a))){return false;}else{_H5=_H7.b;_H6=_Ha.b;continue;}}else{return false;}break;case 3:var _Hb=E(_H6);if(_Hb._==3){_H5=_H7.a;_H6=_Hb.a;continue;}else{return false;}break;case 4:var _Hc=E(_H6);if(_Hc._==4){if(E(_H7.a)!=E(_Hc.a)){return false;}else{if(E(_H7.b)!=E(_Hc.b)){return false;}else{return new F(function(){return _GT(_H7.c,_Hc.c);});}}}else{return false;}break;case 5:var _Hd=E(_H6);if(_Hd._==5){if(E(_H7.a)!=E(_Hd.a)){return false;}else{return new F(function(){return _GT(_H7.b,_Hd.b);});}}else{return false;}break;case 6:var _He=E(_H6);if(_He._==6){if(!B(_GW(_H7.a,_He.a))){return false;}else{return new F(function(){return _GW(_H7.b,_He.b);});}}else{return false;}break;case 7:return (E(_H6)._==7)?true:false;default:return (E(_H6)._==8)?true:false;}}},_Hf=function(_Hg,_Hh){while(1){var _Hi=E(_Hg);switch(_Hi._){case 0:return (E(_Hh)._==0)?true:false;case 1:var _Hj=E(_Hh);if(_Hj._==1){if(E(_Hi.a)!=E(_Hj.a)){return false;}else{if(E(_Hi.b)!=E(_Hj.b)){return false;}else{if(!B(_GW(_Hi.c,_Hj.c))){return false;}else{if(E(_Hi.d)!=E(_Hj.d)){return false;}else{if(E(_Hi.e)!=E(_Hj.e)){return false;}else{if(!B(_Hf(_Hi.f,_Hj.f))){return false;}else{_Hg=_Hi.g;_Hh=_Hj.g;continue;}}}}}}}else{return false;}break;case 2:var _Hk=E(_Hh);if(_Hk._==2){if(E(_Hi.a)!=E(_Hk.a)){return false;}else{_Hg=_Hi.b;_Hh=_Hk.b;continue;}}else{return false;}break;case 3:var _Hl=E(_Hh);if(_Hl._==3){if(E(_Hi.a)!=E(_Hl.a)){return false;}else{if(E(_Hi.b)!=E(_Hl.b)){return false;}else{if(E(_Hi.c)!=E(_Hl.c)){return false;}else{if(!B(_GW(_Hi.d,_Hl.d))){return false;}else{if(E(_Hi.e)!=E(_Hl.e)){return false;}else{_Hg=_Hi.f;_Hh=_Hl.f;continue;}}}}}}else{return false;}break;case 4:var _Hm=E(_Hh);if(_Hm._==4){if(!B(_Hf(_Hi.a,_Hm.a))){return false;}else{_Hg=_Hi.b;_Hh=_Hm.b;continue;}}else{return false;}break;case 5:var _Hn=E(_Hh);if(_Hn._==5){if(!B(_H4(_Hi.a,_Hn.a))){return false;}else{if(!B(_Hf(_Hi.b,_Hn.b))){return false;}else{_Hg=_Hi.c;_Hh=_Hn.c;continue;}}}else{return false;}break;default:var _Ho=E(_Hh);if(_Ho._==6){if(!B(_H4(_Hi.a,_Ho.a))){return false;}else{if(E(_Hi.b)!=E(_Ho.b)){return false;}else{if(!B(_Hf(_Hi.c,_Ho.c))){return false;}else{_Hg=_Hi.d;_Hh=_Ho.d;continue;}}}}else{return false;}}}},_Hp=function(_Hq,_Hr,_Hs,_Ht){if(_Hq!=_Hs){return false;}else{return new F(function(){return _GT(_Hr,_Ht);});}},_Hu=function(_Hv,_Hw){var _Hx=E(_Hv),_Hy=E(_Hw);return new F(function(){return _Hp(E(_Hx.a),_Hx.b,E(_Hy.a),_Hy.b);});},_Hz=function(_HA,_HB,_HC,_HD){return (_HA!=_HC)?true:(E(_HB)!=E(_HD))?true:false;},_HE=function(_HF,_HG){var _HH=E(_HF),_HI=E(_HG);return new F(function(){return _Hz(E(_HH.a),_HH.b,E(_HI.a),_HI.b);});},_HJ=new T2(0,_Hu,_HE),_HK=function(_HL,_HM){return E(_HL)!=E(_HM);},_HN=new T2(0,_GT,_HK),_HO=function(_HP,_HQ,_HR,_HS,_HT,_HU){return (!B(A3(_pR,_HP,_HR,_HT)))?true:(!B(A3(_pR,_HQ,_HS,_HU)))?true:false;},_HV=function(_HW,_HX,_HY,_HZ){var _I0=E(_HY),_I1=E(_HZ);return new F(function(){return _HO(_HW,_HX,_I0.a,_I0.b,_I1.a,_I1.b);});},_I2=function(_I3,_I4,_I5,_I6,_I7,_I8){if(!B(A3(_pR,_I3,_I5,_I7))){return false;}else{return new F(function(){return A3(_pR,_I4,_I6,_I8);});}},_I9=function(_Ia,_Ib,_Ic,_Id){var _Ie=E(_Ic),_If=E(_Id);return new F(function(){return _I2(_Ia,_Ib,_Ie.a,_Ie.b,_If.a,_If.b);});},_Ig=function(_Ih,_Ii){return new T2(0,function(_Ij,_Ik){return new F(function(){return _I9(_Ih,_Ii,_Ij,_Ik);});},function(_Ij,_Ik){return new F(function(){return _HV(_Ih,_Ii,_Ij,_Ik);});});},_Il=function(_Im,_In,_Io){while(1){var _Ip=E(_In);if(!_Ip._){return (E(_Io)._==0)?true:false;}else{var _Iq=E(_Io);if(!_Iq._){return false;}else{if(!B(A3(_pR,_Im,_Ip.a,_Iq.a))){return false;}else{_In=_Ip.b;_Io=_Iq.b;continue;}}}}},_Ir=function(_Is,_It){var _Iu=new T(function(){return B(_Ig(_Is,_It));}),_Iv=function(_Iw,_Ix){var _Iy=function(_Iz){var _IA=function(_IB){if(_Iz!=_IB){return false;}else{return new F(function(){return _Il(_Iu,B(_hc(_1,_Iw)),B(_hc(_1,_Ix)));});}},_IC=E(_Ix);if(!_IC._){return new F(function(){return _IA(_IC.a);});}else{return new F(function(){return _IA(0);});}},_ID=E(_Iw);if(!_ID._){return new F(function(){return _Iy(_ID.a);});}else{return new F(function(){return _Iy(0);});}};return E(_Iv);},_IE=new T(function(){return B(_Ir(_HJ,_HN));}),_IF=new T2(0,_GT,_HK),_IG=function(_IH,_II){var _IJ=E(_IH);if(!_IJ._){var _IK=E(_II);if(!_IK._){if(E(_IJ.a)!=E(_IK.a)){return false;}else{return new F(function(){return _GT(_IJ.b,_IK.b);});}}else{return false;}}else{return (E(_II)._==0)?false:true;}},_IL=function(_IM,_IN,_IO,_IP){if(_IM!=_IO){return false;}else{return new F(function(){return _IG(_IN,_IP);});}},_IQ=function(_IR,_IS){var _IT=E(_IR),_IU=E(_IS);return new F(function(){return _IL(E(_IT.a),_IT.b,E(_IU.a),_IU.b);});},_IV=function(_IW,_IX,_IY,_IZ){if(_IW!=_IY){return true;}else{var _J0=E(_IX);if(!_J0._){var _J1=E(_IZ);return (_J1._==0)?(E(_J0.a)!=E(_J1.a))?true:(E(_J0.b)!=E(_J1.b))?true:false:true;}else{return (E(_IZ)._==0)?true:false;}}},_J2=function(_J3,_J4){var _J5=E(_J3),_J6=E(_J4);return new F(function(){return _IV(E(_J5.a),_J5.b,E(_J6.a),_J6.b);});},_J7=new T2(0,_IQ,_J2),_J8=new T(function(){return B(_Ir(_IF,_J7));}),_J9=function(_Ja,_Jb){var _Jc=E(_Ja),_Jd=E(_Jb);return (_Jc>_Jd)?E(_Jc):E(_Jd);},_Je=function(_Jf,_Jg){var _Jh=E(_Jf),_Ji=E(_Jg);return (_Jh>_Ji)?E(_Ji):E(_Jh);},_Jj=function(_Jk,_Jl){return (_Jk>=_Jl)?(_Jk!=_Jl)?2:1:0;},_Jm=function(_Jn,_Jo){return new F(function(){return _Jj(E(_Jn),E(_Jo));});},_Jp=function(_Jq,_Jr){return E(_Jq)>=E(_Jr);},_Js=function(_Jt,_Ju){return E(_Jt)>E(_Ju);},_Jv=function(_Jw,_Jx){return E(_Jw)<=E(_Jx);},_Jy=function(_Jz,_JA){return E(_Jz)<E(_JA);},_JB={_:0,a:_IF,b:_Jm,c:_Jy,d:_Jv,e:_Js,f:_Jp,g:_J9,h:_Je},_JC=function(_JD,_JE,_JF,_JG,_JH){while(1){var _JI=E(_JH);if(!_JI._){var _JJ=_JI.c,_JK=_JI.d,_JL=E(_JI.b),_JM=E(_JL.a);if(_JD>=_JM){if(_JD!=_JM){_JE=_;_JH=_JK;continue;}else{var _JN=E(_JL.b);if(_JF>=_JN){if(_JF!=_JN){_JE=_;_JH=_JK;continue;}else{var _JO=E(_JL.c);if(_JG>=_JO){if(_JG!=_JO){_JE=_;_JH=_JK;continue;}else{return true;}}else{_JE=_;_JH=_JJ;continue;}}}else{_JE=_;_JH=_JJ;continue;}}}else{_JE=_;_JH=_JJ;continue;}}else{return false;}}},_JP=function(_JQ,_JR,_JS,_JT,_JU){while(1){var _JV=E(_JU);if(!_JV._){var _JW=_JV.c,_JX=_JV.d,_JY=E(_JV.b),_JZ=E(_JY.a);if(_JQ>=_JZ){if(_JQ!=_JZ){_JR=_;_JU=_JX;continue;}else{var _K0=E(_JY.b);if(_JS>=_K0){if(_JS!=_K0){_JR=_;_JU=_JX;continue;}else{var _K1=E(_JT),_K2=E(_JY.c);if(_K1>=_K2){if(_K1!=_K2){return new F(function(){return _JC(_JQ,_,_JS,_K1,_JX);});}else{return true;}}else{return new F(function(){return _JC(_JQ,_,_JS,_K1,_JW);});}}}else{_JR=_;_JU=_JW;continue;}}}else{_JR=_;_JU=_JW;continue;}}else{return false;}}},_K3=function(_K4,_K5,_K6,_K7,_K8){while(1){var _K9=E(_K8);if(!_K9._){var _Ka=_K9.c,_Kb=_K9.d,_Kc=E(_K9.b),_Kd=E(_Kc.a);if(_K4>=_Kd){if(_K4!=_Kd){_K5=_;_K8=_Kb;continue;}else{var _Ke=E(_K6),_Kf=E(_Kc.b);if(_Ke>=_Kf){if(_Ke!=_Kf){return new F(function(){return _JP(_K4,_,_Ke,_K7,_Kb);});}else{var _Kg=E(_K7),_Kh=E(_Kc.c);if(_Kg>=_Kh){if(_Kg!=_Kh){return new F(function(){return _JC(_K4,_,_Ke,_Kg,_Kb);});}else{return true;}}else{return new F(function(){return _JC(_K4,_,_Ke,_Kg,_Ka);});}}}else{return new F(function(){return _JP(_K4,_,_Ke,_K7,_Ka);});}}}else{_K5=_;_K8=_Ka;continue;}}else{return false;}}},_Ki=function(_Kj,_Kk,_Kl,_Km){var _Kn=E(_Km);if(!_Kn._){var _Ko=_Kn.c,_Kp=_Kn.d,_Kq=E(_Kn.b),_Kr=E(_Kj),_Ks=E(_Kq.a);if(_Kr>=_Ks){if(_Kr!=_Ks){return new F(function(){return _K3(_Kr,_,_Kk,_Kl,_Kp);});}else{var _Kt=E(_Kk),_Ku=E(_Kq.b);if(_Kt>=_Ku){if(_Kt!=_Ku){return new F(function(){return _JP(_Kr,_,_Kt,_Kl,_Kp);});}else{var _Kv=E(_Kl),_Kw=E(_Kq.c);if(_Kv>=_Kw){if(_Kv!=_Kw){return new F(function(){return _JC(_Kr,_,_Kt,_Kv,_Kp);});}else{return true;}}else{return new F(function(){return _JC(_Kr,_,_Kt,_Kv,_Ko);});}}}else{return new F(function(){return _JP(_Kr,_,_Kt,_Kl,_Ko);});}}}else{return new F(function(){return _K3(_Kr,_,_Kk,_Kl,_Ko);});}}else{return false;}},_Kx=function(_Ky,_Kz,_KA,_KB,_KC){var _KD=E(_KC);if(!_KD._){if(E(_KD.b)>E(_Kz)){return false;}else{return new F(function(){return _Ki(_KA,_KB,_KD.a,E(_Ky).b);});}}else{return false;}},_KE=function(_KF,_KG,_KH,_KI,_KJ){var _KK=E(_KJ);if(!_KK._){var _KL=new T(function(){var _KM=B(_KE(_KK.a,_KK.b,_KK.c,_KK.d,_KK.e));return new T2(0,_KM.a,_KM.b);});return new T2(0,new T(function(){return E(E(_KL).a);}),new T(function(){return B(_X(_KG,_KH,_KI,E(_KL).b));}));}else{return new T2(0,new T2(0,_KG,_KH),_KI);}},_KN=function(_KO,_KP,_KQ,_KR,_KS){var _KT=E(_KR);if(!_KT._){var _KU=new T(function(){var _KV=B(_KN(_KT.a,_KT.b,_KT.c,_KT.d,_KT.e));return new T2(0,_KV.a,_KV.b);});return new T2(0,new T(function(){return E(E(_KU).a);}),new T(function(){return B(_6(_KP,_KQ,E(_KU).b,_KS));}));}else{return new T2(0,new T2(0,_KP,_KQ),_KS);}},_KW=function(_KX,_KY){var _KZ=E(_KX);if(!_KZ._){var _L0=_KZ.a,_L1=E(_KY);if(!_L1._){var _L2=_L1.a;if(_L0<=_L2){var _L3=B(_KN(_L2,_L1.b,_L1.c,_L1.d,_L1.e)),_L4=E(_L3.a);return new F(function(){return _X(_L4.a,_L4.b,_KZ,_L3.b);});}else{var _L5=B(_KE(_L0,_KZ.b,_KZ.c,_KZ.d,_KZ.e)),_L6=E(_L5.a);return new F(function(){return _6(_L6.a,_L6.b,_L5.b,_L1);});}}else{return E(_KZ);}}else{return E(_KY);}},_L7=function(_L8,_L9,_La,_Lb,_Lc,_Ld){var _Le=E(_L8);if(!_Le._){var _Lf=_Le.a,_Lg=_Le.b,_Lh=_Le.c,_Li=_Le.d,_Lj=_Le.e;if((imul(3,_Lf)|0)>=_L9){if((imul(3,_L9)|0)>=_Lf){return new F(function(){return _KW(_Le,new T5(0,_L9,E(_La),_Lb,E(_Lc),E(_Ld)));});}else{return new F(function(){return _6(_Lg,_Lh,_Li,B(_L7(_Lj,_L9,_La,_Lb,_Lc,_Ld)));});}}else{return new F(function(){return _X(_La,_Lb,B(_Lk(_Lf,_Lg,_Lh,_Li,_Lj,_Lc)),_Ld);});}}else{return new T5(0,_L9,E(_La),_Lb,E(_Lc),E(_Ld));}},_Lk=function(_Ll,_Lm,_Ln,_Lo,_Lp,_Lq){var _Lr=E(_Lq);if(!_Lr._){var _Ls=_Lr.a,_Lt=_Lr.b,_Lu=_Lr.c,_Lv=_Lr.d,_Lw=_Lr.e;if((imul(3,_Ll)|0)>=_Ls){if((imul(3,_Ls)|0)>=_Ll){return new F(function(){return _KW(new T5(0,_Ll,E(_Lm),_Ln,E(_Lo),E(_Lp)),_Lr);});}else{return new F(function(){return _6(_Lm,_Ln,_Lo,B(_L7(_Lp,_Ls,_Lt,_Lu,_Lv,_Lw)));});}}else{return new F(function(){return _X(_Lt,_Lu,B(_Lk(_Ll,_Lm,_Ln,_Lo,_Lp,_Lv)),_Lw);});}}else{return new T5(0,_Ll,E(_Lm),_Ln,E(_Lo),E(_Lp));}},_Lx=function(_Ly,_Lz){var _LA=E(_Ly);if(!_LA._){var _LB=_LA.a,_LC=_LA.b,_LD=_LA.c,_LE=_LA.d,_LF=_LA.e,_LG=E(_Lz);if(!_LG._){var _LH=_LG.a,_LI=_LG.b,_LJ=_LG.c,_LK=_LG.d,_LL=_LG.e;if((imul(3,_LB)|0)>=_LH){if((imul(3,_LH)|0)>=_LB){return new F(function(){return _KW(_LA,_LG);});}else{return new F(function(){return _6(_LC,_LD,_LE,B(_L7(_LF,_LH,_LI,_LJ,_LK,_LL)));});}}else{return new F(function(){return _X(_LI,_LJ,B(_Lk(_LB,_LC,_LD,_LE,_LF,_LK)),_LL);});}}else{return E(_LA);}}else{return E(_Lz);}},_LM=function(_LN,_LO){var _LP=E(_LO);if(!_LP._){var _LQ=_LP.b,_LR=_LP.c,_LS=B(_LM(_LN,_LP.d)),_LT=_LS.a,_LU=_LS.b,_LV=B(_LM(_LN,_LP.e)),_LW=_LV.a,_LX=_LV.b;return (!B(A2(_LN,_LQ,_LR)))?new T2(0,B(_Lx(_LT,_LW)),B(_2h(_LQ,_LR,_LU,_LX))):new T2(0,B(_2h(_LQ,_LR,_LT,_LW)),B(_Lx(_LU,_LX)));}else{return new T2(0,_0,_0);}},_LY=__Z,_LZ=function(_M0,_M1){while(1){var _M2=B((function(_M3,_M4){var _M5=E(_M4);if(!_M5._){var _M6=_M5.e,_M7=new T(function(){var _M8=E(_M5.c),_M9=E(_M8.b);if(!_M9._){return new T2(1,new T3(5,_M5.b,_M8.a,_M9.a),new T(function(){return B(_LZ(_M3,_M6));}));}else{return B(_LZ(_M3,_M6));}},1);_M0=_M7;_M1=_M5.d;return __continue;}else{return E(_M3);}})(_M0,_M1));if(_M2!=__continue){return _M2;}}},_Ma=function(_Mb,_Mc){var _Md=E(_Mc);return (_Md._==0)?new T5(0,_Md.a,E(_Md.b),new T(function(){return B(A1(_Mb,_Md.c));}),E(B(_Ma(_Mb,_Md.d))),E(B(_Ma(_Mb,_Md.e)))):new T0(1);},_Me=new T0(1),_Mf=function(_Mg){var _Mh=E(_Mg),_Mi=E(_Mh.b);return new T2(0,_Mh.a,_Me);},_Mj=function(_Mk){return E(E(_Mk).b);},_Ml=function(_Mm,_Mn,_Mo){var _Mp=E(_Mn);if(!_Mp._){return E(_Mo);}else{var _Mq=function(_Mr,_Ms){while(1){var _Mt=E(_Ms);if(!_Mt._){var _Mu=_Mt.b,_Mv=_Mt.e;switch(B(A3(_Mj,_Mm,_Mr,_Mu))){case 0:return new F(function(){return _2h(_Mu,_Mt.c,B(_Mq(_Mr,_Mt.d)),_Mv);});break;case 1:return E(_Mv);default:_Ms=_Mv;continue;}}else{return new T0(1);}}};return new F(function(){return _Mq(_Mp.a,_Mo);});}},_Mw=function(_Mx,_My,_Mz){var _MA=E(_My);if(!_MA._){return E(_Mz);}else{var _MB=function(_MC,_MD){while(1){var _ME=E(_MD);if(!_ME._){var _MF=_ME.b,_MG=_ME.d;switch(B(A3(_Mj,_Mx,_MF,_MC))){case 0:return new F(function(){return _2h(_MF,_ME.c,_MG,B(_MB(_MC,_ME.e)));});break;case 1:return E(_MG);default:_MD=_MG;continue;}}else{return new T0(1);}}};return new F(function(){return _MB(_MA.a,_Mz);});}},_MH=function(_MI,_MJ,_MK,_ML){var _MM=E(_MJ),_MN=E(_ML);if(!_MN._){var _MO=_MN.b,_MP=_MN.c,_MQ=_MN.d,_MR=_MN.e;switch(B(A3(_Mj,_MI,_MM,_MO))){case 0:return new F(function(){return _X(_MO,_MP,B(_MH(_MI,_MM,_MK,_MQ)),_MR);});break;case 1:return E(_MN);default:return new F(function(){return _6(_MO,_MP,_MQ,B(_MH(_MI,_MM,_MK,_MR)));});}}else{return new T5(0,1,E(_MM),_MK,E(_0),E(_0));}},_MS=function(_MT,_MU,_MV,_MW){return new F(function(){return _MH(_MT,_MU,_MV,_MW);});},_MX=function(_MY){return E(E(_MY).d);},_MZ=function(_N0){return E(E(_N0).f);},_N1=function(_N2,_N3,_N4,_N5){var _N6=E(_N3);if(!_N6._){var _N7=E(_N4);if(!_N7._){return E(_N5);}else{var _N8=function(_N9,_Na){while(1){var _Nb=E(_Na);if(!_Nb._){if(!B(A3(_MZ,_N2,_Nb.b,_N9))){return E(_Nb);}else{_Na=_Nb.d;continue;}}else{return new T0(1);}}};return new F(function(){return _N8(_N7.a,_N5);});}}else{var _Nc=_N6.a,_Nd=E(_N4);if(!_Nd._){var _Ne=function(_Nf,_Ng){while(1){var _Nh=E(_Ng);if(!_Nh._){if(!B(A3(_MX,_N2,_Nh.b,_Nf))){return E(_Nh);}else{_Ng=_Nh.e;continue;}}else{return new T0(1);}}};return new F(function(){return _Ne(_Nc,_N5);});}else{var _Ni=function(_Nj,_Nk,_Nl){while(1){var _Nm=E(_Nl);if(!_Nm._){var _Nn=_Nm.b;if(!B(A3(_MX,_N2,_Nn,_Nj))){if(!B(A3(_MZ,_N2,_Nn,_Nk))){return E(_Nm);}else{_Nl=_Nm.d;continue;}}else{_Nl=_Nm.e;continue;}}else{return new T0(1);}}};return new F(function(){return _Ni(_Nc,_Nd.a,_N5);});}}},_No=function(_Np,_Nq,_Nr,_Ns,_Nt){var _Nu=E(_Nt);if(!_Nu._){var _Nv=_Nu.b,_Nw=_Nu.c,_Nx=_Nu.d,_Ny=_Nu.e,_Nz=E(_Ns);if(!_Nz._){var _NA=_Nz.b,_NB=function(_NC){var _ND=new T1(1,E(_NA));return new F(function(){return _2h(_NA,_Nz.c,B(_No(_Np,_Nq,_ND,_Nz.d,B(_N1(_Np,_Nq,_ND,_Nu)))),B(_No(_Np,_ND,_Nr,_Nz.e,B(_N1(_Np,_ND,_Nr,_Nu)))));});};if(!E(_Nx)._){return new F(function(){return _NB(_);});}else{if(!E(_Ny)._){return new F(function(){return _NB(_);});}else{return new F(function(){return _MS(_Np,_Nv,_Nw,_Nz);});}}}else{return new F(function(){return _2h(_Nv,_Nw,B(_Ml(_Np,_Nq,_Nx)),B(_Mw(_Np,_Nr,_Ny)));});}}else{return E(_Ns);}},_NE=function(_NF,_NG,_NH,_NI,_NJ,_NK,_NL,_NM,_NN,_NO,_NP,_NQ,_NR){var _NS=function(_NT){var _NU=new T1(1,E(_NJ));return new F(function(){return _2h(_NJ,_NK,B(_No(_NF,_NG,_NU,_NL,B(_N1(_NF,_NG,_NU,new T5(0,_NN,E(_NO),_NP,E(_NQ),E(_NR)))))),B(_No(_NF,_NU,_NH,_NM,B(_N1(_NF,_NU,_NH,new T5(0,_NN,E(_NO),_NP,E(_NQ),E(_NR)))))));});};if(!E(_NQ)._){return new F(function(){return _NS(_);});}else{if(!E(_NR)._){return new F(function(){return _NS(_);});}else{return new F(function(){return _MS(_NF,_NO,_NP,new T5(0,_NI,E(_NJ),_NK,E(_NL),E(_NM)));});}}},_NV=function(_NW,_NX,_NY){var _NZ=new T(function(){var _O0=new T(function(){return E(E(_NY).b);}),_O1=B(_LM(function(_O2,_O3){var _O4=E(_O3);return new F(function(){return _Kx(_NW,_O0,_O2,_O4.a,_O4.b);});},_NX));return new T2(0,_O1.a,_O1.b);}),_O5=new T(function(){return E(E(_NZ).a);});return new T2(0,new T(function(){var _O6=B(_Ma(_Mf,_O5));if(!_O6._){var _O7=E(E(_NZ).b);if(!_O7._){return B(_NE(_JB,_LY,_LY,_O6.a,_O6.b,_O6.c,_O6.d,_O6.e,_O7.a,_O7.b,_O7.c,_O7.d,_O7.e));}else{return E(_O6);}}else{return E(E(_NZ).b);}}),new T(function(){return B(_LZ(_1,_O5));}));},_O8=function(_O9,_Oa,_Ob,_Oc){while(1){var _Od=E(_Oc);if(!_Od._){var _Oe=_Od.d,_Of=_Od.e,_Og=E(_Od.b),_Oh=E(_Og.a);if(_O9>=_Oh){if(_O9!=_Oh){_Oa=_;_Oc=_Of;continue;}else{var _Oi=E(_Og.b);if(_Ob>=_Oi){if(_Ob!=_Oi){_Oa=_;_Oc=_Of;continue;}else{return true;}}else{_Oa=_;_Oc=_Oe;continue;}}}else{_Oa=_;_Oc=_Oe;continue;}}else{return false;}}},_Oj=function(_Ok,_Ol,_Om,_On){while(1){var _Oo=E(_On);if(!_Oo._){var _Op=_Oo.d,_Oq=_Oo.e,_Or=E(_Oo.b),_Os=E(_Or.a);if(_Ok>=_Os){if(_Ok!=_Os){_Ol=_;_On=_Oq;continue;}else{var _Ot=E(_Om),_Ou=E(_Or.b);if(_Ot>=_Ou){if(_Ot!=_Ou){return new F(function(){return _O8(_Ok,_,_Ot,_Oq);});}else{return true;}}else{return new F(function(){return _O8(_Ok,_,_Ot,_Op);});}}}else{_Ol=_;_On=_Op;continue;}}else{return false;}}},_Ov=function(_Ow,_Ox,_Oy,_Oz,_OA){var _OB=E(_OA);if(!_OB._){var _OC=_OB.c,_OD=_OB.d,_OE=_OB.e,_OF=E(_OB.b),_OG=E(_OF.a);if(_Ow>=_OG){if(_Ow!=_OG){return new F(function(){return _6(_OF,_OC,_OD,B(_Ov(_Ow,_,_Oy,_Oz,_OE)));});}else{var _OH=E(_OF.b);if(_Oy>=_OH){if(_Oy!=_OH){return new F(function(){return _6(_OF,_OC,_OD,B(_Ov(_Ow,_,_Oy,_Oz,_OE)));});}else{return new T5(0,_OB.a,E(new T2(0,_Ow,_Oy)),_Oz,E(_OD),E(_OE));}}else{return new F(function(){return _X(_OF,_OC,B(_Ov(_Ow,_,_Oy,_Oz,_OD)),_OE);});}}}else{return new F(function(){return _X(_OF,_OC,B(_Ov(_Ow,_,_Oy,_Oz,_OD)),_OE);});}}else{return new T5(0,1,E(new T2(0,_Ow,_Oy)),_Oz,E(_0),E(_0));}},_OI=function(_OJ,_OK,_OL,_OM,_ON){var _OO=E(_ON);if(!_OO._){var _OP=_OO.c,_OQ=_OO.d,_OR=_OO.e,_OS=E(_OO.b),_OT=E(_OS.a);if(_OJ>=_OT){if(_OJ!=_OT){return new F(function(){return _6(_OS,_OP,_OQ,B(_OI(_OJ,_,_OL,_OM,_OR)));});}else{var _OU=E(_OL),_OV=E(_OS.b);if(_OU>=_OV){if(_OU!=_OV){return new F(function(){return _6(_OS,_OP,_OQ,B(_Ov(_OJ,_,_OU,_OM,_OR)));});}else{return new T5(0,_OO.a,E(new T2(0,_OJ,_OU)),_OM,E(_OQ),E(_OR));}}else{return new F(function(){return _X(_OS,_OP,B(_Ov(_OJ,_,_OU,_OM,_OQ)),_OR);});}}}else{return new F(function(){return _X(_OS,_OP,B(_OI(_OJ,_,_OL,_OM,_OQ)),_OR);});}}else{return new T5(0,1,E(new T2(0,_OJ,_OL)),_OM,E(_0),E(_0));}},_OW=function(_OX,_OY,_OZ,_P0){var _P1=E(_P0);if(!_P1._){var _P2=_P1.c,_P3=_P1.d,_P4=_P1.e,_P5=E(_P1.b),_P6=E(_OX),_P7=E(_P5.a);if(_P6>=_P7){if(_P6!=_P7){return new F(function(){return _6(_P5,_P2,_P3,B(_OI(_P6,_,_OY,_OZ,_P4)));});}else{var _P8=E(_OY),_P9=E(_P5.b);if(_P8>=_P9){if(_P8!=_P9){return new F(function(){return _6(_P5,_P2,_P3,B(_Ov(_P6,_,_P8,_OZ,_P4)));});}else{return new T5(0,_P1.a,E(new T2(0,_P6,_P8)),_OZ,E(_P3),E(_P4));}}else{return new F(function(){return _X(_P5,_P2,B(_Ov(_P6,_,_P8,_OZ,_P3)),_P4);});}}}else{return new F(function(){return _X(_P5,_P2,B(_OI(_P6,_,_OY,_OZ,_P3)),_P4);});}}else{return new T5(0,1,E(new T2(0,_OX,_OY)),_OZ,E(_0),E(_0));}},_Pa=function(_Pb,_Pc,_Pd){while(1){var _Pe=B((function(_Pf,_Pg,_Ph){var _Pi=E(_Ph);if(!_Pi._){var _Pj=_Pi.c,_Pk=_Pi.e,_Pl=E(_Pi.b),_Pm=_Pl.a,_Pn=_Pl.b,_Po=B(_Pa(_Pf,_Pg,_Pi.d)),_Pp=_Po.a,_Pq=_Po.b,_Pr=function(_Ps){return new F(function(){return _Pa(new T(function(){return B(_OW(_Pm,_Pn,_Pj,_Pp));}),new T2(1,new T3(7,_Pm,_Pn,_Pj),_Pq),_Pk);});},_Pt=E(_Pp);if(!_Pt._){var _Pu=_Pt.d,_Pv=_Pt.e,_Pw=E(_Pt.b),_Px=E(_Pm),_Py=E(_Pw.a);if(_Px>=_Py){if(_Px!=_Py){if(!B(_Oj(_Px,_,_Pn,_Pv))){return new F(function(){return _Pr(_);});}else{_Pb=_Pt;_Pc=_Pq;_Pd=_Pk;return __continue;}}else{var _Pz=E(_Pn),_PA=E(_Pw.b);if(_Pz>=_PA){if(_Pz!=_PA){if(!B(_O8(_Px,_,_Pz,_Pv))){return new F(function(){return _Pr(_);});}else{_Pb=_Pt;_Pc=_Pq;_Pd=_Pk;return __continue;}}else{_Pb=_Pt;_Pc=_Pq;_Pd=_Pk;return __continue;}}else{if(!B(_O8(_Px,_,_Pz,_Pu))){return new F(function(){return _Pr(_);});}else{_Pb=_Pt;_Pc=_Pq;_Pd=_Pk;return __continue;}}}}else{if(!B(_Oj(_Px,_,_Pn,_Pu))){return new F(function(){return _Pr(_);});}else{_Pb=_Pt;_Pc=_Pq;_Pd=_Pk;return __continue;}}}else{return new F(function(){return _Pr(_);});}}else{return new T2(0,_Pf,_Pg);}})(_Pb,_Pc,_Pd));if(_Pe!=__continue){return _Pe;}}},_PB=function(_PC,_PD,_PE,_PF){while(1){var _PG=E(_PF);if(!_PG._){var _PH=_PG.d,_PI=_PG.e,_PJ=E(_PG.b),_PK=E(_PJ.a);if(_PC>=_PK){if(_PC!=_PK){_PD=_;_PF=_PI;continue;}else{var _PL=E(_PJ.b);if(_PE>=_PL){if(_PE!=_PL){_PD=_;_PF=_PI;continue;}else{return new T1(1,_PG.c);}}else{_PD=_;_PF=_PH;continue;}}}else{_PD=_;_PF=_PH;continue;}}else{return __Z;}}},_PM=function(_PN,_PO,_PP,_PQ){while(1){var _PR=E(_PQ);if(!_PR._){var _PS=_PR.d,_PT=_PR.e,_PU=E(_PR.b),_PV=E(_PU.a);if(_PN>=_PV){if(_PN!=_PV){_PO=_;_PQ=_PT;continue;}else{var _PW=E(_PP),_PX=E(_PU.b);if(_PW>=_PX){if(_PW!=_PX){return new F(function(){return _PB(_PN,_,_PW,_PT);});}else{return new T1(1,_PR.c);}}else{return new F(function(){return _PB(_PN,_,_PW,_PS);});}}}else{_PO=_;_PQ=_PS;continue;}}else{return __Z;}}},_PY=function(_PZ,_Q0,_Q1,_Q2,_Q3){while(1){var _Q4=E(_Q3);if(!_Q4._){var _Q5=_Q4.c,_Q6=_Q4.d,_Q7=E(_Q4.b),_Q8=E(_PZ),_Q9=E(_Q7.a);if(_Q8>=_Q9){if(_Q8!=_Q9){_PZ=_Q8;_Q3=_Q6;continue;}else{var _Qa=E(_Q0),_Qb=E(_Q7.b);if(_Qa>=_Qb){if(_Qa!=_Qb){_PZ=_Q8;_Q0=_Qa;_Q3=_Q6;continue;}else{var _Qc=E(_Q1),_Qd=E(_Q7.c);if(_Qc>=_Qd){if(_Qc!=_Qd){_PZ=_Q8;_Q0=_Qa;_Q1=_Qc;_Q3=_Q6;continue;}else{var _Qe=E(_Q7.d);if(_Q2>=_Qe){if(_Q2!=_Qe){_PZ=_Q8;_Q0=_Qa;_Q1=_Qc;_Q3=_Q6;continue;}else{return true;}}else{_PZ=_Q8;_Q0=_Qa;_Q1=_Qc;_Q3=_Q5;continue;}}}else{_PZ=_Q8;_Q0=_Qa;_Q1=_Qc;_Q3=_Q5;continue;}}}else{_PZ=_Q8;_Q0=_Qa;_Q3=_Q5;continue;}}}else{_PZ=_Q8;_Q3=_Q5;continue;}}else{return false;}}},_Qf=function(_Qg,_Qh){return E(_Qg)+E(_Qh)|0;},_Qi=0,_Qj=function(_Qk,_Ql,_Qm){var _Qn=function(_Qo,_Qp){while(1){var _Qq=B((function(_Qr,_Qs){var _Qt=E(_Qs);if(!_Qt._){var _Qu=new T(function(){return B(_Qn(_Qr,_Qt.e));}),_Qv=function(_Qw){var _Qx=E(_Qt.c),_Qy=E(_Qx.b);if(!_Qy._){if(E(_Qx.a)!=E(_Ql)){return new F(function(){return A1(_Qu,_Qw);});}else{if(E(_Qy.b)>E(_Qm)){return new F(function(){return A1(_Qu,new T(function(){return B(_Qf(_Qw,_Qy.a));}));});}else{return new F(function(){return A1(_Qu,_Qw);});}}}else{return new F(function(){return A1(_Qu,_Qw);});}};_Qo=_Qv;_Qp=_Qt.d;return __continue;}else{return E(_Qr);}})(_Qo,_Qp));if(_Qq!=__continue){return _Qq;}}};return new F(function(){return A3(_Qn,_na,_Qk,_Qi);});},_Qz=function(_QA,_QB,_QC,_QD){while(1){var _QE=E(_QD);if(!_QE._){var _QF=_QE.d,_QG=_QE.e,_QH=E(_QE.b),_QI=E(_QH.a);if(_QA>=_QI){if(_QA!=_QI){_QB=_;_QD=_QG;continue;}else{var _QJ=E(_QH.b);if(_QC>=_QJ){if(_QC!=_QJ){_QB=_;_QD=_QG;continue;}else{return new T1(1,_QE.c);}}else{_QB=_;_QD=_QF;continue;}}}else{_QB=_;_QD=_QF;continue;}}else{return __Z;}}},_QK=function(_QL,_QM,_QN,_QO){while(1){var _QP=E(_QO);if(!_QP._){var _QQ=_QP.d,_QR=_QP.e,_QS=E(_QP.b),_QT=E(_QS.a);if(_QL>=_QT){if(_QL!=_QT){_QM=_;_QO=_QR;continue;}else{var _QU=E(_QN),_QV=E(_QS.b);if(_QU>=_QV){if(_QU!=_QV){return new F(function(){return _Qz(_QL,_,_QU,_QR);});}else{return new T1(1,_QP.c);}}else{return new F(function(){return _Qz(_QL,_,_QU,_QQ);});}}}else{_QM=_;_QO=_QQ;continue;}}else{return __Z;}}},_QW=function(_QX,_QY){while(1){var _QZ=E(_QY);if(!_QZ._){var _R0=E(_QZ.b);if(_QX>=_R0){if(_QX!=_R0){_QY=_QZ.e;continue;}else{return new T1(1,_QZ.c);}}else{_QY=_QZ.d;continue;}}else{return __Z;}}},_R1=function(_R2,_R3,_R4){while(1){var _R5=E(_R4);switch(_R5._){case 0:var _R6=B(_QW(E(_R5.a),_R2));if(!_R6._){return E(_Qi);}else{var _R7=E(E(_R6.a).b);return (_R7._==0)?E(_R7.a):E(_Qi);}break;case 1:return B(_R1(_R2,_R3,_R5.a))+B(_R1(_R2,_R3,_R5.b))|0;case 2:return E(_R5.a);default:var _R8=_R5.b,_R9=_R5.c,_Ra=E(_R3);if(!_Ra._){var _Rb=_Ra.d,_Rc=_Ra.e,_Rd=E(_Ra.b),_Re=E(_R5.a),_Rf=E(_Rd.a);if(_Re>=_Rf){if(_Re!=_Rf){var _Rg=B(_QK(_Re,_,_R8,_Rc));if(!_Rg._){_R3=_Ra;_R4=_R9;continue;}else{return E(_Rg.a);}}else{var _Rh=E(_R8),_Ri=E(_Rd.b);if(_Rh>=_Ri){if(_Rh!=_Ri){var _Rj=B(_Qz(_Re,_,_Rh,_Rc));if(!_Rj._){_R3=_Ra;_R4=_R9;continue;}else{return E(_Rj.a);}}else{return E(_Ra.c);}}else{var _Rk=B(_Qz(_Re,_,_Rh,_Rb));if(!_Rk._){_R3=_Ra;_R4=_R9;continue;}else{return E(_Rk.a);}}}}else{var _Rl=B(_QK(_Re,_,_R8,_Rb));if(!_Rl._){_R3=_Ra;_R4=_R9;continue;}else{return E(_Rl.a);}}}else{_R3=_0;_R4=_R9;continue;}}}},_Rm=__Z,_Rn=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_Ro=new T(function(){return B(err(_Rn));}),_Rp=function(_Rq,_Rr){var _Rs=E(_Rr);if(!_Rs._){return (E(_Rq)==0)?__Z:E(_Ro);}else{var _Rt=_Rs.b,_Ru=E(_Rs.a),_Rv=_Ru.a,_Rw=E(_Ru.b),_Rx=_Rw.a,_Ry=E(_Rw.b);if(!_Ry._){var _Rz=_Ry.b,_RA=E(_Ry.a);return (_Rq>_RA)?(_RA>=_Rq)?E(_Rt):new T2(1,new T2(0,_Rv,new T2(0,_Rx,new T2(0,_Qi,_Rz))),new T(function(){return B(_Rp(_Rq-_RA|0,_Rt));})):new T2(1,new T2(0,_Rv,new T2(0,_Rx,new T2(0,_RA-_Rq|0,_Rz))),_1);}else{return E(_Rt);}}},_RB=function(_RC,_RD){var _RE=E(_RD);if(!_RE._){return (E(_RC)==0)?__Z:E(_Ro);}else{var _RF=_RE.b,_RG=E(_RE.a),_RH=_RG.a,_RI=E(_RG.b),_RJ=_RI.a,_RK=E(_RI.b);if(!_RK._){var _RL=_RK.b,_RM=E(_RC),_RN=E(_RK.a);return (_RM>_RN)?(_RN>=_RM)?E(_RF):new T2(1,new T2(0,_RH,new T2(0,_RJ,new T2(0,_Qi,_RL))),new T(function(){return B(_Rp(_RM-_RN|0,_RF));})):new T2(1,new T2(0,_RH,new T2(0,_RJ,new T2(0,_RN-_RM|0,_RL))),_1);}else{return E(_RF);}}},_RO=function(_RP,_RQ){var _RR=E(_RQ);if(!_RR._){var _RS=_RR.b,_RT=_RR.c,_RU=_RR.d,_RV=_RR.e;if(!B(A2(_RP,_RS,_RT))){return new F(function(){return _Lx(B(_RO(_RP,_RU)),B(_RO(_RP,_RV)));});}else{return new F(function(){return _2h(_RS,_RT,B(_RO(_RP,_RU)),B(_RO(_RP,_RV)));});}}else{return new T0(1);}},_RW=function(_RX,_RY){var _RZ=E(_RX);if(!_RZ._){var _S0=E(_RY);if(!_S0._){return new F(function(){return _Jm(_RZ.b,_S0.b);});}else{return 0;}}else{return (E(_RY)._==0)?2:1;}},_S1=function(_S2,_S3){return new F(function(){return _RW(E(E(_S2).b).b,E(E(_S3).b).b);});},_S4=new T2(1,_1,_1),_S5=function(_S6,_S7){var _S8=function(_S9,_Sa){var _Sb=E(_S9);if(!_Sb._){return E(_Sa);}else{var _Sc=_Sb.a,_Sd=E(_Sa);if(!_Sd._){return E(_Sb);}else{var _Se=_Sd.a;return (B(A2(_S6,_Sc,_Se))==2)?new T2(1,_Se,new T(function(){return B(_S8(_Sb,_Sd.b));})):new T2(1,_Sc,new T(function(){return B(_S8(_Sb.b,_Sd));}));}}},_Sf=function(_Sg){var _Sh=E(_Sg);if(!_Sh._){return __Z;}else{var _Si=E(_Sh.b);return (_Si._==0)?E(_Sh):new T2(1,new T(function(){return B(_S8(_Sh.a,_Si.a));}),new T(function(){return B(_Sf(_Si.b));}));}},_Sj=new T(function(){return B(_Sk(B(_Sf(_1))));}),_Sk=function(_Sl){while(1){var _Sm=E(_Sl);if(!_Sm._){return E(_Sj);}else{if(!E(_Sm.b)._){return E(_Sm.a);}else{_Sl=B(_Sf(_Sm));continue;}}}},_Sn=new T(function(){return B(_So(_1));}),_Sp=function(_Sq,_Sr,_Ss){while(1){var _St=B((function(_Su,_Sv,_Sw){var _Sx=E(_Sw);if(!_Sx._){return new T2(1,new T2(1,_Su,_Sv),_Sn);}else{var _Sy=_Sx.a;if(B(A2(_S6,_Su,_Sy))==2){var _Sz=new T2(1,_Su,_Sv);_Sq=_Sy;_Sr=_Sz;_Ss=_Sx.b;return __continue;}else{return new T2(1,new T2(1,_Su,_Sv),new T(function(){return B(_So(_Sx));}));}}})(_Sq,_Sr,_Ss));if(_St!=__continue){return _St;}}},_SA=function(_SB,_SC,_SD){while(1){var _SE=B((function(_SF,_SG,_SH){var _SI=E(_SH);if(!_SI._){return new T2(1,new T(function(){return B(A1(_SG,new T2(1,_SF,_1)));}),_Sn);}else{var _SJ=_SI.a,_SK=_SI.b;switch(B(A2(_S6,_SF,_SJ))){case 0:_SB=_SJ;_SC=function(_SL){return new F(function(){return A1(_SG,new T2(1,_SF,_SL));});};_SD=_SK;return __continue;case 1:_SB=_SJ;_SC=function(_SM){return new F(function(){return A1(_SG,new T2(1,_SF,_SM));});};_SD=_SK;return __continue;default:return new T2(1,new T(function(){return B(A1(_SG,new T2(1,_SF,_1)));}),new T(function(){return B(_So(_SI));}));}}})(_SB,_SC,_SD));if(_SE!=__continue){return _SE;}}},_So=function(_SN){var _SO=E(_SN);if(!_SO._){return E(_S4);}else{var _SP=_SO.a,_SQ=E(_SO.b);if(!_SQ._){return new T2(1,_SO,_1);}else{var _SR=_SQ.a,_SS=_SQ.b;if(B(A2(_S6,_SP,_SR))==2){return new F(function(){return _Sp(_SR,new T2(1,_SP,_1),_SS);});}else{return new F(function(){return _SA(_SR,function(_ST){return new T2(1,_SP,_ST);},_SS);});}}}};return new F(function(){return _Sk(B(_So(_S7)));});},_SU=function(_SV,_SW,_SX){var _SY=B(_EV(B(_RB(_SW,B(_S5(_S1,B(_hc(_1,B(_RO(function(_SZ,_T0){return new F(function(){return A1(_SV,_T0);});},_SX))))))))));if(!_SY._){var _T1=E(_SX);if(!_T1._){return new F(function(){return _NE(_JB,_LY,_LY,_SY.a,_SY.b,_SY.c,_SY.d,_SY.e,_T1.a,_T1.b,_T1.c,_T1.d,_T1.e);});}else{return E(_SY);}}else{return E(_SX);}},_T2=function(_T3,_T4){var _T5=E(_T3);return new F(function(){return _R1(_T5.a,_T5.b,_T4);});},_T6=function(_T7,_T8,_T9){var _Ta=E(_T9);if(!_Ta._){var _Tb=_Ta.d,_Tc=_Ta.e,_Td=E(_Ta.b),_Te=E(_T7),_Tf=E(_Td.a);if(_Te>=_Tf){if(_Te!=_Tf){return new F(function(){return _Oj(_Te,_,_T8,_Tc);});}else{var _Tg=E(_T8),_Th=E(_Td.b);if(_Tg>=_Th){if(_Tg!=_Th){return new F(function(){return _O8(_Te,_,_Tg,_Tc);});}else{return true;}}else{return new F(function(){return _O8(_Te,_,_Tg,_Tb);});}}}else{return new F(function(){return _Oj(_Te,_,_T8,_Tb);});}}else{return false;}},_Ti=function(_Tj,_Tk,_Tl){while(1){var _Tm=E(_Tk);switch(_Tm._){case 0:return (E(_Tm.a)>E(E(_Tl).b))?true:false;case 1:if(!B(_Ti(_Tj,_Tm.a,_Tl))){return false;}else{_Tk=_Tm.b;continue;}break;case 2:if(!B(_Ti(_Tj,_Tm.a,_Tl))){_Tk=_Tm.b;continue;}else{return true;}break;case 3:return (!B(_Ti(_Tj,_Tm.a,_Tl)))?true:false;case 4:var _Tn=_Tm.b,_To=_Tm.c,_Tp=E(E(_Tj).b);if(!_Tp._){var _Tq=_Tp.d,_Tr=_Tp.e,_Ts=E(_Tp.b),_Tt=E(_Tm.a),_Tu=E(_Ts.a);if(_Tt>=_Tu){if(_Tt!=_Tu){var _Tv=B(_QK(_Tt,_,_Tn,_Tr));if(!_Tv._){return false;}else{return new F(function(){return _GT(_Tv.a,_To);});}}else{var _Tw=E(_Tn),_Tx=E(_Ts.b);if(_Tw>=_Tx){if(_Tw!=_Tx){var _Ty=B(_Qz(_Tt,_,_Tw,_Tr));if(!_Ty._){return false;}else{return new F(function(){return _GT(_Ty.a,_To);});}}else{return new F(function(){return _GT(_Tp.c,_To);});}}else{var _Tz=B(_Qz(_Tt,_,_Tw,_Tq));if(!_Tz._){return false;}else{return new F(function(){return _GT(_Tz.a,_To);});}}}}else{var _TA=B(_QK(_Tt,_,_Tn,_Tq));if(!_TA._){return false;}else{return new F(function(){return _GT(_TA.a,_To);});}}}else{return false;}break;case 5:return new F(function(){return _T6(_Tm.a,_Tm.b,E(_Tj).b);});break;case 6:var _TB=E(_Tj),_TC=_TB.a,_TD=_TB.b;return B(_R1(_TC,_TD,_Tm.a))>=B(_R1(_TC,_TD,_Tm.b));case 7:return true;default:return false;}}},_TE=function(_TF,_TG,_TH,_TI){var _TJ=E(_TH);switch(_TJ._){case 0:return new T3(0,_TG,_Rm,_1);case 1:var _TK=_TJ.a,_TL=_TJ.b,_TM=_TJ.g,_TN=E(_TJ.e),_TO=E(E(_TI).b),_TP=_TN<=_TO,_TQ=new T(function(){var _TR=E(_TG);return B(_R1(_TR.a,_TR.b,_TJ.c));}),_TS=new T(function(){return E(_TJ.d)<=_TO;}),_TT=new T(function(){return B(_E2(E(_TK),new T2(0,_TL,new T(function(){if(!E(_TP)){if(!E(_TS)){return new T2(0,_TQ,_TN);}else{return new T0(1);}}else{return new T0(1);}})),E(_TG).a));});return (!E(_TP))?(!E(_TS))?(!B(_PY(_TK,_TL,_TQ,_TN,E(_TF).a)))?new T3(0,_TG,_TJ,_1):new T3(0,new T(function(){return new T2(0,_TT,E(_TG).b);}),_TJ.f,new T2(1,new T3(3,_TK,_TL,_TQ),_1)):new T3(0,new T(function(){return new T2(0,_TT,E(_TG).b);}),_TM,_1):new T3(0,new T(function(){return new T2(0,_TT,E(_TG).b);}),_TM,_1);case 2:var _TU=_TJ.b,_TV=E(_TG),_TW=_TV.a,_TX=E(_TJ.a),_TY=B(_QW(_TX,_TW));if(!_TY._){return new T3(0,_TV,_TJ,_1);}else{var _TZ=E(_TY.a),_U0=_TZ.a,_U1=E(_TZ.b);if(!_U1._){var _U2=_U1.a;return (!B(_K3(_TX,_,_U0,_U2,E(_TF).b)))?new T3(0,_TV,_TJ,_1):new T3(0,new T2(0,new T(function(){return B(_E2(_TX,new T2(0,_U0,_Me),_TW));}),_TV.b),_TU,new T2(1,new T3(4,_TX,_U0,_U2),_1));}else{return new T3(0,_TV,_TU,new T2(1,new T2(6,_TX,_U0),_1));}}break;case 3:var _U3=_TJ.a,_U4=_TJ.b,_U5=_TJ.c,_U6=_TJ.d,_U7=_TJ.f,_U8=E(E(_TI).b);if(E(_TJ.e)>_U8){var _U9=function(_Ua){var _Ub=E(_TG),_Uc=_Ub.a,_Ud=_Ub.b,_Ue=B(_R1(_Uc,_Ud,_U6));if(E(_Ua)!=_Ue){return new T3(0,_Ub,_TJ,_1);}else{if(B(_Qj(_Uc,_U4,_U8))<_Ue){return new T3(0,_Ub,_U7,new T2(1,new T4(2,_U3,_U4,_U5,_Ue),_1));}else{var _Uf=new T(function(){return B(_SU(function(_Ug){var _Uh=E(_Ug),_Ui=E(_Uh.b);return (_Ui._==0)?(E(_Uh.a)!=E(_U4))?false:(E(_Ui.b)>_U8)?true:false:false;},_Ue,_Uc));});return new T3(0,new T2(0,_Uf,_Ud),_U7,new T2(1,new T4(0,_U3,_U4,_U5,_Ue),_1));}}},_Uj=E(E(_TF).c);if(!_Uj._){var _Uk=_Uj.d,_Ul=_Uj.e,_Um=E(_Uj.b),_Un=E(_U3),_Uo=E(_Um.a);if(_Un>=_Uo){if(_Un!=_Uo){var _Up=B(_PM(_Un,_,_U5,_Ul));if(!_Up._){return new T3(0,_TG,_TJ,_1);}else{return new F(function(){return _U9(_Up.a);});}}else{var _Uq=E(_U5),_Ur=E(_Um.b);if(_Uq>=_Ur){if(_Uq!=_Ur){var _Us=B(_PB(_Un,_,_Uq,_Ul));if(!_Us._){return new T3(0,_TG,_TJ,_1);}else{return new F(function(){return _U9(_Us.a);});}}else{return new F(function(){return _U9(_Uj.c);});}}else{var _Ut=B(_PB(_Un,_,_Uq,_Uk));if(!_Ut._){return new T3(0,_TG,_TJ,_1);}else{return new F(function(){return _U9(_Ut.a);});}}}}else{var _Uu=B(_PM(_Un,_,_U5,_Uk));if(!_Uu._){return new T3(0,_TG,_TJ,_1);}else{return new F(function(){return _U9(_Uu.a);});}}}else{return new T3(0,_TG,_TJ,_1);}}else{return new T3(0,_TG,_U7,new T2(1,new T4(1,_U3,_U4,_U5,new T(function(){return B(_T2(_TG,_U6));})),_1));}break;case 4:var _Uv=new T(function(){var _Uw=B(_TE(_TF,_TG,_TJ.a,_TI));return new T3(0,_Uw.a,_Uw.b,_Uw.c);}),_Ux=new T(function(){var _Uy=B(_TE(_TF,new T(function(){return E(E(_Uv).a);}),_TJ.b,_TI));return new T3(0,_Uy.a,_Uy.b,_Uy.c);}),_Uz=new T(function(){return B(_hq(E(_Uv).c,new T(function(){return E(E(_Ux).c);},1)));}),_UA=new T(function(){var _UB=E(_Uv).b,_UC=E(_Ux).b,_UD=function(_UE){var _UF=E(_UC);switch(_UF._){case 0:return E(_UB);case 1:return new T2(4,_UB,_UF);case 2:return new T2(4,_UB,_UF);case 3:return new T2(4,_UB,_UF);case 4:return new T2(4,_UB,_UF);case 5:return new T2(4,_UB,_UF);default:return new T2(4,_UB,_UF);}};switch(E(_UB)._){case 0:return E(_UC);break;case 1:return B(_UD(_));break;case 2:return B(_UD(_));break;case 3:return B(_UD(_));break;case 4:return B(_UD(_));break;case 5:return B(_UD(_));break;default:return B(_UD(_));}});return new T3(0,new T(function(){return E(E(_Ux).a);}),_UA,_Uz);case 5:return (!B(_Ti(_TG,_TJ.a,_TI)))?new T3(0,_TG,_TJ.c,_1):new T3(0,_TG,_TJ.b,_1);default:var _UG=E(_TI);return (E(_TJ.b)>E(_UG.b))?(!B(_Ti(_TG,_TJ.a,_UG)))?new T3(0,_TG,_TJ,_1):new T3(0,_TG,_TJ.c,_1):new T3(0,_TG,_TJ.d,_1);}},_UH=function(_UI,_UJ,_UK,_UL){var _UM=new T(function(){var _UN=B(_NV(_UI,new T(function(){return E(E(_UJ).a);},1),_UL));return new T2(0,_UN.a,_UN.b);}),_UO=new T(function(){var _UP=B(_Pa(new T(function(){return E(E(_UJ).b);}),_1,E(_UI).d));return new T2(0,_UP.a,_UP.b);}),_UQ=new T(function(){var _UR=new T(function(){var _US=E(_UJ);return new T2(0,new T(function(){return E(E(_UM).a);}),new T(function(){return E(E(_UO).a);}));}),_UT=B(_TE(_UI,_UR,_UK,_UL));return new T3(0,_UT.a,_UT.b,_UT.c);}),_UU=new T(function(){var _UV=new T(function(){return B(_hq(E(_UM).b,new T(function(){return E(E(_UQ).c);},1)));},1);return B(_hq(E(_UO).b,_UV));});return new T3(0,new T(function(){return E(E(_UQ).a);}),new T(function(){return E(E(_UQ).b);}),_UU);},_UW=function(_UX,_UY,_UZ,_V0,_V1,_V2){var _V3=new T2(0,_UY,_UZ),_V4=B(_UH(_UX,_V3,_V0,_V1)),_V5=_V4.b,_V6=_V4.c,_V7=E(_V4.a),_V8=_V7.a,_V9=_V7.b,_Va=function(_Vb){return new F(function(){return _UW(_UX,_V8,_V9,_V5,_V1,new T(function(){return B(_hq(_V6,_V2));}));});};if(!B(A2(_J8,_V8,_UY))){return new F(function(){return _Va(_);});}else{if(!B(A2(_IE,_V9,_UZ))){return new F(function(){return _Va(_);});}else{if(!B(_Hf(_V5,_V0))){return new F(function(){return _Va(_);});}else{if(!E(_V6)._){return new T3(0,_V3,_V0,_V2);}else{return new F(function(){return _Va(_);});}}}}},_Vc=function(_Vd,_Ve){var _Vf=E(_Vd),_Vg=E(_Ve);return (E(_Vf.a)!=E(_Vg.a))?true:(E(_Vf.b)!=E(_Vg.b))?true:(E(_Vf.c)!=E(_Vg.c))?true:(E(_Vf.d)!=E(_Vg.d))?true:false;},_Vh=function(_Vi,_Vj,_Vk,_Vl,_Vm,_Vn,_Vo,_Vp){if(_Vi!=_Vm){return false;}else{if(E(_Vj)!=E(_Vn)){return false;}else{if(E(_Vk)!=E(_Vo)){return false;}else{return new F(function(){return _GT(_Vl,_Vp);});}}}},_Vq=function(_Vr,_Vs){var _Vt=E(_Vr),_Vu=E(_Vs);return new F(function(){return _Vh(E(_Vt.a),_Vt.b,_Vt.c,_Vt.d,E(_Vu.a),_Vu.b,_Vu.c,_Vu.d);});},_Vv=new T2(0,_Vq,_Vc),_Vw=function(_Vx,_Vy,_Vz,_VA,_VB,_VC,_VD,_VE){if(_Vx>=_VB){if(_Vx!=_VB){return false;}else{var _VF=E(_Vy),_VG=E(_VC);if(_VF>=_VG){if(_VF!=_VG){return false;}else{var _VH=E(_Vz),_VI=E(_VD);if(_VH>=_VI){if(_VH!=_VI){return false;}else{return new F(function(){return _Jy(_VA,_VE);});}}else{return true;}}}else{return true;}}}else{return true;}},_VJ=function(_VK,_VL){var _VM=E(_VK),_VN=E(_VL);return new F(function(){return _Vw(E(_VM.a),_VM.b,_VM.c,_VM.d,E(_VN.a),_VN.b,_VN.c,_VN.d);});},_VO=function(_VP,_VQ,_VR,_VS,_VT,_VU,_VV,_VW){if(_VP>=_VT){if(_VP!=_VT){return false;}else{var _VX=E(_VQ),_VY=E(_VU);if(_VX>=_VY){if(_VX!=_VY){return false;}else{var _VZ=E(_VR),_W0=E(_VV);if(_VZ>=_W0){if(_VZ!=_W0){return false;}else{return new F(function(){return _Jv(_VS,_VW);});}}else{return true;}}}else{return true;}}}else{return true;}},_W1=function(_W2,_W3){var _W4=E(_W2),_W5=E(_W3);return new F(function(){return _VO(E(_W4.a),_W4.b,_W4.c,_W4.d,E(_W5.a),_W5.b,_W5.c,_W5.d);});},_W6=function(_W7,_W8,_W9,_Wa,_Wb,_Wc,_Wd,_We){if(_W7>=_Wb){if(_W7!=_Wb){return true;}else{var _Wf=E(_W8),_Wg=E(_Wc);if(_Wf>=_Wg){if(_Wf!=_Wg){return true;}else{var _Wh=E(_W9),_Wi=E(_Wd);if(_Wh>=_Wi){if(_Wh!=_Wi){return true;}else{return new F(function(){return _Js(_Wa,_We);});}}else{return false;}}}else{return false;}}}else{return false;}},_Wj=function(_Wk,_Wl){var _Wm=E(_Wk),_Wn=E(_Wl);return new F(function(){return _W6(E(_Wm.a),_Wm.b,_Wm.c,_Wm.d,E(_Wn.a),_Wn.b,_Wn.c,_Wn.d);});},_Wo=function(_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wv,_Ww){if(_Wp>=_Wt){if(_Wp!=_Wt){return true;}else{var _Wx=E(_Wq),_Wy=E(_Wu);if(_Wx>=_Wy){if(_Wx!=_Wy){return true;}else{var _Wz=E(_Wr),_WA=E(_Wv);if(_Wz>=_WA){if(_Wz!=_WA){return true;}else{return new F(function(){return _Jp(_Ws,_Ww);});}}else{return false;}}}else{return false;}}}else{return false;}},_WB=function(_WC,_WD){var _WE=E(_WC),_WF=E(_WD);return new F(function(){return _Wo(E(_WE.a),_WE.b,_WE.c,_WE.d,E(_WF.a),_WF.b,_WF.c,_WF.d);});},_WG=function(_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO){if(_WH>=_WL){if(_WH!=_WL){return 2;}else{var _WP=E(_WI),_WQ=E(_WM);if(_WP>=_WQ){if(_WP!=_WQ){return 2;}else{var _WR=E(_WJ),_WS=E(_WN);if(_WR>=_WS){if(_WR!=_WS){return 2;}else{return new F(function(){return _Jm(_WK,_WO);});}}else{return 0;}}}else{return 0;}}}else{return 0;}},_WT=function(_WU,_WV){var _WW=E(_WU),_WX=E(_WV);return new F(function(){return _WG(E(_WW.a),_WW.b,_WW.c,_WW.d,E(_WX.a),_WX.b,_WX.c,_WX.d);});},_WY=function(_WZ,_X0){var _X1=E(_WZ),_X2=E(_X1.a),_X3=E(_X0),_X4=E(_X3.a);if(_X2>=_X4){if(_X2!=_X4){return E(_X1);}else{var _X5=E(_X1.b),_X6=E(_X3.b);if(_X5>=_X6){if(_X5!=_X6){return E(_X1);}else{var _X7=E(_X1.c),_X8=E(_X3.c);return (_X7>=_X8)?(_X7!=_X8)?E(_X1):(E(_X1.d)>E(_X3.d))?E(_X1):E(_X3):E(_X3);}}else{return E(_X3);}}}else{return E(_X3);}},_X9=function(_Xa,_Xb){var _Xc=E(_Xa),_Xd=E(_Xc.a),_Xe=E(_Xb),_Xf=E(_Xe.a);if(_Xd>=_Xf){if(_Xd!=_Xf){return E(_Xe);}else{var _Xg=E(_Xc.b),_Xh=E(_Xe.b);if(_Xg>=_Xh){if(_Xg!=_Xh){return E(_Xe);}else{var _Xi=E(_Xc.c),_Xj=E(_Xe.c);return (_Xi>=_Xj)?(_Xi!=_Xj)?E(_Xe):(E(_Xc.d)>E(_Xe.d))?E(_Xe):E(_Xc):E(_Xc);}}else{return E(_Xc);}}}else{return E(_Xc);}},_Xk={_:0,a:_Vv,b:_WT,c:_VJ,d:_W1,e:_Wj,f:_WB,g:_WY,h:_X9},_Xl=function(_Xm,_Xn,_Xo,_Xp){if(_Xm>=_Xo){if(_Xm!=_Xo){return 2;}else{return new F(function(){return _Jm(_Xn,_Xp);});}}else{return 0;}},_Xq=function(_Xr,_Xs){var _Xt=E(_Xr),_Xu=E(_Xs);return new F(function(){return _Xl(E(_Xt.a),_Xt.b,E(_Xu.a),_Xu.b);});},_Xv=function(_Xw,_Xx,_Xy,_Xz){if(_Xw>=_Xy){if(_Xw!=_Xy){return false;}else{return new F(function(){return _Jy(_Xx,_Xz);});}}else{return true;}},_XA=function(_XB,_XC){var _XD=E(_XB),_XE=E(_XC);return new F(function(){return _Xv(E(_XD.a),_XD.b,E(_XE.a),_XE.b);});},_XF=function(_XG,_XH,_XI,_XJ){if(_XG>=_XI){if(_XG!=_XI){return false;}else{return new F(function(){return _Jv(_XH,_XJ);});}}else{return true;}},_XK=function(_XL,_XM){var _XN=E(_XL),_XO=E(_XM);return new F(function(){return _XF(E(_XN.a),_XN.b,E(_XO.a),_XO.b);});},_XP=function(_XQ,_XR,_XS,_XT){if(_XQ>=_XS){if(_XQ!=_XS){return true;}else{return new F(function(){return _Js(_XR,_XT);});}}else{return false;}},_XU=function(_XV,_XW){var _XX=E(_XV),_XY=E(_XW);return new F(function(){return _XP(E(_XX.a),_XX.b,E(_XY.a),_XY.b);});},_XZ=function(_Y0,_Y1,_Y2,_Y3){if(_Y0>=_Y2){if(_Y0!=_Y2){return true;}else{return new F(function(){return _Jp(_Y1,_Y3);});}}else{return false;}},_Y4=function(_Y5,_Y6){var _Y7=E(_Y5),_Y8=E(_Y6);return new F(function(){return _XZ(E(_Y7.a),_Y7.b,E(_Y8.a),_Y8.b);});},_Y9=function(_Ya,_Yb){var _Yc=E(_Ya),_Yd=_Yc.b,_Ye=E(_Yc.a),_Yf=E(_Yb),_Yg=_Yf.b,_Yh=E(_Yf.a);if(_Ye>=_Yh){if(_Ye!=_Yh){return new T2(0,_Ye,_Yd);}else{var _Yi=E(_Yd),_Yj=E(_Yg);return (_Yi>_Yj)?new T2(0,_Ye,_Yi):new T2(0,_Yh,_Yj);}}else{return new T2(0,_Yh,_Yg);}},_Yk=function(_Yl,_Ym){var _Yn=E(_Yl),_Yo=_Yn.b,_Yp=E(_Yn.a),_Yq=E(_Ym),_Yr=_Yq.b,_Ys=E(_Yq.a);if(_Yp>=_Ys){if(_Yp!=_Ys){return new T2(0,_Ys,_Yr);}else{var _Yt=E(_Yo),_Yu=E(_Yr);return (_Yt>_Yu)?new T2(0,_Ys,_Yu):new T2(0,_Yp,_Yt);}}else{return new T2(0,_Yp,_Yo);}},_Yv={_:0,a:_HJ,b:_Xq,c:_XA,d:_XK,e:_XU,f:_Y4,g:_Y9,h:_Yk},_Yw=function(_Yx,_Yy,_Yz,_YA){if(_Yx!=_Yz){return false;}else{return new F(function(){return _GT(_Yy,_YA);});}},_YB=function(_YC,_YD){var _YE=E(_YC),_YF=E(_YD);return new F(function(){return _Yw(E(_YE.a),_YE.b,E(_YF.a),_YF.b);});},_YG=function(_YH,_YI,_YJ,_YK){return (_YH!=_YJ)?true:(E(_YI)!=E(_YK))?true:false;},_YL=function(_YM,_YN){var _YO=E(_YM),_YP=E(_YN);return new F(function(){return _YG(E(_YO.a),_YO.b,E(_YP.a),_YP.b);});},_YQ=new T2(0,_YB,_YL),_YR=function(_YS,_YT,_YU,_YV){if(_YS>=_YU){if(_YS!=_YU){return 2;}else{return new F(function(){return _Jm(_YT,_YV);});}}else{return 0;}},_YW=function(_YX,_YY){var _YZ=E(_YX),_Z0=E(_YY);return new F(function(){return _YR(E(_YZ.a),_YZ.b,E(_Z0.a),_Z0.b);});},_Z1=function(_Z2,_Z3,_Z4,_Z5){if(_Z2>=_Z4){if(_Z2!=_Z4){return false;}else{return new F(function(){return _Jy(_Z3,_Z5);});}}else{return true;}},_Z6=function(_Z7,_Z8){var _Z9=E(_Z7),_Za=E(_Z8);return new F(function(){return _Z1(E(_Z9.a),_Z9.b,E(_Za.a),_Za.b);});},_Zb=function(_Zc,_Zd,_Ze,_Zf){if(_Zc>=_Ze){if(_Zc!=_Ze){return false;}else{return new F(function(){return _Jv(_Zd,_Zf);});}}else{return true;}},_Zg=function(_Zh,_Zi){var _Zj=E(_Zh),_Zk=E(_Zi);return new F(function(){return _Zb(E(_Zj.a),_Zj.b,E(_Zk.a),_Zk.b);});},_Zl=function(_Zm,_Zn,_Zo,_Zp){if(_Zm>=_Zo){if(_Zm!=_Zo){return true;}else{return new F(function(){return _Js(_Zn,_Zp);});}}else{return false;}},_Zq=function(_Zr,_Zs){var _Zt=E(_Zr),_Zu=E(_Zs);return new F(function(){return _Zl(E(_Zt.a),_Zt.b,E(_Zu.a),_Zu.b);});},_Zv=function(_Zw,_Zx,_Zy,_Zz){if(_Zw>=_Zy){if(_Zw!=_Zy){return true;}else{return new F(function(){return _Jp(_Zx,_Zz);});}}else{return false;}},_ZA=function(_ZB,_ZC){var _ZD=E(_ZB),_ZE=E(_ZC);return new F(function(){return _Zv(E(_ZD.a),_ZD.b,E(_ZE.a),_ZE.b);});},_ZF=function(_ZG,_ZH){var _ZI=E(_ZG),_ZJ=_ZI.b,_ZK=E(_ZI.a),_ZL=E(_ZH),_ZM=_ZL.b,_ZN=E(_ZL.a);if(_ZK>=_ZN){if(_ZK!=_ZN){return new T2(0,_ZK,_ZJ);}else{var _ZO=E(_ZJ),_ZP=E(_ZM);return (_ZO>_ZP)?new T2(0,_ZK,_ZO):new T2(0,_ZN,_ZP);}}else{return new T2(0,_ZN,_ZM);}},_ZQ=function(_ZR,_ZS){var _ZT=E(_ZR),_ZU=_ZT.b,_ZV=E(_ZT.a),_ZW=E(_ZS),_ZX=_ZW.b,_ZY=E(_ZW.a);if(_ZV>=_ZY){if(_ZV!=_ZY){return new T2(0,_ZY,_ZX);}else{var _ZZ=E(_ZU),_100=E(_ZX);return (_ZZ>_100)?new T2(0,_ZY,_100):new T2(0,_ZV,_ZZ);}}else{return new T2(0,_ZV,_ZU);}},_101={_:0,a:_YQ,b:_YW,c:_Z6,d:_Zg,e:_Zq,f:_ZA,g:_ZF,h:_ZQ},_102=function(_103,_104){var _105=E(_103),_106=E(_104);return (E(_105.a)!=E(_106.a))?true:(E(_105.b)!=E(_106.b))?true:(E(_105.c)!=E(_106.c))?true:false;},_107=function(_108,_109,_10a,_10b,_10c,_10d){if(_108!=_10b){return false;}else{if(E(_109)!=E(_10c)){return false;}else{return new F(function(){return _GT(_10a,_10d);});}}},_10e=function(_10f,_10g){var _10h=E(_10f),_10i=E(_10g);return new F(function(){return _107(E(_10h.a),_10h.b,_10h.c,E(_10i.a),_10i.b,_10i.c);});},_10j=new T2(0,_10e,_102),_10k=function(_10l,_10m,_10n,_10o,_10p,_10q){if(_10l>=_10o){if(_10l!=_10o){return false;}else{var _10r=E(_10m),_10s=E(_10p);if(_10r>=_10s){if(_10r!=_10s){return false;}else{return new F(function(){return _Jy(_10n,_10q);});}}else{return true;}}}else{return true;}},_10t=function(_10u,_10v){var _10w=E(_10u),_10x=E(_10v);return new F(function(){return _10k(E(_10w.a),_10w.b,_10w.c,E(_10x.a),_10x.b,_10x.c);});},_10y=function(_10z,_10A,_10B,_10C,_10D,_10E){if(_10z>=_10C){if(_10z!=_10C){return false;}else{var _10F=E(_10A),_10G=E(_10D);if(_10F>=_10G){if(_10F!=_10G){return false;}else{return new F(function(){return _Jv(_10B,_10E);});}}else{return true;}}}else{return true;}},_10H=function(_10I,_10J){var _10K=E(_10I),_10L=E(_10J);return new F(function(){return _10y(E(_10K.a),_10K.b,_10K.c,E(_10L.a),_10L.b,_10L.c);});},_10M=function(_10N,_10O,_10P,_10Q,_10R,_10S){if(_10N>=_10Q){if(_10N!=_10Q){return true;}else{var _10T=E(_10O),_10U=E(_10R);if(_10T>=_10U){if(_10T!=_10U){return true;}else{return new F(function(){return _Js(_10P,_10S);});}}else{return false;}}}else{return false;}},_10V=function(_10W,_10X){var _10Y=E(_10W),_10Z=E(_10X);return new F(function(){return _10M(E(_10Y.a),_10Y.b,_10Y.c,E(_10Z.a),_10Z.b,_10Z.c);});},_110=function(_111,_112,_113,_114,_115,_116){if(_111>=_114){if(_111!=_114){return true;}else{var _117=E(_112),_118=E(_115);if(_117>=_118){if(_117!=_118){return true;}else{return new F(function(){return _Jp(_113,_116);});}}else{return false;}}}else{return false;}},_119=function(_11a,_11b){var _11c=E(_11a),_11d=E(_11b);return new F(function(){return _110(E(_11c.a),_11c.b,_11c.c,E(_11d.a),_11d.b,_11d.c);});},_11e=function(_11f,_11g,_11h,_11i,_11j,_11k){if(_11f>=_11i){if(_11f!=_11i){return 2;}else{var _11l=E(_11g),_11m=E(_11j);if(_11l>=_11m){if(_11l!=_11m){return 2;}else{return new F(function(){return _Jm(_11h,_11k);});}}else{return 0;}}}else{return 0;}},_11n=function(_11o,_11p){var _11q=E(_11o),_11r=E(_11p);return new F(function(){return _11e(E(_11q.a),_11q.b,_11q.c,E(_11r.a),_11r.b,_11r.c);});},_11s=function(_11t,_11u){var _11v=E(_11t),_11w=E(_11v.a),_11x=E(_11u),_11y=E(_11x.a);if(_11w>=_11y){if(_11w!=_11y){return E(_11v);}else{var _11z=E(_11v.b),_11A=E(_11x.b);return (_11z>=_11A)?(_11z!=_11A)?E(_11v):(E(_11v.c)>E(_11x.c))?E(_11v):E(_11x):E(_11x);}}else{return E(_11x);}},_11B=function(_11C,_11D){var _11E=E(_11C),_11F=E(_11E.a),_11G=E(_11D),_11H=E(_11G.a);if(_11F>=_11H){if(_11F!=_11H){return E(_11G);}else{var _11I=E(_11E.b),_11J=E(_11G.b);return (_11I>=_11J)?(_11I!=_11J)?E(_11G):(E(_11E.c)>E(_11G.c))?E(_11G):E(_11E):E(_11E);}}else{return E(_11E);}},_11K={_:0,a:_10j,b:_11n,c:_10t,d:_10H,e:_10V,f:_119,g:_11s,h:_11B},_11L=__Z,_11M=function(_11N,_11O,_11P){var _11Q=E(_11O);if(!_11Q._){return E(_11P);}else{var _11R=function(_11S,_11T){while(1){var _11U=E(_11T);if(!_11U._){var _11V=_11U.b,_11W=_11U.d;switch(B(A3(_Mj,_11N,_11S,_11V))){case 0:return new F(function(){return _7J(_11V,B(_11R(_11S,_11U.c)),_11W);});break;case 1:return E(_11W);default:_11T=_11W;continue;}}else{return new T0(1);}}};return new F(function(){return _11R(_11Q.a,_11P);});}},_11X=function(_11Y,_11Z,_120){var _121=E(_11Z);if(!_121._){return E(_120);}else{var _122=function(_123,_124){while(1){var _125=E(_124);if(!_125._){var _126=_125.b,_127=_125.c;switch(B(A3(_Mj,_11Y,_126,_123))){case 0:return new F(function(){return _7J(_126,_127,B(_122(_123,_125.d)));});break;case 1:return E(_127);default:_124=_127;continue;}}else{return new T0(1);}}};return new F(function(){return _122(_121.a,_120);});}},_128=function(_129,_12a,_12b){var _12c=E(_12a),_12d=E(_12b);if(!_12d._){var _12e=_12d.b,_12f=_12d.c,_12g=_12d.d;switch(B(A3(_Mj,_129,_12c,_12e))){case 0:return new F(function(){return _6x(_12e,B(_128(_129,_12c,_12f)),_12g);});break;case 1:return E(_12d);default:return new F(function(){return _5N(_12e,_12f,B(_128(_129,_12c,_12g)));});}}else{return new T4(0,1,E(_12c),E(_5I),E(_5I));}},_12h=function(_12i,_12j,_12k){return new F(function(){return _128(_12i,_12j,_12k);});},_12l=function(_12m,_12n,_12o,_12p){var _12q=E(_12n);if(!_12q._){var _12r=E(_12o);if(!_12r._){return E(_12p);}else{var _12s=function(_12t,_12u){while(1){var _12v=E(_12u);if(!_12v._){if(!B(A3(_MZ,_12m,_12v.b,_12t))){return E(_12v);}else{_12u=_12v.c;continue;}}else{return new T0(1);}}};return new F(function(){return _12s(_12r.a,_12p);});}}else{var _12w=_12q.a,_12x=E(_12o);if(!_12x._){var _12y=function(_12z,_12A){while(1){var _12B=E(_12A);if(!_12B._){if(!B(A3(_MX,_12m,_12B.b,_12z))){return E(_12B);}else{_12A=_12B.d;continue;}}else{return new T0(1);}}};return new F(function(){return _12y(_12w,_12p);});}else{var _12C=function(_12D,_12E,_12F){while(1){var _12G=E(_12F);if(!_12G._){var _12H=_12G.b;if(!B(A3(_MX,_12m,_12H,_12D))){if(!B(A3(_MZ,_12m,_12H,_12E))){return E(_12G);}else{_12F=_12G.c;continue;}}else{_12F=_12G.d;continue;}}else{return new T0(1);}}};return new F(function(){return _12C(_12w,_12x.a,_12p);});}}},_12I=function(_12J,_12K,_12L,_12M,_12N){var _12O=E(_12N);if(!_12O._){var _12P=_12O.b,_12Q=_12O.c,_12R=_12O.d,_12S=E(_12M);if(!_12S._){var _12T=_12S.b,_12U=function(_12V){var _12W=new T1(1,E(_12T));return new F(function(){return _7J(_12T,B(_12I(_12J,_12K,_12W,_12S.c,B(_12l(_12J,_12K,_12W,_12O)))),B(_12I(_12J,_12W,_12L,_12S.d,B(_12l(_12J,_12W,_12L,_12O)))));});};if(!E(_12Q)._){return new F(function(){return _12U(_);});}else{if(!E(_12R)._){return new F(function(){return _12U(_);});}else{return new F(function(){return _12h(_12J,_12P,_12S);});}}}else{return new F(function(){return _7J(_12P,B(_11M(_12J,_12K,_12Q)),B(_11X(_12J,_12L,_12R)));});}}else{return E(_12M);}},_12X=function(_12Y,_12Z,_130,_131,_132,_133,_134,_135,_136,_137,_138){var _139=function(_13a){var _13b=new T1(1,E(_132));return new F(function(){return _7J(_132,B(_12I(_12Y,_12Z,_13b,_133,B(_12l(_12Y,_12Z,_13b,new T4(0,_135,E(_136),E(_137),E(_138)))))),B(_12I(_12Y,_13b,_130,_134,B(_12l(_12Y,_13b,_130,new T4(0,_135,E(_136),E(_137),E(_138)))))));});};if(!E(_137)._){return new F(function(){return _139(_);});}else{if(!E(_138)._){return new F(function(){return _139(_);});}else{return new F(function(){return _12h(_12Y,_136,new T4(0,_131,E(_132),E(_133),E(_134)));});}}},_13c=function(_13d,_13e,_13f,_13g,_13h,_13i,_13j,_13k){return new T4(0,new T(function(){var _13l=E(_13d);if(!_13l._){var _13m=E(_13h);if(!_13m._){return B(_12X(_Xk,_11L,_11L,_13l.a,_13l.b,_13l.c,_13l.d,_13m.a,_13m.b,_13m.c,_13m.d));}else{return E(_13l);}}else{return E(_13h);}}),new T(function(){var _13n=E(_13e);if(!_13n._){var _13o=E(_13i);if(!_13o._){return B(_12X(_11K,_11L,_11L,_13n.a,_13n.b,_13n.c,_13n.d,_13o.a,_13o.b,_13o.c,_13o.d));}else{return E(_13n);}}else{return E(_13i);}}),new T(function(){var _13p=E(_13f);if(!_13p._){var _13q=E(_13j);if(!_13q._){return B(_NE(_101,_LY,_LY,_13p.a,_13p.b,_13p.c,_13p.d,_13p.e,_13q.a,_13q.b,_13q.c,_13q.d,_13q.e));}else{return E(_13p);}}else{return E(_13j);}}),new T(function(){var _13r=E(_13g);if(!_13r._){var _13s=E(_13k);if(!_13s._){return B(_NE(_Yv,_LY,_LY,_13r.a,_13r.b,_13r.c,_13r.d,_13r.e,_13s.a,_13s.b,_13s.c,_13s.d,_13s.e));}else{return E(_13r);}}else{return E(_13k);}}));},_13t=function(_13u,_13v){while(1){var _13w=E(_13v);if(!_13w._){var _13x=E(_13w.b);if(_13u>=_13x){if(_13u!=_13x){_13v=_13w.e;continue;}else{return true;}}else{_13v=_13w.d;continue;}}else{return false;}}},_13y=function(_13z,_13A){while(1){var _13B=E(_13A);if(!_13B._){var _13C=E(_13B.b);if(_13z>=_13C){if(_13z!=_13C){_13A=_13B.e;continue;}else{return new T1(1,_13B.c);}}else{_13A=_13B.d;continue;}}else{return __Z;}}},_13D=function(_13E,_13F){var _13G=E(_13E);switch(_13G._){case 1:var _13H=E(_13F),_13I=_13H.a,_13J=E(_13G.a);return (!B(_13t(_13J,_13I)))?new T4(0,new T4(0,1,E(new T4(0,_13J,_13G.b,new T(function(){return B(_R1(_13I,_13H.b,_13G.c));}),_13G.e)),E(_5I),E(_5I)),_5I,_0,_0):new T4(0,_5I,_5I,_0,_0);case 2:var _13K=E(_13G.a),_13L=B(_13y(_13K,E(_13F).a));if(!_13L._){return new T4(0,_5I,_5I,_0,_0);}else{var _13M=E(_13L.a),_13N=E(_13M.b);return (_13N._==0)?new T4(0,_5I,new T4(0,1,E(new T3(0,_13K,_13M.a,_13N.a)),E(_5I),E(_5I)),_0,_0):new T4(0,_5I,_5I,_0,_0);}break;case 3:return new T4(0,_5I,_5I,new T5(0,1,E(new T2(0,_13G.a,_13G.c)),new T(function(){return B(_T2(_13F,_13G.d));}),E(_0),E(_0)),_0);case 4:var _13O=B(_13D(_13G.a,_13F)),_13P=B(_13D(_13G.b,_13F));return new F(function(){return _13c(_13O.a,_13O.b,_13O.c,_13O.d,_13P.a,_13P.b,_13P.c,_13P.d);});break;default:return new T4(0,_5I,_5I,_0,_0);}},_13Q=function(_13R,_13S){var _13T=new T(function(){var _13U=function(_13V,_13W){while(1){var _13X=B((function(_13Y,_13Z){var _140=E(_13Z);if(!_140._){var _141=_140.e,_142=new T(function(){var _143=E(_140.c),_144=E(_143.b);if(!_144._){var _145=E(E(_13R).b);if(E(_144.b)>_145){var _146=function(_147,_148){while(1){var _149=B((function(_14a,_14b){var _14c=E(_14b);if(!_14c._){var _14d=_14c.e,_14e=new T(function(){var _14f=E(_14c.c),_14g=E(_14f.b);if(!_14g._){if(E(_14g.b)>_145){return B(_146(_14a,_14d));}else{return new T2(1,new T3(0,_14c.b,_14f.a,_14g.a),new T(function(){return B(_146(_14a,_14d));}));}}else{return B(_146(_14a,_14d));}},1);_147=_14e;_148=_14c.d;return __continue;}else{return E(_14a);}})(_147,_148));if(_149!=__continue){return _149;}}};return B(_146(_13Y,_141));}else{var _14h=new T(function(){var _14i=function(_14j,_14k){while(1){var _14l=B((function(_14m,_14n){var _14o=E(_14n);if(!_14o._){var _14p=_14o.e,_14q=new T(function(){var _14r=E(_14o.c),_14s=E(_14r.b);if(!_14s._){if(E(_14s.b)>_145){return B(_14i(_14m,_14p));}else{return new T2(1,new T3(0,_14o.b,_14r.a,_14s.a),new T(function(){return B(_14i(_14m,_14p));}));}}else{return B(_14i(_14m,_14p));}},1);_14j=_14q;_14k=_14o.d;return __continue;}else{return E(_14m);}})(_14j,_14k));if(_14l!=__continue){return _14l;}}};return B(_14i(_13Y,_141));});return new T2(1,new T3(0,_140.b,_143.a,_144.a),_14h);}}else{return B(_13U(_13Y,_141));}},1);_13V=_142;_13W=_140.d;return __continue;}else{return E(_13Y);}})(_13V,_13W));if(_13X!=__continue){return _13X;}}};return B(_c2(B(_13U(_1,_13S))));});return new T4(0,_5I,_13T,_0,_0);},_14t=function(_14u,_14v,_14w,_14x){while(1){var _14y=E(_14x);if(!_14y._){var _14z=_14y.d,_14A=_14y.e,_14B=E(_14y.b),_14C=E(_14B.a);if(_14u>=_14C){if(_14u!=_14C){_14v=_;_14x=_14A;continue;}else{var _14D=E(_14B.b);if(_14w>=_14D){if(_14w!=_14D){_14v=_;_14x=_14A;continue;}else{return true;}}else{_14v=_;_14x=_14z;continue;}}}else{_14v=_;_14x=_14z;continue;}}else{return false;}}},_14E=function(_14F,_14G,_14H,_14I){while(1){var _14J=E(_14I);if(!_14J._){var _14K=_14J.d,_14L=_14J.e,_14M=E(_14J.b),_14N=E(_14M.a);if(_14F>=_14N){if(_14F!=_14N){_14G=_;_14I=_14L;continue;}else{var _14O=E(_14H),_14P=E(_14M.b);if(_14O>=_14P){if(_14O!=_14P){return new F(function(){return _14t(_14F,_,_14O,_14L);});}else{return true;}}else{return new F(function(){return _14t(_14F,_,_14O,_14K);});}}}else{_14G=_;_14I=_14K;continue;}}else{return false;}}},_14Q=function(_14R,_14S,_14T,_14U,_14V){while(1){var _14W=E(_14R);if(!_14W._){return new T4(0,_14S,_14T,_14U,_14V);}else{var _14X=E(_14W.a),_14Y=B(_13c(_14S,_14T,_14U,_14V,_14X.a,_14X.b,_14X.c,_14X.d));_14R=_14W.b;_14S=_14Y.a;_14T=_14Y.b;_14U=_14Y.c;_14V=_14Y.d;continue;}}},_14Z=function(_150,_151,_152,_153,_154){while(1){var _155=E(_150);if(!_155._){return new T4(0,_151,_152,_153,_154);}else{var _156=E(_155.a),_157=B(_13c(_151,_152,_153,_154,_156.a,_156.b,_156.c,_156.d));_150=_155.b;_151=_157.a;_152=_157.b;_153=_157.c;_154=_157.d;continue;}}},_158=function(_159,_15a){var _15b=B(_15c(_159,_15a));return new T4(0,_15b.a,_15b.b,_15b.c,_15b.d);},_15d=0,_15c=function(_15e,_15f){while(1){var _15g=B((function(_15h,_15i){var _15j=E(_15i);switch(_15j._){case 1:var _15k=B(_15c(_15h,_15j.a));return new F(function(){return _14Z(new T2(1,new T(function(){return B(_158(_15h,_15j.b));}),_1),_15k.a,_15k.b,_15k.c,_15k.d);});break;case 2:var _15l=B(_15c(_15h,_15j.a));return new F(function(){return _14Q(new T2(1,new T(function(){return B(_158(_15h,_15j.b));}),_1),_15l.a,_15l.b,_15l.c,_15l.d);});break;case 3:var _15m=_15h;_15e=_15m;_15f=_15j.a;return __continue;case 4:var _15n=_15j.a,_15o=_15j.b,_15p=E(E(_15h).b);if(!_15p._){var _15q=_15p.d,_15r=_15p.e,_15s=E(_15p.b),_15t=E(_15n),_15u=E(_15s.a);if(_15t>=_15u){if(_15t!=_15u){return (!B(_14E(_15t,_,_15o,_15r)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15t,_15o)),_15d,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}else{var _15v=E(_15o),_15w=E(_15s.b);return (_15v>=_15w)?(_15v!=_15w)?(!B(_14t(_15t,_,_15v,_15r)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15t,_15v)),_15d,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0):new T4(0,_5I,_5I,_0,_0):(!B(_14t(_15t,_,_15v,_15q)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15t,_15v)),_15d,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return (!B(_14E(_15t,_,_15o,_15q)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15t,_15o)),_15d,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15n,_15o)),_15d,E(_0),E(_0)));}break;case 5:var _15x=_15j.a,_15y=_15j.b,_15z=E(E(_15h).b);if(!_15z._){var _15A=_15z.d,_15B=_15z.e,_15C=E(_15z.b),_15D=E(_15x),_15E=E(_15C.a);if(_15D>=_15E){if(_15D!=_15E){return (!B(_14E(_15D,_,_15y,_15B)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15D,_15y)),_15d,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}else{var _15F=E(_15y),_15G=E(_15C.b);return (_15F>=_15G)?(_15F!=_15G)?(!B(_14t(_15D,_,_15F,_15B)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15D,_15F)),_15d,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0):new T4(0,_5I,_5I,_0,_0):(!B(_14t(_15D,_,_15F,_15A)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15D,_15F)),_15d,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return (!B(_14E(_15D,_,_15y,_15A)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15D,_15y)),_15d,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_15x,_15y)),_15d,E(_0),E(_0)));}break;default:return new T4(0,_5I,_5I,_0,_0);}})(_15e,_15f));if(_15g!=__continue){return _15g;}}},_15H=function(_15I,_15J,_15K,_15L,_15M){while(1){var _15N=E(_15I);if(!_15N._){return new T4(0,_15J,_15K,_15L,_15M);}else{var _15O=E(_15N.a),_15P=B(_13c(_15J,_15K,_15L,_15M,_15O.a,_15O.b,_15O.c,_15O.d));_15I=_15N.b;_15J=_15P.a;_15K=_15P.b;_15L=_15P.c;_15M=_15P.d;continue;}}},_15Q=function(_15R,_15S,_15T,_15U,_15V){while(1){var _15W=E(_15R);if(!_15W._){return new T4(0,_15S,_15T,_15U,_15V);}else{var _15X=E(_15W.a),_15Y=B(_13c(_15S,_15T,_15U,_15V,_15X.a,_15X.b,_15X.c,_15X.d));_15R=_15W.b;_15S=_15Y.a;_15T=_15Y.b;_15U=_15Y.c;_15V=_15Y.d;continue;}}},_15Z=function(_160,_161){var _162=B(_163(_160,_161));return new T4(0,_162.a,_162.b,_162.c,_162.d);},_163=function(_164,_165){while(1){var _166=B((function(_167,_168){var _169=E(_168);switch(_169._){case 0:return new T4(0,_5I,_5I,_0,_0);case 1:var _16a=B(_163(_167,_169.f));return new F(function(){return _15Q(new T2(1,new T(function(){return B(_15Z(_167,_169.g));}),_1),_16a.a,_16a.b,_16a.c,_16a.d);});break;case 2:var _16b=_167;_164=_16b;_165=_169.b;return __continue;case 3:var _16b=_167;_164=_16b;_165=_169.f;return __continue;case 4:var _16c=B(_163(_167,_169.a));return new F(function(){return _15H(new T2(1,new T(function(){return B(_15Z(_167,_169.b));}),_1),_16c.a,_16c.b,_16c.c,_16c.d);});break;case 5:var _16d=B(_15c(_167,_169.a)),_16e=B(_163(_167,_169.b)),_16f=B(_13c(_16d.a,_16d.b,_16d.c,_16d.d,_16e.a,_16e.b,_16e.c,_16e.d)),_16g=B(_163(_167,_169.c));return new F(function(){return _13c(_16f.a,_16f.b,_16f.c,_16f.d,_16g.a,_16g.b,_16g.c,_16g.d);});break;default:var _16h=B(_15c(_167,_169.a)),_16i=B(_163(_167,_169.c)),_16j=B(_13c(_16h.a,_16h.b,_16h.c,_16h.d,_16i.a,_16i.b,_16i.c,_16i.d)),_16k=B(_163(_167,_169.d));return new F(function(){return _13c(_16j.a,_16j.b,_16j.c,_16j.d,_16k.a,_16k.b,_16k.c,_16k.d);});}})(_164,_165));if(_166!=__continue){return _166;}}},_16l=function(_16m,_16n,_16o,_16p,_16q){while(1){var _16r=E(_16m);if(!_16r._){return new T4(0,_16n,_16o,_16p,_16q);}else{var _16s=E(_16r.a),_16t=B(_13c(_16n,_16o,_16p,_16q,_16s.a,_16s.b,_16s.c,_16s.d));_16m=_16r.b;_16n=_16t.a;_16o=_16t.b;_16p=_16t.c;_16q=_16t.d;continue;}}},_16u=function(_16v,_16w,_16x,_16y,_16z,_16A){var _16B=E(_16v),_16C=B(_13c(_16x,_16y,_16z,_16A,_16B.a,_16B.b,_16B.c,_16B.d));return new F(function(){return _16l(_16w,_16C.a,_16C.b,_16C.c,_16C.d);});},_16D=function(_16E,_16F,_16G,_16H,_16I){var _16J=B(_UW(_16F,_16H,_16I,_16G,_16E,_1)),_16K=_16J.a,_16L=_16J.b,_16M=B(_13D(_16L,_16K));return new F(function(){return _16u(new T(function(){var _16N=B(_13Q(_16E,E(_16K).a));return new T4(0,_16N.a,_16N.b,_16N.c,_16N.d);}),new T2(1,new T(function(){var _16O=B(_163(_16K,_16L));return new T4(0,_16O.a,_16O.b,_16O.c,_16O.d);}),_1),_16M.a,_16M.b,_16M.c,_16M.d);});},_16P="(function (t) {return document.getElementById(t).value})",_16Q=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_16R=new T(function(){return B(unCStr("contractState"));}),_16S=new T(function(){return B(unCStr("currBlock"));}),_16T=new T(function(){return eval("(function (x) { var node = document.getElementById(x); while (node.hasChildNodes()) { node.removeChild(node.lastChild); } })");}),_16U=new T(function(){return B(err(_ha));}),_16V=new T(function(){return B(err(_jS));}),_16W=new T(function(){return B(A3(_xS,_yl,_xn,_DB));}),_16X=new T(function(){return B(err(_ha));}),_16Y=new T(function(){return B(err(_jS));}),_16Z=function(_zv){return new F(function(){return _xH(_BM,_zv);});},_170=function(_171,_172){return new F(function(){return _yv(_16Z,_172);});},_173=new T(function(){return B(_yv(_16Z,_jV));}),_174=function(_zv){return new F(function(){return _l5(_173,_zv);});},_175=function(_176){var _177=new T(function(){return B(A3(_xH,_BM,_176,_jV));});return function(_zc){return new F(function(){return _l5(_177,_zc);});};},_178=new T4(0,_175,_174,_16Z,_170),_179=new T(function(){return B(unCStr("NotRedeemed"));}),_17a=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_17b=function(_17c,_17d){var _17e=new T(function(){var _17f=new T(function(){return B(A1(_17d,_Me));});return B(_wQ(function(_17g){var _17h=E(_17g);return (_17h._==3)?(!B(_lT(_17h.a,_17a)))?new T0(2):E(_17f):new T0(2);}));}),_17i=function(_17j){return E(_17e);},_17k=new T(function(){if(E(_17c)>10){return new T0(2);}else{var _17l=new T(function(){var _17m=new T(function(){var _17n=function(_17o){return new F(function(){return A3(_xS,_yl,_ze,function(_17p){return new F(function(){return A1(_17d,new T2(0,_17o,_17p));});});});};return B(A3(_xS,_yl,_ze,_17n));});return B(_wQ(function(_17q){var _17r=E(_17q);return (_17r._==3)?(!B(_lT(_17r.a,_179)))?new T0(2):E(_17m):new T0(2);}));}),_17s=function(_17t){return E(_17l);};return new T1(1,function(_17u){return new F(function(){return A2(_vx,_17u,_17s);});});}});return new F(function(){return _lf(new T1(1,function(_17v){return new F(function(){return A2(_vx,_17v,_17i);});}),_17k);});},_17w=function(_zv){return new F(function(){return _xH(_17b,_zv);});},_17x=function(_17y,_17z){return new F(function(){return _yv(_17w,_17z);});},_17A=new T(function(){return B(_yv(_17w,_jV));}),_17B=function(_zv){return new F(function(){return _l5(_17A,_zv);});},_17C=function(_17D){var _17E=new T(function(){return B(A3(_xH,_17b,_17D,_jV));});return function(_zc){return new F(function(){return _l5(_17E,_zc);});};},_17F=new T4(0,_17C,_17B,_17w,_17x),_17G=function(_17H,_17I){return new F(function(){return _A0(_zd,_17F,_17I);});},_17J=new T(function(){return B(_yv(_17G,_jV));}),_17K=function(_zv){return new F(function(){return _l5(_17J,_zv);});},_17L=new T(function(){return B(_A0(_zd,_17F,_jV));}),_17M=function(_zv){return new F(function(){return _l5(_17L,_zv);});},_17N=function(_17O,_zv){return new F(function(){return _17M(_zv);});},_17P=function(_17Q,_17R){return new F(function(){return _yv(_17G,_17R);});},_17S=new T4(0,_17N,_17K,_17G,_17P),_17T=function(_17U,_17V){return new F(function(){return _A0(_178,_17S,_17V);});},_17W=function(_17X,_17Y){return new F(function(){return _yv(_17T,_17Y);});},_17Z=new T(function(){return B(_yv(_17W,_jV));}),_180=function(_Av){return new F(function(){return _l5(_17Z,_Av);});},_181=function(_182){return new F(function(){return _yv(_17W,_182);});},_183=function(_184,_185){return new F(function(){return _181(_185);});},_186=new T(function(){return B(_yv(_17T,_jV));}),_187=function(_Av){return new F(function(){return _l5(_186,_Av);});},_188=function(_189,_Av){return new F(function(){return _187(_Av);});},_18a=new T4(0,_188,_180,_17W,_183),_18b=new T(function(){return B(_A0(_18a,_AF,_DB));}),_18c=42,_18d=new T(function(){return B(unCStr("actions"));}),_18e=function(_18f){while(1){var _18g=B((function(_18h){var _18i=E(_18h);if(!_18i._){return __Z;}else{var _18j=_18i.b,_18k=E(_18i.a);if(!E(_18k.b)._){return new T2(1,_18k.a,new T(function(){return B(_18e(_18j));}));}else{_18f=_18j;return __continue;}}})(_18f));if(_18g!=__continue){return _18g;}}},_18l=new T(function(){return B(err(_ha));}),_18m=new T(function(){return B(err(_jS));}),_18n=new T(function(){return B(unCStr("ConstMoney"));}),_18o=new T(function(){return B(unCStr("AvailableMoney"));}),_18p=new T(function(){return B(unCStr("AddMoney"));}),_18q=new T(function(){return B(unCStr("MoneyFromChoice"));}),_18r=function(_18s,_18t){var _18u=new T(function(){var _18v=new T(function(){var _18w=new T(function(){if(_18s>10){return new T0(2);}else{var _18x=new T(function(){var _18y=new T(function(){var _18z=function(_18A){var _18B=function(_18C){return new F(function(){return A3(_xH,_18D,_ze,function(_18E){return new F(function(){return A1(_18t,new T3(3,_18A,_18C,_18E));});});});};return new F(function(){return A3(_xS,_yl,_ze,_18B);});};return B(A3(_xH,_zr,_ze,_18z));});return B(_wQ(function(_18F){var _18G=E(_18F);return (_18G._==3)?(!B(_lT(_18G.a,_18q)))?new T0(2):E(_18y):new T0(2);}));}),_18H=function(_18I){return E(_18x);};return new T1(1,function(_18J){return new F(function(){return A2(_vx,_18J,_18H);});});}});if(_18s>10){return B(_lf(_jU,_18w));}else{var _18K=new T(function(){var _18L=new T(function(){return B(A3(_xS,_yl,_ze,function(_18M){return new F(function(){return A1(_18t,new T1(2,_18M));});}));});return B(_wQ(function(_18N){var _18O=E(_18N);return (_18O._==3)?(!B(_lT(_18O.a,_18n)))?new T0(2):E(_18L):new T0(2);}));}),_18P=function(_18Q){return E(_18K);};return B(_lf(new T1(1,function(_18R){return new F(function(){return A2(_vx,_18R,_18P);});}),_18w));}});if(_18s>10){return B(_lf(_jU,_18v));}else{var _18S=new T(function(){var _18T=new T(function(){var _18U=function(_18V){return new F(function(){return A3(_xH,_18D,_ze,function(_18W){return new F(function(){return A1(_18t,new T2(1,_18V,_18W));});});});};return B(A3(_xH,_18D,_ze,_18U));});return B(_wQ(function(_18X){var _18Y=E(_18X);return (_18Y._==3)?(!B(_lT(_18Y.a,_18p)))?new T0(2):E(_18T):new T0(2);}));}),_18Z=function(_190){return E(_18S);};return B(_lf(new T1(1,function(_191){return new F(function(){return A2(_vx,_191,_18Z);});}),_18v));}});if(_18s>10){return new F(function(){return _lf(_jU,_18u);});}else{var _192=new T(function(){var _193=new T(function(){return B(A3(_xH,_BM,_ze,function(_194){return new F(function(){return A1(_18t,new T1(0,_194));});}));});return B(_wQ(function(_195){var _196=E(_195);return (_196._==3)?(!B(_lT(_196.a,_18o)))?new T0(2):E(_193):new T0(2);}));}),_197=function(_198){return E(_192);};return new F(function(){return _lf(new T1(1,function(_199){return new F(function(){return A2(_vx,_199,_197);});}),_18u);});}},_18D=function(_19a,_19b){return new F(function(){return _18r(E(_19a),_19b);});},_19c=new T0(7),_19d=function(_19e,_19f){return new F(function(){return A1(_19f,_19c);});},_19g=new T(function(){return B(unCStr("TrueObs"));}),_19h=new T2(0,_19g,_19d),_19i=new T0(8),_19j=function(_19k,_19l){return new F(function(){return A1(_19l,_19i);});},_19m=new T(function(){return B(unCStr("FalseObs"));}),_19n=new T2(0,_19m,_19j),_19o=new T2(1,_19n,_1),_19p=new T2(1,_19h,_19o),_19q=function(_19r,_19s,_19t){var _19u=E(_19r);if(!_19u._){return new T0(2);}else{var _19v=E(_19u.a),_19w=_19v.a,_19x=new T(function(){return B(A2(_19v.b,_19s,_19t));}),_19y=new T(function(){return B(_wQ(function(_19z){var _19A=E(_19z);switch(_19A._){case 3:return (!B(_lT(_19w,_19A.a)))?new T0(2):E(_19x);case 4:return (!B(_lT(_19w,_19A.a)))?new T0(2):E(_19x);default:return new T0(2);}}));}),_19B=function(_19C){return E(_19y);};return new F(function(){return _lf(new T1(1,function(_19D){return new F(function(){return A2(_vx,_19D,_19B);});}),new T(function(){return B(_19q(_19u.b,_19s,_19t));}));});}},_19E=new T(function(){return B(unCStr("ValueGE"));}),_19F=new T(function(){return B(unCStr("PersonChoseSomething"));}),_19G=new T(function(){return B(unCStr("PersonChoseThis"));}),_19H=new T(function(){return B(unCStr("BelowTimeout"));}),_19I=new T(function(){return B(unCStr("AndObs"));}),_19J=new T(function(){return B(unCStr("OrObs"));}),_19K=new T(function(){return B(unCStr("NotObs"));}),_19L=function(_19M,_19N){var _19O=new T(function(){var _19P=E(_19M),_19Q=new T(function(){var _19R=new T(function(){var _19S=new T(function(){var _19T=new T(function(){var _19U=new T(function(){var _19V=new T(function(){if(_19P>10){return new T0(2);}else{var _19W=new T(function(){var _19X=new T(function(){var _19Y=function(_19Z){return new F(function(){return A3(_xH,_18D,_ze,function(_1a0){return new F(function(){return A1(_19N,new T2(6,_19Z,_1a0));});});});};return B(A3(_xH,_18D,_ze,_19Y));});return B(_wQ(function(_1a1){var _1a2=E(_1a1);return (_1a2._==3)?(!B(_lT(_1a2.a,_19E)))?new T0(2):E(_19X):new T0(2);}));}),_1a3=function(_1a4){return E(_19W);};return new T1(1,function(_1a5){return new F(function(){return A2(_vx,_1a5,_1a3);});});}});if(_19P>10){return B(_lf(_jU,_19V));}else{var _1a6=new T(function(){var _1a7=new T(function(){var _1a8=function(_1a9){return new F(function(){return A3(_xS,_yl,_ze,function(_1aa){return new F(function(){return A1(_19N,new T2(5,_1a9,_1aa));});});});};return B(A3(_xH,_zr,_ze,_1a8));});return B(_wQ(function(_1ab){var _1ac=E(_1ab);return (_1ac._==3)?(!B(_lT(_1ac.a,_19F)))?new T0(2):E(_1a7):new T0(2);}));}),_1ad=function(_1ae){return E(_1a6);};return B(_lf(new T1(1,function(_1af){return new F(function(){return A2(_vx,_1af,_1ad);});}),_19V));}});if(_19P>10){return B(_lf(_jU,_19U));}else{var _1ag=new T(function(){var _1ah=new T(function(){var _1ai=function(_1aj){var _1ak=function(_1al){return new F(function(){return A3(_xS,_yl,_ze,function(_1am){return new F(function(){return A1(_19N,new T3(4,_1aj,_1al,_1am));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1ak);});};return B(A3(_xH,_zr,_ze,_1ai));});return B(_wQ(function(_1an){var _1ao=E(_1an);return (_1ao._==3)?(!B(_lT(_1ao.a,_19G)))?new T0(2):E(_1ah):new T0(2);}));}),_1ap=function(_1aq){return E(_1ag);};return B(_lf(new T1(1,function(_1ar){return new F(function(){return A2(_vx,_1ar,_1ap);});}),_19U));}});if(_19P>10){return B(_lf(_jU,_19T));}else{var _1as=new T(function(){var _1at=new T(function(){return B(A3(_xH,_19L,_ze,function(_1au){return new F(function(){return A1(_19N,new T1(3,_1au));});}));});return B(_wQ(function(_1av){var _1aw=E(_1av);return (_1aw._==3)?(!B(_lT(_1aw.a,_19K)))?new T0(2):E(_1at):new T0(2);}));}),_1ax=function(_1ay){return E(_1as);};return B(_lf(new T1(1,function(_1az){return new F(function(){return A2(_vx,_1az,_1ax);});}),_19T));}});if(_19P>10){return B(_lf(_jU,_19S));}else{var _1aA=new T(function(){var _1aB=new T(function(){var _1aC=function(_1aD){return new F(function(){return A3(_xH,_19L,_ze,function(_1aE){return new F(function(){return A1(_19N,new T2(2,_1aD,_1aE));});});});};return B(A3(_xH,_19L,_ze,_1aC));});return B(_wQ(function(_1aF){var _1aG=E(_1aF);return (_1aG._==3)?(!B(_lT(_1aG.a,_19J)))?new T0(2):E(_1aB):new T0(2);}));}),_1aH=function(_1aI){return E(_1aA);};return B(_lf(new T1(1,function(_1aJ){return new F(function(){return A2(_vx,_1aJ,_1aH);});}),_19S));}});if(_19P>10){return B(_lf(_jU,_19R));}else{var _1aK=new T(function(){var _1aL=new T(function(){var _1aM=function(_1aN){return new F(function(){return A3(_xH,_19L,_ze,function(_1aO){return new F(function(){return A1(_19N,new T2(1,_1aN,_1aO));});});});};return B(A3(_xH,_19L,_ze,_1aM));});return B(_wQ(function(_1aP){var _1aQ=E(_1aP);return (_1aQ._==3)?(!B(_lT(_1aQ.a,_19I)))?new T0(2):E(_1aL):new T0(2);}));}),_1aR=function(_1aS){return E(_1aK);};return B(_lf(new T1(1,function(_1aT){return new F(function(){return A2(_vx,_1aT,_1aR);});}),_19R));}});if(_19P>10){return B(_lf(_jU,_19Q));}else{var _1aU=new T(function(){var _1aV=new T(function(){return B(A3(_xS,_yl,_ze,function(_1aW){return new F(function(){return A1(_19N,new T1(0,_1aW));});}));});return B(_wQ(function(_1aX){var _1aY=E(_1aX);return (_1aY._==3)?(!B(_lT(_1aY.a,_19H)))?new T0(2):E(_1aV):new T0(2);}));}),_1aZ=function(_1b0){return E(_1aU);};return B(_lf(new T1(1,function(_1b1){return new F(function(){return A2(_vx,_1b1,_1aZ);});}),_19Q));}});return new F(function(){return _lf(B(_19q(_19p,_19M,_19N)),_19O);});},_1b2=new T(function(){return B(unCStr("Null"));}),_1b3=new T(function(){return B(unCStr("CommitCash"));}),_1b4=new T(function(){return B(unCStr("RedeemCC"));}),_1b5=new T(function(){return B(unCStr("Pay"));}),_1b6=new T(function(){return B(unCStr("Both"));}),_1b7=new T(function(){return B(unCStr("Choice"));}),_1b8=new T(function(){return B(unCStr("When"));}),_1b9=function(_1ba,_1bb){var _1bc=new T(function(){var _1bd=new T(function(){return B(A1(_1bb,_Rm));});return B(_wQ(function(_1be){var _1bf=E(_1be);return (_1bf._==3)?(!B(_lT(_1bf.a,_1b2)))?new T0(2):E(_1bd):new T0(2);}));}),_1bg=function(_1bh){return E(_1bc);},_1bi=new T(function(){var _1bj=E(_1ba),_1bk=new T(function(){var _1bl=new T(function(){var _1bm=new T(function(){var _1bn=new T(function(){var _1bo=new T(function(){if(_1bj>10){return new T0(2);}else{var _1bp=new T(function(){var _1bq=new T(function(){var _1br=function(_1bs){var _1bt=function(_1bu){var _1bv=function(_1bw){return new F(function(){return A3(_xH,_1b9,_ze,function(_1bx){return new F(function(){return A1(_1bb,new T4(6,_1bs,_1bu,_1bw,_1bx));});});});};return new F(function(){return A3(_xH,_1b9,_ze,_1bv);});};return new F(function(){return A3(_xS,_yl,_ze,_1bt);});};return B(A3(_xH,_19L,_ze,_1br));});return B(_wQ(function(_1by){var _1bz=E(_1by);return (_1bz._==3)?(!B(_lT(_1bz.a,_1b8)))?new T0(2):E(_1bq):new T0(2);}));}),_1bA=function(_1bB){return E(_1bp);};return new T1(1,function(_1bC){return new F(function(){return A2(_vx,_1bC,_1bA);});});}});if(_1bj>10){return B(_lf(_jU,_1bo));}else{var _1bD=new T(function(){var _1bE=new T(function(){var _1bF=function(_1bG){var _1bH=function(_1bI){return new F(function(){return A3(_xH,_1b9,_ze,function(_1bJ){return new F(function(){return A1(_1bb,new T3(5,_1bG,_1bI,_1bJ));});});});};return new F(function(){return A3(_xH,_1b9,_ze,_1bH);});};return B(A3(_xH,_19L,_ze,_1bF));});return B(_wQ(function(_1bK){var _1bL=E(_1bK);return (_1bL._==3)?(!B(_lT(_1bL.a,_1b7)))?new T0(2):E(_1bE):new T0(2);}));}),_1bM=function(_1bN){return E(_1bD);};return B(_lf(new T1(1,function(_1bO){return new F(function(){return A2(_vx,_1bO,_1bM);});}),_1bo));}});if(_1bj>10){return B(_lf(_jU,_1bn));}else{var _1bP=new T(function(){var _1bQ=new T(function(){var _1bR=function(_1bS){return new F(function(){return A3(_xH,_1b9,_ze,function(_1bT){return new F(function(){return A1(_1bb,new T2(4,_1bS,_1bT));});});});};return B(A3(_xH,_1b9,_ze,_1bR));});return B(_wQ(function(_1bU){var _1bV=E(_1bU);return (_1bV._==3)?(!B(_lT(_1bV.a,_1b6)))?new T0(2):E(_1bQ):new T0(2);}));}),_1bW=function(_1bX){return E(_1bP);};return B(_lf(new T1(1,function(_1bY){return new F(function(){return A2(_vx,_1bY,_1bW);});}),_1bn));}});if(_1bj>10){return B(_lf(_jU,_1bm));}else{var _1bZ=new T(function(){var _1c0=new T(function(){var _1c1=function(_1c2){var _1c3=function(_1c4){var _1c5=function(_1c6){var _1c7=function(_1c8){var _1c9=function(_1ca){return new F(function(){return A3(_xH,_1b9,_ze,function(_1cb){return new F(function(){return A1(_1bb,new T6(3,_1c2,_1c4,_1c6,_1c8,_1ca,_1cb));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1c9);});};return new F(function(){return A3(_xH,_18D,_ze,_1c7);});};return new F(function(){return A3(_xS,_yl,_ze,_1c5);});};return new F(function(){return A3(_xS,_yl,_ze,_1c3);});};return B(A3(_xH,_AS,_ze,_1c1));});return B(_wQ(function(_1cc){var _1cd=E(_1cc);return (_1cd._==3)?(!B(_lT(_1cd.a,_1b5)))?new T0(2):E(_1c0):new T0(2);}));}),_1ce=function(_1cf){return E(_1bZ);};return B(_lf(new T1(1,function(_1cg){return new F(function(){return A2(_vx,_1cg,_1ce);});}),_1bm));}});if(_1bj>10){return B(_lf(_jU,_1bl));}else{var _1ch=new T(function(){var _1ci=new T(function(){var _1cj=function(_1ck){return new F(function(){return A3(_xH,_1b9,_ze,function(_1cl){return new F(function(){return A1(_1bb,new T2(2,_1ck,_1cl));});});});};return B(A3(_xH,_BM,_ze,_1cj));});return B(_wQ(function(_1cm){var _1cn=E(_1cm);return (_1cn._==3)?(!B(_lT(_1cn.a,_1b4)))?new T0(2):E(_1ci):new T0(2);}));}),_1co=function(_1cp){return E(_1ch);};return B(_lf(new T1(1,function(_1cq){return new F(function(){return A2(_vx,_1cq,_1co);});}),_1bl));}});if(_1bj>10){return B(_lf(_jU,_1bk));}else{var _1cr=new T(function(){var _1cs=new T(function(){var _1ct=function(_1cu){var _1cv=function(_1cw){var _1cx=function(_1cy){var _1cz=function(_1cA){var _1cB=function(_1cC){var _1cD=function(_1cE){return new F(function(){return A3(_xH,_1b9,_ze,function(_1cF){return new F(function(){return A1(_1bb,{_:1,a:_1cu,b:_1cw,c:_1cy,d:_1cA,e:_1cC,f:_1cE,g:_1cF});});});});};return new F(function(){return A3(_xH,_1b9,_ze,_1cD);});};return new F(function(){return A3(_xS,_yl,_ze,_1cB);});};return new F(function(){return A3(_xS,_yl,_ze,_1cz);});};return new F(function(){return A3(_xH,_18D,_ze,_1cx);});};return new F(function(){return A3(_xS,_yl,_ze,_1cv);});};return B(A3(_xH,_BM,_ze,_1ct));});return B(_wQ(function(_1cG){var _1cH=E(_1cG);return (_1cH._==3)?(!B(_lT(_1cH.a,_1b3)))?new T0(2):E(_1cs):new T0(2);}));}),_1cI=function(_1cJ){return E(_1cr);};return B(_lf(new T1(1,function(_1cK){return new F(function(){return A2(_vx,_1cK,_1cI);});}),_1bk));}});return new F(function(){return _lf(new T1(1,function(_1cL){return new F(function(){return A2(_vx,_1cL,_1bg);});}),_1bi);});},_1cM=new T(function(){return B(A3(_xH,_1b9,_xn,_DB));}),_1cN=function(_1cO,_){var _1cP=__app0(E(_16Q)),_1cQ=eval(E(_16P)),_1cR=__app1(E(_1cQ),toJSStr(E(_16S))),_1cS=__app1(E(_1cQ),toJSStr(E(_16R))),_1cT=__app1(E(_16T),toJSStr(_18d)),_1cU=B(_18e(B(_l5(_18b,new T(function(){var _1cV=String(_1cS);return fromJSStr(_1cV);})))));if(!_1cU._){return E(_16Y);}else{if(!E(_1cU.b)._){var _1cW=E(_1cU.a),_1cX=new T(function(){var _1cY=B(_18e(B(_l5(_1cM,new T(function(){var _1cZ=String(_1cP);return fromJSStr(_1cZ);})))));if(!_1cY._){return E(_18m);}else{if(!E(_1cY.b)._){return E(_1cY.a);}else{return E(_18l);}}}),_1d0=new T(function(){var _1d1=B(_18e(B(_l5(_16W,new T(function(){var _1d2=String(_1cR);return fromJSStr(_1d2);})))));if(!_1d1._){return E(_16V);}else{if(!E(_1d1.b)._){return E(_1d1.a);}else{return E(_16U);}}}),_1d3=B(_16D(new T2(0,_18c,_1d0),_1cO,_1cX,new T(function(){return B(_EV(_1cW.a));}),new T(function(){return B(_5s(_1cW.b));})));return new F(function(){return _GL(_1d3.a,_1d3.b,_1d3.c,_1d3.d,_);});}else{return E(_16X);}}},_1d4=new T(function(){return B(unCStr("contractInput"));}),_1d5="(function (t, s) {document.getElementById(t).value = s})",_1d6=function(_1d7,_1d8,_){var _1d9=eval(E(_1d5)),_1da=__app2(E(_1d9),toJSStr(E(_1d7)),toJSStr(E(_1d8)));return new F(function(){return _F8(_);});},_1db=function(_1dc,_1dd,_1de,_){var _1df=E(_1d4),_1dg=toJSStr(_1df),_1dh=eval(E(_16P)),_1di=__app1(E(_1dh),_1dg),_1dj=B(_18e(B(_l5(_DG,new T(function(){var _1dk=String(_1di);return fromJSStr(_1dk);})))));if(!_1dj._){return E(_jT);}else{if(!E(_1dj.b)._){var _1dl=E(_1dj.a),_1dm=B(_jD(new T(function(){return B(_gR(_1dl.a));},1),new T(function(){return B(_c2(_1dl.b));},1),new T(function(){return B(_dH(_1de,_1dc,_1dd,B(_fb(_1dl.c))));},1),new T(function(){return B(_5s(_1dl.d));},1))),_1dn=B(_1d6(_1df,new T2(1,_1dm.a,_1dm.b),_)),_1do=__app1(E(_1dh),_1dg),_1dp=new T(function(){var _1dq=B(_18e(B(_l5(_DG,new T(function(){var _1dr=String(_1do);return fromJSStr(_1dr);})))));if(!_1dq._){return E(_jT);}else{if(!E(_1dq.b)._){var _1ds=E(_1dq.a);return new T4(0,new T(function(){return B(_gR(_1ds.a));}),new T(function(){return B(_c2(_1ds.b));}),new T(function(){return B(_fb(_1ds.c));}),new T(function(){return B(_5s(_1ds.d));}));}else{return E(_jR);}}});return new F(function(){return _1cN(_1dp,_);});}else{return E(_jR);}}},_1dt=function(_1du,_1dv,_1dw,_1dx,_1dy){var _1dz=E(_1dy);if(!_1dz._){var _1dA=_1dz.c,_1dB=_1dz.d,_1dC=E(_1dz.b),_1dD=E(_1dC.a);if(_1du>=_1dD){if(_1du!=_1dD){return new F(function(){return _5N(_1dC,_1dA,B(_1dt(_1du,_,_1dw,_1dx,_1dB)));});}else{var _1dE=E(_1dC.b);if(_1dw>=_1dE){if(_1dw!=_1dE){return new F(function(){return _5N(_1dC,_1dA,B(_1dt(_1du,_,_1dw,_1dx,_1dB)));});}else{var _1dF=E(_1dC.c);if(_1dx>=_1dF){if(_1dx!=_1dF){return new F(function(){return _5N(_1dC,_1dA,B(_1dt(_1du,_,_1dw,_1dx,_1dB)));});}else{return new T4(0,_1dz.a,E(new T3(0,_1du,_1dw,_1dx)),E(_1dA),E(_1dB));}}else{return new F(function(){return _6x(_1dC,B(_1dt(_1du,_,_1dw,_1dx,_1dA)),_1dB);});}}}else{return new F(function(){return _6x(_1dC,B(_1dt(_1du,_,_1dw,_1dx,_1dA)),_1dB);});}}}else{return new F(function(){return _6x(_1dC,B(_1dt(_1du,_,_1dw,_1dx,_1dA)),_1dB);});}}else{return new T4(0,1,E(new T3(0,_1du,_1dw,_1dx)),E(_5I),E(_5I));}},_1dG=function(_1dH,_1dI,_1dJ,_1dK,_1dL){var _1dM=E(_1dL);if(!_1dM._){var _1dN=_1dM.c,_1dO=_1dM.d,_1dP=E(_1dM.b),_1dQ=E(_1dP.a);if(_1dH>=_1dQ){if(_1dH!=_1dQ){return new F(function(){return _5N(_1dP,_1dN,B(_1dG(_1dH,_,_1dJ,_1dK,_1dO)));});}else{var _1dR=E(_1dP.b);if(_1dJ>=_1dR){if(_1dJ!=_1dR){return new F(function(){return _5N(_1dP,_1dN,B(_1dG(_1dH,_,_1dJ,_1dK,_1dO)));});}else{var _1dS=E(_1dK),_1dT=E(_1dP.c);if(_1dS>=_1dT){if(_1dS!=_1dT){return new F(function(){return _5N(_1dP,_1dN,B(_1dt(_1dH,_,_1dJ,_1dS,_1dO)));});}else{return new T4(0,_1dM.a,E(new T3(0,_1dH,_1dJ,_1dS)),E(_1dN),E(_1dO));}}else{return new F(function(){return _6x(_1dP,B(_1dt(_1dH,_,_1dJ,_1dS,_1dN)),_1dO);});}}}else{return new F(function(){return _6x(_1dP,B(_1dG(_1dH,_,_1dJ,_1dK,_1dN)),_1dO);});}}}else{return new F(function(){return _6x(_1dP,B(_1dG(_1dH,_,_1dJ,_1dK,_1dN)),_1dO);});}}else{return new T4(0,1,E(new T3(0,_1dH,_1dJ,_1dK)),E(_5I),E(_5I));}},_1dU=function(_1dV,_1dW,_1dX,_1dY,_1dZ){var _1e0=E(_1dZ);if(!_1e0._){var _1e1=_1e0.c,_1e2=_1e0.d,_1e3=E(_1e0.b),_1e4=E(_1e3.a);if(_1dV>=_1e4){if(_1dV!=_1e4){return new F(function(){return _5N(_1e3,_1e1,B(_1dU(_1dV,_,_1dX,_1dY,_1e2)));});}else{var _1e5=E(_1dX),_1e6=E(_1e3.b);if(_1e5>=_1e6){if(_1e5!=_1e6){return new F(function(){return _5N(_1e3,_1e1,B(_1dG(_1dV,_,_1e5,_1dY,_1e2)));});}else{var _1e7=E(_1dY),_1e8=E(_1e3.c);if(_1e7>=_1e8){if(_1e7!=_1e8){return new F(function(){return _5N(_1e3,_1e1,B(_1dt(_1dV,_,_1e5,_1e7,_1e2)));});}else{return new T4(0,_1e0.a,E(new T3(0,_1dV,_1e5,_1e7)),E(_1e1),E(_1e2));}}else{return new F(function(){return _6x(_1e3,B(_1dt(_1dV,_,_1e5,_1e7,_1e1)),_1e2);});}}}else{return new F(function(){return _6x(_1e3,B(_1dG(_1dV,_,_1e5,_1dY,_1e1)),_1e2);});}}}else{return new F(function(){return _6x(_1e3,B(_1dU(_1dV,_,_1dX,_1dY,_1e1)),_1e2);});}}else{return new T4(0,1,E(new T3(0,_1dV,_1dX,_1dY)),E(_5I),E(_5I));}},_1e9=function(_1ea,_1eb,_1ec,_1ed){var _1ee=E(_1ed);if(!_1ee._){var _1ef=_1ee.c,_1eg=_1ee.d,_1eh=E(_1ee.b),_1ei=E(_1ea),_1ej=E(_1eh.a);if(_1ei>=_1ej){if(_1ei!=_1ej){return new F(function(){return _5N(_1eh,_1ef,B(_1dU(_1ei,_,_1eb,_1ec,_1eg)));});}else{var _1ek=E(_1eb),_1el=E(_1eh.b);if(_1ek>=_1el){if(_1ek!=_1el){return new F(function(){return _5N(_1eh,_1ef,B(_1dG(_1ei,_,_1ek,_1ec,_1eg)));});}else{var _1em=E(_1ec),_1en=E(_1eh.c);if(_1em>=_1en){if(_1em!=_1en){return new F(function(){return _5N(_1eh,_1ef,B(_1dt(_1ei,_,_1ek,_1em,_1eg)));});}else{return new T4(0,_1ee.a,E(new T3(0,_1ei,_1ek,_1em)),E(_1ef),E(_1eg));}}else{return new F(function(){return _6x(_1eh,B(_1dt(_1ei,_,_1ek,_1em,_1ef)),_1eg);});}}}else{return new F(function(){return _6x(_1eh,B(_1dG(_1ei,_,_1ek,_1ec,_1ef)),_1eg);});}}}else{return new F(function(){return _6x(_1eh,B(_1dU(_1ei,_,_1eb,_1ec,_1ef)),_1eg);});}}else{return new T4(0,1,E(new T3(0,_1ea,_1eb,_1ec)),E(_5I),E(_5I));}},_1eo=function(_1ep,_1eq,_1er,_){var _1es=E(_1d4),_1et=toJSStr(_1es),_1eu=eval(E(_16P)),_1ev=__app1(E(_1eu),_1et),_1ew=B(_18e(B(_l5(_DG,new T(function(){var _1ex=String(_1ev);return fromJSStr(_1ex);})))));if(!_1ew._){return E(_jT);}else{if(!E(_1ew.b)._){var _1ey=E(_1ew.a),_1ez=B(_jD(new T(function(){return B(_gR(_1ey.a));},1),new T(function(){return B(_1e9(_1er,_1ep,_1eq,B(_c2(_1ey.b))));},1),new T(function(){return B(_fb(_1ey.c));},1),new T(function(){return B(_5s(_1ey.d));},1))),_1eA=B(_1d6(_1es,new T2(1,_1ez.a,_1ez.b),_)),_1eB=__app1(E(_1eu),_1et),_1eC=new T(function(){var _1eD=B(_18e(B(_l5(_DG,new T(function(){var _1eE=String(_1eB);return fromJSStr(_1eE);})))));if(!_1eD._){return E(_jT);}else{if(!E(_1eD.b)._){var _1eF=E(_1eD.a);return new T4(0,new T(function(){return B(_gR(_1eF.a));}),new T(function(){return B(_c2(_1eF.b));}),new T(function(){return B(_fb(_1eF.c));}),new T(function(){return B(_5s(_1eF.d));}));}else{return E(_jR);}}});return new F(function(){return _1cN(_1eC,_);});}else{return E(_jR);}}},_1eG=function(_1eH,_1eI,_1eJ,_1eK,_){var _1eL=E(_1d4),_1eM=toJSStr(_1eL),_1eN=eval(E(_16P)),_1eO=__app1(E(_1eN),_1eM),_1eP=B(_18e(B(_l5(_DG,new T(function(){var _1eQ=String(_1eO);return fromJSStr(_1eQ);})))));if(!_1eP._){return E(_jT);}else{if(!E(_1eP.b)._){var _1eR=E(_1eP.a),_1eS=B(_jD(new T(function(){return B(_fr(_1eJ,_1eH,_1eI,_1eK,B(_gR(_1eR.a))));},1),new T(function(){return B(_c2(_1eR.b));},1),new T(function(){return B(_fb(_1eR.c));},1),new T(function(){return B(_5s(_1eR.d));},1))),_1eT=B(_1d6(_1eL,new T2(1,_1eS.a,_1eS.b),_)),_1eU=__app1(E(_1eN),_1eM),_1eV=new T(function(){var _1eW=B(_18e(B(_l5(_DG,new T(function(){var _1eX=String(_1eU);return fromJSStr(_1eX);})))));if(!_1eW._){return E(_jT);}else{if(!E(_1eW.b)._){var _1eY=E(_1eW.a);return new T4(0,new T(function(){return B(_gR(_1eY.a));}),new T(function(){return B(_c2(_1eY.b));}),new T(function(){return B(_fb(_1eY.c));}),new T(function(){return B(_5s(_1eY.d));}));}else{return E(_jR);}}});return new F(function(){return _1cN(_1eV,_);});}else{return E(_jR);}}},_1eZ=new T(function(){return B(err(_jS));}),_1f0=new T(function(){return B(unCStr("SICC"));}),_1f1=new T(function(){return B(unCStr("SIRC"));}),_1f2=new T(function(){return B(unCStr("SIP"));}),_1f3=11,_1f4=function(_1f5,_1f6){var _1f7=new T(function(){var _1f8=new T(function(){if(_1f5>10){return new T0(2);}else{var _1f9=new T(function(){var _1fa=new T(function(){var _1fb=function(_1fc){var _1fd=function(_1fe){return new F(function(){return A3(_xS,_yl,_1f3,function(_1ff){return new F(function(){return A1(_1f6,new T3(2,_1fc,_1fe,_1ff));});});});};return new F(function(){return A3(_xS,_yl,_1f3,_1fd);});};return B(A3(_xH,_AS,_1f3,_1fb));});return B(_wQ(function(_1fg){var _1fh=E(_1fg);return (_1fh._==3)?(!B(_lT(_1fh.a,_1f2)))?new T0(2):E(_1fa):new T0(2);}));}),_1fi=function(_1fj){return E(_1f9);};return new T1(1,function(_1fk){return new F(function(){return A2(_vx,_1fk,_1fi);});});}});if(_1f5>10){return B(_lf(_jU,_1f8));}else{var _1fl=new T(function(){var _1fm=new T(function(){var _1fn=function(_1fo){var _1fp=function(_1fq){return new F(function(){return A3(_xS,_yl,_1f3,function(_1fr){return new F(function(){return A1(_1f6,new T3(1,_1fo,_1fq,_1fr));});});});};return new F(function(){return A3(_xS,_yl,_1f3,_1fp);});};return B(A3(_xH,_BM,_1f3,_1fn));});return B(_wQ(function(_1fs){var _1ft=E(_1fs);return (_1ft._==3)?(!B(_lT(_1ft.a,_1f1)))?new T0(2):E(_1fm):new T0(2);}));}),_1fu=function(_1fv){return E(_1fl);};return B(_lf(new T1(1,function(_1fw){return new F(function(){return A2(_vx,_1fw,_1fu);});}),_1f8));}});if(_1f5>10){return new F(function(){return _lf(_jU,_1f7);});}else{var _1fx=new T(function(){var _1fy=new T(function(){var _1fz=function(_1fA){var _1fB=function(_1fC){var _1fD=function(_1fE){return new F(function(){return A3(_xS,_yl,_1f3,function(_1fF){return new F(function(){return A1(_1f6,new T4(0,_1fA,_1fC,_1fE,_1fF));});});});};return new F(function(){return A3(_xS,_yl,_1f3,_1fD);});};return new F(function(){return A3(_xS,_yl,_1f3,_1fB);});};return B(A3(_xH,_BM,_1f3,_1fz));});return B(_wQ(function(_1fG){var _1fH=E(_1fG);return (_1fH._==3)?(!B(_lT(_1fH.a,_1f0)))?new T0(2):E(_1fy):new T0(2);}));}),_1fI=function(_1fJ){return E(_1fx);};return new F(function(){return _lf(new T1(1,function(_1fK){return new F(function(){return A2(_vx,_1fK,_1fI);});}),_1f7);});}},_1fL=function(_1fM,_1fN){return new F(function(){return _1f4(E(_1fM),_1fN);});},_1fO=new T(function(){return B(A3(_xH,_1fL,_xn,_DB));}),_1fP=function(_1fQ,_){var _1fR=B(_18e(B(_l5(_1fO,_1fQ))));if(!_1fR._){return E(_1eZ);}else{if(!E(_1fR.b)._){var _1fS=E(_1fR.a);switch(_1fS._){case 0:return new F(function(){return _1eG(_1fS.b,_1fS.c,_1fS.a,_1fS.d,_);});break;case 1:return new F(function(){return _1eo(_1fS.b,_1fS.c,_1fS.a,_);});break;default:return new F(function(){return _1db(_1fS.b,_1fS.c,_1fS.a,_);});}}else{return E(_hb);}}},_1fT=function(_1fU,_1fV,_1fW,_){var _1fX=E(_1d4),_1fY=toJSStr(_1fX),_1fZ=eval(E(_16P)),_1g0=__app1(E(_1fZ),_1fY),_1g1=B(_18e(B(_l5(_DG,new T(function(){var _1g2=String(_1g0);return fromJSStr(_1g2);})))));if(!_1g1._){return E(_jT);}else{if(!E(_1g1.b)._){var _1g3=E(_1g1.a),_1g4=B(_jD(new T(function(){return B(_gR(_1g3.a));},1),new T(function(){return B(_c2(_1g3.b));},1),new T(function(){return B(_fb(_1g3.c));},1),new T(function(){return B(_3Y(_1fW,_1fU,_1fV,B(_5s(_1g3.d))));},1))),_1g5=B(_1d6(_1fX,new T2(1,_1g4.a,_1g4.b),_)),_1g6=__app1(E(_1fZ),_1fY),_1g7=new T(function(){var _1g8=B(_18e(B(_l5(_DG,new T(function(){var _1g9=String(_1g6);return fromJSStr(_1g9);})))));if(!_1g8._){return E(_jT);}else{if(!E(_1g8.b)._){var _1ga=E(_1g8.a);return new T4(0,new T(function(){return B(_gR(_1ga.a));}),new T(function(){return B(_c2(_1ga.b));}),new T(function(){return B(_fb(_1ga.c));}),new T(function(){return B(_5s(_1ga.d));}));}else{return E(_jR);}}});return new F(function(){return _1cN(_1g7,_);});}else{return E(_jR);}}},_1gb=new T(function(){return B(err(_ha));}),_1gc=new T(function(){return B(err(_jS));}),_1gd=new T(function(){return B(_A0(_zE,_zd,_DB));}),_1ge=function(_1gf,_1gg,_){var _1gh=new T(function(){var _1gi=B(_18e(B(_l5(_1gd,_1gf))));if(!_1gi._){return E(_1gc);}else{if(!E(_1gi.b)._){var _1gj=E(_1gi.a);return new T2(0,_1gj.a,_1gj.b);}else{return E(_1gb);}}});return new F(function(){return _1fT(new T(function(){return E(E(_1gh).b);}),_1gg,new T(function(){return E(E(_1gh).a);}),_);});},_1gk=new T(function(){return B(unCStr("When"));}),_1gl=new T(function(){return B(unCStr("Choice"));}),_1gm=new T(function(){return B(unCStr("Both"));}),_1gn=new T(function(){return B(unCStr("Pay"));}),_1go=new T(function(){return B(unCStr("RedeemCC"));}),_1gp=new T(function(){return B(unCStr("CommitCash"));}),_1gq=new T(function(){return B(unCStr("Null"));}),_1gr=32,_1gs=new T2(1,_1gr,_1),_1gt=function(_1gu){var _1gv=E(_1gu);return (_1gv==1)?E(_1gs):new T2(1,_1gr,new T(function(){return B(_1gt(_1gv-1|0));}));},_1gw=new T(function(){return B(unCStr("head"));}),_1gx=new T(function(){return B(_io(_1gw));}),_1gy=function(_1gz){return new F(function(){return _hA(0,E(_1gz),_1);});},_1gA=new T(function(){return B(unCStr("IdentPay"));}),_1gB=new T(function(){return B(unCStr("ValueGE"));}),_1gC=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1gD=new T(function(){return B(unCStr("PersonChoseThis"));}),_1gE=new T(function(){return B(unCStr("NotObs"));}),_1gF=new T(function(){return B(unCStr("OrObs"));}),_1gG=new T(function(){return B(unCStr("AndObs"));}),_1gH=new T(function(){return B(unCStr("BelowTimeout"));}),_1gI=new T(function(){return B(unCStr("IdentChoice"));}),_1gJ=new T(function(){return B(unCStr("IdentCC"));}),_1gK=new T(function(){return B(unCStr("MoneyFromChoice"));}),_1gL=new T(function(){return B(unCStr("ConstMoney"));}),_1gM=new T(function(){return B(unCStr("AddMoney"));}),_1gN=new T(function(){return B(unCStr("AvailableMoney"));}),_1gO=new T(function(){return B(unCStr("FalseObs"));}),_1gP=new T(function(){return B(unCStr("TrueObs"));}),_1gQ=function(_1gR){var _1gS=E(_1gR);switch(_1gS._){case 0:var _1gT=E(_1gS.a);switch(_1gT._){case 0:return new T2(0,_1gq,_1);case 1:return new T2(0,_1gp,new T2(1,new T1(3,_1gT.a),new T2(1,new T1(6,_1gT.b),new T2(1,new T1(2,_1gT.c),new T2(1,new T1(6,_1gT.d),new T2(1,new T1(6,_1gT.e),new T2(1,new T1(0,_1gT.f),new T2(1,new T1(0,_1gT.g),_1))))))));case 2:return new T2(0,_1go,new T2(1,new T1(3,_1gT.a),new T2(1,new T1(0,_1gT.b),_1)));case 3:return new T2(0,_1gn,new T2(1,new T1(5,_1gT.a),new T2(1,new T1(6,_1gT.b),new T2(1,new T1(6,_1gT.c),new T2(1,new T1(2,_1gT.d),new T2(1,new T1(6,_1gT.e),new T2(1,new T1(0,_1gT.f),_1)))))));case 4:return new T2(0,_1gm,new T2(1,new T1(0,_1gT.a),new T2(1,new T1(0,_1gT.b),_1)));case 5:return new T2(0,_1gl,new T2(1,new T1(1,_1gT.a),new T2(1,new T1(0,_1gT.b),new T2(1,new T1(0,_1gT.c),_1))));default:return new T2(0,_1gk,new T2(1,new T1(1,_1gT.a),new T2(1,new T1(6,_1gT.b),new T2(1,new T1(0,_1gT.c),new T2(1,new T1(0,_1gT.d),_1)))));}break;case 1:var _1gU=E(_1gS.a);switch(_1gU._){case 0:return new T2(0,_1gH,new T2(1,new T1(6,_1gU.a),_1));case 1:return new T2(0,_1gG,new T2(1,new T1(1,_1gU.a),new T2(1,new T1(1,_1gU.b),_1)));case 2:return new T2(0,_1gF,new T2(1,new T1(1,_1gU.a),new T2(1,new T1(1,_1gU.b),_1)));case 3:return new T2(0,_1gE,new T2(1,new T1(1,_1gU.a),_1));case 4:return new T2(0,_1gD,new T2(1,new T1(4,_1gU.a),new T2(1,new T1(6,_1gU.b),new T2(1,new T1(6,_1gU.c),_1))));case 5:return new T2(0,_1gC,new T2(1,new T1(4,_1gU.a),new T2(1,new T1(6,_1gU.b),_1)));case 6:return new T2(0,_1gB,new T2(1,new T1(2,_1gU.a),new T2(1,new T1(2,_1gU.b),_1)));case 7:return new T2(0,_1gP,_1);default:return new T2(0,_1gO,_1);}break;case 2:var _1gV=E(_1gS.a);switch(_1gV._){case 0:return new T2(0,_1gN,new T2(1,new T1(3,_1gV.a),_1));case 1:return new T2(0,_1gM,new T2(1,new T1(2,_1gV.a),new T2(1,new T1(2,_1gV.b),_1)));case 2:return new T2(0,_1gL,new T2(1,new T1(6,_1gV.a),_1));default:return new T2(0,_1gK,new T2(1,new T1(4,_1gV.a),new T2(1,new T1(6,_1gV.b),new T2(1,new T1(2,_1gV.c),_1))));}break;case 3:return new T2(0,_1gJ,new T2(1,new T1(6,_1gS.a),_1));case 4:return new T2(0,_1gI,new T2(1,new T1(6,_1gS.a),_1));case 5:return new T2(0,_1gA,new T2(1,new T1(6,_1gS.a),_1));default:return new T2(0,new T(function(){return B(_1gy(_1gS.a));}),_1);}},_1gW=function(_1gX){var _1gY=B(_1gQ(_1gX)),_1gZ=_1gY.a,_1h0=E(_1gY.b);if(!_1h0._){return new T1(0,new T2(0,_1gZ,_1));}else{switch(E(_1gX)._){case 0:return new T1(2,new T2(0,_1gZ,_1h0));case 1:return new T1(2,new T2(0,_1gZ,_1h0));case 2:return new T1(2,new T2(0,_1gZ,_1h0));default:return new T1(1,new T2(0,_1gZ,_1h0));}}},_1h1=function(_1h2,_1h3){var _1h4=E(_1h3);if(!_1h4._){return __Z;}else{var _1h5=_1h4.a,_1h6=new T(function(){var _1h7=B(_kG(new T(function(){return B(A1(_1h2,_1h5));}),_1h4.b));return new T2(0,_1h7.a,_1h7.b);});return new T2(1,new T2(1,_1h5,new T(function(){return E(E(_1h6).a);})),new T(function(){return B(_1h1(_1h2,E(_1h6).b));}));}},_1h8=function(_1h9){var _1ha=E(_1h9);if(!_1ha._){return __Z;}else{return new F(function(){return _hq(_1ha.a,new T(function(){return B(_1h8(_1ha.b));},1));});}},_1hb=function(_1hc,_1hd){return (E(_1hc)._==2)?false:(E(_1hd)._==2)?false:true;},_1he=function(_1hf,_1hg){var _1hh=E(_1hg);return (_1hh._==0)?__Z:new T2(1,_1hf,new T2(1,_1hh.a,new T(function(){return B(_1he(_1hf,_1hh.b));})));},_1hi=new T(function(){return B(unCStr("\n"));}),_1hj=new T(function(){return B(unCStr("tail"));}),_1hk=new T(function(){return B(_io(_1hj));}),_1hl=function(_1hm,_1hn,_1ho){var _1hp=E(_1ho);if(!_1hp._){return E(_1hn);}else{var _1hq=new T(function(){return (E(_1hm)+B(_oy(_1hn,0))|0)+1|0;}),_1hr=new T(function(){return B(_1h1(_1hb,B(_oD(_1gW,_1hp))));}),_1hs=new T(function(){var _1ht=E(_1hr);if(!_1ht._){return E(_1hk);}else{var _1hu=new T(function(){var _1hv=E(_1hq);if(0>=_1hv){return __Z;}else{return B(_1gt(_1hv));}}),_1hw=function(_1hx){var _1hy=new T(function(){var _1hz=function(_1hA){var _1hB=E(_1hA);if(!_1hB._){return __Z;}else{var _1hC=new T(function(){return B(_hq(B(_1hD(_1hq,_1hB.a)),new T(function(){return B(_1hz(_1hB.b));},1)));});return new T2(1,_1gr,_1hC);}},_1hE=B(_1hz(_1hx));if(!_1hE._){return __Z;}else{return E(_1hE.b);}},1);return new F(function(){return _hq(_1hu,_1hy);});};return B(_1he(_1hi,B(_oD(_1hw,_1ht.b))));}}),_1hF=new T(function(){var _1hG=new T(function(){var _1hH=E(_1hr);if(!_1hH._){return E(_1gx);}else{var _1hI=function(_1hJ){var _1hK=E(_1hJ);if(!_1hK._){return __Z;}else{var _1hL=new T(function(){return B(_hq(B(_1hD(_1hq,_1hK.a)),new T(function(){return B(_1hI(_1hK.b));},1)));});return new T2(1,_1gr,_1hL);}};return B(_1hI(_1hH.a));}},1);return B(_hq(_1hn,_1hG));});return new F(function(){return _1h8(new T2(1,_1hF,_1hs));});}},_1hM=new T(function(){return B(unCStr(")"));}),_1hD=function(_1hN,_1hO){var _1hP=E(_1hO);switch(_1hP._){case 0:var _1hQ=E(_1hP.a);return new F(function(){return _1hR(0,_1hQ.a,_1hQ.b);});break;case 1:return new F(function(){return unAppCStr("(",new T(function(){var _1hS=E(_1hP.a);return B(_hq(B(_1hR(0,_1hS.a,_1hS.b)),_1hM));}));});break;default:var _1hT=new T(function(){var _1hU=E(_1hP.a);return B(_hq(B(_1hl(new T(function(){return E(_1hN)+1|0;},1),_1hU.a,_1hU.b)),_1hM));});return new F(function(){return unAppCStr("(",_1hT);});}},_1hR=function(_1hV,_1hW,_1hX){var _1hY=E(_1hX);if(!_1hY._){return E(_1hW);}else{var _1hZ=new T(function(){return (_1hV+B(_oy(_1hW,0))|0)+1|0;}),_1i0=new T(function(){return B(_1h1(_1hb,B(_oD(_1gW,_1hY))));}),_1i1=new T(function(){var _1i2=E(_1i0);if(!_1i2._){return E(_1hk);}else{var _1i3=new T(function(){var _1i4=E(_1hZ);if(0>=_1i4){return __Z;}else{return B(_1gt(_1i4));}}),_1i5=function(_1i6){var _1i7=new T(function(){var _1i8=function(_1i9){var _1ia=E(_1i9);if(!_1ia._){return __Z;}else{var _1ib=new T(function(){return B(_hq(B(_1hD(_1hZ,_1ia.a)),new T(function(){return B(_1i8(_1ia.b));},1)));});return new T2(1,_1gr,_1ib);}},_1ic=B(_1i8(_1i6));if(!_1ic._){return __Z;}else{return E(_1ic.b);}},1);return new F(function(){return _hq(_1i3,_1i7);});};return B(_1he(_1hi,B(_oD(_1i5,_1i2.b))));}}),_1id=new T(function(){var _1ie=new T(function(){var _1if=E(_1i0);if(!_1if._){return E(_1gx);}else{var _1ig=function(_1ih){var _1ii=E(_1ih);if(!_1ii._){return __Z;}else{var _1ij=new T(function(){return B(_hq(B(_1hD(_1hZ,_1ii.a)),new T(function(){return B(_1ig(_1ii.b));},1)));});return new T2(1,_1gr,_1ij);}};return B(_1ig(_1if.a));}},1);return B(_hq(_1hW,_1ie));});return new F(function(){return _1h8(new T2(1,_1id,_1i1));});}},_1ik=new T(function(){return B(_1hR(0,_1gq,_1));}),_1il=function(_1im,_){return new T(function(){var _1in=B(_18e(B(_l5(_1cM,_1im))));if(!_1in._){return E(_18m);}else{if(!E(_1in.b)._){var _1io=E(_1in.a);switch(_1io._){case 0:return E(_1ik);break;case 1:return B(_1hR(0,_1gp,new T2(1,new T1(3,_1io.a),new T2(1,new T1(6,_1io.b),new T2(1,new T1(2,_1io.c),new T2(1,new T1(6,_1io.d),new T2(1,new T1(6,_1io.e),new T2(1,new T1(0,_1io.f),new T2(1,new T1(0,_1io.g),_1)))))))));break;case 2:return B(_1hR(0,_1go,new T2(1,new T1(3,_1io.a),new T2(1,new T1(0,_1io.b),_1))));break;case 3:return B(_1hR(0,_1gn,new T2(1,new T1(5,_1io.a),new T2(1,new T1(6,_1io.b),new T2(1,new T1(6,_1io.c),new T2(1,new T1(2,_1io.d),new T2(1,new T1(6,_1io.e),new T2(1,new T1(0,_1io.f),_1))))))));break;case 4:return B(_1hR(0,_1gm,new T2(1,new T1(0,_1io.a),new T2(1,new T1(0,_1io.b),_1))));break;case 5:return B(_1hR(0,_1gl,new T2(1,new T1(1,_1io.a),new T2(1,new T1(0,_1io.b),new T2(1,new T1(0,_1io.c),_1)))));break;default:return B(_1hR(0,_1gk,new T2(1,new T1(1,_1io.a),new T2(1,new T1(6,_1io.b),new T2(1,new T1(0,_1io.c),new T2(1,new T1(0,_1io.d),_1))))));}}else{return E(_18l);}}});},_1ip=new T(function(){return B(unCStr("codeArea"));}),_1iq=function(_){var _1ir=__app0(E(_16Q)),_1is=B(_1il(new T(function(){var _1it=String(_1ir);return fromJSStr(_1it);}),_)),_1iu=B(_1d6(_1ip,_1is,_)),_1iv=eval(E(_16P)),_1iw=__app1(E(_1iv),toJSStr(E(_1d4))),_1ix=new T(function(){var _1iy=B(_18e(B(_l5(_DG,new T(function(){var _1iz=String(_1iw);return fromJSStr(_1iz);})))));if(!_1iy._){return E(_jT);}else{if(!E(_1iy.b)._){var _1iA=E(_1iy.a);return new T4(0,new T(function(){return B(_gR(_1iA.a));}),new T(function(){return B(_c2(_1iA.b));}),new T(function(){return B(_fb(_1iA.c));}),new T(function(){return B(_5s(_1iA.d));}));}else{return E(_jR);}}});return new F(function(){return _1cN(_1ix,_);});},_1iB="(function (b) { return (b.inputList.length); })",_1iC="(function (b, x) { return (b.inputList[x]); })",_1iD=function(_1iE,_1iF,_){var _1iG=eval(E(_1iC)),_1iH=__app2(E(_1iG),_1iE,_1iF);return new T1(0,_1iH);},_1iI=function(_1iJ,_1iK,_1iL,_){var _1iM=E(_1iL);if(!_1iM._){return _1;}else{var _1iN=B(_1iD(_1iJ,E(_1iM.a),_)),_1iO=B(_1iI(_1iJ,_,_1iM.b,_));return new T2(1,_1iN,_1iO);}},_1iP=function(_1iQ,_1iR){if(_1iQ<=_1iR){var _1iS=function(_1iT){return new T2(1,_1iT,new T(function(){if(_1iT!=_1iR){return B(_1iS(_1iT+1|0));}else{return __Z;}}));};return new F(function(){return _1iS(_1iQ);});}else{return __Z;}},_1iU=function(_1iV,_){var _1iW=eval(E(_1iB)),_1iX=__app1(E(_1iW),_1iV),_1iY=Number(_1iX),_1iZ=jsTrunc(_1iY);return new F(function(){return _1iI(_1iV,_,new T(function(){return B(_1iP(0,_1iZ-1|0));}),_);});},_1j0="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_1j1="(function (x) { return x.name; })",_1j2=new T(function(){return B(unCStr("\""));}),_1j3=function(_1j4){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_hq(_1j4,_1j2));}))));});},_1j5=function(_1j6,_1j7,_){var _1j8=E(_1j7);if(!_1j8._){return new F(function(){return _1j3(_1j6);});}else{var _1j9=E(_1j8.a),_1ja=E(_1j1),_1jb=eval(_1ja),_1jc=__app1(E(_1jb),E(_1j9.a)),_1jd=String(_1jc);if(!B(_lT(fromJSStr(_1jd),_1j6))){var _1je=function(_1jf,_1jg,_){while(1){var _1jh=E(_1jg);if(!_1jh._){return new F(function(){return _1j3(_1jf);});}else{var _1ji=E(_1jh.a),_1jj=eval(_1ja),_1jk=__app1(E(_1jj),E(_1ji.a)),_1jl=String(_1jk);if(!B(_lT(fromJSStr(_1jl),_1jf))){_1jg=_1jh.b;continue;}else{return _1ji;}}}};return new F(function(){return _1je(_1j6,_1j8.b,_);});}else{return _1j9;}}},_1jm=function(_1jn,_1jo,_1jp,_){var _1jq=B(_1iU(_1jo,_)),_1jr=B(_1j5(_1jn,_1jq,_)),_1js=eval(E(_1j0)),_1jt=__app2(E(_1js),E(E(_1jp).a),E(E(_1jr).a));return new F(function(){return _F8(_);});},_1ju="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_1jv=function(_1jw,_1jx,_1jy,_){var _1jz=B(_1iU(_1jx,_)),_1jA=B(_1j5(_1jw,_1jz,_)),_1jB=eval(E(_1ju)),_1jC=__app2(E(_1jB),E(E(_1jy).a),E(E(_1jA).a));return new F(function(){return _F8(_);});},_1jD=function(_1jE){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_hq(_1jE,_1j2));}))));});},_1jF=function(_1jG,_1jH,_){var _1jI=E(_1jH);if(!_1jI._){return new F(function(){return _1jD(_1jG);});}else{var _1jJ=E(_1jI.a),_1jK=E(_1j1),_1jL=eval(_1jK),_1jM=__app1(E(_1jL),E(_1jJ.a)),_1jN=String(_1jM);if(!B(_lT(fromJSStr(_1jN),_1jG))){var _1jO=function(_1jP,_1jQ,_){while(1){var _1jR=E(_1jQ);if(!_1jR._){return new F(function(){return _1jD(_1jP);});}else{var _1jS=E(_1jR.a),_1jT=eval(_1jK),_1jU=__app1(E(_1jT),E(_1jS.a)),_1jV=String(_1jU);if(!B(_lT(fromJSStr(_1jV),_1jP))){_1jQ=_1jR.b;continue;}else{return _1jS;}}}};return new F(function(){return _1jO(_1jG,_1jI.b,_);});}else{return _1jJ;}}},_1jW="(function (b) { return (b.fieldRow.length); })",_1jX="(function (b, x) { return (b.fieldRow[x]); })",_1jY=function(_1jZ,_1k0,_){var _1k1=eval(E(_1jX)),_1k2=__app2(E(_1k1),_1jZ,_1k0);return new T1(0,_1k2);},_1k3=function(_1k4,_1k5,_1k6,_){var _1k7=E(_1k6);if(!_1k7._){return _1;}else{var _1k8=B(_1jY(_1k4,E(_1k7.a),_)),_1k9=B(_1k3(_1k4,_,_1k7.b,_));return new T2(1,_1k8,_1k9);}},_1ka=function(_1kb,_){var _1kc=eval(E(_1jW)),_1kd=__app1(E(_1kc),_1kb),_1ke=Number(_1kd),_1kf=jsTrunc(_1ke);return new F(function(){return _1k3(_1kb,_,new T(function(){return B(_1iP(0,_1kf-1|0));}),_);});},_1kg=function(_1kh,_){var _1ki=E(_1kh);if(!_1ki._){return _1;}else{var _1kj=B(_1ka(E(E(_1ki.a).a),_)),_1kk=B(_1kg(_1ki.b,_));return new T2(1,_1kj,_1kk);}},_1kl=function(_1km){var _1kn=E(_1km);if(!_1kn._){return __Z;}else{return new F(function(){return _hq(_1kn.a,new T(function(){return B(_1kl(_1kn.b));},1));});}},_1ko=function(_1kp,_1kq,_){var _1kr=B(_1iU(_1kq,_)),_1ks=B(_1kg(_1kr,_));return new F(function(){return _1jF(_1kp,B(_1kl(_1ks)),_);});},_1kt=function(_1ku,_1kv,_1kw,_){var _1kx=B(_1iU(_1kv,_)),_1ky=B(_1j5(_1ku,_1kx,_)),_1kz=eval(E(_1ju)),_1kA=__app2(E(_1kz),E(E(_1kw).a),E(E(_1ky).a));return new F(function(){return _F8(_);});},_1kB=new T(function(){return B(unCStr("contract_commitcash"));}),_1kC=new T(function(){return B(unCStr("contract_redeemcc"));}),_1kD=new T(function(){return B(unCStr("contract_pay"));}),_1kE=new T(function(){return B(unCStr("contract_both"));}),_1kF=new T(function(){return B(unCStr("contract_choice"));}),_1kG=new T(function(){return B(unCStr("contract_when"));}),_1kH="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_1kI=function(_1kJ,_){var _1kK=eval(E(_1kH)),_1kL=__app1(E(_1kK),toJSStr(E(_1kJ)));return new T1(0,_1kL);},_1kM=new T(function(){return B(unCStr("payer_id"));}),_1kN=new T(function(){return B(unCStr("pay_id"));}),_1kO=new T(function(){return B(unCStr("ccommit_id"));}),_1kP=new T(function(){return B(unCStr("end_expiration"));}),_1kQ=new T(function(){return B(unCStr("start_expiration"));}),_1kR=new T(function(){return B(unCStr("person_id"));}),_1kS=new T(function(){return B(unCStr("contract_null"));}),_1kT=new T(function(){return B(unCStr("contract2"));}),_1kU=new T(function(){return B(unCStr("contract1"));}),_1kV=new T(function(){return B(unCStr("observation"));}),_1kW=new T(function(){return B(unCStr("timeout"));}),_1kX=new T(function(){return B(unCStr("contract"));}),_1kY=new T(function(){return B(unCStr("expiration"));}),_1kZ=new T(function(){return B(unCStr("ammount"));}),_1l0=new T(function(){return B(unCStr("payee_id"));}),_1l1=new T(function(){return B(unCStr("value_available_money"));}),_1l2=new T(function(){return B(unCStr("value_add_money"));}),_1l3=new T(function(){return B(unCStr("value_const_money"));}),_1l4=new T(function(){return B(unCStr("money_from_choice"));}),_1l5=new T(function(){return B(unCStr("value2"));}),_1l6=new T(function(){return B(unCStr("value1"));}),_1l7=new T(function(){return B(unCStr("choice_id"));}),_1l8=new T(function(){return B(unCStr("default"));}),_1l9=new T(function(){return B(unCStr("money"));}),_1la=new T(function(){return B(unCStr("commit_id"));}),_1lb="(function (b, s) { return (b.setText(s)); })",_1lc=function(_1ld,_){var _1le=E(_1ld);switch(_1le._){case 0:var _1lf=B(_1kI(_1l1,_)),_1lg=E(_1lf),_1lh=B(_1ko(_1la,E(_1lg.a),_)),_1li=eval(E(_1lb)),_1lj=__app2(E(_1li),E(E(_1lh).a),toJSStr(B(_hA(0,E(_1le.a),_1))));return _1lg;case 1:var _1lk=B(_1lc(_1le.a,_)),_1ll=B(_1lc(_1le.b,_)),_1lm=B(_1kI(_1l2,_)),_1ln=E(_1lm),_1lo=E(_1ln.a),_1lp=B(_1jv(_1l6,_1lo,_1lk,_)),_1lq=B(_1jv(_1l5,_1lo,_1ll,_));return _1ln;case 2:var _1lr=B(_1kI(_1l3,_)),_1ls=E(_1lr),_1lt=B(_1ko(_1l9,E(_1ls.a),_)),_1lu=eval(E(_1lb)),_1lv=__app2(E(_1lu),E(E(_1lt).a),toJSStr(B(_hA(0,E(_1le.a),_1))));return _1ls;default:var _1lw=B(_1lc(_1le.c,_)),_1lx=B(_1kI(_1l4,_)),_1ly=E(_1lx),_1lz=E(_1ly.a),_1lA=B(_1ko(_1l7,_1lz,_)),_1lB=eval(E(_1lb)),_1lC=__app2(E(_1lB),E(E(_1lA).a),toJSStr(B(_hA(0,E(_1le.a),_1)))),_1lD=B(_1ko(_1kR,_1lz,_)),_1lE=__app2(E(_1lB),E(E(_1lD).a),toJSStr(B(_hA(0,E(_1le.b),_1)))),_1lF=B(_1jv(_1l8,_1lz,_1lw,_));return _1ly;}},_1lG=new T(function(){return B(unCStr("observation_personchosethis"));}),_1lH=new T(function(){return B(unCStr("observation_personchosesomething"));}),_1lI=new T(function(){return B(unCStr("observation_value_ge"));}),_1lJ=new T(function(){return B(unCStr("observation_trueobs"));}),_1lK=new T(function(){return B(unCStr("observation_falseobs"));}),_1lL=new T(function(){return B(unCStr("observation_belowtimeout"));}),_1lM=new T(function(){return B(unCStr("observation_andobs"));}),_1lN=new T(function(){return B(unCStr("observation_orobs"));}),_1lO=new T(function(){return B(unCStr("observation_notobs"));}),_1lP=new T(function(){return B(unCStr("person"));}),_1lQ=new T(function(){return B(unCStr("choice_value"));}),_1lR=new T(function(){return B(unCStr("observation2"));}),_1lS=new T(function(){return B(unCStr("observation1"));}),_1lT=new T(function(){return B(unCStr("block_number"));}),_1lU=function(_1lV,_){var _1lW=E(_1lV);switch(_1lW._){case 0:var _1lX=B(_1kI(_1lL,_)),_1lY=E(_1lX),_1lZ=B(_1ko(_1lT,E(_1lY.a),_)),_1m0=eval(E(_1lb)),_1m1=__app2(E(_1m0),E(E(_1lZ).a),toJSStr(B(_hA(0,E(_1lW.a),_1))));return _1lY;case 1:var _1m2=B(_1lU(_1lW.a,_)),_1m3=B(_1lU(_1lW.b,_)),_1m4=B(_1kI(_1lM,_)),_1m5=E(_1m4),_1m6=E(_1m5.a),_1m7=B(_1kt(_1lS,_1m6,_1m2,_)),_1m8=B(_1kt(_1lR,_1m6,_1m3,_));return _1m5;case 2:var _1m9=B(_1lU(_1lW.a,_)),_1ma=B(_1lU(_1lW.b,_)),_1mb=B(_1kI(_1lN,_)),_1mc=E(_1mb),_1md=E(_1mc.a),_1me=B(_1kt(_1lS,_1md,_1m9,_)),_1mf=B(_1kt(_1lR,_1md,_1ma,_));return _1mc;case 3:var _1mg=B(_1lU(_1lW.a,_)),_1mh=B(_1kI(_1lO,_)),_1mi=E(_1mh),_1mj=B(_1kt(_1kV,E(_1mi.a),_1mg,_));return _1mi;case 4:var _1mk=B(_1kI(_1lG,_)),_1ml=E(_1mk),_1mm=E(_1ml.a),_1mn=B(_1ko(_1l7,_1mm,_)),_1mo=eval(E(_1lb)),_1mp=__app2(E(_1mo),E(E(_1mn).a),toJSStr(B(_hA(0,E(_1lW.a),_1)))),_1mq=B(_1ko(_1lP,_1mm,_)),_1mr=__app2(E(_1mo),E(E(_1mq).a),toJSStr(B(_hA(0,E(_1lW.b),_1)))),_1ms=B(_1ko(_1lQ,_1mm,_)),_1mt=__app2(E(_1mo),E(E(_1ms).a),toJSStr(B(_hA(0,E(_1lW.c),_1))));return _1ml;case 5:var _1mu=B(_1kI(_1lH,_)),_1mv=E(_1mu),_1mw=E(_1mv.a),_1mx=B(_1ko(_1l7,_1mw,_)),_1my=eval(E(_1lb)),_1mz=__app2(E(_1my),E(E(_1mx).a),toJSStr(B(_hA(0,E(_1lW.a),_1)))),_1mA=B(_1ko(_1lP,_1mw,_)),_1mB=__app2(E(_1my),E(E(_1mA).a),toJSStr(B(_hA(0,E(_1lW.b),_1))));return _1mv;case 6:var _1mC=B(_1lc(_1lW.a,_)),_1mD=B(_1lc(_1lW.b,_)),_1mE=B(_1kI(_1lI,_)),_1mF=E(_1mE),_1mG=E(_1mF.a),_1mH=B(_1jv(_1l6,_1mG,_1mC,_)),_1mI=B(_1jv(_1l5,_1mG,_1mD,_));return _1mF;case 7:return new F(function(){return _1kI(_1lJ,_);});break;default:return new F(function(){return _1kI(_1lK,_);});}},_1mJ=function(_1mK,_){var _1mL=E(_1mK);switch(_1mL._){case 0:return new F(function(){return _1kI(_1kS,_);});break;case 1:var _1mM=B(_1mJ(_1mL.f,_)),_1mN=B(_1mJ(_1mL.g,_)),_1mO=B(_1lc(_1mL.c,_)),_1mP=B(_1kI(_1kB,_)),_1mQ=E(_1mP),_1mR=E(_1mQ.a),_1mS=B(_1ko(_1kO,_1mR,_)),_1mT=eval(E(_1lb)),_1mU=__app2(E(_1mT),E(E(_1mS).a),toJSStr(B(_hA(0,E(_1mL.a),_1)))),_1mV=B(_1ko(_1kR,_1mR,_)),_1mW=__app2(E(_1mT),E(E(_1mV).a),toJSStr(B(_hA(0,E(_1mL.b),_1)))),_1mX=B(_1jv(_1kZ,_1mR,_1mO,_)),_1mY=B(_1ko(_1kQ,_1mR,_)),_1mZ=__app2(E(_1mT),E(E(_1mY).a),toJSStr(B(_hA(0,E(_1mL.d),_1)))),_1n0=B(_1ko(_1kP,_1mR,_)),_1n1=__app2(E(_1mT),E(E(_1n0).a),toJSStr(B(_hA(0,E(_1mL.e),_1)))),_1n2=B(_1jm(_1kU,_1mR,_1mM,_)),_1n3=B(_1jm(_1kT,_1mR,_1mN,_));return _1mQ;case 2:var _1n4=B(_1mJ(_1mL.b,_)),_1n5=B(_1kI(_1kC,_)),_1n6=E(_1n5),_1n7=E(_1n6.a),_1n8=B(_1ko(_1kO,_1n7,_)),_1n9=eval(E(_1lb)),_1na=__app2(E(_1n9),E(E(_1n8).a),toJSStr(B(_hA(0,E(_1mL.a),_1)))),_1nb=B(_1jm(_1kX,_1n7,_1n4,_));return _1n6;case 3:var _1nc=B(_1mJ(_1mL.f,_)),_1nd=B(_1kI(_1kD,_)),_1ne=B(_1lc(_1mL.d,_)),_1nf=E(_1nd),_1ng=E(_1nf.a),_1nh=B(_1ko(_1kN,_1ng,_)),_1ni=eval(E(_1lb)),_1nj=__app2(E(_1ni),E(E(_1nh).a),toJSStr(B(_hA(0,E(_1mL.a),_1)))),_1nk=B(_1ko(_1kM,_1ng,_)),_1nl=__app2(E(_1ni),E(E(_1nk).a),toJSStr(B(_hA(0,E(_1mL.b),_1)))),_1nm=B(_1ko(_1l0,_1ng,_)),_1nn=__app2(E(_1ni),E(E(_1nm).a),toJSStr(B(_hA(0,E(_1mL.c),_1)))),_1no=B(_1jv(_1kZ,_1ng,_1ne,_)),_1np=B(_1ko(_1kY,_1ng,_)),_1nq=__app2(E(_1ni),E(E(_1np).a),toJSStr(B(_hA(0,E(_1mL.e),_1)))),_1nr=B(_1jm(_1kX,_1ng,_1nc,_));return _1nf;case 4:var _1ns=B(_1mJ(_1mL.a,_)),_1nt=B(_1mJ(_1mL.b,_)),_1nu=B(_1kI(_1kE,_)),_1nv=E(_1nu),_1nw=E(_1nv.a),_1nx=B(_1jm(_1kU,_1nw,_1ns,_)),_1ny=B(_1jm(_1kT,_1nw,_1nt,_));return _1nv;case 5:var _1nz=B(_1lU(_1mL.a,_)),_1nA=B(_1mJ(_1mL.b,_)),_1nB=B(_1mJ(_1mL.c,_)),_1nC=B(_1kI(_1kF,_)),_1nD=E(_1nC),_1nE=E(_1nD.a),_1nF=B(_1kt(_1kV,_1nE,_1nz,_)),_1nG=B(_1jm(_1kU,_1nE,_1nA,_)),_1nH=B(_1jm(_1kT,_1nE,_1nB,_));return _1nD;default:var _1nI=B(_1lU(_1mL.a,_)),_1nJ=B(_1mJ(_1mL.c,_)),_1nK=B(_1mJ(_1mL.d,_)),_1nL=B(_1kI(_1kG,_)),_1nM=E(_1nL),_1nN=E(_1nM.a),_1nO=B(_1ko(_1kW,_1nN,_)),_1nP=eval(E(_1lb)),_1nQ=__app2(E(_1nP),E(E(_1nO).a),toJSStr(B(_hA(0,E(_1mL.b),_1)))),_1nR=B(_1kt(_1kV,_1nN,_1nI,_)),_1nS=B(_1jm(_1kU,_1nN,_1nJ,_)),_1nT=B(_1jm(_1kT,_1nN,_1nK,_));return _1nM;}},_1nU=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_1nV=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_1nW=new T(function(){return B(unCStr("base_contract"));}),_1nX=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_1nY=function(_1nZ,_){var _1o0=__app0(E(_1nU)),_1o1=__app0(E(_1nV)),_1o2=B(_18e(B(_l5(_1cM,_1nZ))));if(!_1o2._){return E(_18m);}else{if(!E(_1o2.b)._){var _1o3=B(_1mJ(_1o2.a,_)),_1o4=B(_1jm(_1nW,_1o1,_1o3,_)),_1o5=__app0(E(_1nX)),_1o6=eval(E(_16P)),_1o7=__app1(E(_1o6),toJSStr(E(_1d4))),_1o8=new T(function(){var _1o9=B(_18e(B(_l5(_DG,new T(function(){var _1oa=String(_1o7);return fromJSStr(_1oa);})))));if(!_1o9._){return E(_jT);}else{if(!E(_1o9.b)._){var _1ob=E(_1o9.a);return new T4(0,new T(function(){return B(_gR(_1ob.a));}),new T(function(){return B(_c2(_1ob.b));}),new T(function(){return B(_fb(_1ob.c));}),new T(function(){return B(_5s(_1ob.d));}));}else{return E(_jR);}}});return new F(function(){return _1cN(_1o8,_);});}else{return E(_18l);}}},_1oc=function(_){var _1od=eval(E(_16P)),_1oe=__app1(E(_1od),toJSStr(E(_1ip)));return new F(function(){return _1nY(new T(function(){var _1of=String(_1oe);return fromJSStr(_1of);}),_);});},_1og=new T(function(){return B(unCStr("contractOutput"));}),_1oh=new T(function(){return B(unCStr("([], [], [], [])"));}),_1oi=new T(function(){return B(unCStr("([], [])"));}),_1oj=new T(function(){return B(_hA(0,0,_1));}),_1ok=function(_){var _1ol=__app0(E(_1nU)),_1om=B(_1d6(_1ip,_1,_)),_1on=B(_1d6(_16S,_1oj,_)),_1oo=B(_1d6(_16R,_1oi,_)),_1op=B(_1d6(_1d4,_1oh,_));return new F(function(){return _1d6(_1og,_1,_);});},_1oq=new T(function(){return B(unCStr("NotRedeemed "));}),_1or=function(_1os,_1ot,_1ou){var _1ov=E(_1ot);if(!_1ov._){var _1ow=function(_1ox){return new F(function(){return _hA(11,E(_1ov.a),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1ov.b),_1ox));})));});};if(E(_1os)<11){return new F(function(){return _hq(_1oq,new T(function(){return B(_1ow(_1ou));},1));});}else{var _1oy=new T(function(){return B(_hq(_1oq,new T(function(){return B(_1ow(new T2(1,_hy,_1ou)));},1)));});return new T2(1,_hz,_1oy);}}else{return new F(function(){return _hq(_17a,_1ou);});}},_1oz=0,_1oA=function(_1oB,_1oC,_1oD){var _1oE=new T(function(){var _1oF=function(_1oG){var _1oH=E(_1oC),_1oI=new T(function(){return B(A3(_is,_hk,new T2(1,function(_1oJ){return new F(function(){return _hA(0,E(_1oH.a),_1oJ);});},new T2(1,function(_Av){return new F(function(){return _1or(_1oz,_1oH.b,_Av);});},_1)),new T2(1,_hy,_1oG)));});return new T2(1,_hz,_1oI);};return B(A3(_is,_hk,new T2(1,function(_1oK){return new F(function(){return _hF(0,_1oB,_1oK);});},new T2(1,_1oF,_1)),new T2(1,_hy,_1oD)));});return new T2(0,_hz,_1oE);},_1oL=function(_1oM,_1oN){var _1oO=E(_1oM),_1oP=B(_1oA(_1oO.a,_1oO.b,_1oN));return new T2(1,_1oP.a,_1oP.b);},_1oQ=function(_1oR,_1oS){return new F(function(){return _iR(_1oL,_1oR,_1oS);});},_1oT=new T(function(){return B(unCStr("ChoiceMade "));}),_1oU=new T(function(){return B(unCStr("DuplicateRedeem "));}),_1oV=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_1oW=new T(function(){return B(unCStr("CommitRedeemed "));}),_1oX=new T(function(){return B(unCStr("SuccessfulCommit "));}),_1oY=new T(function(){return B(unCStr("FailedPay "));}),_1oZ=new T(function(){return B(unCStr("ExpiredPay "));}),_1p0=new T(function(){return B(unCStr("SuccessfulPay "));}),_1p1=function(_1p2,_1p3,_1p4){var _1p5=E(_1p3);switch(_1p5._){case 0:var _1p6=function(_1p7){var _1p8=new T(function(){var _1p9=new T(function(){return B(_hA(11,E(_1p5.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1p5.d),_1p7));}))));});return B(_hA(11,E(_1p5.b),new T2(1,_hK,_1p9)));});return new F(function(){return _ih(11,_1p5.a,new T2(1,_hK,_1p8));});};if(_1p2<11){return new F(function(){return _hq(_1p0,new T(function(){return B(_1p6(_1p4));},1));});}else{var _1pa=new T(function(){return B(_hq(_1p0,new T(function(){return B(_1p6(new T2(1,_hy,_1p4)));},1)));});return new T2(1,_hz,_1pa);}break;case 1:var _1pb=function(_1pc){var _1pd=new T(function(){var _1pe=new T(function(){return B(_hA(11,E(_1p5.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1p5.d),_1pc));}))));});return B(_hA(11,E(_1p5.b),new T2(1,_hK,_1pe)));});return new F(function(){return _ih(11,_1p5.a,new T2(1,_hK,_1pd));});};if(_1p2<11){return new F(function(){return _hq(_1oZ,new T(function(){return B(_1pb(_1p4));},1));});}else{var _1pf=new T(function(){return B(_hq(_1oZ,new T(function(){return B(_1pb(new T2(1,_hy,_1p4)));},1)));});return new T2(1,_hz,_1pf);}break;case 2:var _1pg=function(_1ph){var _1pi=new T(function(){var _1pj=new T(function(){return B(_hA(11,E(_1p5.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1p5.d),_1ph));}))));});return B(_hA(11,E(_1p5.b),new T2(1,_hK,_1pj)));});return new F(function(){return _ih(11,_1p5.a,new T2(1,_hK,_1pi));});};if(_1p2<11){return new F(function(){return _hq(_1oY,new T(function(){return B(_1pg(_1p4));},1));});}else{var _1pk=new T(function(){return B(_hq(_1oY,new T(function(){return B(_1pg(new T2(1,_hy,_1p4)));},1)));});return new T2(1,_hz,_1pk);}break;case 3:var _1pl=function(_1pm){var _1pn=new T(function(){var _1po=new T(function(){return B(_hA(11,E(_1p5.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1p5.c),_1pm));}))));});return B(_hF(11,_1p5.a,new T2(1,_hK,_1po)));},1);return new F(function(){return _hq(_1oX,_1pn);});};if(_1p2<11){return new F(function(){return _1pl(_1p4);});}else{return new T2(1,_hz,new T(function(){return B(_1pl(new T2(1,_hy,_1p4)));}));}break;case 4:var _1pp=function(_1pq){var _1pr=new T(function(){var _1ps=new T(function(){return B(_hA(11,E(_1p5.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1p5.c),_1pq));}))));});return B(_hF(11,_1p5.a,new T2(1,_hK,_1ps)));},1);return new F(function(){return _hq(_1oW,_1pr);});};if(_1p2<11){return new F(function(){return _1pp(_1p4);});}else{return new T2(1,_hz,new T(function(){return B(_1pp(new T2(1,_hy,_1p4)));}));}break;case 5:var _1pt=function(_1pu){var _1pv=new T(function(){var _1pw=new T(function(){return B(_hA(11,E(_1p5.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1p5.c),_1pu));}))));});return B(_hF(11,_1p5.a,new T2(1,_hK,_1pw)));},1);return new F(function(){return _hq(_1oV,_1pv);});};if(_1p2<11){return new F(function(){return _1pt(_1p4);});}else{return new T2(1,_hz,new T(function(){return B(_1pt(new T2(1,_hy,_1p4)));}));}break;case 6:var _1px=function(_1py){return new F(function(){return _hF(11,_1p5.a,new T2(1,_hK,new T(function(){return B(_hA(11,E(_1p5.b),_1py));})));});};if(_1p2<11){return new F(function(){return _hq(_1oU,new T(function(){return B(_1px(_1p4));},1));});}else{var _1pz=new T(function(){return B(_hq(_1oU,new T(function(){return B(_1px(new T2(1,_hy,_1p4)));},1)));});return new T2(1,_hz,_1pz);}break;default:var _1pA=function(_1pB){var _1pC=new T(function(){var _1pD=new T(function(){return B(_hA(11,E(_1p5.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1p5.c),_1pB));}))));});return B(_j6(11,_1p5.a,new T2(1,_hK,_1pD)));},1);return new F(function(){return _hq(_1oT,_1pC);});};if(_1p2<11){return new F(function(){return _1pA(_1p4);});}else{return new T2(1,_hz,new T(function(){return B(_1pA(new T2(1,_hy,_1p4)));}));}}},_1pE=new T(function(){return B(unAppCStr("[]",_1));}),_1pF=new T2(1,_iP,_1),_1pG=function(_1pH){var _1pI=E(_1pH);if(!_1pI._){return E(_1pF);}else{var _1pJ=new T(function(){return B(_1p1(0,_1pI.a,new T(function(){return B(_1pG(_1pI.b));})));});return new T2(1,_hj,_1pJ);}},_1pK=function(_){var _1pL=E(_1d4),_1pM=toJSStr(_1pL),_1pN=eval(E(_16P)),_1pO=_1pN,_1pP=__app1(E(_1pO),_1pM),_1pQ=E(_16R),_1pR=__app1(E(_1pO),toJSStr(_1pQ)),_1pS=__app0(E(_16Q)),_1pT=E(_16S),_1pU=__app1(E(_1pO),toJSStr(_1pT)),_1pV=new T(function(){var _1pW=B(_18e(B(_l5(_16W,new T(function(){var _1pX=String(_1pU);return fromJSStr(_1pX);})))));if(!_1pW._){return E(_16V);}else{if(!E(_1pW.b)._){return E(_1pW.a);}else{return E(_16U);}}}),_1pY=B(_18e(B(_l5(_18b,new T(function(){var _1pZ=String(_1pR);return fromJSStr(_1pZ);})))));if(!_1pY._){return E(_16Y);}else{if(!E(_1pY.b)._){var _1q0=E(_1pY.a),_1q1=new T(function(){var _1q2=B(_18e(B(_l5(_1cM,new T(function(){var _1q3=String(_1pS);return fromJSStr(_1q3);})))));if(!_1q2._){return E(_18m);}else{if(!E(_1q2.b)._){return E(_1q2.a);}else{return E(_18l);}}}),_1q4=new T(function(){var _1q5=B(_18e(B(_l5(_DG,new T(function(){var _1q6=String(_1pP);return fromJSStr(_1q6);})))));if(!_1q5._){return E(_jT);}else{if(!E(_1q5.b)._){var _1q7=E(_1q5.a);return new T4(0,new T(function(){return B(_gR(_1q7.a));}),new T(function(){return B(_c2(_1q7.b));}),new T(function(){return B(_fb(_1q7.c));}),new T(function(){return B(_5s(_1q7.d));}));}else{return E(_jR);}}}),_1q8=B(_UW(_1q4,new T(function(){return B(_EV(_1q0.a));}),new T(function(){return B(_5s(_1q0.b));}),_1q1,new T2(0,_18c,_1pV),_1)),_1q9=function(_,_1qa){var _1qb=function(_,_1qc){var _1qd=E(_1q8.a),_1qe=new T(function(){var _1qf=new T(function(){return B(_hc(_1,_1qd.b));}),_1qg=new T(function(){return B(_hc(_1,_1qd.a));});return B(A3(_is,_hk,new T2(1,function(_1qh){return new F(function(){return _1oQ(_1qg,_1qh);});},new T2(1,function(_1qi){return new F(function(){return _js(_1qf,_1qi);});},_1)),_jv));}),_1qj=B(_1d6(_1pQ,new T2(1,_hz,_1qe),_)),_1qk=B(_1d6(_1pL,_1oh,_)),_1ql=B(_1d6(_1pT,B(_hA(0,E(_1pV)+1|0,_1)),_)),_1qm=__app1(E(_1pO),toJSStr(E(_1ip))),_1qn=B(_1nY(new T(function(){var _1qo=String(_1qm);return fromJSStr(_1qo);}),_)),_1qp=__app1(E(_1pO),_1pM),_1qq=new T(function(){var _1qr=B(_18e(B(_l5(_DG,new T(function(){var _1qs=String(_1qp);return fromJSStr(_1qs);})))));if(!_1qr._){return E(_jT);}else{if(!E(_1qr.b)._){var _1qt=E(_1qr.a);return new T4(0,new T(function(){return B(_gR(_1qt.a));}),new T(function(){return B(_c2(_1qt.b));}),new T(function(){return B(_fb(_1qt.c));}),new T(function(){return B(_5s(_1qt.d));}));}else{return E(_jR);}}});return new F(function(){return _1cN(_1qq,_);});},_1qu=E(_1q8.b);switch(_1qu._){case 0:var _1qv=B(_1d6(_1ip,_1ik,_));return new F(function(){return _1qb(_,_1qv);});break;case 1:var _1qw=B(_1d6(_1ip,B(_1hR(0,_1gp,new T2(1,new T1(3,_1qu.a),new T2(1,new T1(6,_1qu.b),new T2(1,new T1(2,_1qu.c),new T2(1,new T1(6,_1qu.d),new T2(1,new T1(6,_1qu.e),new T2(1,new T1(0,_1qu.f),new T2(1,new T1(0,_1qu.g),_1))))))))),_));return new F(function(){return _1qb(_,_1qw);});break;case 2:var _1qx=B(_1d6(_1ip,B(_1hR(0,_1go,new T2(1,new T1(3,_1qu.a),new T2(1,new T1(0,_1qu.b),_1)))),_));return new F(function(){return _1qb(_,_1qx);});break;case 3:var _1qy=B(_1d6(_1ip,B(_1hR(0,_1gn,new T2(1,new T1(5,_1qu.a),new T2(1,new T1(6,_1qu.b),new T2(1,new T1(6,_1qu.c),new T2(1,new T1(2,_1qu.d),new T2(1,new T1(6,_1qu.e),new T2(1,new T1(0,_1qu.f),_1)))))))),_));return new F(function(){return _1qb(_,_1qy);});break;case 4:var _1qz=B(_1d6(_1ip,B(_1hR(0,_1gm,new T2(1,new T1(0,_1qu.a),new T2(1,new T1(0,_1qu.b),_1)))),_));return new F(function(){return _1qb(_,_1qz);});break;case 5:var _1qA=B(_1d6(_1ip,B(_1hR(0,_1gl,new T2(1,new T1(1,_1qu.a),new T2(1,new T1(0,_1qu.b),new T2(1,new T1(0,_1qu.c),_1))))),_));return new F(function(){return _1qb(_,_1qA);});break;default:var _1qB=B(_1d6(_1ip,B(_1hR(0,_1gk,new T2(1,new T1(1,_1qu.a),new T2(1,new T1(6,_1qu.b),new T2(1,new T1(0,_1qu.c),new T2(1,new T1(0,_1qu.d),_1)))))),_));return new F(function(){return _1qb(_,_1qB);});}},_1qC=E(_1q8.c);if(!_1qC._){var _1qD=B(_1d6(_1og,_1pE,_));return new F(function(){return _1q9(_,_1qD);});}else{var _1qE=new T(function(){return B(_1p1(0,_1qC.a,new T(function(){return B(_1pG(_1qC.b));})));}),_1qF=B(_1d6(_1og,new T2(1,_iQ,_1qE),_));return new F(function(){return _1q9(_,_1qF);});}}else{return E(_16X);}}},_1qG=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qH=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qI=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qJ=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qK=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qL=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qM=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qN=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qO=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qP=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qQ=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qR=function(_){return new F(function(){return __jsNull();});},_1qS=function(_1qT){var _1qU=B(A1(_1qT,_));return E(_1qU);},_1qV=new T(function(){return B(_1qS(_1qR));}),_1qW=new T(function(){return E(_1qV);}),_1qX=function(_){var _1qY=eval(E(_16P)),_1qZ=__app1(E(_1qY),toJSStr(E(_1d4))),_1r0=new T(function(){var _1r1=B(_18e(B(_l5(_DG,new T(function(){var _1r2=String(_1qZ);return fromJSStr(_1r2);})))));if(!_1r1._){return E(_jT);}else{if(!E(_1r1.b)._){var _1r3=E(_1r1.a);return new T4(0,new T(function(){return B(_gR(_1r3.a));}),new T(function(){return B(_c2(_1r3.b));}),new T(function(){return B(_fb(_1r3.c));}),new T(function(){return B(_5s(_1r3.d));}));}else{return E(_jR);}}});return new F(function(){return _1cN(_1r0,_);});},_1r4=function(_){var _1r5=eval(E(_16P)),_1r6=__app1(E(_1r5),toJSStr(E(_1ip))),_1r7=B(_1nY(new T(function(){var _1r8=String(_1r6);return fromJSStr(_1r8);}),_)),_1r9=__createJSFunc(0,function(_){var _1ra=B(_1ok(_));return _1qW;}),_1rb=__app2(E(_1qN),"clear_workspace",_1r9),_1rc=__createJSFunc(0,function(_){var _1rd=B(_1iq(_));return _1qW;}),_1re=__app2(E(_1qM),"b2c",_1rc),_1rf=__createJSFunc(0,function(_){var _1rg=B(_1oc(_));return _1qW;}),_1rh=__app2(E(_1qL),"c2b",_1rf),_1ri=function(_1rj){var _1rk=new T(function(){var _1rl=Number(E(_1rj));return jsTrunc(_1rl);}),_1rm=function(_1rn){var _1ro=new T(function(){var _1rp=Number(E(_1rn));return jsTrunc(_1rp);}),_1rq=function(_1rr){var _1rs=new T(function(){var _1rt=Number(E(_1rr));return jsTrunc(_1rt);}),_1ru=function(_1rv,_){var _1rw=B(_1eG(_1rk,_1ro,_1rs,new T(function(){var _1rx=Number(E(_1rv));return jsTrunc(_1rx);}),_));return _1qW;};return E(_1ru);};return E(_1rq);};return E(_1rm);},_1ry=__createJSFunc(5,E(_1ri)),_1rz=__app2(E(_1qK),"commit",_1ry),_1rA=function(_1rB){var _1rC=new T(function(){var _1rD=Number(E(_1rB));return jsTrunc(_1rD);}),_1rE=function(_1rF){var _1rG=new T(function(){var _1rH=Number(E(_1rF));return jsTrunc(_1rH);}),_1rI=function(_1rJ,_){var _1rK=B(_1eo(_1rC,_1rG,new T(function(){var _1rL=Number(E(_1rJ));return jsTrunc(_1rL);}),_));return _1qW;};return E(_1rI);};return E(_1rE);},_1rM=__createJSFunc(4,E(_1rA)),_1rN=__app2(E(_1qJ),"redeem",_1rM),_1rO=function(_1rP){var _1rQ=new T(function(){var _1rR=Number(E(_1rP));return jsTrunc(_1rR);}),_1rS=function(_1rT){var _1rU=new T(function(){var _1rV=Number(E(_1rT));return jsTrunc(_1rV);}),_1rW=function(_1rX,_){var _1rY=B(_1db(_1rQ,_1rU,new T(function(){var _1rZ=Number(E(_1rX));return jsTrunc(_1rZ);}),_));return _1qW;};return E(_1rW);};return E(_1rS);},_1s0=__createJSFunc(4,E(_1rO)),_1s1=__app2(E(_1qI),"claim",_1s0),_1s2=function(_1s3){var _1s4=new T(function(){var _1s5=Number(E(_1s3));return jsTrunc(_1s5);}),_1s6=function(_1s7){var _1s8=new T(function(){var _1s9=Number(E(_1s7));return jsTrunc(_1s9);}),_1sa=function(_1sb,_){var _1sc=B(_1fT(_1s4,_1s8,new T(function(){var _1sd=Number(E(_1sb));return jsTrunc(_1sd);}),_));return _1qW;};return E(_1sa);};return E(_1s6);},_1se=__createJSFunc(4,E(_1s2)),_1sf=__app2(E(_1qH),"choose",_1se),_1sg=__createJSFunc(0,function(_){var _1sh=B(_1pK(_));return _1qW;}),_1si=__app2(E(_1qG),"execute",_1sg),_1sj=__createJSFunc(0,function(_){var _1sk=B(_1qX(_));return _1qW;}),_1sl=__app2(E(_1qQ),"refreshActions",_1sj),_1sm=function(_1sn,_){var _1so=B(_1fP(new T(function(){var _1sp=String(E(_1sn));return fromJSStr(_1sp);}),_));return _1qW;},_1sq=__createJSFunc(2,E(_1sm)),_1sr=__app2(E(_1qP),"addAction",_1sq),_1ss=function(_1st){var _1su=new T(function(){var _1sv=String(E(_1st));return fromJSStr(_1sv);}),_1sw=function(_1sx,_){var _1sy=B(_1ge(_1su,new T(function(){var _1sz=Number(E(_1sx));return jsTrunc(_1sz);}),_));return _1qW;};return E(_1sw);},_1sA=__createJSFunc(3,E(_1ss)),_1sB=__app2(E(_1qO),"addActionWithNum",_1sA),_1sC=__app1(E(_1r5),toJSStr(E(_1d4))),_1sD=new T(function(){var _1sE=B(_18e(B(_l5(_DG,new T(function(){var _1sF=String(_1sC);return fromJSStr(_1sF);})))));if(!_1sE._){return E(_jT);}else{if(!E(_1sE.b)._){var _1sG=E(_1sE.a);return new T4(0,new T(function(){return B(_gR(_1sG.a));}),new T(function(){return B(_c2(_1sG.b));}),new T(function(){return B(_fb(_1sG.c));}),new T(function(){return B(_5s(_1sG.d));}));}else{return E(_jR);}}}),_1sH=B(_1cN(_1sD,_));return _h9;},_1sI=function(_){return new F(function(){return _1r4(_);});};
var hasteMain = function() {B(A(_1sI, [0]));};window.onload = hasteMain;