"use strict";
var __haste_prog_id = '940a806ac7f6bff2cbb384f08caf8d88b01493137e9ae27bf20dc31425b15bcf';
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

var _0=0,_1=new T(function(){return B(unCStr("IdentChoice "));}),_2=function(_3,_4){var _5=E(_3);return (_5._==0)?E(_4):new T2(1,_5.a,new T(function(){return B(_2(_5.b,_4));}));},_6=function(_7,_8){var _9=jsShowI(_7);return new F(function(){return _2(fromJSStr(_9),_8);});},_a=41,_b=40,_c=function(_d,_e,_f){if(_e>=0){return new F(function(){return _6(_e,_f);});}else{if(_d<=6){return new F(function(){return _6(_e,_f);});}else{return new T2(1,_b,new T(function(){var _g=jsShowI(_e);return B(_2(fromJSStr(_g),new T2(1,_a,_f)));}));}}},_h=function(_i,_j,_k){if(_i<11){return new F(function(){return _2(_1,new T(function(){return B(_c(11,E(_j),_k));},1));});}else{var _l=new T(function(){return B(_2(_1,new T(function(){return B(_c(11,E(_j),new T2(1,_a,_k)));},1)));});return new T2(1,_b,_l);}},_m=new T(function(){return B(unCStr("FalseObs"));}),_n=new T(function(){return B(unCStr("TrueObs"));}),_o=new T(function(){return B(unCStr("PersonChoseSomething "));}),_p=new T(function(){return B(unCStr("PersonChoseThis "));}),_q=new T(function(){return B(unCStr("NotObs "));}),_r=new T(function(){return B(unCStr("OrObs "));}),_s=new T(function(){return B(unCStr("AndObs "));}),_t=new T(function(){return B(unCStr("BelowTimeout "));}),_u=32,_v=function(_w,_x,_y){var _z=E(_x);switch(_z._){case 0:var _A=_z.a;if(_w<11){return new F(function(){return _2(_t,new T(function(){return B(_c(11,E(_A),_y));},1));});}else{var _B=new T(function(){return B(_2(_t,new T(function(){return B(_c(11,E(_A),new T2(1,_a,_y)));},1)));});return new T2(1,_b,_B);}break;case 1:var _C=function(_D){var _E=new T(function(){return B(_v(11,_z.a,new T2(1,_u,new T(function(){return B(_v(11,_z.b,_D));}))));},1);return new F(function(){return _2(_s,_E);});};if(_w<11){return new F(function(){return _C(_y);});}else{return new T2(1,_b,new T(function(){return B(_C(new T2(1,_a,_y)));}));}break;case 2:var _F=function(_G){var _H=new T(function(){return B(_v(11,_z.a,new T2(1,_u,new T(function(){return B(_v(11,_z.b,_G));}))));},1);return new F(function(){return _2(_r,_H);});};if(_w<11){return new F(function(){return _F(_y);});}else{return new T2(1,_b,new T(function(){return B(_F(new T2(1,_a,_y)));}));}break;case 3:var _I=_z.a;if(_w<11){return new F(function(){return _2(_q,new T(function(){return B(_v(11,_I,_y));},1));});}else{var _J=new T(function(){return B(_2(_q,new T(function(){return B(_v(11,_I,new T2(1,_a,_y)));},1)));});return new T2(1,_b,_J);}break;case 4:var _K=function(_L){var _M=new T(function(){var _N=new T(function(){return B(_c(11,E(_z.b),new T2(1,_u,new T(function(){return B(_c(11,E(_z.c),_L));}))));});return B(_h(11,_z.a,new T2(1,_u,_N)));},1);return new F(function(){return _2(_p,_M);});};if(_w<11){return new F(function(){return _K(_y);});}else{return new T2(1,_b,new T(function(){return B(_K(new T2(1,_a,_y)));}));}break;case 5:var _O=function(_P){return new F(function(){return _h(11,_z.a,new T2(1,_u,new T(function(){return B(_c(11,E(_z.b),_P));})));});};if(_w<11){return new F(function(){return _2(_o,new T(function(){return B(_O(_y));},1));});}else{var _Q=new T(function(){return B(_2(_o,new T(function(){return B(_O(new T2(1,_a,_y)));},1)));});return new T2(1,_b,_Q);}break;case 6:return new F(function(){return _2(_n,_y);});break;default:return new F(function(){return _2(_m,_y);});}},_R=new T(function(){return B(unCStr("IdentCC "));}),_S=function(_T,_U,_V){if(_T<11){return new F(function(){return _2(_R,new T(function(){return B(_c(11,E(_U),_V));},1));});}else{var _W=new T(function(){return B(_2(_R,new T(function(){return B(_c(11,E(_U),new T2(1,_a,_V)));},1)));});return new T2(1,_b,_W);}},_X=new T(function(){return B(unCStr("IdentPay "));}),_Y=function(_Z,_10,_11){if(_Z<11){return new F(function(){return _2(_X,new T(function(){return B(_c(11,E(_10),_11));},1));});}else{var _12=new T(function(){return B(_2(_X,new T(function(){return B(_c(11,E(_10),new T2(1,_a,_11)));},1)));});return new T2(1,_b,_12);}},_13=new T(function(){return B(unCStr("Null"));}),_14=new T(function(){return B(unCStr("When "));}),_15=new T(function(){return B(unCStr("CommitCash "));}),_16=new T(function(){return B(unCStr("Choice "));}),_17=new T(function(){return B(unCStr("Both "));}),_18=new T(function(){return B(unCStr("Pay "));}),_19=new T(function(){return B(unCStr("RedeemCC "));}),_1a=function(_1b,_1c,_1d){var _1e=E(_1c);switch(_1e._){case 0:return new F(function(){return _2(_13,_1d);});break;case 1:var _1f=function(_1g){var _1h=new T(function(){return B(_S(11,_1e.a,new T2(1,_u,new T(function(){return B(_1a(11,_1e.b,_1g));}))));},1);return new F(function(){return _2(_19,_1h);});};if(_1b<11){return new F(function(){return _1f(_1d);});}else{return new T2(1,_b,new T(function(){return B(_1f(new T2(1,_a,_1d)));}));}break;case 2:var _1i=function(_1j){var _1k=new T(function(){var _1l=new T(function(){var _1m=new T(function(){var _1n=new T(function(){var _1o=new T(function(){return B(_c(11,E(_1e.e),new T2(1,_u,new T(function(){return B(_1a(11,_1e.f,_1j));}))));});return B(_c(11,E(_1e.d),new T2(1,_u,_1o)));});return B(_c(11,E(_1e.c),new T2(1,_u,_1n)));});return B(_c(11,E(_1e.b),new T2(1,_u,_1m)));});return B(_Y(11,_1e.a,new T2(1,_u,_1l)));},1);return new F(function(){return _2(_18,_1k);});};if(_1b<11){return new F(function(){return _1i(_1d);});}else{return new T2(1,_b,new T(function(){return B(_1i(new T2(1,_a,_1d)));}));}break;case 3:var _1p=function(_1q){var _1r=new T(function(){return B(_1a(11,_1e.a,new T2(1,_u,new T(function(){return B(_1a(11,_1e.b,_1q));}))));},1);return new F(function(){return _2(_17,_1r);});};if(_1b<11){return new F(function(){return _1p(_1d);});}else{return new T2(1,_b,new T(function(){return B(_1p(new T2(1,_a,_1d)));}));}break;case 4:var _1s=function(_1t){var _1u=new T(function(){return B(_1a(11,_1e.b,new T2(1,_u,new T(function(){return B(_1a(11,_1e.c,_1t));}))));});return new F(function(){return _v(11,_1e.a,new T2(1,_u,_1u));});};if(_1b<11){return new F(function(){return _2(_16,new T(function(){return B(_1s(_1d));},1));});}else{var _1v=new T(function(){return B(_2(_16,new T(function(){return B(_1s(new T2(1,_a,_1d)));},1)));});return new T2(1,_b,_1v);}break;case 5:var _1w=function(_1x){var _1y=new T(function(){var _1z=new T(function(){var _1A=new T(function(){var _1B=new T(function(){var _1C=new T(function(){return B(_c(11,E(_1e.e),new T2(1,_u,new T(function(){return B(_1a(11,_1e.f,_1x));}))));});return B(_c(11,E(_1e.d),new T2(1,_u,_1C)));});return B(_c(11,E(_1e.c),new T2(1,_u,_1B)));});return B(_c(11,E(_1e.b),new T2(1,_u,_1A)));});return B(_S(11,_1e.a,new T2(1,_u,_1z)));},1);return new F(function(){return _2(_15,_1y);});};if(_1b<11){return new F(function(){return _1w(_1d);});}else{return new T2(1,_b,new T(function(){return B(_1w(new T2(1,_a,_1d)));}));}break;default:var _1D=function(_1E){var _1F=new T(function(){var _1G=new T(function(){var _1H=new T(function(){return B(_1a(11,_1e.c,new T2(1,_u,new T(function(){return B(_1a(11,_1e.d,_1E));}))));});return B(_c(11,E(_1e.b),new T2(1,_u,_1H)));});return B(_v(11,_1e.a,new T2(1,_u,_1G)));},1);return new F(function(){return _2(_14,_1F);});};if(_1b<11){return new F(function(){return _1D(_1d);});}else{return new T2(1,_b,new T(function(){return B(_1D(new T2(1,_a,_1d)));}));}}},_1I=__Z,_1J=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_1K=new T(function(){return B(err(_1J));}),_1L=new T(function(){return B(unCStr("codeArea"));}),_1M=function(_){return _0;},_1N="(function (t, s) {document.getElementById(t).value = s})",_1O=function(_1P,_1Q,_){var _1R=eval(E(_1N)),_1S=__app2(E(_1R),toJSStr(E(_1P)),toJSStr(E(_1Q)));return new F(function(){return _1M(_);});},_1T=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_1U=new T(function(){return B(err(_1T));}),_1V=new T(function(){return B(unCStr("base"));}),_1W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1X=new T(function(){return B(unCStr("PatternMatchFail"));}),_1Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_1V,_1W,_1X),_1Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_1Y,_1I,_1I),_20=function(_21){return E(_1Z);},_22=function(_23){return E(E(_23).a);},_24=function(_25,_26,_27){var _28=B(A1(_25,_)),_29=B(A1(_26,_)),_2a=hs_eqWord64(_28.a,_29.a);if(!_2a){return __Z;}else{var _2b=hs_eqWord64(_28.b,_29.b);return (!_2b)?__Z:new T1(1,_27);}},_2c=function(_2d){var _2e=E(_2d);return new F(function(){return _24(B(_22(_2e.a)),_20,_2e.b);});},_2f=function(_2g){return E(E(_2g).a);},_2h=function(_2i){return new T2(0,_2j,_2i);},_2k=function(_2l,_2m){return new F(function(){return _2(E(_2l).a,_2m);});},_2n=44,_2o=93,_2p=91,_2q=function(_2r,_2s,_2t){var _2u=E(_2s);if(!_2u._){return new F(function(){return unAppCStr("[]",_2t);});}else{var _2v=new T(function(){var _2w=new T(function(){var _2x=function(_2y){var _2z=E(_2y);if(!_2z._){return E(new T2(1,_2o,_2t));}else{var _2A=new T(function(){return B(A2(_2r,_2z.a,new T(function(){return B(_2x(_2z.b));})));});return new T2(1,_2n,_2A);}};return B(_2x(_2u.b));});return B(A2(_2r,_2u.a,_2w));});return new T2(1,_2p,_2v);}},_2B=function(_2C,_2D){return new F(function(){return _2q(_2k,_2C,_2D);});},_2E=function(_2F,_2G,_2H){return new F(function(){return _2(E(_2G).a,_2H);});},_2I=new T3(0,_2E,_2f,_2B),_2j=new T(function(){return new T5(0,_20,_2I,_2h,_2c,_2f);}),_2J=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_2K=function(_2L){return E(E(_2L).c);},_2M=function(_2N,_2O){return new F(function(){return die(new T(function(){return B(A2(_2K,_2O,_2N));}));});},_2P=function(_2Q,_2R){return new F(function(){return _2M(_2Q,_2R);});},_2S=function(_2T,_2U){var _2V=E(_2U);if(!_2V._){return new T2(0,_1I,_1I);}else{var _2W=_2V.a;if(!B(A1(_2T,_2W))){return new T2(0,_1I,_2V);}else{var _2X=new T(function(){var _2Y=B(_2S(_2T,_2V.b));return new T2(0,_2Y.a,_2Y.b);});return new T2(0,new T2(1,_2W,new T(function(){return E(E(_2X).a);})),new T(function(){return E(E(_2X).b);}));}}},_2Z=32,_30=new T(function(){return B(unCStr("\n"));}),_31=function(_32){return (E(_32)==124)?false:true;},_33=function(_34,_35){var _36=B(_2S(_31,B(unCStr(_34)))),_37=_36.a,_38=function(_39,_3a){var _3b=new T(function(){var _3c=new T(function(){return B(_2(_35,new T(function(){return B(_2(_3a,_30));},1)));});return B(unAppCStr(": ",_3c));},1);return new F(function(){return _2(_39,_3b);});},_3d=E(_36.b);if(!_3d._){return new F(function(){return _38(_37,_1I);});}else{if(E(_3d.a)==124){return new F(function(){return _38(_37,new T2(1,_2Z,_3d.b));});}else{return new F(function(){return _38(_37,_1I);});}}},_3e=function(_3f){return new F(function(){return _2P(new T1(0,new T(function(){return B(_33(_3f,_2J));})),_2j);});},_3g=new T(function(){return B(_3e("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_3h=function(_3i,_3j){while(1){var _3k=B((function(_3l,_3m){var _3n=E(_3l);switch(_3n._){case 0:var _3o=E(_3m);if(!_3o._){return __Z;}else{_3i=B(A1(_3n.a,_3o.a));_3j=_3o.b;return __continue;}break;case 1:var _3p=B(A1(_3n.a,_3m)),_3q=_3m;_3i=_3p;_3j=_3q;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_3n.a,_3m),new T(function(){return B(_3h(_3n.b,_3m));}));default:return E(_3n.a);}})(_3i,_3j));if(_3k!=__continue){return _3k;}}},_3r=function(_3s,_3t){var _3u=function(_3v){var _3w=E(_3t);if(_3w._==3){return new T2(3,_3w.a,new T(function(){return B(_3r(_3s,_3w.b));}));}else{var _3x=E(_3s);if(_3x._==2){return E(_3w);}else{var _3y=E(_3w);if(_3y._==2){return E(_3x);}else{var _3z=function(_3A){var _3B=E(_3y);if(_3B._==4){var _3C=function(_3D){return new T1(4,new T(function(){return B(_2(B(_3h(_3x,_3D)),_3B.a));}));};return new T1(1,_3C);}else{var _3E=E(_3x);if(_3E._==1){var _3F=_3E.a,_3G=E(_3B);if(!_3G._){return new T1(1,function(_3H){return new F(function(){return _3r(B(A1(_3F,_3H)),_3G);});});}else{var _3I=function(_3J){return new F(function(){return _3r(B(A1(_3F,_3J)),new T(function(){return B(A1(_3G.a,_3J));}));});};return new T1(1,_3I);}}else{var _3K=E(_3B);if(!_3K._){return E(_3g);}else{var _3L=function(_3M){return new F(function(){return _3r(_3E,new T(function(){return B(A1(_3K.a,_3M));}));});};return new T1(1,_3L);}}}},_3N=E(_3x);switch(_3N._){case 1:var _3O=E(_3y);if(_3O._==4){var _3P=function(_3Q){return new T1(4,new T(function(){return B(_2(B(_3h(B(A1(_3N.a,_3Q)),_3Q)),_3O.a));}));};return new T1(1,_3P);}else{return new F(function(){return _3z(_);});}break;case 4:var _3R=_3N.a,_3S=E(_3y);switch(_3S._){case 0:var _3T=function(_3U){var _3V=new T(function(){return B(_2(_3R,new T(function(){return B(_3h(_3S,_3U));},1)));});return new T1(4,_3V);};return new T1(1,_3T);case 1:var _3W=function(_3X){var _3Y=new T(function(){return B(_2(_3R,new T(function(){return B(_3h(B(A1(_3S.a,_3X)),_3X));},1)));});return new T1(4,_3Y);};return new T1(1,_3W);default:return new T1(4,new T(function(){return B(_2(_3R,_3S.a));}));}break;default:return new F(function(){return _3z(_);});}}}}},_3Z=E(_3s);switch(_3Z._){case 0:var _40=E(_3t);if(!_40._){var _41=function(_42){return new F(function(){return _3r(B(A1(_3Z.a,_42)),new T(function(){return B(A1(_40.a,_42));}));});};return new T1(0,_41);}else{return new F(function(){return _3u(_);});}break;case 3:return new T2(3,_3Z.a,new T(function(){return B(_3r(_3Z.b,_3t));}));default:return new F(function(){return _3u(_);});}},_43=11,_44=new T(function(){return B(unCStr("IdentCC"));}),_45=new T(function(){return B(unCStr("("));}),_46=new T(function(){return B(unCStr(")"));}),_47=function(_48,_49){while(1){var _4a=E(_48);if(!_4a._){return (E(_49)._==0)?true:false;}else{var _4b=E(_49);if(!_4b._){return false;}else{if(E(_4a.a)!=E(_4b.a)){return false;}else{_48=_4a.b;_49=_4b.b;continue;}}}}},_4c=function(_4d,_4e){return E(_4d)!=E(_4e);},_4f=function(_4g,_4h){return E(_4g)==E(_4h);},_4i=new T2(0,_4f,_4c),_4j=function(_4k,_4l){while(1){var _4m=E(_4k);if(!_4m._){return (E(_4l)._==0)?true:false;}else{var _4n=E(_4l);if(!_4n._){return false;}else{if(E(_4m.a)!=E(_4n.a)){return false;}else{_4k=_4m.b;_4l=_4n.b;continue;}}}}},_4o=function(_4p,_4q){return (!B(_4j(_4p,_4q)))?true:false;},_4r=new T2(0,_4j,_4o),_4s=function(_4t,_4u){var _4v=E(_4t);switch(_4v._){case 0:return new T1(0,function(_4w){return new F(function(){return _4s(B(A1(_4v.a,_4w)),_4u);});});case 1:return new T1(1,function(_4x){return new F(function(){return _4s(B(A1(_4v.a,_4x)),_4u);});});case 2:return new T0(2);case 3:return new F(function(){return _3r(B(A1(_4u,_4v.a)),new T(function(){return B(_4s(_4v.b,_4u));}));});break;default:var _4y=function(_4z){var _4A=E(_4z);if(!_4A._){return __Z;}else{var _4B=E(_4A.a);return new F(function(){return _2(B(_3h(B(A1(_4u,_4B.a)),_4B.b)),new T(function(){return B(_4y(_4A.b));},1));});}},_4C=B(_4y(_4v.a));return (_4C._==0)?new T0(2):new T1(4,_4C);}},_4D=new T0(2),_4E=function(_4F){return new T2(3,_4F,_4D);},_4G=function(_4H,_4I){var _4J=E(_4H);if(!_4J){return new F(function(){return A1(_4I,_0);});}else{var _4K=new T(function(){return B(_4G(_4J-1|0,_4I));});return new T1(0,function(_4L){return E(_4K);});}},_4M=function(_4N,_4O,_4P){var _4Q=new T(function(){return B(A1(_4N,_4E));}),_4R=function(_4S,_4T,_4U,_4V){while(1){var _4W=B((function(_4X,_4Y,_4Z,_50){var _51=E(_4X);switch(_51._){case 0:var _52=E(_4Y);if(!_52._){return new F(function(){return A1(_4O,_50);});}else{var _53=_4Z+1|0,_54=_50;_4S=B(A1(_51.a,_52.a));_4T=_52.b;_4U=_53;_4V=_54;return __continue;}break;case 1:var _55=B(A1(_51.a,_4Y)),_56=_4Y,_53=_4Z,_54=_50;_4S=_55;_4T=_56;_4U=_53;_4V=_54;return __continue;case 2:return new F(function(){return A1(_4O,_50);});break;case 3:var _57=new T(function(){return B(_4s(_51,_50));});return new F(function(){return _4G(_4Z,function(_58){return E(_57);});});break;default:return new F(function(){return _4s(_51,_50);});}})(_4S,_4T,_4U,_4V));if(_4W!=__continue){return _4W;}}};return function(_59){return new F(function(){return _4R(_4Q,_59,0,_4P);});};},_5a=function(_5b){return new F(function(){return A1(_5b,_1I);});},_5c=function(_5d,_5e){var _5f=function(_5g){var _5h=E(_5g);if(!_5h._){return E(_5a);}else{var _5i=_5h.a;if(!B(A1(_5d,_5i))){return E(_5a);}else{var _5j=new T(function(){return B(_5f(_5h.b));}),_5k=function(_5l){var _5m=new T(function(){return B(A1(_5j,function(_5n){return new F(function(){return A1(_5l,new T2(1,_5i,_5n));});}));});return new T1(0,function(_5o){return E(_5m);});};return E(_5k);}}};return function(_5p){return new F(function(){return A2(_5f,_5p,_5e);});};},_5q=new T0(6),_5r=function(_5s){return E(_5s);},_5t=new T(function(){return B(unCStr("valDig: Bad base"));}),_5u=new T(function(){return B(err(_5t));}),_5v=function(_5w,_5x){var _5y=function(_5z,_5A){var _5B=E(_5z);if(!_5B._){var _5C=new T(function(){return B(A1(_5A,_1I));});return function(_5D){return new F(function(){return A1(_5D,_5C);});};}else{var _5E=E(_5B.a),_5F=function(_5G){var _5H=new T(function(){return B(_5y(_5B.b,function(_5I){return new F(function(){return A1(_5A,new T2(1,_5G,_5I));});}));}),_5J=function(_5K){var _5L=new T(function(){return B(A1(_5H,_5K));});return new T1(0,function(_5M){return E(_5L);});};return E(_5J);};switch(E(_5w)){case 8:if(48>_5E){var _5N=new T(function(){return B(A1(_5A,_1I));});return function(_5O){return new F(function(){return A1(_5O,_5N);});};}else{if(_5E>55){var _5P=new T(function(){return B(A1(_5A,_1I));});return function(_5Q){return new F(function(){return A1(_5Q,_5P);});};}else{return new F(function(){return _5F(_5E-48|0);});}}break;case 10:if(48>_5E){var _5R=new T(function(){return B(A1(_5A,_1I));});return function(_5S){return new F(function(){return A1(_5S,_5R);});};}else{if(_5E>57){var _5T=new T(function(){return B(A1(_5A,_1I));});return function(_5U){return new F(function(){return A1(_5U,_5T);});};}else{return new F(function(){return _5F(_5E-48|0);});}}break;case 16:if(48>_5E){if(97>_5E){if(65>_5E){var _5V=new T(function(){return B(A1(_5A,_1I));});return function(_5W){return new F(function(){return A1(_5W,_5V);});};}else{if(_5E>70){var _5X=new T(function(){return B(A1(_5A,_1I));});return function(_5Y){return new F(function(){return A1(_5Y,_5X);});};}else{return new F(function(){return _5F((_5E-65|0)+10|0);});}}}else{if(_5E>102){if(65>_5E){var _5Z=new T(function(){return B(A1(_5A,_1I));});return function(_60){return new F(function(){return A1(_60,_5Z);});};}else{if(_5E>70){var _61=new T(function(){return B(A1(_5A,_1I));});return function(_62){return new F(function(){return A1(_62,_61);});};}else{return new F(function(){return _5F((_5E-65|0)+10|0);});}}}else{return new F(function(){return _5F((_5E-97|0)+10|0);});}}}else{if(_5E>57){if(97>_5E){if(65>_5E){var _63=new T(function(){return B(A1(_5A,_1I));});return function(_64){return new F(function(){return A1(_64,_63);});};}else{if(_5E>70){var _65=new T(function(){return B(A1(_5A,_1I));});return function(_66){return new F(function(){return A1(_66,_65);});};}else{return new F(function(){return _5F((_5E-65|0)+10|0);});}}}else{if(_5E>102){if(65>_5E){var _67=new T(function(){return B(A1(_5A,_1I));});return function(_68){return new F(function(){return A1(_68,_67);});};}else{if(_5E>70){var _69=new T(function(){return B(A1(_5A,_1I));});return function(_6a){return new F(function(){return A1(_6a,_69);});};}else{return new F(function(){return _5F((_5E-65|0)+10|0);});}}}else{return new F(function(){return _5F((_5E-97|0)+10|0);});}}}else{return new F(function(){return _5F(_5E-48|0);});}}break;default:return E(_5u);}}},_6b=function(_6c){var _6d=E(_6c);if(!_6d._){return new T0(2);}else{return new F(function(){return A1(_5x,_6d);});}};return function(_6e){return new F(function(){return A3(_5y,_6e,_5r,_6b);});};},_6f=16,_6g=8,_6h=function(_6i){var _6j=function(_6k){return new F(function(){return A1(_6i,new T1(5,new T2(0,_6g,_6k)));});},_6l=function(_6m){return new F(function(){return A1(_6i,new T1(5,new T2(0,_6f,_6m)));});},_6n=function(_6o){switch(E(_6o)){case 79:return new T1(1,B(_5v(_6g,_6j)));case 88:return new T1(1,B(_5v(_6f,_6l)));case 111:return new T1(1,B(_5v(_6g,_6j)));case 120:return new T1(1,B(_5v(_6f,_6l)));default:return new T0(2);}};return function(_6p){return (E(_6p)==48)?E(new T1(0,_6n)):new T0(2);};},_6q=function(_6r){return new T1(0,B(_6h(_6r)));},_6s=__Z,_6t=function(_6u){return new F(function(){return A1(_6u,_6s);});},_6v=function(_6w){return new F(function(){return A1(_6w,_6s);});},_6x=10,_6y=new T1(0,1),_6z=new T1(0,2147483647),_6A=function(_6B,_6C){while(1){var _6D=E(_6B);if(!_6D._){var _6E=_6D.a,_6F=E(_6C);if(!_6F._){var _6G=_6F.a,_6H=addC(_6E,_6G);if(!E(_6H.b)){return new T1(0,_6H.a);}else{_6B=new T1(1,I_fromInt(_6E));_6C=new T1(1,I_fromInt(_6G));continue;}}else{_6B=new T1(1,I_fromInt(_6E));_6C=_6F;continue;}}else{var _6I=E(_6C);if(!_6I._){_6B=_6D;_6C=new T1(1,I_fromInt(_6I.a));continue;}else{return new T1(1,I_add(_6D.a,_6I.a));}}}},_6J=new T(function(){return B(_6A(_6z,_6y));}),_6K=function(_6L){var _6M=E(_6L);if(!_6M._){var _6N=E(_6M.a);return (_6N==( -2147483648))?E(_6J):new T1(0, -_6N);}else{return new T1(1,I_negate(_6M.a));}},_6O=new T1(0,10),_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){return E(_6R);}else{var _6T=_6R+1|0;_6Q=_6S.b;_6R=_6T;continue;}}},_6U=function(_6V,_6W){var _6X=E(_6W);return (_6X._==0)?__Z:new T2(1,new T(function(){return B(A1(_6V,_6X.a));}),new T(function(){return B(_6U(_6V,_6X.b));}));},_6Y=function(_6Z){return new T1(0,_6Z);},_70=function(_71){return new F(function(){return _6Y(E(_71));});},_72=new T(function(){return B(unCStr("this should not happen"));}),_73=new T(function(){return B(err(_72));}),_74=function(_75,_76){while(1){var _77=E(_75);if(!_77._){var _78=_77.a,_79=E(_76);if(!_79._){var _7a=_79.a;if(!(imul(_78,_7a)|0)){return new T1(0,imul(_78,_7a)|0);}else{_75=new T1(1,I_fromInt(_78));_76=new T1(1,I_fromInt(_7a));continue;}}else{_75=new T1(1,I_fromInt(_78));_76=_79;continue;}}else{var _7b=E(_76);if(!_7b._){_75=_77;_76=new T1(1,I_fromInt(_7b.a));continue;}else{return new T1(1,I_mul(_77.a,_7b.a));}}}},_7c=function(_7d,_7e){var _7f=E(_7e);if(!_7f._){return __Z;}else{var _7g=E(_7f.b);return (_7g._==0)?E(_73):new T2(1,B(_6A(B(_74(_7f.a,_7d)),_7g.a)),new T(function(){return B(_7c(_7d,_7g.b));}));}},_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){while(1){var _7m=B((function(_7n,_7o,_7p){var _7q=E(_7p);if(!_7q._){return E(_7h);}else{if(!E(_7q.b)._){return E(_7q.a);}else{var _7r=E(_7o);if(_7r<=40){var _7s=function(_7t,_7u){while(1){var _7v=E(_7u);if(!_7v._){return E(_7t);}else{var _7w=B(_6A(B(_74(_7t,_7n)),_7v.a));_7t=_7w;_7u=_7v.b;continue;}}};return new F(function(){return _7s(_7h,_7q);});}else{var _7x=B(_74(_7n,_7n));if(!(_7r%2)){var _7y=B(_7c(_7n,_7q));_7j=_7x;_7k=quot(_7r+1|0,2);_7l=_7y;return __continue;}else{var _7y=B(_7c(_7n,new T2(1,_7h,_7q)));_7j=_7x;_7k=quot(_7r+1|0,2);_7l=_7y;return __continue;}}}}})(_7j,_7k,_7l));if(_7m!=__continue){return _7m;}}},_7z=function(_7A,_7B){return new F(function(){return _7i(_7A,new T(function(){return B(_6P(_7B,0));},1),B(_6U(_70,_7B)));});},_7C=function(_7D){var _7E=new T(function(){var _7F=new T(function(){var _7G=function(_7H){return new F(function(){return A1(_7D,new T1(1,new T(function(){return B(_7z(_6O,_7H));})));});};return new T1(1,B(_5v(_6x,_7G)));}),_7I=function(_7J){if(E(_7J)==43){var _7K=function(_7L){return new F(function(){return A1(_7D,new T1(1,new T(function(){return B(_7z(_6O,_7L));})));});};return new T1(1,B(_5v(_6x,_7K)));}else{return new T0(2);}},_7M=function(_7N){if(E(_7N)==45){var _7O=function(_7P){return new F(function(){return A1(_7D,new T1(1,new T(function(){return B(_6K(B(_7z(_6O,_7P))));})));});};return new T1(1,B(_5v(_6x,_7O)));}else{return new T0(2);}};return B(_3r(B(_3r(new T1(0,_7M),new T1(0,_7I))),_7F));});return new F(function(){return _3r(new T1(0,function(_7Q){return (E(_7Q)==101)?E(_7E):new T0(2);}),new T1(0,function(_7R){return (E(_7R)==69)?E(_7E):new T0(2);}));});},_7S=function(_7T){var _7U=function(_7V){return new F(function(){return A1(_7T,new T1(1,_7V));});};return function(_7W){return (E(_7W)==46)?new T1(1,B(_5v(_6x,_7U))):new T0(2);};},_7X=function(_7Y){return new T1(0,B(_7S(_7Y)));},_7Z=function(_80){var _81=function(_82){var _83=function(_84){return new T1(1,B(_4M(_7C,_6t,function(_85){return new F(function(){return A1(_80,new T1(5,new T3(1,_82,_84,_85)));});})));};return new T1(1,B(_4M(_7X,_6v,_83)));};return new F(function(){return _5v(_6x,_81);});},_86=function(_87){return new T1(1,B(_7Z(_87)));},_88=function(_89){return E(E(_89).a);},_8a=function(_8b,_8c,_8d){while(1){var _8e=E(_8d);if(!_8e._){return false;}else{if(!B(A3(_88,_8b,_8c,_8e.a))){_8d=_8e.b;continue;}else{return true;}}}},_8f=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_8g=function(_8h){return new F(function(){return _8a(_4i,_8h,_8f);});},_8i=false,_8j=true,_8k=function(_8l){var _8m=new T(function(){return B(A1(_8l,_6g));}),_8n=new T(function(){return B(A1(_8l,_6f));});return function(_8o){switch(E(_8o)){case 79:return E(_8m);case 88:return E(_8n);case 111:return E(_8m);case 120:return E(_8n);default:return new T0(2);}};},_8p=function(_8q){return new T1(0,B(_8k(_8q)));},_8r=function(_8s){return new F(function(){return A1(_8s,_6x);});},_8t=function(_8u){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_c(9,_8u,_1I));}))));});},_8v=function(_8w){var _8x=E(_8w);if(!_8x._){return E(_8x.a);}else{return new F(function(){return I_toInt(_8x.a);});}},_8y=function(_8z,_8A){var _8B=E(_8z);if(!_8B._){var _8C=_8B.a,_8D=E(_8A);return (_8D._==0)?_8C<=_8D.a:I_compareInt(_8D.a,_8C)>=0;}else{var _8E=_8B.a,_8F=E(_8A);return (_8F._==0)?I_compareInt(_8E,_8F.a)<=0:I_compare(_8E,_8F.a)<=0;}},_8G=function(_8H){return new T0(2);},_8I=function(_8J){var _8K=E(_8J);if(!_8K._){return E(_8G);}else{var _8L=_8K.a,_8M=E(_8K.b);if(!_8M._){return E(_8L);}else{var _8N=new T(function(){return B(_8I(_8M));}),_8O=function(_8P){return new F(function(){return _3r(B(A1(_8L,_8P)),new T(function(){return B(A1(_8N,_8P));}));});};return E(_8O);}}},_8Q=function(_8R,_8S){var _8T=function(_8U,_8V,_8W){var _8X=E(_8U);if(!_8X._){return new F(function(){return A1(_8W,_8R);});}else{var _8Y=E(_8V);if(!_8Y._){return new T0(2);}else{if(E(_8X.a)!=E(_8Y.a)){return new T0(2);}else{var _8Z=new T(function(){return B(_8T(_8X.b,_8Y.b,_8W));});return new T1(0,function(_90){return E(_8Z);});}}}};return function(_91){return new F(function(){return _8T(_8R,_91,_8S);});};},_92=new T(function(){return B(unCStr("SO"));}),_93=14,_94=function(_95){var _96=new T(function(){return B(A1(_95,_93));});return new T1(1,B(_8Q(_92,function(_97){return E(_96);})));},_98=new T(function(){return B(unCStr("SOH"));}),_99=1,_9a=function(_9b){var _9c=new T(function(){return B(A1(_9b,_99));});return new T1(1,B(_8Q(_98,function(_9d){return E(_9c);})));},_9e=function(_9f){return new T1(1,B(_4M(_9a,_94,_9f)));},_9g=new T(function(){return B(unCStr("NUL"));}),_9h=0,_9i=function(_9j){var _9k=new T(function(){return B(A1(_9j,_9h));});return new T1(1,B(_8Q(_9g,function(_9l){return E(_9k);})));},_9m=new T(function(){return B(unCStr("STX"));}),_9n=2,_9o=function(_9p){var _9q=new T(function(){return B(A1(_9p,_9n));});return new T1(1,B(_8Q(_9m,function(_9r){return E(_9q);})));},_9s=new T(function(){return B(unCStr("ETX"));}),_9t=3,_9u=function(_9v){var _9w=new T(function(){return B(A1(_9v,_9t));});return new T1(1,B(_8Q(_9s,function(_9x){return E(_9w);})));},_9y=new T(function(){return B(unCStr("EOT"));}),_9z=4,_9A=function(_9B){var _9C=new T(function(){return B(A1(_9B,_9z));});return new T1(1,B(_8Q(_9y,function(_9D){return E(_9C);})));},_9E=new T(function(){return B(unCStr("ENQ"));}),_9F=5,_9G=function(_9H){var _9I=new T(function(){return B(A1(_9H,_9F));});return new T1(1,B(_8Q(_9E,function(_9J){return E(_9I);})));},_9K=new T(function(){return B(unCStr("ACK"));}),_9L=6,_9M=function(_9N){var _9O=new T(function(){return B(A1(_9N,_9L));});return new T1(1,B(_8Q(_9K,function(_9P){return E(_9O);})));},_9Q=new T(function(){return B(unCStr("BEL"));}),_9R=7,_9S=function(_9T){var _9U=new T(function(){return B(A1(_9T,_9R));});return new T1(1,B(_8Q(_9Q,function(_9V){return E(_9U);})));},_9W=new T(function(){return B(unCStr("BS"));}),_9X=8,_9Y=function(_9Z){var _a0=new T(function(){return B(A1(_9Z,_9X));});return new T1(1,B(_8Q(_9W,function(_a1){return E(_a0);})));},_a2=new T(function(){return B(unCStr("HT"));}),_a3=9,_a4=function(_a5){var _a6=new T(function(){return B(A1(_a5,_a3));});return new T1(1,B(_8Q(_a2,function(_a7){return E(_a6);})));},_a8=new T(function(){return B(unCStr("LF"));}),_a9=10,_aa=function(_ab){var _ac=new T(function(){return B(A1(_ab,_a9));});return new T1(1,B(_8Q(_a8,function(_ad){return E(_ac);})));},_ae=new T(function(){return B(unCStr("VT"));}),_af=11,_ag=function(_ah){var _ai=new T(function(){return B(A1(_ah,_af));});return new T1(1,B(_8Q(_ae,function(_aj){return E(_ai);})));},_ak=new T(function(){return B(unCStr("FF"));}),_al=12,_am=function(_an){var _ao=new T(function(){return B(A1(_an,_al));});return new T1(1,B(_8Q(_ak,function(_ap){return E(_ao);})));},_aq=new T(function(){return B(unCStr("CR"));}),_ar=13,_as=function(_at){var _au=new T(function(){return B(A1(_at,_ar));});return new T1(1,B(_8Q(_aq,function(_av){return E(_au);})));},_aw=new T(function(){return B(unCStr("SI"));}),_ax=15,_ay=function(_az){var _aA=new T(function(){return B(A1(_az,_ax));});return new T1(1,B(_8Q(_aw,function(_aB){return E(_aA);})));},_aC=new T(function(){return B(unCStr("DLE"));}),_aD=16,_aE=function(_aF){var _aG=new T(function(){return B(A1(_aF,_aD));});return new T1(1,B(_8Q(_aC,function(_aH){return E(_aG);})));},_aI=new T(function(){return B(unCStr("DC1"));}),_aJ=17,_aK=function(_aL){var _aM=new T(function(){return B(A1(_aL,_aJ));});return new T1(1,B(_8Q(_aI,function(_aN){return E(_aM);})));},_aO=new T(function(){return B(unCStr("DC2"));}),_aP=18,_aQ=function(_aR){var _aS=new T(function(){return B(A1(_aR,_aP));});return new T1(1,B(_8Q(_aO,function(_aT){return E(_aS);})));},_aU=new T(function(){return B(unCStr("DC3"));}),_aV=19,_aW=function(_aX){var _aY=new T(function(){return B(A1(_aX,_aV));});return new T1(1,B(_8Q(_aU,function(_aZ){return E(_aY);})));},_b0=new T(function(){return B(unCStr("DC4"));}),_b1=20,_b2=function(_b3){var _b4=new T(function(){return B(A1(_b3,_b1));});return new T1(1,B(_8Q(_b0,function(_b5){return E(_b4);})));},_b6=new T(function(){return B(unCStr("NAK"));}),_b7=21,_b8=function(_b9){var _ba=new T(function(){return B(A1(_b9,_b7));});return new T1(1,B(_8Q(_b6,function(_bb){return E(_ba);})));},_bc=new T(function(){return B(unCStr("SYN"));}),_bd=22,_be=function(_bf){var _bg=new T(function(){return B(A1(_bf,_bd));});return new T1(1,B(_8Q(_bc,function(_bh){return E(_bg);})));},_bi=new T(function(){return B(unCStr("ETB"));}),_bj=23,_bk=function(_bl){var _bm=new T(function(){return B(A1(_bl,_bj));});return new T1(1,B(_8Q(_bi,function(_bn){return E(_bm);})));},_bo=new T(function(){return B(unCStr("CAN"));}),_bp=24,_bq=function(_br){var _bs=new T(function(){return B(A1(_br,_bp));});return new T1(1,B(_8Q(_bo,function(_bt){return E(_bs);})));},_bu=new T(function(){return B(unCStr("EM"));}),_bv=25,_bw=function(_bx){var _by=new T(function(){return B(A1(_bx,_bv));});return new T1(1,B(_8Q(_bu,function(_bz){return E(_by);})));},_bA=new T(function(){return B(unCStr("SUB"));}),_bB=26,_bC=function(_bD){var _bE=new T(function(){return B(A1(_bD,_bB));});return new T1(1,B(_8Q(_bA,function(_bF){return E(_bE);})));},_bG=new T(function(){return B(unCStr("ESC"));}),_bH=27,_bI=function(_bJ){var _bK=new T(function(){return B(A1(_bJ,_bH));});return new T1(1,B(_8Q(_bG,function(_bL){return E(_bK);})));},_bM=new T(function(){return B(unCStr("FS"));}),_bN=28,_bO=function(_bP){var _bQ=new T(function(){return B(A1(_bP,_bN));});return new T1(1,B(_8Q(_bM,function(_bR){return E(_bQ);})));},_bS=new T(function(){return B(unCStr("GS"));}),_bT=29,_bU=function(_bV){var _bW=new T(function(){return B(A1(_bV,_bT));});return new T1(1,B(_8Q(_bS,function(_bX){return E(_bW);})));},_bY=new T(function(){return B(unCStr("RS"));}),_bZ=30,_c0=function(_c1){var _c2=new T(function(){return B(A1(_c1,_bZ));});return new T1(1,B(_8Q(_bY,function(_c3){return E(_c2);})));},_c4=new T(function(){return B(unCStr("US"));}),_c5=31,_c6=function(_c7){var _c8=new T(function(){return B(A1(_c7,_c5));});return new T1(1,B(_8Q(_c4,function(_c9){return E(_c8);})));},_ca=new T(function(){return B(unCStr("SP"));}),_cb=32,_cc=function(_cd){var _ce=new T(function(){return B(A1(_cd,_cb));});return new T1(1,B(_8Q(_ca,function(_cf){return E(_ce);})));},_cg=new T(function(){return B(unCStr("DEL"));}),_ch=127,_ci=function(_cj){var _ck=new T(function(){return B(A1(_cj,_ch));});return new T1(1,B(_8Q(_cg,function(_cl){return E(_ck);})));},_cm=new T2(1,_ci,_1I),_cn=new T2(1,_cc,_cm),_co=new T2(1,_c6,_cn),_cp=new T2(1,_c0,_co),_cq=new T2(1,_bU,_cp),_cr=new T2(1,_bO,_cq),_cs=new T2(1,_bI,_cr),_ct=new T2(1,_bC,_cs),_cu=new T2(1,_bw,_ct),_cv=new T2(1,_bq,_cu),_cw=new T2(1,_bk,_cv),_cx=new T2(1,_be,_cw),_cy=new T2(1,_b8,_cx),_cz=new T2(1,_b2,_cy),_cA=new T2(1,_aW,_cz),_cB=new T2(1,_aQ,_cA),_cC=new T2(1,_aK,_cB),_cD=new T2(1,_aE,_cC),_cE=new T2(1,_ay,_cD),_cF=new T2(1,_as,_cE),_cG=new T2(1,_am,_cF),_cH=new T2(1,_ag,_cG),_cI=new T2(1,_aa,_cH),_cJ=new T2(1,_a4,_cI),_cK=new T2(1,_9Y,_cJ),_cL=new T2(1,_9S,_cK),_cM=new T2(1,_9M,_cL),_cN=new T2(1,_9G,_cM),_cO=new T2(1,_9A,_cN),_cP=new T2(1,_9u,_cO),_cQ=new T2(1,_9o,_cP),_cR=new T2(1,_9i,_cQ),_cS=new T2(1,_9e,_cR),_cT=new T(function(){return B(_8I(_cS));}),_cU=34,_cV=new T1(0,1114111),_cW=92,_cX=39,_cY=function(_cZ){var _d0=new T(function(){return B(A1(_cZ,_9R));}),_d1=new T(function(){return B(A1(_cZ,_9X));}),_d2=new T(function(){return B(A1(_cZ,_a3));}),_d3=new T(function(){return B(A1(_cZ,_a9));}),_d4=new T(function(){return B(A1(_cZ,_af));}),_d5=new T(function(){return B(A1(_cZ,_al));}),_d6=new T(function(){return B(A1(_cZ,_ar));}),_d7=new T(function(){return B(A1(_cZ,_cW));}),_d8=new T(function(){return B(A1(_cZ,_cX));}),_d9=new T(function(){return B(A1(_cZ,_cU));}),_da=new T(function(){var _db=function(_dc){var _dd=new T(function(){return B(_6Y(E(_dc)));}),_de=function(_df){var _dg=B(_7z(_dd,_df));if(!B(_8y(_dg,_cV))){return new T0(2);}else{return new F(function(){return A1(_cZ,new T(function(){var _dh=B(_8v(_dg));if(_dh>>>0>1114111){return B(_8t(_dh));}else{return _dh;}}));});}};return new T1(1,B(_5v(_dc,_de)));},_di=new T(function(){var _dj=new T(function(){return B(A1(_cZ,_c5));}),_dk=new T(function(){return B(A1(_cZ,_bZ));}),_dl=new T(function(){return B(A1(_cZ,_bT));}),_dm=new T(function(){return B(A1(_cZ,_bN));}),_dn=new T(function(){return B(A1(_cZ,_bH));}),_do=new T(function(){return B(A1(_cZ,_bB));}),_dp=new T(function(){return B(A1(_cZ,_bv));}),_dq=new T(function(){return B(A1(_cZ,_bp));}),_dr=new T(function(){return B(A1(_cZ,_bj));}),_ds=new T(function(){return B(A1(_cZ,_bd));}),_dt=new T(function(){return B(A1(_cZ,_b7));}),_du=new T(function(){return B(A1(_cZ,_b1));}),_dv=new T(function(){return B(A1(_cZ,_aV));}),_dw=new T(function(){return B(A1(_cZ,_aP));}),_dx=new T(function(){return B(A1(_cZ,_aJ));}),_dy=new T(function(){return B(A1(_cZ,_aD));}),_dz=new T(function(){return B(A1(_cZ,_ax));}),_dA=new T(function(){return B(A1(_cZ,_93));}),_dB=new T(function(){return B(A1(_cZ,_9L));}),_dC=new T(function(){return B(A1(_cZ,_9F));}),_dD=new T(function(){return B(A1(_cZ,_9z));}),_dE=new T(function(){return B(A1(_cZ,_9t));}),_dF=new T(function(){return B(A1(_cZ,_9n));}),_dG=new T(function(){return B(A1(_cZ,_99));}),_dH=new T(function(){return B(A1(_cZ,_9h));}),_dI=function(_dJ){switch(E(_dJ)){case 64:return E(_dH);case 65:return E(_dG);case 66:return E(_dF);case 67:return E(_dE);case 68:return E(_dD);case 69:return E(_dC);case 70:return E(_dB);case 71:return E(_d0);case 72:return E(_d1);case 73:return E(_d2);case 74:return E(_d3);case 75:return E(_d4);case 76:return E(_d5);case 77:return E(_d6);case 78:return E(_dA);case 79:return E(_dz);case 80:return E(_dy);case 81:return E(_dx);case 82:return E(_dw);case 83:return E(_dv);case 84:return E(_du);case 85:return E(_dt);case 86:return E(_ds);case 87:return E(_dr);case 88:return E(_dq);case 89:return E(_dp);case 90:return E(_do);case 91:return E(_dn);case 92:return E(_dm);case 93:return E(_dl);case 94:return E(_dk);case 95:return E(_dj);default:return new T0(2);}};return B(_3r(new T1(0,function(_dK){return (E(_dK)==94)?E(new T1(0,_dI)):new T0(2);}),new T(function(){return B(A1(_cT,_cZ));})));});return B(_3r(new T1(1,B(_4M(_8p,_8r,_db))),_di));});return new F(function(){return _3r(new T1(0,function(_dL){switch(E(_dL)){case 34:return E(_d9);case 39:return E(_d8);case 92:return E(_d7);case 97:return E(_d0);case 98:return E(_d1);case 102:return E(_d5);case 110:return E(_d3);case 114:return E(_d6);case 116:return E(_d2);case 118:return E(_d4);default:return new T0(2);}}),_da);});},_dM=function(_dN){return new F(function(){return A1(_dN,_0);});},_dO=function(_dP){var _dQ=E(_dP);if(!_dQ._){return E(_dM);}else{var _dR=E(_dQ.a),_dS=_dR>>>0,_dT=new T(function(){return B(_dO(_dQ.b));});if(_dS>887){var _dU=u_iswspace(_dR);if(!E(_dU)){return E(_dM);}else{var _dV=function(_dW){var _dX=new T(function(){return B(A1(_dT,_dW));});return new T1(0,function(_dY){return E(_dX);});};return E(_dV);}}else{var _dZ=E(_dS);if(_dZ==32){var _e0=function(_e1){var _e2=new T(function(){return B(A1(_dT,_e1));});return new T1(0,function(_e3){return E(_e2);});};return E(_e0);}else{if(_dZ-9>>>0>4){if(E(_dZ)==160){var _e4=function(_e5){var _e6=new T(function(){return B(A1(_dT,_e5));});return new T1(0,function(_e7){return E(_e6);});};return E(_e4);}else{return E(_dM);}}else{var _e8=function(_e9){var _ea=new T(function(){return B(A1(_dT,_e9));});return new T1(0,function(_eb){return E(_ea);});};return E(_e8);}}}}},_ec=function(_ed){var _ee=new T(function(){return B(_ec(_ed));}),_ef=function(_eg){return (E(_eg)==92)?E(_ee):new T0(2);},_eh=function(_ei){return E(new T1(0,_ef));},_ej=new T1(1,function(_ek){return new F(function(){return A2(_dO,_ek,_eh);});}),_el=new T(function(){return B(_cY(function(_em){return new F(function(){return A1(_ed,new T2(0,_em,_8j));});}));}),_en=function(_eo){var _ep=E(_eo);if(_ep==38){return E(_ee);}else{var _eq=_ep>>>0;if(_eq>887){var _er=u_iswspace(_ep);return (E(_er)==0)?new T0(2):E(_ej);}else{var _es=E(_eq);return (_es==32)?E(_ej):(_es-9>>>0>4)?(E(_es)==160)?E(_ej):new T0(2):E(_ej);}}};return new F(function(){return _3r(new T1(0,function(_et){return (E(_et)==92)?E(new T1(0,_en)):new T0(2);}),new T1(0,function(_eu){var _ev=E(_eu);if(E(_ev)==92){return E(_el);}else{return new F(function(){return A1(_ed,new T2(0,_ev,_8i));});}}));});},_ew=function(_ex,_ey){var _ez=new T(function(){return B(A1(_ey,new T1(1,new T(function(){return B(A1(_ex,_1I));}))));}),_eA=function(_eB){var _eC=E(_eB),_eD=E(_eC.a);if(E(_eD)==34){if(!E(_eC.b)){return E(_ez);}else{return new F(function(){return _ew(function(_eE){return new F(function(){return A1(_ex,new T2(1,_eD,_eE));});},_ey);});}}else{return new F(function(){return _ew(function(_eF){return new F(function(){return A1(_ex,new T2(1,_eD,_eF));});},_ey);});}};return new F(function(){return _ec(_eA);});},_eG=new T(function(){return B(unCStr("_\'"));}),_eH=function(_eI){var _eJ=u_iswalnum(_eI);if(!E(_eJ)){return new F(function(){return _8a(_4i,_eI,_eG);});}else{return true;}},_eK=function(_eL){return new F(function(){return _eH(E(_eL));});},_eM=new T(function(){return B(unCStr(",;()[]{}`"));}),_eN=new T(function(){return B(unCStr("=>"));}),_eO=new T2(1,_eN,_1I),_eP=new T(function(){return B(unCStr("~"));}),_eQ=new T2(1,_eP,_eO),_eR=new T(function(){return B(unCStr("@"));}),_eS=new T2(1,_eR,_eQ),_eT=new T(function(){return B(unCStr("->"));}),_eU=new T2(1,_eT,_eS),_eV=new T(function(){return B(unCStr("<-"));}),_eW=new T2(1,_eV,_eU),_eX=new T(function(){return B(unCStr("|"));}),_eY=new T2(1,_eX,_eW),_eZ=new T(function(){return B(unCStr("\\"));}),_f0=new T2(1,_eZ,_eY),_f1=new T(function(){return B(unCStr("="));}),_f2=new T2(1,_f1,_f0),_f3=new T(function(){return B(unCStr("::"));}),_f4=new T2(1,_f3,_f2),_f5=new T(function(){return B(unCStr(".."));}),_f6=new T2(1,_f5,_f4),_f7=function(_f8){var _f9=new T(function(){return B(A1(_f8,_5q));}),_fa=new T(function(){var _fb=new T(function(){var _fc=function(_fd){var _fe=new T(function(){return B(A1(_f8,new T1(0,_fd)));});return new T1(0,function(_ff){return (E(_ff)==39)?E(_fe):new T0(2);});};return B(_cY(_fc));}),_fg=function(_fh){var _fi=E(_fh);switch(E(_fi)){case 39:return new T0(2);case 92:return E(_fb);default:var _fj=new T(function(){return B(A1(_f8,new T1(0,_fi)));});return new T1(0,function(_fk){return (E(_fk)==39)?E(_fj):new T0(2);});}},_fl=new T(function(){var _fm=new T(function(){return B(_ew(_5r,_f8));}),_fn=new T(function(){var _fo=new T(function(){var _fp=new T(function(){var _fq=function(_fr){var _fs=E(_fr),_ft=u_iswalpha(_fs);return (E(_ft)==0)?(E(_fs)==95)?new T1(1,B(_5c(_eK,function(_fu){return new F(function(){return A1(_f8,new T1(3,new T2(1,_fs,_fu)));});}))):new T0(2):new T1(1,B(_5c(_eK,function(_fv){return new F(function(){return A1(_f8,new T1(3,new T2(1,_fs,_fv)));});})));};return B(_3r(new T1(0,_fq),new T(function(){return new T1(1,B(_4M(_6q,_86,_f8)));})));}),_fw=function(_fx){return (!B(_8a(_4i,_fx,_8f)))?new T0(2):new T1(1,B(_5c(_8g,function(_fy){var _fz=new T2(1,_fx,_fy);if(!B(_8a(_4r,_fz,_f6))){return new F(function(){return A1(_f8,new T1(4,_fz));});}else{return new F(function(){return A1(_f8,new T1(2,_fz));});}})));};return B(_3r(new T1(0,_fw),_fp));});return B(_3r(new T1(0,function(_fA){if(!B(_8a(_4i,_fA,_eM))){return new T0(2);}else{return new F(function(){return A1(_f8,new T1(2,new T2(1,_fA,_1I)));});}}),_fo));});return B(_3r(new T1(0,function(_fB){return (E(_fB)==34)?E(_fm):new T0(2);}),_fn));});return B(_3r(new T1(0,function(_fC){return (E(_fC)==39)?E(new T1(0,_fg)):new T0(2);}),_fl));});return new F(function(){return _3r(new T1(1,function(_fD){return (E(_fD)._==0)?E(_f9):new T0(2);}),_fa);});},_fE=0,_fF=function(_fG,_fH){var _fI=new T(function(){var _fJ=new T(function(){var _fK=function(_fL){var _fM=new T(function(){var _fN=new T(function(){return B(A1(_fH,_fL));});return B(_f7(function(_fO){var _fP=E(_fO);return (_fP._==2)?(!B(_47(_fP.a,_46)))?new T0(2):E(_fN):new T0(2);}));}),_fQ=function(_fR){return E(_fM);};return new T1(1,function(_fS){return new F(function(){return A2(_dO,_fS,_fQ);});});};return B(A2(_fG,_fE,_fK));});return B(_f7(function(_fT){var _fU=E(_fT);return (_fU._==2)?(!B(_47(_fU.a,_45)))?new T0(2):E(_fJ):new T0(2);}));}),_fV=function(_fW){return E(_fI);};return function(_fX){return new F(function(){return A2(_dO,_fX,_fV);});};},_fY=function(_fZ,_g0){var _g1=function(_g2){var _g3=new T(function(){return B(A1(_fZ,_g2));}),_g4=function(_g5){return new F(function(){return _3r(B(A1(_g3,_g5)),new T(function(){return new T1(1,B(_fF(_g1,_g5)));}));});};return E(_g4);},_g6=new T(function(){return B(A1(_fZ,_g0));}),_g7=function(_g8){return new F(function(){return _3r(B(A1(_g6,_g8)),new T(function(){return new T1(1,B(_fF(_g1,_g8)));}));});};return E(_g7);},_g9=function(_ga,_gb){var _gc=function(_gd,_ge){var _gf=function(_gg){return new F(function(){return A1(_ge,new T(function(){return  -E(_gg);}));});},_gh=new T(function(){return B(_f7(function(_gi){return new F(function(){return A3(_ga,_gi,_gd,_gf);});}));}),_gj=function(_gk){return E(_gh);},_gl=function(_gm){return new F(function(){return A2(_dO,_gm,_gj);});},_gn=new T(function(){return B(_f7(function(_go){var _gp=E(_go);if(_gp._==4){var _gq=E(_gp.a);if(!_gq._){return new F(function(){return A3(_ga,_gp,_gd,_ge);});}else{if(E(_gq.a)==45){if(!E(_gq.b)._){return E(new T1(1,_gl));}else{return new F(function(){return A3(_ga,_gp,_gd,_ge);});}}else{return new F(function(){return A3(_ga,_gp,_gd,_ge);});}}}else{return new F(function(){return A3(_ga,_gp,_gd,_ge);});}}));}),_gr=function(_gs){return E(_gn);};return new T1(1,function(_gt){return new F(function(){return A2(_dO,_gt,_gr);});});};return new F(function(){return _fY(_gc,_gb);});},_gu=function(_gv){var _gw=E(_gv);if(!_gw._){var _gx=_gw.b,_gy=new T(function(){return B(_7i(new T(function(){return B(_6Y(E(_gw.a)));}),new T(function(){return B(_6P(_gx,0));},1),B(_6U(_70,_gx))));});return new T1(1,_gy);}else{return (E(_gw.b)._==0)?(E(_gw.c)._==0)?new T1(1,new T(function(){return B(_7z(_6O,_gw.a));})):__Z:__Z;}},_gz=function(_gA,_gB){return new T0(2);},_gC=function(_gD){var _gE=E(_gD);if(_gE._==5){var _gF=B(_gu(_gE.a));if(!_gF._){return E(_gz);}else{var _gG=new T(function(){return B(_8v(_gF.a));});return function(_gH,_gI){return new F(function(){return A1(_gI,_gG);});};}}else{return E(_gz);}},_gJ=function(_gK,_gL){if(_gK>10){return new T0(2);}else{var _gM=new T(function(){var _gN=new T(function(){return B(A3(_g9,_gC,_43,function(_gO){return new F(function(){return A1(_gL,_gO);});}));});return B(_f7(function(_gP){var _gQ=E(_gP);return (_gQ._==3)?(!B(_47(_gQ.a,_44)))?new T0(2):E(_gN):new T0(2);}));}),_gR=function(_gS){return E(_gM);};return new T1(1,function(_gT){return new F(function(){return A2(_dO,_gT,_gR);});});}},_gU=function(_gV,_gW){return new F(function(){return _gJ(E(_gV),_gW);});},_gX=new T(function(){return B(unCStr("IdentPay"));}),_gY=function(_gZ,_h0){if(_gZ>10){return new T0(2);}else{var _h1=new T(function(){var _h2=new T(function(){return B(A3(_g9,_gC,_43,function(_h3){return new F(function(){return A1(_h0,_h3);});}));});return B(_f7(function(_h4){var _h5=E(_h4);return (_h5._==3)?(!B(_47(_h5.a,_gX)))?new T0(2):E(_h2):new T0(2);}));}),_h6=function(_h7){return E(_h1);};return new T1(1,function(_h8){return new F(function(){return A2(_dO,_h8,_h6);});});}},_h9=function(_ha,_hb){return new F(function(){return _gY(E(_ha),_hb);});},_hc=new T(function(){return B(unCStr("IdentChoice"));}),_hd=function(_he,_hf){if(_he>10){return new T0(2);}else{var _hg=new T(function(){var _hh=new T(function(){return B(A3(_g9,_gC,_43,function(_hi){return new F(function(){return A1(_hf,_hi);});}));});return B(_f7(function(_hj){var _hk=E(_hj);return (_hk._==3)?(!B(_47(_hk.a,_hc)))?new T0(2):E(_hh):new T0(2);}));}),_hl=function(_hm){return E(_hg);};return new T1(1,function(_hn){return new F(function(){return A2(_dO,_hn,_hl);});});}},_ho=function(_hp,_hq){return new F(function(){return _hd(E(_hp),_hq);});},_hr=new T0(6),_hs=function(_ht,_hu){return new F(function(){return A1(_hu,_hr);});},_hv=new T2(0,_n,_hs),_hw=new T0(7),_hx=function(_hy,_hz){return new F(function(){return A1(_hz,_hw);});},_hA=new T2(0,_m,_hx),_hB=new T2(1,_hA,_1I),_hC=new T2(1,_hv,_hB),_hD=function(_hE,_hF,_hG){var _hH=E(_hE);if(!_hH._){return new T0(2);}else{var _hI=E(_hH.a),_hJ=_hI.a,_hK=new T(function(){return B(A2(_hI.b,_hF,_hG));}),_hL=new T(function(){return B(_f7(function(_hM){var _hN=E(_hM);switch(_hN._){case 3:return (!B(_47(_hJ,_hN.a)))?new T0(2):E(_hK);case 4:return (!B(_47(_hJ,_hN.a)))?new T0(2):E(_hK);default:return new T0(2);}}));}),_hO=function(_hP){return E(_hL);};return new F(function(){return _3r(new T1(1,function(_hQ){return new F(function(){return A2(_dO,_hQ,_hO);});}),new T(function(){return B(_hD(_hH.b,_hF,_hG));}));});}},_hR=new T(function(){return B(unCStr("PersonChoseSomething"));}),_hS=new T(function(){return B(unCStr("PersonChoseThis"));}),_hT=new T(function(){return B(unCStr("BelowTimeout"));}),_hU=new T(function(){return B(unCStr("AndObs"));}),_hV=new T(function(){return B(unCStr("OrObs"));}),_hW=new T(function(){return B(unCStr("NotObs"));}),_hX=function(_hY,_hZ){var _i0=new T(function(){var _i1=E(_hY),_i2=new T(function(){var _i3=new T(function(){var _i4=new T(function(){var _i5=new T(function(){var _i6=new T(function(){if(_i1>10){return new T0(2);}else{var _i7=new T(function(){var _i8=new T(function(){var _i9=function(_ia){return new F(function(){return A3(_g9,_gC,_43,function(_ib){return new F(function(){return A1(_hZ,new T2(5,_ia,_ib));});});});};return B(A3(_fY,_ho,_43,_i9));});return B(_f7(function(_ic){var _id=E(_ic);return (_id._==3)?(!B(_47(_id.a,_hR)))?new T0(2):E(_i8):new T0(2);}));}),_ie=function(_if){return E(_i7);};return new T1(1,function(_ig){return new F(function(){return A2(_dO,_ig,_ie);});});}});if(_i1>10){return B(_3r(_4D,_i6));}else{var _ih=new T(function(){var _ii=new T(function(){var _ij=function(_ik){var _il=function(_im){return new F(function(){return A3(_g9,_gC,_43,function(_in){return new F(function(){return A1(_hZ,new T3(4,_ik,_im,_in));});});});};return new F(function(){return A3(_g9,_gC,_43,_il);});};return B(A3(_fY,_ho,_43,_ij));});return B(_f7(function(_io){var _ip=E(_io);return (_ip._==3)?(!B(_47(_ip.a,_hS)))?new T0(2):E(_ii):new T0(2);}));}),_iq=function(_ir){return E(_ih);};return B(_3r(new T1(1,function(_is){return new F(function(){return A2(_dO,_is,_iq);});}),_i6));}});if(_i1>10){return B(_3r(_4D,_i5));}else{var _it=new T(function(){var _iu=new T(function(){return B(A3(_fY,_hX,_43,function(_iv){return new F(function(){return A1(_hZ,new T1(3,_iv));});}));});return B(_f7(function(_iw){var _ix=E(_iw);return (_ix._==3)?(!B(_47(_ix.a,_hW)))?new T0(2):E(_iu):new T0(2);}));}),_iy=function(_iz){return E(_it);};return B(_3r(new T1(1,function(_iA){return new F(function(){return A2(_dO,_iA,_iy);});}),_i5));}});if(_i1>10){return B(_3r(_4D,_i4));}else{var _iB=new T(function(){var _iC=new T(function(){var _iD=function(_iE){return new F(function(){return A3(_fY,_hX,_43,function(_iF){return new F(function(){return A1(_hZ,new T2(2,_iE,_iF));});});});};return B(A3(_fY,_hX,_43,_iD));});return B(_f7(function(_iG){var _iH=E(_iG);return (_iH._==3)?(!B(_47(_iH.a,_hV)))?new T0(2):E(_iC):new T0(2);}));}),_iI=function(_iJ){return E(_iB);};return B(_3r(new T1(1,function(_iK){return new F(function(){return A2(_dO,_iK,_iI);});}),_i4));}});if(_i1>10){return B(_3r(_4D,_i3));}else{var _iL=new T(function(){var _iM=new T(function(){var _iN=function(_iO){return new F(function(){return A3(_fY,_hX,_43,function(_iP){return new F(function(){return A1(_hZ,new T2(1,_iO,_iP));});});});};return B(A3(_fY,_hX,_43,_iN));});return B(_f7(function(_iQ){var _iR=E(_iQ);return (_iR._==3)?(!B(_47(_iR.a,_hU)))?new T0(2):E(_iM):new T0(2);}));}),_iS=function(_iT){return E(_iL);};return B(_3r(new T1(1,function(_iU){return new F(function(){return A2(_dO,_iU,_iS);});}),_i3));}});if(_i1>10){return B(_3r(_4D,_i2));}else{var _iV=new T(function(){var _iW=new T(function(){return B(A3(_g9,_gC,_43,function(_iX){return new F(function(){return A1(_hZ,new T1(0,_iX));});}));});return B(_f7(function(_iY){var _iZ=E(_iY);return (_iZ._==3)?(!B(_47(_iZ.a,_hT)))?new T0(2):E(_iW):new T0(2);}));}),_j0=function(_j1){return E(_iV);};return B(_3r(new T1(1,function(_j2){return new F(function(){return A2(_dO,_j2,_j0);});}),_i2));}});return new F(function(){return _3r(B(_hD(_hC,_hY,_hZ)),_i0);});},_j3=__Z,_j4=new T(function(){return B(unCStr("RedeemCC"));}),_j5=new T(function(){return B(unCStr("Pay"));}),_j6=new T(function(){return B(unCStr("Both"));}),_j7=new T(function(){return B(unCStr("Choice"));}),_j8=new T(function(){return B(unCStr("CommitCash"));}),_j9=new T(function(){return B(unCStr("When"));}),_ja=function(_jb,_jc){var _jd=new T(function(){var _je=new T(function(){return B(A1(_jc,_j3));});return B(_f7(function(_jf){var _jg=E(_jf);return (_jg._==3)?(!B(_47(_jg.a,_13)))?new T0(2):E(_je):new T0(2);}));}),_jh=function(_ji){return E(_jd);},_jj=new T(function(){var _jk=E(_jb),_jl=new T(function(){var _jm=new T(function(){var _jn=new T(function(){var _jo=new T(function(){var _jp=new T(function(){if(_jk>10){return new T0(2);}else{var _jq=new T(function(){var _jr=new T(function(){var _js=function(_jt){var _ju=function(_jv){var _jw=function(_jx){return new F(function(){return A3(_fY,_ja,_43,function(_jy){return new F(function(){return A1(_jc,new T4(6,_jt,_jv,_jx,_jy));});});});};return new F(function(){return A3(_fY,_ja,_43,_jw);});};return new F(function(){return A3(_g9,_gC,_43,_ju);});};return B(A3(_fY,_hX,_43,_js));});return B(_f7(function(_jz){var _jA=E(_jz);return (_jA._==3)?(!B(_47(_jA.a,_j9)))?new T0(2):E(_jr):new T0(2);}));}),_jB=function(_jC){return E(_jq);};return new T1(1,function(_jD){return new F(function(){return A2(_dO,_jD,_jB);});});}});if(_jk>10){return B(_3r(_4D,_jp));}else{var _jE=new T(function(){var _jF=new T(function(){var _jG=function(_jH){var _jI=function(_jJ){var _jK=function(_jL){var _jM=function(_jN){var _jO=function(_jP){return new F(function(){return A3(_fY,_ja,_43,function(_jQ){return new F(function(){return A1(_jc,new T6(5,_jH,_jJ,_jL,_jN,_jP,_jQ));});});});};return new F(function(){return A3(_g9,_gC,_43,_jO);});};return new F(function(){return A3(_g9,_gC,_43,_jM);});};return new F(function(){return A3(_g9,_gC,_43,_jK);});};return new F(function(){return A3(_g9,_gC,_43,_jI);});};return B(A3(_fY,_gU,_43,_jG));});return B(_f7(function(_jR){var _jS=E(_jR);return (_jS._==3)?(!B(_47(_jS.a,_j8)))?new T0(2):E(_jF):new T0(2);}));}),_jT=function(_jU){return E(_jE);};return B(_3r(new T1(1,function(_jV){return new F(function(){return A2(_dO,_jV,_jT);});}),_jp));}});if(_jk>10){return B(_3r(_4D,_jo));}else{var _jW=new T(function(){var _jX=new T(function(){var _jY=function(_jZ){var _k0=function(_k1){return new F(function(){return A3(_fY,_ja,_43,function(_k2){return new F(function(){return A1(_jc,new T3(4,_jZ,_k1,_k2));});});});};return new F(function(){return A3(_fY,_ja,_43,_k0);});};return B(A3(_fY,_hX,_43,_jY));});return B(_f7(function(_k3){var _k4=E(_k3);return (_k4._==3)?(!B(_47(_k4.a,_j7)))?new T0(2):E(_jX):new T0(2);}));}),_k5=function(_k6){return E(_jW);};return B(_3r(new T1(1,function(_k7){return new F(function(){return A2(_dO,_k7,_k5);});}),_jo));}});if(_jk>10){return B(_3r(_4D,_jn));}else{var _k8=new T(function(){var _k9=new T(function(){var _ka=function(_kb){return new F(function(){return A3(_fY,_ja,_43,function(_kc){return new F(function(){return A1(_jc,new T2(3,_kb,_kc));});});});};return B(A3(_fY,_ja,_43,_ka));});return B(_f7(function(_kd){var _ke=E(_kd);return (_ke._==3)?(!B(_47(_ke.a,_j6)))?new T0(2):E(_k9):new T0(2);}));}),_kf=function(_kg){return E(_k8);};return B(_3r(new T1(1,function(_kh){return new F(function(){return A2(_dO,_kh,_kf);});}),_jn));}});if(_jk>10){return B(_3r(_4D,_jm));}else{var _ki=new T(function(){var _kj=new T(function(){var _kk=function(_kl){var _km=function(_kn){var _ko=function(_kp){var _kq=function(_kr){var _ks=function(_kt){return new F(function(){return A3(_fY,_ja,_43,function(_ku){return new F(function(){return A1(_jc,new T6(2,_kl,_kn,_kp,_kr,_kt,_ku));});});});};return new F(function(){return A3(_g9,_gC,_43,_ks);});};return new F(function(){return A3(_g9,_gC,_43,_kq);});};return new F(function(){return A3(_g9,_gC,_43,_ko);});};return new F(function(){return A3(_g9,_gC,_43,_km);});};return B(A3(_fY,_h9,_43,_kk));});return B(_f7(function(_kv){var _kw=E(_kv);return (_kw._==3)?(!B(_47(_kw.a,_j5)))?new T0(2):E(_kj):new T0(2);}));}),_kx=function(_ky){return E(_ki);};return B(_3r(new T1(1,function(_kz){return new F(function(){return A2(_dO,_kz,_kx);});}),_jm));}});if(_jk>10){return B(_3r(_4D,_jl));}else{var _kA=new T(function(){var _kB=new T(function(){var _kC=function(_kD){return new F(function(){return A3(_fY,_ja,_43,function(_kE){return new F(function(){return A1(_jc,new T2(1,_kD,_kE));});});});};return B(A3(_fY,_gU,_43,_kC));});return B(_f7(function(_kF){var _kG=E(_kF);return (_kG._==3)?(!B(_47(_kG.a,_j4)))?new T0(2):E(_kB):new T0(2);}));}),_kH=function(_kI){return E(_kA);};return B(_3r(new T1(1,function(_kJ){return new F(function(){return A2(_dO,_kJ,_kH);});}),_jl));}});return new F(function(){return _3r(new T1(1,function(_kK){return new F(function(){return A2(_dO,_kK,_jh);});}),_jj);});},_kL=function(_kM){var _kN=function(_kO){return E(new T2(3,_kM,_4D));};return new T1(1,function(_kP){return new F(function(){return A2(_dO,_kP,_kN);});});},_kQ=new T(function(){return B(A3(_fY,_ja,_fE,_kL));}),_kR=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_kS=function(_kT){while(1){var _kU=B((function(_kV){var _kW=E(_kV);if(!_kW._){return __Z;}else{var _kX=_kW.b,_kY=E(_kW.a);if(!E(_kY.b)._){return new T2(1,_kY.a,new T(function(){return B(_kS(_kX));}));}else{_kT=_kX;return __continue;}}})(_kT));if(_kU!=__continue){return _kU;}}},_kZ=function(_){var _l0=__app0(E(_kR)),_l1=B(_kS(B(_3h(_kQ,new T(function(){var _l2=String(_l0);return fromJSStr(_l2);})))));if(!_l1._){return E(_1U);}else{if(!E(_l1.b)._){return new F(function(){return _1O(_1L,B(_1a(0,_l1.a,_1I)),_);});}else{return E(_1K);}}},_l3="(function (b) { return (b.inputList.length); })",_l4="(function (b, x) { return (b.inputList[x]); })",_l5=function(_l6,_l7,_){var _l8=eval(E(_l4)),_l9=__app2(E(_l8),_l6,_l7);return new T1(0,_l9);},_la=function(_lb,_lc,_ld,_){var _le=E(_ld);if(!_le._){return _1I;}else{var _lf=B(_l5(_lb,E(_le.a),_)),_lg=B(_la(_lb,_,_le.b,_));return new T2(1,_lf,_lg);}},_lh=function(_li,_lj){if(_li<=_lj){var _lk=function(_ll){return new T2(1,_ll,new T(function(){if(_ll!=_lj){return B(_lk(_ll+1|0));}else{return __Z;}}));};return new F(function(){return _lk(_li);});}else{return __Z;}},_lm=function(_ln,_){var _lo=eval(E(_l3)),_lp=__app1(E(_lo),_ln),_lq=Number(_lp),_lr=jsTrunc(_lq);return new F(function(){return _la(_ln,_,new T(function(){return B(_lh(0,_lr-1|0));}),_);});},_ls="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_lt="(function (x) { return x.name; })",_lu=new T(function(){return B(unCStr("\""));}),_lv=function(_lw){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_2(_lw,_lu));}))));});},_lx=function(_ly,_lz,_){var _lA=E(_lz);if(!_lA._){return new F(function(){return _lv(_ly);});}else{var _lB=E(_lA.a),_lC=E(_lt),_lD=eval(_lC),_lE=__app1(E(_lD),E(_lB.a)),_lF=String(_lE);if(!B(_47(fromJSStr(_lF),_ly))){var _lG=function(_lH,_lI,_){while(1){var _lJ=E(_lI);if(!_lJ._){return new F(function(){return _lv(_lH);});}else{var _lK=E(_lJ.a),_lL=eval(_lC),_lM=__app1(E(_lL),E(_lK.a)),_lN=String(_lM);if(!B(_47(fromJSStr(_lN),_lH))){_lI=_lJ.b;continue;}else{return _lK;}}}};return new F(function(){return _lG(_ly,_lA.b,_);});}else{return _lB;}}},_lO=function(_lP,_lQ,_lR,_){var _lS=B(_lm(_lQ,_)),_lT=B(_lx(_lP,_lS,_)),_lU=eval(E(_ls)),_lV=__app2(E(_lU),E(E(_lR).a),E(E(_lT).a));return new F(function(){return _1M(_);});},_lW=function(_lX){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_2(_lX,_lu));}))));});},_lY=function(_lZ,_m0,_){var _m1=E(_m0);if(!_m1._){return new F(function(){return _lW(_lZ);});}else{var _m2=E(_m1.a),_m3=E(_lt),_m4=eval(_m3),_m5=__app1(E(_m4),E(_m2.a)),_m6=String(_m5);if(!B(_47(fromJSStr(_m6),_lZ))){var _m7=function(_m8,_m9,_){while(1){var _ma=E(_m9);if(!_ma._){return new F(function(){return _lW(_m8);});}else{var _mb=E(_ma.a),_mc=eval(_m3),_md=__app1(E(_mc),E(_mb.a)),_me=String(_md);if(!B(_47(fromJSStr(_me),_m8))){_m9=_ma.b;continue;}else{return _mb;}}}};return new F(function(){return _m7(_lZ,_m1.b,_);});}else{return _m2;}}},_mf="(function (b) { return (b.fieldRow.length); })",_mg="(function (b, x) { return (b.fieldRow[x]); })",_mh=function(_mi,_mj,_){var _mk=eval(E(_mg)),_ml=__app2(E(_mk),_mi,_mj);return new T1(0,_ml);},_mm=function(_mn,_mo,_mp,_){var _mq=E(_mp);if(!_mq._){return _1I;}else{var _mr=B(_mh(_mn,E(_mq.a),_)),_ms=B(_mm(_mn,_,_mq.b,_));return new T2(1,_mr,_ms);}},_mt=function(_mu,_){var _mv=eval(E(_mf)),_mw=__app1(E(_mv),_mu),_mx=Number(_mw),_my=jsTrunc(_mx);return new F(function(){return _mm(_mu,_,new T(function(){return B(_lh(0,_my-1|0));}),_);});},_mz=function(_mA,_){var _mB=E(_mA);if(!_mB._){return _1I;}else{var _mC=B(_mt(E(E(_mB.a).a),_)),_mD=B(_mz(_mB.b,_));return new T2(1,_mC,_mD);}},_mE=function(_mF){var _mG=E(_mF);if(!_mG._){return __Z;}else{return new F(function(){return _2(_mG.a,new T(function(){return B(_mE(_mG.b));},1));});}},_mH=function(_mI,_mJ,_){var _mK=B(_lm(_mJ,_)),_mL=B(_mz(_mK,_));return new F(function(){return _lY(_mI,B(_mE(_mL)),_);});},_mM="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_mN=function(_mO,_mP,_mQ,_){var _mR=B(_lm(_mP,_)),_mS=B(_lx(_mO,_mR,_)),_mT=eval(E(_mM)),_mU=__app2(E(_mT),E(E(_mQ).a),E(E(_mS).a));return new F(function(){return _1M(_);});},_mV=new T(function(){return B(unCStr("contract_redeemcc"));}),_mW=new T(function(){return B(unCStr("contract_pay"));}),_mX=new T(function(){return B(unCStr("contract_both"));}),_mY=new T(function(){return B(unCStr("contract_choice"));}),_mZ=new T(function(){return B(unCStr("contract_commitcash"));}),_n0=new T(function(){return B(unCStr("contract_when"));}),_n1="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_n2=function(_n3,_){var _n4=eval(E(_n1)),_n5=__app1(E(_n4),toJSStr(E(_n3)));return new T1(0,_n5);},_n6=new T(function(){return B(unCStr("contract2"));}),_n7=new T(function(){return B(unCStr("contract1"));}),_n8=new T(function(){return B(unCStr("expiration"));}),_n9=new T(function(){return B(unCStr("payee_id"));}),_na=new T(function(){return B(unCStr("payer_id"));}),_nb=new T(function(){return B(unCStr("pay_id"));}),_nc=new T(function(){return B(unCStr("contract_null"));}),_nd=new T(function(){return B(unCStr("observation"));}),_ne=new T(function(){return B(unCStr("timeout"));}),_nf=new T(function(){return B(unCStr("contract"));}),_ng=new T(function(){return B(unCStr("end_expiration"));}),_nh=new T(function(){return B(unCStr("start_expiration"));}),_ni=new T(function(){return B(unCStr("ammount"));}),_nj=new T(function(){return B(unCStr("person_id"));}),_nk=new T(function(){return B(unCStr("ccommit_id"));}),_nl=new T(function(){return B(unCStr("observation_personchosethis"));}),_nm=new T(function(){return B(unCStr("observation_personchosesomething"));}),_nn=new T(function(){return B(unCStr("observation_trueobs"));}),_no=new T(function(){return B(unCStr("observation_falseobs"));}),_np=new T(function(){return B(unCStr("observation_belowtimeout"));}),_nq=new T(function(){return B(unCStr("observation_andobs"));}),_nr=new T(function(){return B(unCStr("observation_orobs"));}),_ns=new T(function(){return B(unCStr("observation_notobs"));}),_nt=new T(function(){return B(unCStr("person"));}),_nu=new T(function(){return B(unCStr("choice_id"));}),_nv=new T(function(){return B(unCStr("choice_value"));}),_nw=new T(function(){return B(unCStr("observation2"));}),_nx=new T(function(){return B(unCStr("observation1"));}),_ny=new T(function(){return B(unCStr("block_number"));}),_nz="(function (b, s) { return (b.setText(s)); })",_nA=function(_nB,_){var _nC=E(_nB);switch(_nC._){case 0:var _nD=B(_n2(_np,_)),_nE=E(_nD),_nF=B(_mH(_ny,E(_nE.a),_)),_nG=eval(E(_nz)),_nH=__app2(E(_nG),E(E(_nF).a),toJSStr(B(_c(0,E(_nC.a),_1I))));return _nE;case 1:var _nI=B(_nA(_nC.a,_)),_nJ=B(_nA(_nC.b,_)),_nK=B(_n2(_nq,_)),_nL=E(_nK),_nM=E(_nL.a),_nN=B(_mN(_nx,_nM,_nI,_)),_nO=B(_mN(_nw,_nM,_nJ,_));return _nL;case 2:var _nP=B(_nA(_nC.a,_)),_nQ=B(_nA(_nC.b,_)),_nR=B(_n2(_nr,_)),_nS=E(_nR),_nT=E(_nS.a),_nU=B(_mN(_nx,_nT,_nP,_)),_nV=B(_mN(_nw,_nT,_nQ,_));return _nS;case 3:var _nW=B(_nA(_nC.a,_)),_nX=B(_n2(_ns,_)),_nY=E(_nX),_nZ=B(_mN(_nd,E(_nY.a),_nW,_));return _nY;case 4:var _o0=B(_n2(_nl,_)),_o1=E(_o0),_o2=E(_o1.a),_o3=B(_mH(_nu,_o2,_)),_o4=eval(E(_nz)),_o5=__app2(E(_o4),E(E(_o3).a),toJSStr(B(_c(0,E(_nC.a),_1I)))),_o6=B(_mH(_nt,_o2,_)),_o7=__app2(E(_o4),E(E(_o6).a),toJSStr(B(_c(0,E(_nC.b),_1I)))),_o8=B(_mH(_nv,_o2,_)),_o9=__app2(E(_o4),E(E(_o8).a),toJSStr(B(_c(0,E(_nC.c),_1I))));return _o1;case 5:var _oa=B(_n2(_nm,_)),_ob=E(_oa),_oc=E(_ob.a),_od=B(_mH(_nu,_oc,_)),_oe=eval(E(_nz)),_of=__app2(E(_oe),E(E(_od).a),toJSStr(B(_c(0,E(_nC.a),_1I)))),_og=B(_mH(_nt,_oc,_)),_oh=__app2(E(_oe),E(E(_og).a),toJSStr(B(_c(0,E(_nC.b),_1I))));return _ob;case 6:return new F(function(){return _n2(_nn,_);});break;default:return new F(function(){return _n2(_no,_);});}},_oi=function(_oj,_){var _ok=E(_oj);switch(_ok._){case 0:return new F(function(){return _n2(_nc,_);});break;case 1:var _ol=B(_oi(_ok.b,_)),_om=B(_n2(_mV,_)),_on=E(_om),_oo=E(_on.a),_op=B(_mH(_nk,_oo,_)),_oq=eval(E(_nz)),_or=__app2(E(_oq),E(E(_op).a),toJSStr(B(_c(0,E(_ok.a),_1I)))),_os=B(_lO(_nf,_oo,_ol,_));return _on;case 2:var _ot=B(_oi(_ok.f,_)),_ou=B(_n2(_mW,_)),_ov=E(_ou),_ow=E(_ov.a),_ox=B(_mH(_nb,_ow,_)),_oy=eval(E(_nz)),_oz=__app2(E(_oy),E(E(_ox).a),toJSStr(B(_c(0,E(_ok.a),_1I)))),_oA=B(_mH(_na,_ow,_)),_oB=__app2(E(_oy),E(E(_oA).a),toJSStr(B(_c(0,E(_ok.b),_1I)))),_oC=B(_mH(_n9,_ow,_)),_oD=__app2(E(_oy),E(E(_oC).a),toJSStr(B(_c(0,E(_ok.c),_1I)))),_oE=B(_mH(_ni,_ow,_)),_oF=__app2(E(_oy),E(E(_oE).a),toJSStr(B(_c(0,E(_ok.d),_1I)))),_oG=B(_mH(_n8,_ow,_)),_oH=__app2(E(_oy),E(E(_oG).a),toJSStr(B(_c(0,E(_ok.e),_1I)))),_oI=B(_lO(_nf,_ow,_ot,_));return _ov;case 3:var _oJ=B(_oi(_ok.a,_)),_oK=B(_oi(_ok.b,_)),_oL=B(_n2(_mX,_)),_oM=E(_oL),_oN=E(_oM.a),_oO=B(_lO(_n7,_oN,_oJ,_)),_oP=B(_lO(_n6,_oN,_oK,_));return _oM;case 4:var _oQ=B(_nA(_ok.a,_)),_oR=B(_oi(_ok.b,_)),_oS=B(_oi(_ok.c,_)),_oT=B(_n2(_mY,_)),_oU=E(_oT),_oV=E(_oU.a),_oW=B(_mN(_nd,_oV,_oQ,_)),_oX=B(_lO(_n7,_oV,_oR,_)),_oY=B(_lO(_n6,_oV,_oS,_));return _oU;case 5:var _oZ=B(_oi(_ok.f,_)),_p0=B(_n2(_mZ,_)),_p1=E(_p0),_p2=E(_p1.a),_p3=B(_mH(_nk,_p2,_)),_p4=eval(E(_nz)),_p5=__app2(E(_p4),E(E(_p3).a),toJSStr(B(_c(0,E(_ok.a),_1I)))),_p6=B(_mH(_nj,_p2,_)),_p7=__app2(E(_p4),E(E(_p6).a),toJSStr(B(_c(0,E(_ok.b),_1I)))),_p8=B(_mH(_ni,_p2,_)),_p9=__app2(E(_p4),E(E(_p8).a),toJSStr(B(_c(0,E(_ok.c),_1I)))),_pa=B(_mH(_nh,_p2,_)),_pb=__app2(E(_p4),E(E(_pa).a),toJSStr(B(_c(0,E(_ok.d),_1I)))),_pc=B(_mH(_ng,_p2,_)),_pd=__app2(E(_p4),E(E(_pc).a),toJSStr(B(_c(0,E(_ok.e),_1I)))),_pe=B(_lO(_nf,_p2,_oZ,_));return _p1;default:var _pf=B(_nA(_ok.a,_)),_pg=B(_oi(_ok.c,_)),_ph=B(_oi(_ok.d,_)),_pi=B(_n2(_n0,_)),_pj=E(_pi),_pk=E(_pj.a),_pl=B(_mH(_ne,_pk,_)),_pm=eval(E(_nz)),_pn=__app2(E(_pm),E(E(_pl).a),toJSStr(B(_c(0,E(_ok.b),_1I)))),_po=B(_mN(_nd,_pk,_pf,_)),_pp=B(_lO(_n7,_pk,_pg,_)),_pq=B(_lO(_n6,_pk,_ph,_));return _pj;}},_pr=new T(function(){return B(unCStr("base_contract"));}),_ps=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_pt=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_pu=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_pv=function(_pw,_){var _px=__app0(E(_pu)),_py=__app0(E(_pt)),_pz=B(_kS(B(_3h(_kQ,_pw))));if(!_pz._){return E(_1U);}else{if(!E(_pz.b)._){var _pA=B(_oi(_pz.a,_)),_pB=B(_lO(_pr,_py,_pA,_)),_pC=__app0(E(_ps));return _0;}else{return E(_1K);}}},_pD="(function (t) {return document.getElementById(t).value})",_pE=function(_){var _pF=eval(E(_pD)),_pG=__app1(E(_pF),toJSStr(E(_1L)));return new F(function(){return _pv(new T(function(){var _pH=String(_pG);return fromJSStr(_pH);}),_);});},_pI=new T0(1),_pJ=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_pK=function(_pL){return new F(function(){return err(_pJ);});},_pM=new T(function(){return B(_pK(_));}),_pN=function(_pO,_pP,_pQ){var _pR=E(_pQ);if(!_pR._){var _pS=_pR.a,_pT=E(_pP);if(!_pT._){var _pU=_pT.a,_pV=_pT.b;if(_pU<=(imul(3,_pS)|0)){return new T4(0,(1+_pU|0)+_pS|0,E(_pO),E(_pT),E(_pR));}else{var _pW=E(_pT.c);if(!_pW._){var _pX=_pW.a,_pY=E(_pT.d);if(!_pY._){var _pZ=_pY.a,_q0=_pY.b,_q1=_pY.c;if(_pZ>=(imul(2,_pX)|0)){var _q2=function(_q3){var _q4=E(_pY.d);return (_q4._==0)?new T4(0,(1+_pU|0)+_pS|0,E(_q0),E(new T4(0,(1+_pX|0)+_q3|0,E(_pV),E(_pW),E(_q1))),E(new T4(0,(1+_pS|0)+_q4.a|0,E(_pO),E(_q4),E(_pR)))):new T4(0,(1+_pU|0)+_pS|0,E(_q0),E(new T4(0,(1+_pX|0)+_q3|0,E(_pV),E(_pW),E(_q1))),E(new T4(0,1+_pS|0,E(_pO),E(_pI),E(_pR))));},_q5=E(_q1);if(!_q5._){return new F(function(){return _q2(_q5.a);});}else{return new F(function(){return _q2(0);});}}else{return new T4(0,(1+_pU|0)+_pS|0,E(_pV),E(_pW),E(new T4(0,(1+_pS|0)+_pZ|0,E(_pO),E(_pY),E(_pR))));}}else{return E(_pM);}}else{return E(_pM);}}}else{return new T4(0,1+_pS|0,E(_pO),E(_pI),E(_pR));}}else{var _q6=E(_pP);if(!_q6._){var _q7=_q6.a,_q8=_q6.b,_q9=_q6.d,_qa=E(_q6.c);if(!_qa._){var _qb=_qa.a,_qc=E(_q9);if(!_qc._){var _qd=_qc.a,_qe=_qc.b,_qf=_qc.c;if(_qd>=(imul(2,_qb)|0)){var _qg=function(_qh){var _qi=E(_qc.d);return (_qi._==0)?new T4(0,1+_q7|0,E(_qe),E(new T4(0,(1+_qb|0)+_qh|0,E(_q8),E(_qa),E(_qf))),E(new T4(0,1+_qi.a|0,E(_pO),E(_qi),E(_pI)))):new T4(0,1+_q7|0,E(_qe),E(new T4(0,(1+_qb|0)+_qh|0,E(_q8),E(_qa),E(_qf))),E(new T4(0,1,E(_pO),E(_pI),E(_pI))));},_qj=E(_qf);if(!_qj._){return new F(function(){return _qg(_qj.a);});}else{return new F(function(){return _qg(0);});}}else{return new T4(0,1+_q7|0,E(_q8),E(_qa),E(new T4(0,1+_qd|0,E(_pO),E(_qc),E(_pI))));}}else{return new T4(0,3,E(_q8),E(_qa),E(new T4(0,1,E(_pO),E(_pI),E(_pI))));}}else{var _qk=E(_q9);return (_qk._==0)?new T4(0,3,E(_qk.b),E(new T4(0,1,E(_q8),E(_pI),E(_pI))),E(new T4(0,1,E(_pO),E(_pI),E(_pI)))):new T4(0,2,E(_pO),E(_q6),E(_pI));}}else{return new T4(0,1,E(_pO),E(_pI),E(_pI));}}},_ql=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_qm=function(_qn){return new F(function(){return err(_ql);});},_qo=new T(function(){return B(_qm(_));}),_qp=function(_qq,_qr,_qs){var _qt=E(_qr);if(!_qt._){var _qu=_qt.a,_qv=E(_qs);if(!_qv._){var _qw=_qv.a,_qx=_qv.b;if(_qw<=(imul(3,_qu)|0)){return new T4(0,(1+_qu|0)+_qw|0,E(_qq),E(_qt),E(_qv));}else{var _qy=E(_qv.c);if(!_qy._){var _qz=_qy.a,_qA=_qy.b,_qB=_qy.c,_qC=E(_qv.d);if(!_qC._){var _qD=_qC.a;if(_qz>=(imul(2,_qD)|0)){var _qE=function(_qF){var _qG=E(_qq),_qH=E(_qy.d);return (_qH._==0)?new T4(0,(1+_qu|0)+_qw|0,E(_qA),E(new T4(0,(1+_qu|0)+_qF|0,E(_qG),E(_qt),E(_qB))),E(new T4(0,(1+_qD|0)+_qH.a|0,E(_qx),E(_qH),E(_qC)))):new T4(0,(1+_qu|0)+_qw|0,E(_qA),E(new T4(0,(1+_qu|0)+_qF|0,E(_qG),E(_qt),E(_qB))),E(new T4(0,1+_qD|0,E(_qx),E(_pI),E(_qC))));},_qI=E(_qB);if(!_qI._){return new F(function(){return _qE(_qI.a);});}else{return new F(function(){return _qE(0);});}}else{return new T4(0,(1+_qu|0)+_qw|0,E(_qx),E(new T4(0,(1+_qu|0)+_qz|0,E(_qq),E(_qt),E(_qy))),E(_qC));}}else{return E(_qo);}}else{return E(_qo);}}}else{return new T4(0,1+_qu|0,E(_qq),E(_qt),E(_pI));}}else{var _qJ=E(_qs);if(!_qJ._){var _qK=_qJ.a,_qL=_qJ.b,_qM=_qJ.d,_qN=E(_qJ.c);if(!_qN._){var _qO=_qN.a,_qP=_qN.b,_qQ=_qN.c,_qR=E(_qM);if(!_qR._){var _qS=_qR.a;if(_qO>=(imul(2,_qS)|0)){var _qT=function(_qU){var _qV=E(_qq),_qW=E(_qN.d);return (_qW._==0)?new T4(0,1+_qK|0,E(_qP),E(new T4(0,1+_qU|0,E(_qV),E(_pI),E(_qQ))),E(new T4(0,(1+_qS|0)+_qW.a|0,E(_qL),E(_qW),E(_qR)))):new T4(0,1+_qK|0,E(_qP),E(new T4(0,1+_qU|0,E(_qV),E(_pI),E(_qQ))),E(new T4(0,1+_qS|0,E(_qL),E(_pI),E(_qR))));},_qX=E(_qQ);if(!_qX._){return new F(function(){return _qT(_qX.a);});}else{return new F(function(){return _qT(0);});}}else{return new T4(0,1+_qK|0,E(_qL),E(new T4(0,1+_qO|0,E(_qq),E(_pI),E(_qN))),E(_qR));}}else{return new T4(0,3,E(_qP),E(new T4(0,1,E(_qq),E(_pI),E(_pI))),E(new T4(0,1,E(_qL),E(_pI),E(_pI))));}}else{var _qY=E(_qM);return (_qY._==0)?new T4(0,3,E(_qL),E(new T4(0,1,E(_qq),E(_pI),E(_pI))),E(_qY)):new T4(0,2,E(_qq),E(_pI),E(_qJ));}}else{return new T4(0,1,E(_qq),E(_pI),E(_pI));}}},_qZ=function(_r0,_r1,_r2,_r3,_r4){var _r5=E(_r4);if(!_r5._){var _r6=_r5.c,_r7=_r5.d,_r8=E(_r5.b),_r9=E(_r0),_ra=E(_r8.a);if(_r9>=_ra){if(_r9!=_ra){return new F(function(){return _qp(_r8,_r6,B(_qZ(_r9,_r1,_r2,_r3,_r7)));});}else{var _rb=E(_r1),_rc=E(_r8.b);if(_rb>=_rc){if(_rb!=_rc){return new F(function(){return _qp(_r8,_r6,B(_qZ(_r9,_rb,_r2,_r3,_r7)));});}else{var _rd=E(_r2),_re=E(_r8.c);if(_rd>=_re){if(_rd!=_re){return new F(function(){return _qp(_r8,_r6,B(_qZ(_r9,_rb,_rd,_r3,_r7)));});}else{var _rf=E(_r3),_rg=E(_r8.d);if(_rf>=_rg){if(_rf!=_rg){return new F(function(){return _qp(_r8,_r6,B(_qZ(_r9,_rb,_rd,_rf,_r7)));});}else{return new T4(0,_r5.a,E(new T4(0,_r9,_rb,_rd,_rf)),E(_r6),E(_r7));}}else{return new F(function(){return _pN(_r8,B(_qZ(_r9,_rb,_rd,_rf,_r6)),_r7);});}}}else{return new F(function(){return _pN(_r8,B(_qZ(_r9,_rb,_rd,_r3,_r6)),_r7);});}}}else{return new F(function(){return _pN(_r8,B(_qZ(_r9,_rb,_r2,_r3,_r6)),_r7);});}}}else{return new F(function(){return _pN(_r8,B(_qZ(_r9,_r1,_r2,_r3,_r6)),_r7);});}}else{return new T4(0,1,E(new T4(0,_r0,_r1,_r2,_r3)),E(_pI),E(_pI));}},_rh=function(_ri,_rj){while(1){var _rk=E(_rj);if(!_rk._){return E(_ri);}else{var _rl=E(_rk.a),_rm=B(_qZ(_rl.a,_rl.b,_rl.c,_rl.d,_ri));_ri=_rm;_rj=_rk.b;continue;}}},_rn=function(_ro,_rp,_rq,_rr,_rs,_rt){return new F(function(){return _rh(B(_qZ(_rp,_rq,_rr,_rs,_ro)),_rt);});},_ru=function(_rv){return new T4(0,1,E(_rv),E(_pI),E(_pI));},_rw=function(_rx,_ry){var _rz=E(_ry);if(!_rz._){return new F(function(){return _qp(_rz.b,_rz.c,B(_rw(_rx,_rz.d)));});}else{return new F(function(){return _ru(_rx);});}},_rA=function(_rB,_rC){var _rD=E(_rC);if(!_rD._){return new F(function(){return _pN(_rD.b,B(_rA(_rB,_rD.c)),_rD.d);});}else{return new F(function(){return _ru(_rB);});}},_rE=function(_rF,_rG,_rH,_rI,_rJ){return new F(function(){return _qp(_rH,_rI,B(_rw(_rF,_rJ)));});},_rK=function(_rL,_rM,_rN,_rO,_rP){return new F(function(){return _pN(_rN,B(_rA(_rL,_rO)),_rP);});},_rQ=function(_rR,_rS,_rT,_rU,_rV,_rW){var _rX=E(_rS);if(!_rX._){var _rY=_rX.a,_rZ=_rX.b,_s0=_rX.c,_s1=_rX.d;if((imul(3,_rY)|0)>=_rT){if((imul(3,_rT)|0)>=_rY){return new T4(0,(_rY+_rT|0)+1|0,E(_rR),E(_rX),E(new T4(0,_rT,E(_rU),E(_rV),E(_rW))));}else{return new F(function(){return _qp(_rZ,_s0,B(_rQ(_rR,_s1,_rT,_rU,_rV,_rW)));});}}else{return new F(function(){return _pN(_rU,B(_s2(_rR,_rY,_rZ,_s0,_s1,_rV)),_rW);});}}else{return new F(function(){return _rK(_rR,_rT,_rU,_rV,_rW);});}},_s2=function(_s3,_s4,_s5,_s6,_s7,_s8){var _s9=E(_s8);if(!_s9._){var _sa=_s9.a,_sb=_s9.b,_sc=_s9.c,_sd=_s9.d;if((imul(3,_s4)|0)>=_sa){if((imul(3,_sa)|0)>=_s4){return new T4(0,(_s4+_sa|0)+1|0,E(_s3),E(new T4(0,_s4,E(_s5),E(_s6),E(_s7))),E(_s9));}else{return new F(function(){return _qp(_s5,_s6,B(_rQ(_s3,_s7,_sa,_sb,_sc,_sd)));});}}else{return new F(function(){return _pN(_sb,B(_s2(_s3,_s4,_s5,_s6,_s7,_sc)),_sd);});}}else{return new F(function(){return _rE(_s3,_s4,_s5,_s6,_s7);});}},_se=function(_sf,_sg,_sh){var _si=E(_sg);if(!_si._){var _sj=_si.a,_sk=_si.b,_sl=_si.c,_sm=_si.d,_sn=E(_sh);if(!_sn._){var _so=_sn.a,_sp=_sn.b,_sq=_sn.c,_sr=_sn.d;if((imul(3,_sj)|0)>=_so){if((imul(3,_so)|0)>=_sj){return new T4(0,(_sj+_so|0)+1|0,E(_sf),E(_si),E(_sn));}else{return new F(function(){return _qp(_sk,_sl,B(_rQ(_sf,_sm,_so,_sp,_sq,_sr)));});}}else{return new F(function(){return _pN(_sp,B(_s2(_sf,_sj,_sk,_sl,_sm,_sq)),_sr);});}}else{return new F(function(){return _rE(_sf,_sj,_sk,_sl,_sm);});}}else{return new F(function(){return _rA(_sf,_sh);});}},_ss=function(_st,_su){var _sv=E(_su);if(!_sv._){return new T3(0,_pI,_1I,_1I);}else{var _sw=_sv.a,_sx=E(_st);if(_sx==1){var _sy=E(_sv.b);if(!_sy._){return new T3(0,new T(function(){return new T4(0,1,E(_sw),E(_pI),E(_pI));}),_1I,_1I);}else{var _sz=E(_sw),_sA=E(_sz.a),_sB=E(_sy.a),_sC=E(_sB.a);if(_sA>=_sC){if(_sA!=_sC){return new T3(0,new T4(0,1,E(_sz),E(_pI),E(_pI)),_1I,_sy);}else{var _sD=E(_sz.b),_sE=E(_sB.b);if(_sD>=_sE){if(_sD!=_sE){return new T3(0,new T4(0,1,E(_sz),E(_pI),E(_pI)),_1I,_sy);}else{var _sF=E(_sz.c),_sG=E(_sB.c);return (_sF>=_sG)?(_sF!=_sG)?new T3(0,new T4(0,1,E(_sz),E(_pI),E(_pI)),_1I,_sy):(E(_sz.d)<E(_sB.d))?new T3(0,new T4(0,1,E(_sz),E(_pI),E(_pI)),_sy,_1I):new T3(0,new T4(0,1,E(_sz),E(_pI),E(_pI)),_1I,_sy):new T3(0,new T4(0,1,E(_sz),E(_pI),E(_pI)),_sy,_1I);}}else{return new T3(0,new T4(0,1,E(_sz),E(_pI),E(_pI)),_sy,_1I);}}}else{return new T3(0,new T4(0,1,E(_sz),E(_pI),E(_pI)),_sy,_1I);}}}else{var _sH=B(_ss(_sx>>1,_sv)),_sI=_sH.a,_sJ=_sH.c,_sK=E(_sH.b);if(!_sK._){return new T3(0,_sI,_1I,_sJ);}else{var _sL=_sK.a,_sM=E(_sK.b);if(!_sM._){return new T3(0,new T(function(){return B(_rw(_sL,_sI));}),_1I,_sJ);}else{var _sN=E(_sL),_sO=E(_sN.a),_sP=E(_sM.a),_sQ=E(_sP.a);if(_sO>=_sQ){if(_sO!=_sQ){return new T3(0,_sI,_1I,_sK);}else{var _sR=E(_sN.b),_sS=E(_sP.b);if(_sR>=_sS){if(_sR!=_sS){return new T3(0,_sI,_1I,_sK);}else{var _sT=E(_sN.c),_sU=E(_sP.c);if(_sT>=_sU){if(_sT!=_sU){return new T3(0,_sI,_1I,_sK);}else{if(E(_sN.d)<E(_sP.d)){var _sV=B(_ss(_sx>>1,_sM));return new T3(0,new T(function(){return B(_se(_sN,_sI,_sV.a));}),_sV.b,_sV.c);}else{return new T3(0,_sI,_1I,_sK);}}}else{var _sW=B(_ss(_sx>>1,_sM));return new T3(0,new T(function(){return B(_se(_sN,_sI,_sW.a));}),_sW.b,_sW.c);}}}else{var _sX=B(_ss(_sx>>1,_sM));return new T3(0,new T(function(){return B(_se(_sN,_sI,_sX.a));}),_sX.b,_sX.c);}}}else{var _sY=B(_ss(_sx>>1,_sM));return new T3(0,new T(function(){return B(_se(_sN,_sI,_sY.a));}),_sY.b,_sY.c);}}}}}},_sZ=function(_t0,_t1,_t2){var _t3=E(_t2);if(!_t3._){return E(_t1);}else{var _t4=_t3.a,_t5=E(_t3.b);if(!_t5._){return new F(function(){return _rw(_t4,_t1);});}else{var _t6=E(_t4),_t7=_t6.b,_t8=_t6.c,_t9=_t6.d,_ta=E(_t6.a),_tb=E(_t5.a),_tc=E(_tb.a),_td=function(_te){var _tf=B(_ss(_t0,_t5)),_tg=_tf.a,_th=E(_tf.c);if(!_th._){return new F(function(){return _sZ(_t0<<1,B(_se(_t6,_t1,_tg)),_tf.b);});}else{return new F(function(){return _rh(B(_se(_t6,_t1,_tg)),_th);});}};if(_ta>=_tc){if(_ta!=_tc){return new F(function(){return _rn(_t1,_ta,_t7,_t8,_t9,_t5);});}else{var _ti=E(_t7),_tj=E(_tb.b);if(_ti>=_tj){if(_ti!=_tj){return new F(function(){return _rn(_t1,_ta,_ti,_t8,_t9,_t5);});}else{var _tk=E(_t8),_tl=E(_tb.c);if(_tk>=_tl){if(_tk!=_tl){return new F(function(){return _rn(_t1,_ta,_ti,_tk,_t9,_t5);});}else{var _tm=E(_t9);if(_tm<E(_tb.d)){return new F(function(){return _td(_);});}else{return new F(function(){return _rn(_t1,_ta,_ti,_tk,_tm,_t5);});}}}else{return new F(function(){return _td(_);});}}}else{return new F(function(){return _td(_);});}}}else{return new F(function(){return _td(_);});}}}},_tn=function(_to){var _tp=E(_to);if(!_tp._){return new T0(1);}else{var _tq=_tp.a,_tr=E(_tp.b);if(!_tr._){return new T4(0,1,E(_tq),E(_pI),E(_pI));}else{var _ts=_tr.b,_tt=E(_tq),_tu=E(_tt.a),_tv=E(_tr.a),_tw=_tv.b,_tx=_tv.c,_ty=_tv.d,_tz=E(_tv.a);if(_tu>=_tz){if(_tu!=_tz){return new F(function(){return _rn(new T4(0,1,E(_tt),E(_pI),E(_pI)),_tz,_tw,_tx,_ty,_ts);});}else{var _tA=E(_tt.b),_tB=E(_tw);if(_tA>=_tB){if(_tA!=_tB){return new F(function(){return _rn(new T4(0,1,E(_tt),E(_pI),E(_pI)),_tz,_tB,_tx,_ty,_ts);});}else{var _tC=E(_tt.c),_tD=E(_tx);if(_tC>=_tD){if(_tC!=_tD){return new F(function(){return _rn(new T4(0,1,E(_tt),E(_pI),E(_pI)),_tz,_tB,_tD,_ty,_ts);});}else{var _tE=E(_ty);if(E(_tt.d)<_tE){return new F(function(){return _sZ(1,new T4(0,1,E(_tt),E(_pI),E(_pI)),_tr);});}else{return new F(function(){return _rn(new T4(0,1,E(_tt),E(_pI),E(_pI)),_tz,_tB,_tD,_tE,_ts);});}}}else{return new F(function(){return _sZ(1,new T4(0,1,E(_tt),E(_pI),E(_pI)),_tr);});}}}else{return new F(function(){return _sZ(1,new T4(0,1,E(_tt),E(_pI),E(_pI)),_tr);});}}}else{return new F(function(){return _sZ(1,new T4(0,1,E(_tt),E(_pI),E(_pI)),_tr);});}}}},_tF=function(_tG,_tH,_tI,_tJ,_tK){var _tL=E(_tG);if(_tL==1){var _tM=E(_tK);if(!_tM._){return new T3(0,new T4(0,1,E(new T3(0,_tH,_tI,_tJ)),E(_pI),E(_pI)),_1I,_1I);}else{var _tN=E(_tH),_tO=E(_tM.a),_tP=E(_tO.a);if(_tN>=_tP){if(_tN!=_tP){return new T3(0,new T4(0,1,E(new T3(0,_tN,_tI,_tJ)),E(_pI),E(_pI)),_1I,_tM);}else{var _tQ=E(_tO.b);return (_tI>=_tQ)?(_tI!=_tQ)?new T3(0,new T4(0,1,E(new T3(0,_tN,_tI,_tJ)),E(_pI),E(_pI)),_1I,_tM):(_tJ<E(_tO.c))?new T3(0,new T4(0,1,E(new T3(0,_tN,_tI,_tJ)),E(_pI),E(_pI)),_tM,_1I):new T3(0,new T4(0,1,E(new T3(0,_tN,_tI,_tJ)),E(_pI),E(_pI)),_1I,_tM):new T3(0,new T4(0,1,E(new T3(0,_tN,_tI,_tJ)),E(_pI),E(_pI)),_tM,_1I);}}else{return new T3(0,new T4(0,1,E(new T3(0,_tN,_tI,_tJ)),E(_pI),E(_pI)),_tM,_1I);}}}else{var _tR=B(_tF(_tL>>1,_tH,_tI,_tJ,_tK)),_tS=_tR.a,_tT=_tR.c,_tU=E(_tR.b);if(!_tU._){return new T3(0,_tS,_1I,_tT);}else{var _tV=_tU.a,_tW=E(_tU.b);if(!_tW._){return new T3(0,new T(function(){return B(_rw(_tV,_tS));}),_1I,_tT);}else{var _tX=_tW.b,_tY=E(_tV),_tZ=E(_tY.a),_u0=E(_tW.a),_u1=_u0.b,_u2=_u0.c,_u3=E(_u0.a);if(_tZ>=_u3){if(_tZ!=_u3){return new T3(0,_tS,_1I,_tU);}else{var _u4=E(_tY.b),_u5=E(_u1);if(_u4>=_u5){if(_u4!=_u5){return new T3(0,_tS,_1I,_tU);}else{var _u6=E(_u2);if(E(_tY.c)<_u6){var _u7=B(_tF(_tL>>1,_u3,_u5,_u6,_tX));return new T3(0,new T(function(){return B(_se(_tY,_tS,_u7.a));}),_u7.b,_u7.c);}else{return new T3(0,_tS,_1I,_tU);}}}else{var _u8=B(_u9(_tL>>1,_u3,_u5,_u2,_tX));return new T3(0,new T(function(){return B(_se(_tY,_tS,_u8.a));}),_u8.b,_u8.c);}}}else{var _ua=B(_ub(_tL>>1,_u3,_u1,_u2,_tX));return new T3(0,new T(function(){return B(_se(_tY,_tS,_ua.a));}),_ua.b,_ua.c);}}}}},_u9=function(_uc,_ud,_ue,_uf,_ug){var _uh=E(_uc);if(_uh==1){var _ui=E(_ug);if(!_ui._){return new T3(0,new T4(0,1,E(new T3(0,_ud,_ue,_uf)),E(_pI),E(_pI)),_1I,_1I);}else{var _uj=E(_ud),_uk=E(_ui.a),_ul=E(_uk.a);if(_uj>=_ul){if(_uj!=_ul){return new T3(0,new T4(0,1,E(new T3(0,_uj,_ue,_uf)),E(_pI),E(_pI)),_1I,_ui);}else{var _um=E(_uk.b);if(_ue>=_um){if(_ue!=_um){return new T3(0,new T4(0,1,E(new T3(0,_uj,_ue,_uf)),E(_pI),E(_pI)),_1I,_ui);}else{var _un=E(_uf);return (_un<E(_uk.c))?new T3(0,new T4(0,1,E(new T3(0,_uj,_ue,_un)),E(_pI),E(_pI)),_ui,_1I):new T3(0,new T4(0,1,E(new T3(0,_uj,_ue,_un)),E(_pI),E(_pI)),_1I,_ui);}}else{return new T3(0,new T4(0,1,E(new T3(0,_uj,_ue,_uf)),E(_pI),E(_pI)),_ui,_1I);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_uj,_ue,_uf)),E(_pI),E(_pI)),_ui,_1I);}}}else{var _uo=B(_u9(_uh>>1,_ud,_ue,_uf,_ug)),_up=_uo.a,_uq=_uo.c,_ur=E(_uo.b);if(!_ur._){return new T3(0,_up,_1I,_uq);}else{var _us=_ur.a,_ut=E(_ur.b);if(!_ut._){return new T3(0,new T(function(){return B(_rw(_us,_up));}),_1I,_uq);}else{var _uu=_ut.b,_uv=E(_us),_uw=E(_uv.a),_ux=E(_ut.a),_uy=_ux.b,_uz=_ux.c,_uA=E(_ux.a);if(_uw>=_uA){if(_uw!=_uA){return new T3(0,_up,_1I,_ur);}else{var _uB=E(_uv.b),_uC=E(_uy);if(_uB>=_uC){if(_uB!=_uC){return new T3(0,_up,_1I,_ur);}else{var _uD=E(_uz);if(E(_uv.c)<_uD){var _uE=B(_tF(_uh>>1,_uA,_uC,_uD,_uu));return new T3(0,new T(function(){return B(_se(_uv,_up,_uE.a));}),_uE.b,_uE.c);}else{return new T3(0,_up,_1I,_ur);}}}else{var _uF=B(_u9(_uh>>1,_uA,_uC,_uz,_uu));return new T3(0,new T(function(){return B(_se(_uv,_up,_uF.a));}),_uF.b,_uF.c);}}}else{var _uG=B(_ub(_uh>>1,_uA,_uy,_uz,_uu));return new T3(0,new T(function(){return B(_se(_uv,_up,_uG.a));}),_uG.b,_uG.c);}}}}},_ub=function(_uH,_uI,_uJ,_uK,_uL){var _uM=E(_uH);if(_uM==1){var _uN=E(_uL);if(!_uN._){return new T3(0,new T4(0,1,E(new T3(0,_uI,_uJ,_uK)),E(_pI),E(_pI)),_1I,_1I);}else{var _uO=E(_uI),_uP=E(_uN.a),_uQ=E(_uP.a);if(_uO>=_uQ){if(_uO!=_uQ){return new T3(0,new T4(0,1,E(new T3(0,_uO,_uJ,_uK)),E(_pI),E(_pI)),_1I,_uN);}else{var _uR=E(_uJ),_uS=E(_uP.b);if(_uR>=_uS){if(_uR!=_uS){return new T3(0,new T4(0,1,E(new T3(0,_uO,_uR,_uK)),E(_pI),E(_pI)),_1I,_uN);}else{var _uT=E(_uK);return (_uT<E(_uP.c))?new T3(0,new T4(0,1,E(new T3(0,_uO,_uR,_uT)),E(_pI),E(_pI)),_uN,_1I):new T3(0,new T4(0,1,E(new T3(0,_uO,_uR,_uT)),E(_pI),E(_pI)),_1I,_uN);}}else{return new T3(0,new T4(0,1,E(new T3(0,_uO,_uR,_uK)),E(_pI),E(_pI)),_uN,_1I);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_uO,_uJ,_uK)),E(_pI),E(_pI)),_uN,_1I);}}}else{var _uU=B(_ub(_uM>>1,_uI,_uJ,_uK,_uL)),_uV=_uU.a,_uW=_uU.c,_uX=E(_uU.b);if(!_uX._){return new T3(0,_uV,_1I,_uW);}else{var _uY=_uX.a,_uZ=E(_uX.b);if(!_uZ._){return new T3(0,new T(function(){return B(_rw(_uY,_uV));}),_1I,_uW);}else{var _v0=_uZ.b,_v1=E(_uY),_v2=E(_v1.a),_v3=E(_uZ.a),_v4=_v3.b,_v5=_v3.c,_v6=E(_v3.a);if(_v2>=_v6){if(_v2!=_v6){return new T3(0,_uV,_1I,_uX);}else{var _v7=E(_v1.b),_v8=E(_v4);if(_v7>=_v8){if(_v7!=_v8){return new T3(0,_uV,_1I,_uX);}else{var _v9=E(_v5);if(E(_v1.c)<_v9){var _va=B(_tF(_uM>>1,_v6,_v8,_v9,_v0));return new T3(0,new T(function(){return B(_se(_v1,_uV,_va.a));}),_va.b,_va.c);}else{return new T3(0,_uV,_1I,_uX);}}}else{var _vb=B(_u9(_uM>>1,_v6,_v8,_v5,_v0));return new T3(0,new T(function(){return B(_se(_v1,_uV,_vb.a));}),_vb.b,_vb.c);}}}else{var _vc=B(_ub(_uM>>1,_v6,_v4,_v5,_v0));return new T3(0,new T(function(){return B(_se(_v1,_uV,_vc.a));}),_vc.b,_vc.c);}}}}},_vd=function(_ve,_vf,_vg,_vh,_vi){var _vj=E(_vi);if(!_vj._){var _vk=_vj.c,_vl=_vj.d,_vm=E(_vj.b),_vn=E(_vm.a);if(_ve>=_vn){if(_ve!=_vn){return new F(function(){return _qp(_vm,_vk,B(_vd(_ve,_,_vg,_vh,_vl)));});}else{var _vo=E(_vm.b);if(_vg>=_vo){if(_vg!=_vo){return new F(function(){return _qp(_vm,_vk,B(_vd(_ve,_,_vg,_vh,_vl)));});}else{var _vp=E(_vm.c);if(_vh>=_vp){if(_vh!=_vp){return new F(function(){return _qp(_vm,_vk,B(_vd(_ve,_,_vg,_vh,_vl)));});}else{return new T4(0,_vj.a,E(new T3(0,_ve,_vg,_vh)),E(_vk),E(_vl));}}else{return new F(function(){return _pN(_vm,B(_vd(_ve,_,_vg,_vh,_vk)),_vl);});}}}else{return new F(function(){return _pN(_vm,B(_vd(_ve,_,_vg,_vh,_vk)),_vl);});}}}else{return new F(function(){return _pN(_vm,B(_vd(_ve,_,_vg,_vh,_vk)),_vl);});}}else{return new T4(0,1,E(new T3(0,_ve,_vg,_vh)),E(_pI),E(_pI));}},_vq=function(_vr,_vs,_vt,_vu,_vv){var _vw=E(_vv);if(!_vw._){var _vx=_vw.c,_vy=_vw.d,_vz=E(_vw.b),_vA=E(_vz.a);if(_vr>=_vA){if(_vr!=_vA){return new F(function(){return _qp(_vz,_vx,B(_vq(_vr,_,_vt,_vu,_vy)));});}else{var _vB=E(_vz.b);if(_vt>=_vB){if(_vt!=_vB){return new F(function(){return _qp(_vz,_vx,B(_vq(_vr,_,_vt,_vu,_vy)));});}else{var _vC=E(_vu),_vD=E(_vz.c);if(_vC>=_vD){if(_vC!=_vD){return new F(function(){return _qp(_vz,_vx,B(_vd(_vr,_,_vt,_vC,_vy)));});}else{return new T4(0,_vw.a,E(new T3(0,_vr,_vt,_vC)),E(_vx),E(_vy));}}else{return new F(function(){return _pN(_vz,B(_vd(_vr,_,_vt,_vC,_vx)),_vy);});}}}else{return new F(function(){return _pN(_vz,B(_vq(_vr,_,_vt,_vu,_vx)),_vy);});}}}else{return new F(function(){return _pN(_vz,B(_vq(_vr,_,_vt,_vu,_vx)),_vy);});}}else{return new T4(0,1,E(new T3(0,_vr,_vt,_vu)),E(_pI),E(_pI));}},_vE=function(_vF,_vG,_vH,_vI,_vJ){var _vK=E(_vJ);if(!_vK._){var _vL=_vK.c,_vM=_vK.d,_vN=E(_vK.b),_vO=E(_vN.a);if(_vF>=_vO){if(_vF!=_vO){return new F(function(){return _qp(_vN,_vL,B(_vE(_vF,_,_vH,_vI,_vM)));});}else{var _vP=E(_vH),_vQ=E(_vN.b);if(_vP>=_vQ){if(_vP!=_vQ){return new F(function(){return _qp(_vN,_vL,B(_vq(_vF,_,_vP,_vI,_vM)));});}else{var _vR=E(_vI),_vS=E(_vN.c);if(_vR>=_vS){if(_vR!=_vS){return new F(function(){return _qp(_vN,_vL,B(_vd(_vF,_,_vP,_vR,_vM)));});}else{return new T4(0,_vK.a,E(new T3(0,_vF,_vP,_vR)),E(_vL),E(_vM));}}else{return new F(function(){return _pN(_vN,B(_vd(_vF,_,_vP,_vR,_vL)),_vM);});}}}else{return new F(function(){return _pN(_vN,B(_vq(_vF,_,_vP,_vI,_vL)),_vM);});}}}else{return new F(function(){return _pN(_vN,B(_vE(_vF,_,_vH,_vI,_vL)),_vM);});}}else{return new T4(0,1,E(new T3(0,_vF,_vH,_vI)),E(_pI),E(_pI));}},_vT=function(_vU,_vV,_vW,_vX){var _vY=E(_vX);if(!_vY._){var _vZ=_vY.c,_w0=_vY.d,_w1=E(_vY.b),_w2=E(_vU),_w3=E(_w1.a);if(_w2>=_w3){if(_w2!=_w3){return new F(function(){return _qp(_w1,_vZ,B(_vE(_w2,_,_vV,_vW,_w0)));});}else{var _w4=E(_vV),_w5=E(_w1.b);if(_w4>=_w5){if(_w4!=_w5){return new F(function(){return _qp(_w1,_vZ,B(_vq(_w2,_,_w4,_vW,_w0)));});}else{var _w6=E(_vW),_w7=E(_w1.c);if(_w6>=_w7){if(_w6!=_w7){return new F(function(){return _qp(_w1,_vZ,B(_vd(_w2,_,_w4,_w6,_w0)));});}else{return new T4(0,_vY.a,E(new T3(0,_w2,_w4,_w6)),E(_vZ),E(_w0));}}else{return new F(function(){return _pN(_w1,B(_vd(_w2,_,_w4,_w6,_vZ)),_w0);});}}}else{return new F(function(){return _pN(_w1,B(_vq(_w2,_,_w4,_vW,_vZ)),_w0);});}}}else{return new F(function(){return _pN(_w1,B(_vE(_w2,_,_vV,_vW,_vZ)),_w0);});}}else{return new T4(0,1,E(new T3(0,_vU,_vV,_vW)),E(_pI),E(_pI));}},_w8=function(_w9,_wa){while(1){var _wb=E(_wa);if(!_wb._){return E(_w9);}else{var _wc=E(_wb.a),_wd=B(_vT(_wc.a,_wc.b,_wc.c,_w9));_w9=_wd;_wa=_wb.b;continue;}}},_we=function(_wf,_wg,_wh,_wi,_wj){return new F(function(){return _w8(B(_vT(_wg,_wh,_wi,_wf)),_wj);});},_wk=function(_wl,_wm,_wn){var _wo=E(_wm);return new F(function(){return _w8(B(_vT(_wo.a,_wo.b,_wo.c,_wl)),_wn);});},_wp=function(_wq,_wr,_ws){var _wt=E(_ws);if(!_wt._){return E(_wr);}else{var _wu=_wt.a,_wv=E(_wt.b);if(!_wv._){return new F(function(){return _rw(_wu,_wr);});}else{var _ww=E(_wu),_wx=_ww.b,_wy=_ww.c,_wz=E(_ww.a),_wA=E(_wv.a),_wB=_wA.b,_wC=_wA.c,_wD=E(_wA.a),_wE=function(_wF){var _wG=B(_ub(_wq,_wD,_wB,_wC,_wv.b)),_wH=_wG.a,_wI=E(_wG.c);if(!_wI._){return new F(function(){return _wp(_wq<<1,B(_se(_ww,_wr,_wH)),_wG.b);});}else{return new F(function(){return _wk(B(_se(_ww,_wr,_wH)),_wI.a,_wI.b);});}};if(_wz>=_wD){if(_wz!=_wD){return new F(function(){return _we(_wr,_wz,_wx,_wy,_wv);});}else{var _wJ=E(_wx),_wK=E(_wB);if(_wJ>=_wK){if(_wJ!=_wK){return new F(function(){return _we(_wr,_wz,_wJ,_wy,_wv);});}else{var _wL=E(_wy);if(_wL<E(_wC)){return new F(function(){return _wE(_);});}else{return new F(function(){return _we(_wr,_wz,_wJ,_wL,_wv);});}}}else{return new F(function(){return _wE(_);});}}}else{return new F(function(){return _wE(_);});}}}},_wM=function(_wN,_wO,_wP,_wQ,_wR,_wS){var _wT=E(_wS);if(!_wT._){return new F(function(){return _rw(new T3(0,_wP,_wQ,_wR),_wO);});}else{var _wU=E(_wP),_wV=E(_wT.a),_wW=_wV.b,_wX=_wV.c,_wY=E(_wV.a),_wZ=function(_x0){var _x1=B(_ub(_wN,_wY,_wW,_wX,_wT.b)),_x2=_x1.a,_x3=E(_x1.c);if(!_x3._){return new F(function(){return _wp(_wN<<1,B(_se(new T3(0,_wU,_wQ,_wR),_wO,_x2)),_x1.b);});}else{return new F(function(){return _wk(B(_se(new T3(0,_wU,_wQ,_wR),_wO,_x2)),_x3.a,_x3.b);});}};if(_wU>=_wY){if(_wU!=_wY){return new F(function(){return _we(_wO,_wU,_wQ,_wR,_wT);});}else{var _x4=E(_wW);if(_wQ>=_x4){if(_wQ!=_x4){return new F(function(){return _we(_wO,_wU,_wQ,_wR,_wT);});}else{var _x5=E(_wR);if(_x5<E(_wX)){return new F(function(){return _wZ(_);});}else{return new F(function(){return _we(_wO,_wU,_wQ,_x5,_wT);});}}}else{return new F(function(){return _wZ(_);});}}}else{return new F(function(){return _wZ(_);});}}},_x6=function(_x7,_x8,_x9,_xa,_xb,_xc){var _xd=E(_xc);if(!_xd._){return new F(function(){return _rw(new T3(0,_x9,_xa,_xb),_x8);});}else{var _xe=E(_x9),_xf=E(_xd.a),_xg=_xf.b,_xh=_xf.c,_xi=E(_xf.a),_xj=function(_xk){var _xl=B(_ub(_x7,_xi,_xg,_xh,_xd.b)),_xm=_xl.a,_xn=E(_xl.c);if(!_xn._){return new F(function(){return _wp(_x7<<1,B(_se(new T3(0,_xe,_xa,_xb),_x8,_xm)),_xl.b);});}else{return new F(function(){return _wk(B(_se(new T3(0,_xe,_xa,_xb),_x8,_xm)),_xn.a,_xn.b);});}};if(_xe>=_xi){if(_xe!=_xi){return new F(function(){return _we(_x8,_xe,_xa,_xb,_xd);});}else{var _xo=E(_xg);if(_xa>=_xo){if(_xa!=_xo){return new F(function(){return _we(_x8,_xe,_xa,_xb,_xd);});}else{if(_xb<E(_xh)){return new F(function(){return _xj(_);});}else{return new F(function(){return _we(_x8,_xe,_xa,_xb,_xd);});}}}else{return new F(function(){return _xj(_);});}}}else{return new F(function(){return _xj(_);});}}},_xp=function(_xq,_xr,_xs,_xt,_xu,_xv){var _xw=E(_xv);if(!_xw._){return new F(function(){return _rw(new T3(0,_xs,_xt,_xu),_xr);});}else{var _xx=E(_xs),_xy=E(_xw.a),_xz=_xy.b,_xA=_xy.c,_xB=E(_xy.a),_xC=function(_xD){var _xE=B(_ub(_xq,_xB,_xz,_xA,_xw.b)),_xF=_xE.a,_xG=E(_xE.c);if(!_xG._){return new F(function(){return _wp(_xq<<1,B(_se(new T3(0,_xx,_xt,_xu),_xr,_xF)),_xE.b);});}else{return new F(function(){return _wk(B(_se(new T3(0,_xx,_xt,_xu),_xr,_xF)),_xG.a,_xG.b);});}};if(_xx>=_xB){if(_xx!=_xB){return new F(function(){return _we(_xr,_xx,_xt,_xu,_xw);});}else{var _xH=E(_xt),_xI=E(_xz);if(_xH>=_xI){if(_xH!=_xI){return new F(function(){return _we(_xr,_xx,_xH,_xu,_xw);});}else{var _xJ=E(_xu);if(_xJ<E(_xA)){return new F(function(){return _xC(_);});}else{return new F(function(){return _we(_xr,_xx,_xH,_xJ,_xw);});}}}else{return new F(function(){return _xC(_);});}}}else{return new F(function(){return _xC(_);});}}},_xK=function(_xL){var _xM=E(_xL);if(!_xM._){return new T0(1);}else{var _xN=_xM.a,_xO=E(_xM.b);if(!_xO._){return new T4(0,1,E(_xN),E(_pI),E(_pI));}else{var _xP=_xO.b,_xQ=E(_xN),_xR=E(_xQ.a),_xS=E(_xO.a),_xT=_xS.b,_xU=_xS.c,_xV=E(_xS.a);if(_xR>=_xV){if(_xR!=_xV){return new F(function(){return _we(new T4(0,1,E(_xQ),E(_pI),E(_pI)),_xV,_xT,_xU,_xP);});}else{var _xW=E(_xQ.b),_xX=E(_xT);if(_xW>=_xX){if(_xW!=_xX){return new F(function(){return _we(new T4(0,1,E(_xQ),E(_pI),E(_pI)),_xV,_xX,_xU,_xP);});}else{var _xY=E(_xU);if(E(_xQ.c)<_xY){return new F(function(){return _x6(1,new T4(0,1,E(_xQ),E(_pI),E(_pI)),_xV,_xX,_xY,_xP);});}else{return new F(function(){return _we(new T4(0,1,E(_xQ),E(_pI),E(_pI)),_xV,_xX,_xY,_xP);});}}}else{return new F(function(){return _wM(1,new T4(0,1,E(_xQ),E(_pI),E(_pI)),_xV,_xX,_xU,_xP);});}}}else{return new F(function(){return _xp(1,new T4(0,1,E(_xQ),E(_pI),E(_pI)),_xV,_xT,_xU,_xP);});}}}},_xZ=new T0(1),_y0=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_y1=function(_y2){return new F(function(){return err(_y0);});},_y3=new T(function(){return B(_y1(_));}),_y4=function(_y5,_y6,_y7,_y8){var _y9=E(_y7);if(!_y9._){var _ya=_y9.a,_yb=E(_y8);if(!_yb._){var _yc=_yb.a,_yd=_yb.b,_ye=_yb.c;if(_yc<=(imul(3,_ya)|0)){return new T5(0,(1+_ya|0)+_yc|0,E(_y5),_y6,E(_y9),E(_yb));}else{var _yf=E(_yb.d);if(!_yf._){var _yg=_yf.a,_yh=_yf.b,_yi=_yf.c,_yj=_yf.d,_yk=E(_yb.e);if(!_yk._){var _yl=_yk.a;if(_yg>=(imul(2,_yl)|0)){var _ym=function(_yn){var _yo=E(_y5),_yp=E(_yf.e);return (_yp._==0)?new T5(0,(1+_ya|0)+_yc|0,E(_yh),_yi,E(new T5(0,(1+_ya|0)+_yn|0,E(_yo),_y6,E(_y9),E(_yj))),E(new T5(0,(1+_yl|0)+_yp.a|0,E(_yd),_ye,E(_yp),E(_yk)))):new T5(0,(1+_ya|0)+_yc|0,E(_yh),_yi,E(new T5(0,(1+_ya|0)+_yn|0,E(_yo),_y6,E(_y9),E(_yj))),E(new T5(0,1+_yl|0,E(_yd),_ye,E(_xZ),E(_yk))));},_yq=E(_yj);if(!_yq._){return new F(function(){return _ym(_yq.a);});}else{return new F(function(){return _ym(0);});}}else{return new T5(0,(1+_ya|0)+_yc|0,E(_yd),_ye,E(new T5(0,(1+_ya|0)+_yg|0,E(_y5),_y6,E(_y9),E(_yf))),E(_yk));}}else{return E(_y3);}}else{return E(_y3);}}}else{return new T5(0,1+_ya|0,E(_y5),_y6,E(_y9),E(_xZ));}}else{var _yr=E(_y8);if(!_yr._){var _ys=_yr.a,_yt=_yr.b,_yu=_yr.c,_yv=_yr.e,_yw=E(_yr.d);if(!_yw._){var _yx=_yw.a,_yy=_yw.b,_yz=_yw.c,_yA=_yw.d,_yB=E(_yv);if(!_yB._){var _yC=_yB.a;if(_yx>=(imul(2,_yC)|0)){var _yD=function(_yE){var _yF=E(_y5),_yG=E(_yw.e);return (_yG._==0)?new T5(0,1+_ys|0,E(_yy),_yz,E(new T5(0,1+_yE|0,E(_yF),_y6,E(_xZ),E(_yA))),E(new T5(0,(1+_yC|0)+_yG.a|0,E(_yt),_yu,E(_yG),E(_yB)))):new T5(0,1+_ys|0,E(_yy),_yz,E(new T5(0,1+_yE|0,E(_yF),_y6,E(_xZ),E(_yA))),E(new T5(0,1+_yC|0,E(_yt),_yu,E(_xZ),E(_yB))));},_yH=E(_yA);if(!_yH._){return new F(function(){return _yD(_yH.a);});}else{return new F(function(){return _yD(0);});}}else{return new T5(0,1+_ys|0,E(_yt),_yu,E(new T5(0,1+_yx|0,E(_y5),_y6,E(_xZ),E(_yw))),E(_yB));}}else{return new T5(0,3,E(_yy),_yz,E(new T5(0,1,E(_y5),_y6,E(_xZ),E(_xZ))),E(new T5(0,1,E(_yt),_yu,E(_xZ),E(_xZ))));}}else{var _yI=E(_yv);return (_yI._==0)?new T5(0,3,E(_yt),_yu,E(new T5(0,1,E(_y5),_y6,E(_xZ),E(_xZ))),E(_yI)):new T5(0,2,E(_y5),_y6,E(_xZ),E(_yr));}}else{return new T5(0,1,E(_y5),_y6,E(_xZ),E(_xZ));}}},_yJ=function(_yK,_yL){return new T5(0,1,E(_yK),_yL,E(_xZ),E(_xZ));},_yM=function(_yN,_yO,_yP){var _yQ=E(_yP);if(!_yQ._){return new F(function(){return _y4(_yQ.b,_yQ.c,_yQ.d,B(_yM(_yN,_yO,_yQ.e)));});}else{return new F(function(){return _yJ(_yN,_yO);});}},_yR=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_yS=function(_yT){return new F(function(){return err(_yR);});},_yU=new T(function(){return B(_yS(_));}),_yV=function(_yW,_yX,_yY,_yZ){var _z0=E(_yZ);if(!_z0._){var _z1=_z0.a,_z2=E(_yY);if(!_z2._){var _z3=_z2.a,_z4=_z2.b,_z5=_z2.c;if(_z3<=(imul(3,_z1)|0)){return new T5(0,(1+_z3|0)+_z1|0,E(_yW),_yX,E(_z2),E(_z0));}else{var _z6=E(_z2.d);if(!_z6._){var _z7=_z6.a,_z8=E(_z2.e);if(!_z8._){var _z9=_z8.a,_za=_z8.b,_zb=_z8.c,_zc=_z8.d;if(_z9>=(imul(2,_z7)|0)){var _zd=function(_ze){var _zf=E(_z8.e);return (_zf._==0)?new T5(0,(1+_z3|0)+_z1|0,E(_za),_zb,E(new T5(0,(1+_z7|0)+_ze|0,E(_z4),_z5,E(_z6),E(_zc))),E(new T5(0,(1+_z1|0)+_zf.a|0,E(_yW),_yX,E(_zf),E(_z0)))):new T5(0,(1+_z3|0)+_z1|0,E(_za),_zb,E(new T5(0,(1+_z7|0)+_ze|0,E(_z4),_z5,E(_z6),E(_zc))),E(new T5(0,1+_z1|0,E(_yW),_yX,E(_xZ),E(_z0))));},_zg=E(_zc);if(!_zg._){return new F(function(){return _zd(_zg.a);});}else{return new F(function(){return _zd(0);});}}else{return new T5(0,(1+_z3|0)+_z1|0,E(_z4),_z5,E(_z6),E(new T5(0,(1+_z1|0)+_z9|0,E(_yW),_yX,E(_z8),E(_z0))));}}else{return E(_yU);}}else{return E(_yU);}}}else{return new T5(0,1+_z1|0,E(_yW),_yX,E(_xZ),E(_z0));}}else{var _zh=E(_yY);if(!_zh._){var _zi=_zh.a,_zj=_zh.b,_zk=_zh.c,_zl=_zh.e,_zm=E(_zh.d);if(!_zm._){var _zn=_zm.a,_zo=E(_zl);if(!_zo._){var _zp=_zo.a,_zq=_zo.b,_zr=_zo.c,_zs=_zo.d;if(_zp>=(imul(2,_zn)|0)){var _zt=function(_zu){var _zv=E(_zo.e);return (_zv._==0)?new T5(0,1+_zi|0,E(_zq),_zr,E(new T5(0,(1+_zn|0)+_zu|0,E(_zj),_zk,E(_zm),E(_zs))),E(new T5(0,1+_zv.a|0,E(_yW),_yX,E(_zv),E(_xZ)))):new T5(0,1+_zi|0,E(_zq),_zr,E(new T5(0,(1+_zn|0)+_zu|0,E(_zj),_zk,E(_zm),E(_zs))),E(new T5(0,1,E(_yW),_yX,E(_xZ),E(_xZ))));},_zw=E(_zs);if(!_zw._){return new F(function(){return _zt(_zw.a);});}else{return new F(function(){return _zt(0);});}}else{return new T5(0,1+_zi|0,E(_zj),_zk,E(_zm),E(new T5(0,1+_zp|0,E(_yW),_yX,E(_zo),E(_xZ))));}}else{return new T5(0,3,E(_zj),_zk,E(_zm),E(new T5(0,1,E(_yW),_yX,E(_xZ),E(_xZ))));}}else{var _zx=E(_zl);return (_zx._==0)?new T5(0,3,E(_zx.b),_zx.c,E(new T5(0,1,E(_zj),_zk,E(_xZ),E(_xZ))),E(new T5(0,1,E(_yW),_yX,E(_xZ),E(_xZ)))):new T5(0,2,E(_yW),_yX,E(_zh),E(_xZ));}}else{return new T5(0,1,E(_yW),_yX,E(_xZ),E(_xZ));}}},_zy=function(_zz,_zA,_zB){var _zC=E(_zB);if(!_zC._){return new F(function(){return _yV(_zC.b,_zC.c,B(_zy(_zz,_zA,_zC.d)),_zC.e);});}else{return new F(function(){return _yJ(_zz,_zA);});}},_zD=function(_zE,_zF,_zG,_zH,_zI,_zJ,_zK){return new F(function(){return _yV(_zH,_zI,B(_zy(_zE,_zF,_zJ)),_zK);});},_zL=function(_zM,_zN,_zO,_zP,_zQ,_zR,_zS,_zT){var _zU=E(_zO);if(!_zU._){var _zV=_zU.a,_zW=_zU.b,_zX=_zU.c,_zY=_zU.d,_zZ=_zU.e;if((imul(3,_zV)|0)>=_zP){if((imul(3,_zP)|0)>=_zV){return new T5(0,(_zV+_zP|0)+1|0,E(_zM),_zN,E(_zU),E(new T5(0,_zP,E(_zQ),_zR,E(_zS),E(_zT))));}else{return new F(function(){return _y4(_zW,_zX,_zY,B(_zL(_zM,_zN,_zZ,_zP,_zQ,_zR,_zS,_zT)));});}}else{return new F(function(){return _yV(_zQ,_zR,B(_A0(_zM,_zN,_zV,_zW,_zX,_zY,_zZ,_zS)),_zT);});}}else{return new F(function(){return _zD(_zM,_zN,_zP,_zQ,_zR,_zS,_zT);});}},_A0=function(_A1,_A2,_A3,_A4,_A5,_A6,_A7,_A8){var _A9=E(_A8);if(!_A9._){var _Aa=_A9.a,_Ab=_A9.b,_Ac=_A9.c,_Ad=_A9.d,_Ae=_A9.e;if((imul(3,_A3)|0)>=_Aa){if((imul(3,_Aa)|0)>=_A3){return new T5(0,(_A3+_Aa|0)+1|0,E(_A1),_A2,E(new T5(0,_A3,E(_A4),_A5,E(_A6),E(_A7))),E(_A9));}else{return new F(function(){return _y4(_A4,_A5,_A6,B(_zL(_A1,_A2,_A7,_Aa,_Ab,_Ac,_Ad,_Ae)));});}}else{return new F(function(){return _yV(_Ab,_Ac,B(_A0(_A1,_A2,_A3,_A4,_A5,_A6,_A7,_Ad)),_Ae);});}}else{return new F(function(){return _yM(_A1,_A2,new T5(0,_A3,E(_A4),_A5,E(_A6),E(_A7)));});}},_Af=function(_Ag,_Ah,_Ai,_Aj){var _Ak=E(_Ai);if(!_Ak._){var _Al=_Ak.a,_Am=_Ak.b,_An=_Ak.c,_Ao=_Ak.d,_Ap=_Ak.e,_Aq=E(_Aj);if(!_Aq._){var _Ar=_Aq.a,_As=_Aq.b,_At=_Aq.c,_Au=_Aq.d,_Av=_Aq.e;if((imul(3,_Al)|0)>=_Ar){if((imul(3,_Ar)|0)>=_Al){return new T5(0,(_Al+_Ar|0)+1|0,E(_Ag),_Ah,E(_Ak),E(_Aq));}else{return new F(function(){return _y4(_Am,_An,_Ao,B(_zL(_Ag,_Ah,_Ap,_Ar,_As,_At,_Au,_Av)));});}}else{return new F(function(){return _yV(_As,_At,B(_A0(_Ag,_Ah,_Al,_Am,_An,_Ao,_Ap,_Au)),_Av);});}}else{return new F(function(){return _yM(_Ag,_Ah,_Ak);});}}else{return new F(function(){return _zy(_Ag,_Ah,_Aj);});}},_Aw=function(_Ax,_Ay,_Az,_AA,_AB){var _AC=E(_Ax);if(_AC==1){var _AD=E(_AB);if(!_AD._){return new T3(0,new T5(0,1,E(new T2(0,_Ay,_Az)),_AA,E(_xZ),E(_xZ)),_1I,_1I);}else{var _AE=E(E(_AD.a).a),_AF=E(_Ay),_AG=E(_AE.a);return (_AF>=_AG)?(_AF!=_AG)?new T3(0,new T5(0,1,E(new T2(0,_AF,_Az)),_AA,E(_xZ),E(_xZ)),_1I,_AD):(_Az<E(_AE.b))?new T3(0,new T5(0,1,E(new T2(0,_AF,_Az)),_AA,E(_xZ),E(_xZ)),_AD,_1I):new T3(0,new T5(0,1,E(new T2(0,_AF,_Az)),_AA,E(_xZ),E(_xZ)),_1I,_AD):new T3(0,new T5(0,1,E(new T2(0,_AF,_Az)),_AA,E(_xZ),E(_xZ)),_AD,_1I);}}else{var _AH=B(_Aw(_AC>>1,_Ay,_Az,_AA,_AB)),_AI=_AH.a,_AJ=_AH.c,_AK=E(_AH.b);if(!_AK._){return new T3(0,_AI,_1I,_AJ);}else{var _AL=E(_AK.a),_AM=_AL.a,_AN=_AL.b,_AO=E(_AK.b);if(!_AO._){return new T3(0,new T(function(){return B(_yM(_AM,_AN,_AI));}),_1I,_AJ);}else{var _AP=_AO.b,_AQ=E(_AO.a),_AR=_AQ.b,_AS=E(_AM),_AT=E(_AQ.a),_AU=_AT.b,_AV=E(_AS.a),_AW=E(_AT.a);if(_AV>=_AW){if(_AV!=_AW){return new T3(0,_AI,_1I,_AK);}else{var _AX=E(_AU);if(E(_AS.b)<_AX){var _AY=B(_Aw(_AC>>1,_AW,_AX,_AR,_AP));return new T3(0,new T(function(){return B(_Af(_AS,_AN,_AI,_AY.a));}),_AY.b,_AY.c);}else{return new T3(0,_AI,_1I,_AK);}}}else{var _AZ=B(_B0(_AC>>1,_AW,_AU,_AR,_AP));return new T3(0,new T(function(){return B(_Af(_AS,_AN,_AI,_AZ.a));}),_AZ.b,_AZ.c);}}}}},_B0=function(_B1,_B2,_B3,_B4,_B5){var _B6=E(_B1);if(_B6==1){var _B7=E(_B5);if(!_B7._){return new T3(0,new T5(0,1,E(new T2(0,_B2,_B3)),_B4,E(_xZ),E(_xZ)),_1I,_1I);}else{var _B8=E(E(_B7.a).a),_B9=E(_B2),_Ba=E(_B8.a);if(_B9>=_Ba){if(_B9!=_Ba){return new T3(0,new T5(0,1,E(new T2(0,_B9,_B3)),_B4,E(_xZ),E(_xZ)),_1I,_B7);}else{var _Bb=E(_B3);return (_Bb<E(_B8.b))?new T3(0,new T5(0,1,E(new T2(0,_B9,_Bb)),_B4,E(_xZ),E(_xZ)),_B7,_1I):new T3(0,new T5(0,1,E(new T2(0,_B9,_Bb)),_B4,E(_xZ),E(_xZ)),_1I,_B7);}}else{return new T3(0,new T5(0,1,E(new T2(0,_B9,_B3)),_B4,E(_xZ),E(_xZ)),_B7,_1I);}}}else{var _Bc=B(_B0(_B6>>1,_B2,_B3,_B4,_B5)),_Bd=_Bc.a,_Be=_Bc.c,_Bf=E(_Bc.b);if(!_Bf._){return new T3(0,_Bd,_1I,_Be);}else{var _Bg=E(_Bf.a),_Bh=_Bg.a,_Bi=_Bg.b,_Bj=E(_Bf.b);if(!_Bj._){return new T3(0,new T(function(){return B(_yM(_Bh,_Bi,_Bd));}),_1I,_Be);}else{var _Bk=_Bj.b,_Bl=E(_Bj.a),_Bm=_Bl.b,_Bn=E(_Bh),_Bo=E(_Bl.a),_Bp=_Bo.b,_Bq=E(_Bn.a),_Br=E(_Bo.a);if(_Bq>=_Br){if(_Bq!=_Br){return new T3(0,_Bd,_1I,_Bf);}else{var _Bs=E(_Bp);if(E(_Bn.b)<_Bs){var _Bt=B(_Aw(_B6>>1,_Br,_Bs,_Bm,_Bk));return new T3(0,new T(function(){return B(_Af(_Bn,_Bi,_Bd,_Bt.a));}),_Bt.b,_Bt.c);}else{return new T3(0,_Bd,_1I,_Bf);}}}else{var _Bu=B(_B0(_B6>>1,_Br,_Bp,_Bm,_Bk));return new T3(0,new T(function(){return B(_Af(_Bn,_Bi,_Bd,_Bu.a));}),_Bu.b,_Bu.c);}}}}},_Bv=function(_Bw,_Bx,_By,_Bz,_BA){var _BB=E(_BA);if(!_BB._){var _BC=_BB.c,_BD=_BB.d,_BE=_BB.e,_BF=E(_BB.b),_BG=E(_BF.a);if(_Bw>=_BG){if(_Bw!=_BG){return new F(function(){return _y4(_BF,_BC,_BD,B(_Bv(_Bw,_,_By,_Bz,_BE)));});}else{var _BH=E(_BF.b);if(_By>=_BH){if(_By!=_BH){return new F(function(){return _y4(_BF,_BC,_BD,B(_Bv(_Bw,_,_By,_Bz,_BE)));});}else{return new T5(0,_BB.a,E(new T2(0,_Bw,_By)),_Bz,E(_BD),E(_BE));}}else{return new F(function(){return _yV(_BF,_BC,B(_Bv(_Bw,_,_By,_Bz,_BD)),_BE);});}}}else{return new F(function(){return _yV(_BF,_BC,B(_Bv(_Bw,_,_By,_Bz,_BD)),_BE);});}}else{return new T5(0,1,E(new T2(0,_Bw,_By)),_Bz,E(_xZ),E(_xZ));}},_BI=function(_BJ,_BK,_BL,_BM,_BN){var _BO=E(_BN);if(!_BO._){var _BP=_BO.c,_BQ=_BO.d,_BR=_BO.e,_BS=E(_BO.b),_BT=E(_BS.a);if(_BJ>=_BT){if(_BJ!=_BT){return new F(function(){return _y4(_BS,_BP,_BQ,B(_BI(_BJ,_,_BL,_BM,_BR)));});}else{var _BU=E(_BL),_BV=E(_BS.b);if(_BU>=_BV){if(_BU!=_BV){return new F(function(){return _y4(_BS,_BP,_BQ,B(_Bv(_BJ,_,_BU,_BM,_BR)));});}else{return new T5(0,_BO.a,E(new T2(0,_BJ,_BU)),_BM,E(_BQ),E(_BR));}}else{return new F(function(){return _yV(_BS,_BP,B(_Bv(_BJ,_,_BU,_BM,_BQ)),_BR);});}}}else{return new F(function(){return _yV(_BS,_BP,B(_BI(_BJ,_,_BL,_BM,_BQ)),_BR);});}}else{return new T5(0,1,E(new T2(0,_BJ,_BL)),_BM,E(_xZ),E(_xZ));}},_BW=function(_BX,_BY,_BZ,_C0){var _C1=E(_C0);if(!_C1._){var _C2=_C1.c,_C3=_C1.d,_C4=_C1.e,_C5=E(_C1.b),_C6=E(_BX),_C7=E(_C5.a);if(_C6>=_C7){if(_C6!=_C7){return new F(function(){return _y4(_C5,_C2,_C3,B(_BI(_C6,_,_BY,_BZ,_C4)));});}else{var _C8=E(_BY),_C9=E(_C5.b);if(_C8>=_C9){if(_C8!=_C9){return new F(function(){return _y4(_C5,_C2,_C3,B(_Bv(_C6,_,_C8,_BZ,_C4)));});}else{return new T5(0,_C1.a,E(new T2(0,_C6,_C8)),_BZ,E(_C3),E(_C4));}}else{return new F(function(){return _yV(_C5,_C2,B(_Bv(_C6,_,_C8,_BZ,_C3)),_C4);});}}}else{return new F(function(){return _yV(_C5,_C2,B(_BI(_C6,_,_BY,_BZ,_C3)),_C4);});}}else{return new T5(0,1,E(new T2(0,_BX,_BY)),_BZ,E(_xZ),E(_xZ));}},_Ca=function(_Cb,_Cc){while(1){var _Cd=E(_Cc);if(!_Cd._){return E(_Cb);}else{var _Ce=E(_Cd.a),_Cf=E(_Ce.a),_Cg=B(_BW(_Cf.a,_Cf.b,_Ce.b,_Cb));_Cb=_Cg;_Cc=_Cd.b;continue;}}},_Ch=function(_Ci,_Cj,_Ck,_Cl,_Cm){return new F(function(){return _Ca(B(_BW(_Cj,_Ck,_Cl,_Ci)),_Cm);});},_Cn=function(_Co,_Cp,_Cq){var _Cr=E(_Cp),_Cs=E(_Cr.a);return new F(function(){return _Ca(B(_BW(_Cs.a,_Cs.b,_Cr.b,_Co)),_Cq);});},_Ct=function(_Cu,_Cv,_Cw){var _Cx=E(_Cw);if(!_Cx._){return E(_Cv);}else{var _Cy=E(_Cx.a),_Cz=_Cy.a,_CA=_Cy.b,_CB=E(_Cx.b);if(!_CB._){return new F(function(){return _yM(_Cz,_CA,_Cv);});}else{var _CC=E(_CB.a),_CD=E(_Cz),_CE=_CD.b,_CF=E(_CC.a),_CG=_CF.b,_CH=E(_CD.a),_CI=E(_CF.a),_CJ=function(_CK){var _CL=B(_B0(_Cu,_CI,_CG,_CC.b,_CB.b)),_CM=_CL.a,_CN=E(_CL.c);if(!_CN._){return new F(function(){return _Ct(_Cu<<1,B(_Af(_CD,_CA,_Cv,_CM)),_CL.b);});}else{return new F(function(){return _Cn(B(_Af(_CD,_CA,_Cv,_CM)),_CN.a,_CN.b);});}};if(_CH>=_CI){if(_CH!=_CI){return new F(function(){return _Ch(_Cv,_CH,_CE,_CA,_CB);});}else{var _CO=E(_CE);if(_CO<E(_CG)){return new F(function(){return _CJ(_);});}else{return new F(function(){return _Ch(_Cv,_CH,_CO,_CA,_CB);});}}}else{return new F(function(){return _CJ(_);});}}}},_CP=function(_CQ,_CR,_CS,_CT,_CU,_CV){var _CW=E(_CV);if(!_CW._){return new F(function(){return _yM(new T2(0,_CS,_CT),_CU,_CR);});}else{var _CX=E(_CW.a),_CY=E(_CX.a),_CZ=_CY.b,_D0=E(_CS),_D1=E(_CY.a),_D2=function(_D3){var _D4=B(_B0(_CQ,_D1,_CZ,_CX.b,_CW.b)),_D5=_D4.a,_D6=E(_D4.c);if(!_D6._){return new F(function(){return _Ct(_CQ<<1,B(_Af(new T2(0,_D0,_CT),_CU,_CR,_D5)),_D4.b);});}else{return new F(function(){return _Cn(B(_Af(new T2(0,_D0,_CT),_CU,_CR,_D5)),_D6.a,_D6.b);});}};if(_D0>=_D1){if(_D0!=_D1){return new F(function(){return _Ch(_CR,_D0,_CT,_CU,_CW);});}else{if(_CT<E(_CZ)){return new F(function(){return _D2(_);});}else{return new F(function(){return _Ch(_CR,_D0,_CT,_CU,_CW);});}}}else{return new F(function(){return _D2(_);});}}},_D7=function(_D8,_D9,_Da,_Db,_Dc,_Dd){var _De=E(_Dd);if(!_De._){return new F(function(){return _yM(new T2(0,_Da,_Db),_Dc,_D9);});}else{var _Df=E(_De.a),_Dg=E(_Df.a),_Dh=_Dg.b,_Di=E(_Da),_Dj=E(_Dg.a),_Dk=function(_Dl){var _Dm=B(_B0(_D8,_Dj,_Dh,_Df.b,_De.b)),_Dn=_Dm.a,_Do=E(_Dm.c);if(!_Do._){return new F(function(){return _Ct(_D8<<1,B(_Af(new T2(0,_Di,_Db),_Dc,_D9,_Dn)),_Dm.b);});}else{return new F(function(){return _Cn(B(_Af(new T2(0,_Di,_Db),_Dc,_D9,_Dn)),_Do.a,_Do.b);});}};if(_Di>=_Dj){if(_Di!=_Dj){return new F(function(){return _Ch(_D9,_Di,_Db,_Dc,_De);});}else{var _Dp=E(_Db);if(_Dp<E(_Dh)){return new F(function(){return _Dk(_);});}else{return new F(function(){return _Ch(_D9,_Di,_Dp,_Dc,_De);});}}}else{return new F(function(){return _Dk(_);});}}},_Dq=function(_Dr){var _Ds=E(_Dr);if(!_Ds._){return new T0(1);}else{var _Dt=E(_Ds.a),_Du=_Dt.a,_Dv=_Dt.b,_Dw=E(_Ds.b);if(!_Dw._){return new T5(0,1,E(_Du),_Dv,E(_xZ),E(_xZ));}else{var _Dx=_Dw.b,_Dy=E(_Dw.a),_Dz=_Dy.b,_DA=E(_Du),_DB=E(_Dy.a),_DC=_DB.b,_DD=E(_DA.a),_DE=E(_DB.a);if(_DD>=_DE){if(_DD!=_DE){return new F(function(){return _Ch(new T5(0,1,E(_DA),_Dv,E(_xZ),E(_xZ)),_DE,_DC,_Dz,_Dx);});}else{var _DF=E(_DC);if(E(_DA.b)<_DF){return new F(function(){return _CP(1,new T5(0,1,E(_DA),_Dv,E(_xZ),E(_xZ)),_DE,_DF,_Dz,_Dx);});}else{return new F(function(){return _Ch(new T5(0,1,E(_DA),_Dv,E(_xZ),E(_xZ)),_DE,_DF,_Dz,_Dx);});}}}else{return new F(function(){return _D7(1,new T5(0,1,E(_DA),_Dv,E(_xZ),E(_xZ)),_DE,_DC,_Dz,_Dx);});}}}},_DG=function(_DH,_DI,_DJ,_DK,_DL){var _DM=E(_DH);if(_DM==1){var _DN=E(_DL);if(!_DN._){return new T3(0,new T5(0,1,E(new T2(0,_DI,_DJ)),_DK,E(_xZ),E(_xZ)),_1I,_1I);}else{var _DO=E(E(_DN.a).a),_DP=E(_DI),_DQ=E(_DO.a);return (_DP>=_DQ)?(_DP!=_DQ)?new T3(0,new T5(0,1,E(new T2(0,_DP,_DJ)),_DK,E(_xZ),E(_xZ)),_1I,_DN):(_DJ<E(_DO.b))?new T3(0,new T5(0,1,E(new T2(0,_DP,_DJ)),_DK,E(_xZ),E(_xZ)),_DN,_1I):new T3(0,new T5(0,1,E(new T2(0,_DP,_DJ)),_DK,E(_xZ),E(_xZ)),_1I,_DN):new T3(0,new T5(0,1,E(new T2(0,_DP,_DJ)),_DK,E(_xZ),E(_xZ)),_DN,_1I);}}else{var _DR=B(_DG(_DM>>1,_DI,_DJ,_DK,_DL)),_DS=_DR.a,_DT=_DR.c,_DU=E(_DR.b);if(!_DU._){return new T3(0,_DS,_1I,_DT);}else{var _DV=E(_DU.a),_DW=_DV.a,_DX=_DV.b,_DY=E(_DU.b);if(!_DY._){return new T3(0,new T(function(){return B(_yM(_DW,_DX,_DS));}),_1I,_DT);}else{var _DZ=_DY.b,_E0=E(_DY.a),_E1=_E0.b,_E2=E(_DW),_E3=E(_E0.a),_E4=_E3.b,_E5=E(_E2.a),_E6=E(_E3.a);if(_E5>=_E6){if(_E5!=_E6){return new T3(0,_DS,_1I,_DU);}else{var _E7=E(_E4);if(E(_E2.b)<_E7){var _E8=B(_DG(_DM>>1,_E6,_E7,_E1,_DZ));return new T3(0,new T(function(){return B(_Af(_E2,_DX,_DS,_E8.a));}),_E8.b,_E8.c);}else{return new T3(0,_DS,_1I,_DU);}}}else{var _E9=B(_Ea(_DM>>1,_E6,_E4,_E1,_DZ));return new T3(0,new T(function(){return B(_Af(_E2,_DX,_DS,_E9.a));}),_E9.b,_E9.c);}}}}},_Ea=function(_Eb,_Ec,_Ed,_Ee,_Ef){var _Eg=E(_Eb);if(_Eg==1){var _Eh=E(_Ef);if(!_Eh._){return new T3(0,new T5(0,1,E(new T2(0,_Ec,_Ed)),_Ee,E(_xZ),E(_xZ)),_1I,_1I);}else{var _Ei=E(E(_Eh.a).a),_Ej=E(_Ec),_Ek=E(_Ei.a);if(_Ej>=_Ek){if(_Ej!=_Ek){return new T3(0,new T5(0,1,E(new T2(0,_Ej,_Ed)),_Ee,E(_xZ),E(_xZ)),_1I,_Eh);}else{var _El=E(_Ed);return (_El<E(_Ei.b))?new T3(0,new T5(0,1,E(new T2(0,_Ej,_El)),_Ee,E(_xZ),E(_xZ)),_Eh,_1I):new T3(0,new T5(0,1,E(new T2(0,_Ej,_El)),_Ee,E(_xZ),E(_xZ)),_1I,_Eh);}}else{return new T3(0,new T5(0,1,E(new T2(0,_Ej,_Ed)),_Ee,E(_xZ),E(_xZ)),_Eh,_1I);}}}else{var _Em=B(_Ea(_Eg>>1,_Ec,_Ed,_Ee,_Ef)),_En=_Em.a,_Eo=_Em.c,_Ep=E(_Em.b);if(!_Ep._){return new T3(0,_En,_1I,_Eo);}else{var _Eq=E(_Ep.a),_Er=_Eq.a,_Es=_Eq.b,_Et=E(_Ep.b);if(!_Et._){return new T3(0,new T(function(){return B(_yM(_Er,_Es,_En));}),_1I,_Eo);}else{var _Eu=_Et.b,_Ev=E(_Et.a),_Ew=_Ev.b,_Ex=E(_Er),_Ey=E(_Ev.a),_Ez=_Ey.b,_EA=E(_Ex.a),_EB=E(_Ey.a);if(_EA>=_EB){if(_EA!=_EB){return new T3(0,_En,_1I,_Ep);}else{var _EC=E(_Ez);if(E(_Ex.b)<_EC){var _ED=B(_DG(_Eg>>1,_EB,_EC,_Ew,_Eu));return new T3(0,new T(function(){return B(_Af(_Ex,_Es,_En,_ED.a));}),_ED.b,_ED.c);}else{return new T3(0,_En,_1I,_Ep);}}}else{var _EE=B(_Ea(_Eg>>1,_EB,_Ez,_Ew,_Eu));return new T3(0,new T(function(){return B(_Af(_Ex,_Es,_En,_EE.a));}),_EE.b,_EE.c);}}}}},_EF=function(_EG,_EH,_EI,_EJ,_EK){var _EL=E(_EK);if(!_EL._){var _EM=_EL.c,_EN=_EL.d,_EO=_EL.e,_EP=E(_EL.b),_EQ=E(_EP.a);if(_EG>=_EQ){if(_EG!=_EQ){return new F(function(){return _y4(_EP,_EM,_EN,B(_EF(_EG,_,_EI,_EJ,_EO)));});}else{var _ER=E(_EP.b);if(_EI>=_ER){if(_EI!=_ER){return new F(function(){return _y4(_EP,_EM,_EN,B(_EF(_EG,_,_EI,_EJ,_EO)));});}else{return new T5(0,_EL.a,E(new T2(0,_EG,_EI)),_EJ,E(_EN),E(_EO));}}else{return new F(function(){return _yV(_EP,_EM,B(_EF(_EG,_,_EI,_EJ,_EN)),_EO);});}}}else{return new F(function(){return _yV(_EP,_EM,B(_EF(_EG,_,_EI,_EJ,_EN)),_EO);});}}else{return new T5(0,1,E(new T2(0,_EG,_EI)),_EJ,E(_xZ),E(_xZ));}},_ES=function(_ET,_EU,_EV,_EW,_EX){var _EY=E(_EX);if(!_EY._){var _EZ=_EY.c,_F0=_EY.d,_F1=_EY.e,_F2=E(_EY.b),_F3=E(_F2.a);if(_ET>=_F3){if(_ET!=_F3){return new F(function(){return _y4(_F2,_EZ,_F0,B(_ES(_ET,_,_EV,_EW,_F1)));});}else{var _F4=E(_EV),_F5=E(_F2.b);if(_F4>=_F5){if(_F4!=_F5){return new F(function(){return _y4(_F2,_EZ,_F0,B(_EF(_ET,_,_F4,_EW,_F1)));});}else{return new T5(0,_EY.a,E(new T2(0,_ET,_F4)),_EW,E(_F0),E(_F1));}}else{return new F(function(){return _yV(_F2,_EZ,B(_EF(_ET,_,_F4,_EW,_F0)),_F1);});}}}else{return new F(function(){return _yV(_F2,_EZ,B(_ES(_ET,_,_EV,_EW,_F0)),_F1);});}}else{return new T5(0,1,E(new T2(0,_ET,_EV)),_EW,E(_xZ),E(_xZ));}},_F6=function(_F7,_F8,_F9,_Fa){var _Fb=E(_Fa);if(!_Fb._){var _Fc=_Fb.c,_Fd=_Fb.d,_Fe=_Fb.e,_Ff=E(_Fb.b),_Fg=E(_F7),_Fh=E(_Ff.a);if(_Fg>=_Fh){if(_Fg!=_Fh){return new F(function(){return _y4(_Ff,_Fc,_Fd,B(_ES(_Fg,_,_F8,_F9,_Fe)));});}else{var _Fi=E(_F8),_Fj=E(_Ff.b);if(_Fi>=_Fj){if(_Fi!=_Fj){return new F(function(){return _y4(_Ff,_Fc,_Fd,B(_EF(_Fg,_,_Fi,_F9,_Fe)));});}else{return new T5(0,_Fb.a,E(new T2(0,_Fg,_Fi)),_F9,E(_Fd),E(_Fe));}}else{return new F(function(){return _yV(_Ff,_Fc,B(_EF(_Fg,_,_Fi,_F9,_Fd)),_Fe);});}}}else{return new F(function(){return _yV(_Ff,_Fc,B(_ES(_Fg,_,_F8,_F9,_Fd)),_Fe);});}}else{return new T5(0,1,E(new T2(0,_F7,_F8)),_F9,E(_xZ),E(_xZ));}},_Fk=function(_Fl,_Fm){while(1){var _Fn=E(_Fm);if(!_Fn._){return E(_Fl);}else{var _Fo=E(_Fn.a),_Fp=E(_Fo.a),_Fq=B(_F6(_Fp.a,_Fp.b,_Fo.b,_Fl));_Fl=_Fq;_Fm=_Fn.b;continue;}}},_Fr=function(_Fs,_Ft,_Fu,_Fv,_Fw){return new F(function(){return _Fk(B(_F6(_Ft,_Fu,_Fv,_Fs)),_Fw);});},_Fx=function(_Fy,_Fz,_FA){var _FB=E(_Fz),_FC=E(_FB.a);return new F(function(){return _Fk(B(_F6(_FC.a,_FC.b,_FB.b,_Fy)),_FA);});},_FD=function(_FE,_FF,_FG){var _FH=E(_FG);if(!_FH._){return E(_FF);}else{var _FI=E(_FH.a),_FJ=_FI.a,_FK=_FI.b,_FL=E(_FH.b);if(!_FL._){return new F(function(){return _yM(_FJ,_FK,_FF);});}else{var _FM=E(_FL.a),_FN=E(_FJ),_FO=_FN.b,_FP=E(_FM.a),_FQ=_FP.b,_FR=E(_FN.a),_FS=E(_FP.a),_FT=function(_FU){var _FV=B(_Ea(_FE,_FS,_FQ,_FM.b,_FL.b)),_FW=_FV.a,_FX=E(_FV.c);if(!_FX._){return new F(function(){return _FD(_FE<<1,B(_Af(_FN,_FK,_FF,_FW)),_FV.b);});}else{return new F(function(){return _Fx(B(_Af(_FN,_FK,_FF,_FW)),_FX.a,_FX.b);});}};if(_FR>=_FS){if(_FR!=_FS){return new F(function(){return _Fr(_FF,_FR,_FO,_FK,_FL);});}else{var _FY=E(_FO);if(_FY<E(_FQ)){return new F(function(){return _FT(_);});}else{return new F(function(){return _Fr(_FF,_FR,_FY,_FK,_FL);});}}}else{return new F(function(){return _FT(_);});}}}},_FZ=function(_G0,_G1,_G2,_G3,_G4,_G5){var _G6=E(_G5);if(!_G6._){return new F(function(){return _yM(new T2(0,_G2,_G3),_G4,_G1);});}else{var _G7=E(_G6.a),_G8=E(_G7.a),_G9=_G8.b,_Ga=E(_G2),_Gb=E(_G8.a),_Gc=function(_Gd){var _Ge=B(_Ea(_G0,_Gb,_G9,_G7.b,_G6.b)),_Gf=_Ge.a,_Gg=E(_Ge.c);if(!_Gg._){return new F(function(){return _FD(_G0<<1,B(_Af(new T2(0,_Ga,_G3),_G4,_G1,_Gf)),_Ge.b);});}else{return new F(function(){return _Fx(B(_Af(new T2(0,_Ga,_G3),_G4,_G1,_Gf)),_Gg.a,_Gg.b);});}};if(_Ga>=_Gb){if(_Ga!=_Gb){return new F(function(){return _Fr(_G1,_Ga,_G3,_G4,_G6);});}else{var _Gh=E(_G3);if(_Gh<E(_G9)){return new F(function(){return _Gc(_);});}else{return new F(function(){return _Fr(_G1,_Ga,_Gh,_G4,_G6);});}}}else{return new F(function(){return _Gc(_);});}}},_Gi=function(_Gj,_Gk,_Gl,_Gm,_Gn,_Go){var _Gp=E(_Go);if(!_Gp._){return new F(function(){return _yM(new T2(0,_Gl,_Gm),_Gn,_Gk);});}else{var _Gq=E(_Gp.a),_Gr=E(_Gq.a),_Gs=_Gr.b,_Gt=E(_Gl),_Gu=E(_Gr.a),_Gv=function(_Gw){var _Gx=B(_Ea(_Gj,_Gu,_Gs,_Gq.b,_Gp.b)),_Gy=_Gx.a,_Gz=E(_Gx.c);if(!_Gz._){return new F(function(){return _FD(_Gj<<1,B(_Af(new T2(0,_Gt,_Gm),_Gn,_Gk,_Gy)),_Gx.b);});}else{return new F(function(){return _Fx(B(_Af(new T2(0,_Gt,_Gm),_Gn,_Gk,_Gy)),_Gz.a,_Gz.b);});}};if(_Gt>=_Gu){if(_Gt!=_Gu){return new F(function(){return _Fr(_Gk,_Gt,_Gm,_Gn,_Gp);});}else{if(_Gm<E(_Gs)){return new F(function(){return _Gv(_);});}else{return new F(function(){return _Fr(_Gk,_Gt,_Gm,_Gn,_Gp);});}}}else{return new F(function(){return _Gv(_);});}}},_GA=function(_GB){var _GC=E(_GB);if(!_GC._){return new T0(1);}else{var _GD=E(_GC.a),_GE=_GD.a,_GF=_GD.b,_GG=E(_GC.b);if(!_GG._){return new T5(0,1,E(_GE),_GF,E(_xZ),E(_xZ));}else{var _GH=_GG.b,_GI=E(_GG.a),_GJ=_GI.b,_GK=E(_GE),_GL=E(_GI.a),_GM=_GL.b,_GN=E(_GK.a),_GO=E(_GL.a);if(_GN>=_GO){if(_GN!=_GO){return new F(function(){return _Fr(new T5(0,1,E(_GK),_GF,E(_xZ),E(_xZ)),_GO,_GM,_GJ,_GH);});}else{var _GP=E(_GM);if(E(_GK.b)<_GP){return new F(function(){return _Gi(1,new T5(0,1,E(_GK),_GF,E(_xZ),E(_xZ)),_GO,_GP,_GJ,_GH);});}else{return new F(function(){return _Fr(new T5(0,1,E(_GK),_GF,E(_xZ),E(_xZ)),_GO,_GP,_GJ,_GH);});}}}else{return new F(function(){return _FZ(1,new T5(0,1,E(_GK),_GF,E(_xZ),E(_xZ)),_GO,_GM,_GJ,_GH);});}}}},_GQ=function(_GR,_GS){while(1){var _GT=B((function(_GU,_GV){var _GW=E(_GV);if(!_GW._){_GR=new T2(1,new T2(0,_GW.b,_GW.c),new T(function(){return B(_GQ(_GU,_GW.e));}));_GS=_GW.d;return __continue;}else{return E(_GU);}})(_GR,_GS));if(_GT!=__continue){return _GT;}}},_GX=function(_GY,_GZ,_H0){return new F(function(){return A1(_GY,new T2(1,_2n,new T(function(){return B(A1(_GZ,_H0));})));});},_H1=new T(function(){return B(unCStr("CC "));}),_H2=function(_H3,_H4,_H5,_H6,_H7,_H8){var _H9=function(_Ha){var _Hb=new T(function(){var _Hc=new T(function(){return B(_c(11,E(_H6),new T2(1,_u,new T(function(){return B(_c(11,E(_H7),_Ha));}))));});return B(_c(11,E(_H5),new T2(1,_u,_Hc)));});return new F(function(){return _S(11,_H4,new T2(1,_u,_Hb));});};if(_H3<11){return new F(function(){return _2(_H1,new T(function(){return B(_H9(_H8));},1));});}else{var _Hd=new T(function(){return B(_2(_H1,new T(function(){return B(_H9(new T2(1,_a,_H8)));},1)));});return new T2(1,_b,_Hd);}},_He=function(_Hf,_Hg){var _Hh=E(_Hf);return new F(function(){return _H2(0,_Hh.a,_Hh.b,_Hh.c,_Hh.d,_Hg);});},_Hi=new T(function(){return B(unCStr("RC "));}),_Hj=function(_Hk,_Hl,_Hm,_Hn,_Ho){var _Hp=function(_Hq){var _Hr=new T(function(){var _Hs=new T(function(){return B(_c(11,E(_Hm),new T2(1,_u,new T(function(){return B(_c(11,E(_Hn),_Hq));}))));});return B(_S(11,_Hl,new T2(1,_u,_Hs)));},1);return new F(function(){return _2(_Hi,_Hr);});};if(_Hk<11){return new F(function(){return _Hp(_Ho);});}else{return new T2(1,_b,new T(function(){return B(_Hp(new T2(1,_a,_Ho)));}));}},_Ht=function(_Hu,_Hv){var _Hw=E(_Hu);return new F(function(){return _Hj(0,_Hw.a,_Hw.b,_Hw.c,_Hv);});},_Hx=new T(function(){return B(unCStr(": empty list"));}),_Hy=new T(function(){return B(unCStr("Prelude."));}),_Hz=function(_HA){return new F(function(){return err(B(_2(_Hy,new T(function(){return B(_2(_HA,_Hx));},1))));});},_HB=new T(function(){return B(unCStr("foldr1"));}),_HC=new T(function(){return B(_Hz(_HB));}),_HD=function(_HE,_HF){var _HG=E(_HF);if(!_HG._){return E(_HC);}else{var _HH=_HG.a,_HI=E(_HG.b);if(!_HI._){return E(_HH);}else{return new F(function(){return A2(_HE,_HH,new T(function(){return B(_HD(_HE,_HI));}));});}}},_HJ=function(_HK,_HL,_HM){var _HN=new T(function(){var _HO=function(_HP){var _HQ=E(_HK),_HR=new T(function(){return B(A3(_HD,_GX,new T2(1,function(_HS){return new F(function(){return _Y(0,_HQ.a,_HS);});},new T2(1,function(_HT){return new F(function(){return _c(0,E(_HQ.b),_HT);});},_1I)),new T2(1,_a,_HP)));});return new T2(1,_b,_HR);};return B(A3(_HD,_GX,new T2(1,_HO,new T2(1,function(_HU){return new F(function(){return _c(0,E(_HL),_HU);});},_1I)),new T2(1,_a,_HM)));});return new T2(0,_b,_HN);},_HV=function(_HW,_HX){var _HY=E(_HW),_HZ=B(_HJ(_HY.a,_HY.b,_HX));return new T2(1,_HZ.a,_HZ.b);},_I0=function(_I1,_I2){return new F(function(){return _2q(_HV,_I1,_I2);});},_I3=function(_I4,_I5,_I6){var _I7=new T(function(){var _I8=function(_I9){var _Ia=E(_I4),_Ib=new T(function(){return B(A3(_HD,_GX,new T2(1,function(_Ic){return new F(function(){return _h(0,_Ia.a,_Ic);});},new T2(1,function(_Id){return new F(function(){return _c(0,E(_Ia.b),_Id);});},_1I)),new T2(1,_a,_I9)));});return new T2(1,_b,_Ib);};return B(A3(_HD,_GX,new T2(1,_I8,new T2(1,function(_Ie){return new F(function(){return _c(0,E(_I5),_Ie);});},_1I)),new T2(1,_a,_I6)));});return new T2(0,_b,_I7);},_If=function(_Ig,_Ih){var _Ii=E(_Ig),_Ij=B(_I3(_Ii.a,_Ii.b,_Ih));return new T2(1,_Ij.a,_Ij.b);},_Ik=function(_Il,_Im){return new F(function(){return _2q(_If,_Il,_Im);});},_In=new T2(1,_a,_1I),_Io=function(_Ip,_Iq){while(1){var _Ir=B((function(_Is,_It){var _Iu=E(_It);if(!_Iu._){_Ip=new T2(1,_Iu.b,new T(function(){return B(_Io(_Is,_Iu.d));}));_Iq=_Iu.c;return __continue;}else{return E(_Is);}})(_Ip,_Iq));if(_Ir!=__continue){return _Ir;}}},_Iv=function(_Iw,_Ix,_Iy,_Iz){var _IA=new T(function(){var _IB=new T(function(){return B(_GQ(_1I,_Iz));}),_IC=new T(function(){return B(_GQ(_1I,_Iy));}),_ID=new T(function(){return B(_Io(_1I,_Ix));}),_IE=new T(function(){return B(_Io(_1I,_Iw));});return B(A3(_HD,_GX,new T2(1,function(_IF){return new F(function(){return _2q(_He,_IE,_IF);});},new T2(1,function(_IG){return new F(function(){return _2q(_Ht,_ID,_IG);});},new T2(1,function(_IH){return new F(function(){return _I0(_IC,_IH);});},new T2(1,function(_II){return new F(function(){return _Ik(_IB,_II);});},_1I)))),_In));});return new T2(0,_b,_IA);},_IJ=new T(function(){return B(err(_1J));}),_IK=new T(function(){return B(err(_1T));}),_IL=function(_IM){return new F(function(){return _g9(_gC,_IM);});},_IN=new T(function(){return B(unCStr("["));}),_IO=function(_IP,_IQ){var _IR=function(_IS,_IT){var _IU=new T(function(){return B(A1(_IT,_1I));}),_IV=new T(function(){var _IW=function(_IX){return new F(function(){return _IR(_8j,function(_IY){return new F(function(){return A1(_IT,new T2(1,_IX,_IY));});});});};return B(A2(_IP,_fE,_IW));}),_IZ=new T(function(){return B(_f7(function(_J0){var _J1=E(_J0);if(_J1._==2){var _J2=E(_J1.a);if(!_J2._){return new T0(2);}else{var _J3=_J2.b;switch(E(_J2.a)){case 44:return (E(_J3)._==0)?(!E(_IS))?new T0(2):E(_IV):new T0(2);case 93:return (E(_J3)._==0)?E(_IU):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_J4=function(_J5){return E(_IZ);};return new T1(1,function(_J6){return new F(function(){return A2(_dO,_J6,_J4);});});},_J7=function(_J8,_J9){return new F(function(){return _Ja(_J9);});},_Ja=function(_Jb){var _Jc=new T(function(){var _Jd=new T(function(){var _Je=new T(function(){var _Jf=function(_Jg){return new F(function(){return _IR(_8j,function(_Jh){return new F(function(){return A1(_Jb,new T2(1,_Jg,_Jh));});});});};return B(A2(_IP,_fE,_Jf));});return B(_3r(B(_IR(_8i,_Jb)),_Je));});return B(_f7(function(_Ji){var _Jj=E(_Ji);return (_Jj._==2)?(!B(_47(_Jj.a,_IN)))?new T0(2):E(_Jd):new T0(2);}));}),_Jk=function(_Jl){return E(_Jc);};return new F(function(){return _3r(new T1(1,function(_Jm){return new F(function(){return A2(_dO,_Jm,_Jk);});}),new T(function(){return new T1(1,B(_fF(_J7,_Jb)));}));});};return new F(function(){return _Ja(_IQ);});},_Jn=function(_Jo,_Jp){return new F(function(){return _IO(_IL,_Jp);});},_Jq=new T(function(){return B(_IO(_IL,_4E));}),_Jr=function(_IM){return new F(function(){return _3h(_Jq,_IM);});},_Js=function(_Jt){var _Ju=new T(function(){return B(A3(_g9,_gC,_Jt,_4E));});return function(_Jv){return new F(function(){return _3h(_Ju,_Jv);});};},_Jw=new T4(0,_Js,_Jr,_IL,_Jn),_Jx=function(_Jy){return new F(function(){return _fY(_ho,_Jy);});},_Jz=function(_JA,_JB){return new F(function(){return _IO(_Jx,_JB);});},_JC=new T(function(){return B(_IO(_Jx,_4E));}),_JD=function(_Jy){return new F(function(){return _3h(_JC,_Jy);});},_JE=function(_JF){var _JG=new T(function(){return B(A3(_fY,_ho,_JF,_4E));});return function(_Jv){return new F(function(){return _3h(_JG,_Jv);});};},_JH=new T4(0,_JE,_JD,_Jx,_Jz),_JI=new T(function(){return B(unCStr(","));}),_JJ=function(_JK){return E(E(_JK).c);},_JL=function(_JM,_JN,_JO){var _JP=new T(function(){return B(_JJ(_JN));}),_JQ=new T(function(){return B(A2(_JJ,_JM,_JO));}),_JR=function(_JS){var _JT=function(_JU){var _JV=new T(function(){var _JW=new T(function(){return B(A2(_JP,_JO,function(_JX){return new F(function(){return A1(_JS,new T2(0,_JU,_JX));});}));});return B(_f7(function(_JY){var _JZ=E(_JY);return (_JZ._==2)?(!B(_47(_JZ.a,_JI)))?new T0(2):E(_JW):new T0(2);}));}),_K0=function(_K1){return E(_JV);};return new T1(1,function(_K2){return new F(function(){return A2(_dO,_K2,_K0);});});};return new F(function(){return A1(_JQ,_JT);});};return E(_JR);},_K3=function(_K4,_K5,_K6){var _K7=function(_IM){return new F(function(){return _JL(_K4,_K5,_IM);});},_K8=function(_K9,_Ka){return new F(function(){return _Kb(_Ka);});},_Kb=function(_Kc){return new F(function(){return _3r(new T1(1,B(_fF(_K7,_Kc))),new T(function(){return new T1(1,B(_fF(_K8,_Kc)));}));});};return new F(function(){return _Kb(_K6);});},_Kd=function(_Ke,_Kf){return new F(function(){return _K3(_JH,_Jw,_Kf);});},_Kg=new T(function(){return B(_IO(_Kd,_4E));}),_Kh=function(_Jy){return new F(function(){return _3h(_Kg,_Jy);});},_Ki=new T(function(){return B(_K3(_JH,_Jw,_4E));}),_Kj=function(_Jy){return new F(function(){return _3h(_Ki,_Jy);});},_Kk=function(_Kl,_Jy){return new F(function(){return _Kj(_Jy);});},_Km=function(_Kn,_Ko){return new F(function(){return _IO(_Kd,_Ko);});},_Kp=new T4(0,_Kk,_Kh,_Kd,_Km),_Kq=function(_Kr,_Ks){return new F(function(){return _K3(_Kp,_Jw,_Ks);});},_Kt=function(_Ku,_Kv){return new F(function(){return _IO(_Kq,_Kv);});},_Kw=new T(function(){return B(_IO(_Kt,_4E));}),_Kx=function(_Ky){return new F(function(){return _3h(_Kw,_Ky);});},_Kz=function(_KA){return new F(function(){return _IO(_Kt,_KA);});},_KB=function(_KC,_KD){return new F(function(){return _Kz(_KD);});},_KE=new T(function(){return B(_IO(_Kq,_4E));}),_KF=function(_Ky){return new F(function(){return _3h(_KE,_Ky);});},_KG=function(_KH,_Ky){return new F(function(){return _KF(_Ky);});},_KI=new T4(0,_KG,_Kx,_Kt,_KB),_KJ=function(_Jy){return new F(function(){return _fY(_h9,_Jy);});},_KK=function(_KL,_KM){return new F(function(){return _IO(_KJ,_KM);});},_KN=new T(function(){return B(_IO(_KJ,_4E));}),_KO=function(_Jy){return new F(function(){return _3h(_KN,_Jy);});},_KP=function(_KQ){var _KR=new T(function(){return B(A3(_fY,_h9,_KQ,_4E));});return function(_Jv){return new F(function(){return _3h(_KR,_Jv);});};},_KS=new T4(0,_KP,_KO,_KJ,_KK),_KT=function(_KU,_KV){return new F(function(){return _K3(_KS,_Jw,_KV);});},_KW=new T(function(){return B(_IO(_KT,_4E));}),_KX=function(_Jy){return new F(function(){return _3h(_KW,_Jy);});},_KY=new T(function(){return B(_K3(_KS,_Jw,_4E));}),_KZ=function(_Jy){return new F(function(){return _3h(_KY,_Jy);});},_L0=function(_L1,_Jy){return new F(function(){return _KZ(_Jy);});},_L2=function(_L3,_L4){return new F(function(){return _IO(_KT,_L4);});},_L5=new T4(0,_L0,_KX,_KT,_L2),_L6=function(_L7,_L8){return new F(function(){return _K3(_L5,_Jw,_L8);});},_L9=function(_La,_Lb){return new F(function(){return _IO(_L6,_Lb);});},_Lc=new T(function(){return B(_IO(_L9,_4E));}),_Ld=function(_Ky){return new F(function(){return _3h(_Lc,_Ky);});},_Le=function(_Lf){return new F(function(){return _IO(_L9,_Lf);});},_Lg=function(_Lh,_Li){return new F(function(){return _Le(_Li);});},_Lj=new T(function(){return B(_IO(_L6,_4E));}),_Lk=function(_Ky){return new F(function(){return _3h(_Lj,_Ky);});},_Ll=function(_Lm,_Ky){return new F(function(){return _Lk(_Ky);});},_Ln=new T4(0,_Ll,_Ld,_L9,_Lg),_Lo=new T(function(){return B(unCStr("RC"));}),_Lp=function(_Lq,_Lr){if(_Lq>10){return new T0(2);}else{var _Ls=new T(function(){var _Lt=new T(function(){var _Lu=function(_Lv){var _Lw=function(_Lx){return new F(function(){return A3(_g9,_gC,_43,function(_Ly){return new F(function(){return A1(_Lr,new T3(0,_Lv,_Lx,_Ly));});});});};return new F(function(){return A3(_g9,_gC,_43,_Lw);});};return B(A3(_fY,_gU,_43,_Lu));});return B(_f7(function(_Lz){var _LA=E(_Lz);return (_LA._==3)?(!B(_47(_LA.a,_Lo)))?new T0(2):E(_Lt):new T0(2);}));}),_LB=function(_LC){return E(_Ls);};return new T1(1,function(_LD){return new F(function(){return A2(_dO,_LD,_LB);});});}},_LE=function(_LF,_LG){return new F(function(){return _Lp(E(_LF),_LG);});},_LH=function(_Jy){return new F(function(){return _fY(_LE,_Jy);});},_LI=function(_LJ,_LK){return new F(function(){return _IO(_LH,_LK);});},_LL=new T(function(){return B(_IO(_LI,_4E));}),_LM=function(_Ky){return new F(function(){return _3h(_LL,_Ky);});},_LN=new T(function(){return B(_IO(_LH,_4E));}),_LO=function(_Ky){return new F(function(){return _3h(_LN,_Ky);});},_LP=function(_LQ,_Ky){return new F(function(){return _LO(_Ky);});},_LR=function(_LS,_LT){return new F(function(){return _IO(_LI,_LT);});},_LU=new T4(0,_LP,_LM,_LI,_LR),_LV=new T(function(){return B(unCStr("CC"));}),_LW=function(_LX,_LY){if(_LX>10){return new T0(2);}else{var _LZ=new T(function(){var _M0=new T(function(){var _M1=function(_M2){var _M3=function(_M4){var _M5=function(_M6){return new F(function(){return A3(_g9,_gC,_43,function(_M7){return new F(function(){return A1(_LY,new T4(0,_M2,_M4,_M6,_M7));});});});};return new F(function(){return A3(_g9,_gC,_43,_M5);});};return new F(function(){return A3(_g9,_gC,_43,_M3);});};return B(A3(_fY,_gU,_43,_M1));});return B(_f7(function(_M8){var _M9=E(_M8);return (_M9._==3)?(!B(_47(_M9.a,_LV)))?new T0(2):E(_M0):new T0(2);}));}),_Ma=function(_Mb){return E(_LZ);};return new T1(1,function(_Mc){return new F(function(){return A2(_dO,_Mc,_Ma);});});}},_Md=function(_Me,_Mf){return new F(function(){return _LW(E(_Me),_Mf);});},_Mg=function(_Jy){return new F(function(){return _fY(_Md,_Jy);});},_Mh=function(_Mi,_Mj){return new F(function(){return _IO(_Mg,_Mj);});},_Mk=new T(function(){return B(_IO(_Mh,_4E));}),_Ml=function(_Ky){return new F(function(){return _3h(_Mk,_Ky);});},_Mm=new T(function(){return B(_IO(_Mg,_4E));}),_Mn=function(_Ky){return new F(function(){return _3h(_Mm,_Ky);});},_Mo=function(_Mp,_Ky){return new F(function(){return _Mn(_Ky);});},_Mq=function(_Mr,_Ms){return new F(function(){return _IO(_Mh,_Ms);});},_Mt=new T4(0,_Mo,_Ml,_Mh,_Mq),_Mu=function(_Mv,_Mw,_Mx,_My,_Mz){var _MA=new T(function(){return B(_JL(_Mv,_Mw,_Mz));}),_MB=new T(function(){return B(_JJ(_My));}),_MC=function(_MD){var _ME=function(_MF){var _MG=E(_MF),_MH=new T(function(){var _MI=new T(function(){var _MJ=function(_MK){var _ML=new T(function(){var _MM=new T(function(){return B(A2(_MB,_Mz,function(_MN){return new F(function(){return A1(_MD,new T4(0,_MG.a,_MG.b,_MK,_MN));});}));});return B(_f7(function(_MO){var _MP=E(_MO);return (_MP._==2)?(!B(_47(_MP.a,_JI)))?new T0(2):E(_MM):new T0(2);}));}),_MQ=function(_MR){return E(_ML);};return new T1(1,function(_MS){return new F(function(){return A2(_dO,_MS,_MQ);});});};return B(A3(_JJ,_Mx,_Mz,_MJ));});return B(_f7(function(_MT){var _MU=E(_MT);return (_MU._==2)?(!B(_47(_MU.a,_JI)))?new T0(2):E(_MI):new T0(2);}));}),_MV=function(_MW){return E(_MH);};return new T1(1,function(_MX){return new F(function(){return A2(_dO,_MX,_MV);});});};return new F(function(){return A1(_MA,_ME);});};return E(_MC);},_MY=function(_MZ,_N0,_N1,_N2,_N3){var _N4=function(_IM){return new F(function(){return _Mu(_MZ,_N0,_N1,_N2,_IM);});},_N5=function(_N6,_N7){return new F(function(){return _N8(_N7);});},_N8=function(_N9){return new F(function(){return _3r(new T1(1,B(_fF(_N4,_N9))),new T(function(){return new T1(1,B(_fF(_N5,_N9)));}));});};return new F(function(){return _N8(_N3);});},_Na=new T(function(){return B(_MY(_Mt,_LU,_Ln,_KI,_kL));}),_Nb=new T(function(){return B(unCStr("contractInput"));}),_Nc=function(_Nd,_Ne,_Nf,_){var _Ng=E(_Nb),_Nh=eval(E(_pD)),_Ni=__app1(E(_Nh),toJSStr(_Ng)),_Nj=B(_kS(B(_3h(_Na,new T(function(){var _Nk=String(_Ni);return fromJSStr(_Nk);})))));if(!_Nj._){return E(_IK);}else{if(!E(_Nj.b)._){var _Nl=E(_Nj.a),_Nm=B(_Iv(new T(function(){return B(_tn(_Nl.a));},1),new T(function(){return B(_xK(_Nl.b));},1),new T(function(){return B(_GA(_Nl.c));},1),new T(function(){return B(_BW(_Nf,_Nd,_Ne,B(_Dq(_Nl.d))));},1)));return new F(function(){return _1O(_Ng,new T2(1,_Nm.a,_Nm.b),_);});}else{return E(_IJ);}}},_Nn=function(_No,_Np,_Nq,_){var _Nr=E(_Nb),_Ns=eval(E(_pD)),_Nt=__app1(E(_Ns),toJSStr(_Nr)),_Nu=B(_kS(B(_3h(_Na,new T(function(){var _Nv=String(_Nt);return fromJSStr(_Nv);})))));if(!_Nu._){return E(_IK);}else{if(!E(_Nu.b)._){var _Nw=E(_Nu.a),_Nx=B(_Iv(new T(function(){return B(_tn(_Nw.a));},1),new T(function(){return B(_xK(_Nw.b));},1),new T(function(){return B(_F6(_Nq,_No,_Np,B(_GA(_Nw.c))));},1),new T(function(){return B(_Dq(_Nw.d));},1)));return new F(function(){return _1O(_Nr,new T2(1,_Nx.a,_Nx.b),_);});}else{return E(_IJ);}}},_Ny=new T(function(){return B(unCStr("contractOutput"));}),_Nz=new T(function(){return B(unCStr("([], [], [], [])"));}),_NA=new T(function(){return B(unCStr("([], [])"));}),_NB=new T(function(){return B(unCStr("contractState"));}),_NC=new T(function(){return B(_c(0,0,_1I));}),_ND=new T(function(){return B(unCStr("currBlock"));}),_NE=function(_){var _NF=__app0(E(_pu)),_NG=B(_1O(_1L,_1I,_)),_NH=B(_1O(_ND,_NC,_)),_NI=B(_1O(_NB,_NA,_)),_NJ=B(_1O(_Nb,_Nz,_));return new F(function(){return _1O(_Ny,_1I,_);});},_NK=function(_NL,_NM,_NN,_NO,_){var _NP=E(_Nb),_NQ=eval(E(_pD)),_NR=__app1(E(_NQ),toJSStr(_NP)),_NS=B(_kS(B(_3h(_Na,new T(function(){var _NT=String(_NR);return fromJSStr(_NT);})))));if(!_NS._){return E(_IK);}else{if(!E(_NS.b)._){var _NU=E(_NS.a),_NV=B(_Iv(new T(function(){return B(_qZ(_NN,_NL,_NM,_NO,B(_tn(_NU.a))));},1),new T(function(){return B(_xK(_NU.b));},1),new T(function(){return B(_GA(_NU.c));},1),new T(function(){return B(_Dq(_NU.d));},1)));return new F(function(){return _1O(_NP,new T2(1,_NV.a,_NV.b),_);});}else{return E(_IJ);}}},_NW=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_NX=new T(function(){return B(unCStr("NotRedeemed "));}),_NY=function(_NZ,_O0,_O1){var _O2=E(_O0);if(!_O2._){var _O3=function(_O4){return new F(function(){return _c(11,E(_O2.a),new T2(1,_u,new T(function(){return B(_c(11,E(_O2.b),_O4));})));});};if(E(_NZ)<11){return new F(function(){return _2(_NX,new T(function(){return B(_O3(_O1));},1));});}else{var _O5=new T(function(){return B(_2(_NX,new T(function(){return B(_O3(new T2(1,_a,_O1)));},1)));});return new T2(1,_b,_O5);}}else{return new F(function(){return _2(_NW,_O1);});}},_O6=0,_O7=function(_O8,_O9,_Oa){var _Ob=new T(function(){var _Oc=function(_Od){var _Oe=E(_O9),_Of=new T(function(){return B(A3(_HD,_GX,new T2(1,function(_Og){return new F(function(){return _c(0,E(_Oe.a),_Og);});},new T2(1,function(_Ky){return new F(function(){return _NY(_O6,_Oe.b,_Ky);});},_1I)),new T2(1,_a,_Od)));});return new T2(1,_b,_Of);};return B(A3(_HD,_GX,new T2(1,function(_Oh){return new F(function(){return _S(0,_O8,_Oh);});},new T2(1,_Oc,_1I)),new T2(1,_a,_Oa)));});return new T2(0,_b,_Ob);},_Oi=function(_Oj,_Ok){var _Ol=E(_Oj),_Om=B(_O7(_Ol.a,_Ol.b,_Ok));return new T2(1,_Om.a,_Om.b);},_On=function(_Oo,_Op){return new F(function(){return _2q(_Oi,_Oo,_Op);});},_Oq=function(_Or,_Os,_Ot,_Ou){var _Ov=E(_Or);if(_Ov==1){var _Ow=E(_Ou);if(!_Ow._){return new T3(0,new T(function(){var _Ox=E(_Os);return new T5(0,1,E(_Ox),_Ot,E(_xZ),E(_xZ));}),_1I,_1I);}else{var _Oy=E(_Os);return (_Oy<E(E(_Ow.a).a))?new T3(0,new T5(0,1,E(_Oy),_Ot,E(_xZ),E(_xZ)),_Ow,_1I):new T3(0,new T5(0,1,E(_Oy),_Ot,E(_xZ),E(_xZ)),_1I,_Ow);}}else{var _Oz=B(_Oq(_Ov>>1,_Os,_Ot,_Ou)),_OA=_Oz.a,_OB=_Oz.c,_OC=E(_Oz.b);if(!_OC._){return new T3(0,_OA,_1I,_OB);}else{var _OD=E(_OC.a),_OE=_OD.a,_OF=_OD.b,_OG=E(_OC.b);if(!_OG._){return new T3(0,new T(function(){return B(_yM(_OE,_OF,_OA));}),_1I,_OB);}else{var _OH=E(_OG.a),_OI=E(_OE),_OJ=E(_OH.a);if(_OI<_OJ){var _OK=B(_Oq(_Ov>>1,_OJ,_OH.b,_OG.b));return new T3(0,new T(function(){return B(_Af(_OI,_OF,_OA,_OK.a));}),_OK.b,_OK.c);}else{return new T3(0,_OA,_1I,_OC);}}}}},_OL=function(_OM,_ON,_OO){var _OP=E(_OO);if(!_OP._){var _OQ=_OP.c,_OR=_OP.d,_OS=_OP.e,_OT=E(_OP.b);if(_OM>=_OT){if(_OM!=_OT){return new F(function(){return _y4(_OT,_OQ,_OR,B(_OL(_OM,_ON,_OS)));});}else{return new T5(0,_OP.a,E(_OM),_ON,E(_OR),E(_OS));}}else{return new F(function(){return _yV(_OT,_OQ,B(_OL(_OM,_ON,_OR)),_OS);});}}else{return new T5(0,1,E(_OM),_ON,E(_xZ),E(_xZ));}},_OU=function(_OV,_OW){while(1){var _OX=E(_OW);if(!_OX._){return E(_OV);}else{var _OY=E(_OX.a),_OZ=B(_OL(E(_OY.a),_OY.b,_OV));_OV=_OZ;_OW=_OX.b;continue;}}},_P0=function(_P1,_P2,_P3,_P4){return new F(function(){return _OU(B(_OL(E(_P2),_P3,_P1)),_P4);});},_P5=function(_P6,_P7,_P8){var _P9=E(_P7);return new F(function(){return _OU(B(_OL(E(_P9.a),_P9.b,_P6)),_P8);});},_Pa=function(_Pb,_Pc,_Pd){while(1){var _Pe=E(_Pd);if(!_Pe._){return E(_Pc);}else{var _Pf=E(_Pe.a),_Pg=_Pf.a,_Ph=_Pf.b,_Pi=E(_Pe.b);if(!_Pi._){return new F(function(){return _yM(_Pg,_Ph,_Pc);});}else{var _Pj=E(_Pi.a),_Pk=E(_Pg),_Pl=E(_Pj.a);if(_Pk<_Pl){var _Pm=B(_Oq(_Pb,_Pl,_Pj.b,_Pi.b)),_Pn=_Pm.a,_Po=E(_Pm.c);if(!_Po._){var _Pp=_Pb<<1,_Pq=B(_Af(_Pk,_Ph,_Pc,_Pn));_Pb=_Pp;_Pc=_Pq;_Pd=_Pm.b;continue;}else{return new F(function(){return _P5(B(_Af(_Pk,_Ph,_Pc,_Pn)),_Po.a,_Po.b);});}}else{return new F(function(){return _P0(_Pc,_Pk,_Ph,_Pi);});}}}}},_Pr=function(_Ps,_Pt,_Pu,_Pv,_Pw){var _Px=E(_Pw);if(!_Px._){return new F(function(){return _yM(_Pu,_Pv,_Pt);});}else{var _Py=E(_Px.a),_Pz=E(_Pu),_PA=E(_Py.a);if(_Pz<_PA){var _PB=B(_Oq(_Ps,_PA,_Py.b,_Px.b)),_PC=_PB.a,_PD=E(_PB.c);if(!_PD._){return new F(function(){return _Pa(_Ps<<1,B(_Af(_Pz,_Pv,_Pt,_PC)),_PB.b);});}else{return new F(function(){return _P5(B(_Af(_Pz,_Pv,_Pt,_PC)),_PD.a,_PD.b);});}}else{return new F(function(){return _P0(_Pt,_Pz,_Pv,_Px);});}}},_PE=function(_PF){var _PG=E(_PF);if(!_PG._){return new T0(1);}else{var _PH=E(_PG.a),_PI=_PH.a,_PJ=_PH.b,_PK=E(_PG.b);if(!_PK._){var _PL=E(_PI);return new T5(0,1,E(_PL),_PJ,E(_xZ),E(_xZ));}else{var _PM=_PK.b,_PN=E(_PK.a),_PO=_PN.b,_PP=E(_PI),_PQ=E(_PN.a);if(_PP<_PQ){return new F(function(){return _Pr(1,new T5(0,1,E(_PP),_PJ,E(_xZ),E(_xZ)),_PQ,_PO,_PM);});}else{return new F(function(){return _P0(new T5(0,1,E(_PP),_PJ,E(_xZ),E(_xZ)),_PQ,_PO,_PM);});}}}},_PR=new T(function(){return B(unCStr("ChoiceMade "));}),_PS=new T(function(){return B(unCStr("DuplicateRedeem "));}),_PT=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_PU=new T(function(){return B(unCStr("CommitRedeemed "));}),_PV=new T(function(){return B(unCStr("SuccessfulCommit "));}),_PW=new T(function(){return B(unCStr("FailedPay "));}),_PX=new T(function(){return B(unCStr("ExpiredPay "));}),_PY=new T(function(){return B(unCStr("SuccessfulPay "));}),_PZ=function(_Q0,_Q1,_Q2){var _Q3=E(_Q1);switch(_Q3._){case 0:var _Q4=function(_Q5){var _Q6=new T(function(){var _Q7=new T(function(){return B(_c(11,E(_Q3.c),new T2(1,_u,new T(function(){return B(_c(11,E(_Q3.d),_Q5));}))));});return B(_c(11,E(_Q3.b),new T2(1,_u,_Q7)));});return new F(function(){return _Y(11,_Q3.a,new T2(1,_u,_Q6));});};if(_Q0<11){return new F(function(){return _2(_PY,new T(function(){return B(_Q4(_Q2));},1));});}else{var _Q8=new T(function(){return B(_2(_PY,new T(function(){return B(_Q4(new T2(1,_a,_Q2)));},1)));});return new T2(1,_b,_Q8);}break;case 1:var _Q9=function(_Qa){var _Qb=new T(function(){var _Qc=new T(function(){return B(_c(11,E(_Q3.c),new T2(1,_u,new T(function(){return B(_c(11,E(_Q3.d),_Qa));}))));});return B(_c(11,E(_Q3.b),new T2(1,_u,_Qc)));});return new F(function(){return _Y(11,_Q3.a,new T2(1,_u,_Qb));});};if(_Q0<11){return new F(function(){return _2(_PX,new T(function(){return B(_Q9(_Q2));},1));});}else{var _Qd=new T(function(){return B(_2(_PX,new T(function(){return B(_Q9(new T2(1,_a,_Q2)));},1)));});return new T2(1,_b,_Qd);}break;case 2:var _Qe=function(_Qf){var _Qg=new T(function(){var _Qh=new T(function(){return B(_c(11,E(_Q3.c),new T2(1,_u,new T(function(){return B(_c(11,E(_Q3.d),_Qf));}))));});return B(_c(11,E(_Q3.b),new T2(1,_u,_Qh)));});return new F(function(){return _Y(11,_Q3.a,new T2(1,_u,_Qg));});};if(_Q0<11){return new F(function(){return _2(_PW,new T(function(){return B(_Qe(_Q2));},1));});}else{var _Qi=new T(function(){return B(_2(_PW,new T(function(){return B(_Qe(new T2(1,_a,_Q2)));},1)));});return new T2(1,_b,_Qi);}break;case 3:var _Qj=function(_Qk){var _Ql=new T(function(){var _Qm=new T(function(){return B(_c(11,E(_Q3.b),new T2(1,_u,new T(function(){return B(_c(11,E(_Q3.c),_Qk));}))));});return B(_S(11,_Q3.a,new T2(1,_u,_Qm)));},1);return new F(function(){return _2(_PV,_Ql);});};if(_Q0<11){return new F(function(){return _Qj(_Q2);});}else{return new T2(1,_b,new T(function(){return B(_Qj(new T2(1,_a,_Q2)));}));}break;case 4:var _Qn=function(_Qo){var _Qp=new T(function(){var _Qq=new T(function(){return B(_c(11,E(_Q3.b),new T2(1,_u,new T(function(){return B(_c(11,E(_Q3.c),_Qo));}))));});return B(_S(11,_Q3.a,new T2(1,_u,_Qq)));},1);return new F(function(){return _2(_PU,_Qp);});};if(_Q0<11){return new F(function(){return _Qn(_Q2);});}else{return new T2(1,_b,new T(function(){return B(_Qn(new T2(1,_a,_Q2)));}));}break;case 5:var _Qr=function(_Qs){var _Qt=new T(function(){var _Qu=new T(function(){return B(_c(11,E(_Q3.b),new T2(1,_u,new T(function(){return B(_c(11,E(_Q3.c),_Qs));}))));});return B(_S(11,_Q3.a,new T2(1,_u,_Qu)));},1);return new F(function(){return _2(_PT,_Qt);});};if(_Q0<11){return new F(function(){return _Qr(_Q2);});}else{return new T2(1,_b,new T(function(){return B(_Qr(new T2(1,_a,_Q2)));}));}break;case 6:var _Qv=function(_Qw){return new F(function(){return _S(11,_Q3.a,new T2(1,_u,new T(function(){return B(_c(11,E(_Q3.b),_Qw));})));});};if(_Q0<11){return new F(function(){return _2(_PS,new T(function(){return B(_Qv(_Q2));},1));});}else{var _Qx=new T(function(){return B(_2(_PS,new T(function(){return B(_Qv(new T2(1,_a,_Q2)));},1)));});return new T2(1,_b,_Qx);}break;default:var _Qy=function(_Qz){var _QA=new T(function(){var _QB=new T(function(){return B(_c(11,E(_Q3.b),new T2(1,_u,new T(function(){return B(_c(11,E(_Q3.c),_Qz));}))));});return B(_h(11,_Q3.a,new T2(1,_u,_QB)));},1);return new F(function(){return _2(_PR,_QA);});};if(_Q0<11){return new F(function(){return _Qy(_Q2);});}else{return new T2(1,_b,new T(function(){return B(_Qy(new T2(1,_a,_Q2)));}));}}},_QC=function(_QD,_QE){return E(_QD)==E(_QE);},_QF=function(_QG,_QH){var _QI=E(_QG);switch(_QI._){case 0:var _QJ=E(_QH);if(!_QJ._){if(E(_QI.a)!=E(_QJ.a)){return false;}else{if(E(_QI.b)!=E(_QJ.b)){return false;}else{if(E(_QI.c)!=E(_QJ.c)){return false;}else{return new F(function(){return _QC(_QI.d,_QJ.d);});}}}}else{return false;}break;case 1:var _QK=E(_QH);if(_QK._==1){if(E(_QI.a)!=E(_QK.a)){return false;}else{if(E(_QI.b)!=E(_QK.b)){return false;}else{if(E(_QI.c)!=E(_QK.c)){return false;}else{return new F(function(){return _QC(_QI.d,_QK.d);});}}}}else{return false;}break;case 2:var _QL=E(_QH);if(_QL._==2){if(E(_QI.a)!=E(_QL.a)){return false;}else{if(E(_QI.b)!=E(_QL.b)){return false;}else{if(E(_QI.c)!=E(_QL.c)){return false;}else{return new F(function(){return _QC(_QI.d,_QL.d);});}}}}else{return false;}break;case 3:var _QM=E(_QH);if(_QM._==3){if(E(_QI.a)!=E(_QM.a)){return false;}else{if(E(_QI.b)!=E(_QM.b)){return false;}else{return new F(function(){return _QC(_QI.c,_QM.c);});}}}else{return false;}break;case 4:var _QN=E(_QH);if(_QN._==4){if(E(_QI.a)!=E(_QN.a)){return false;}else{if(E(_QI.b)!=E(_QN.b)){return false;}else{return new F(function(){return _QC(_QI.c,_QN.c);});}}}else{return false;}break;case 5:var _QO=E(_QH);if(_QO._==5){if(E(_QI.a)!=E(_QO.a)){return false;}else{if(E(_QI.b)!=E(_QO.b)){return false;}else{return new F(function(){return _QC(_QI.c,_QO.c);});}}}else{return false;}break;case 6:var _QP=E(_QH);if(_QP._==6){if(E(_QI.a)!=E(_QP.a)){return false;}else{return new F(function(){return _QC(_QI.b,_QP.b);});}}else{return false;}break;default:var _QQ=E(_QH);if(_QQ._==7){if(E(_QI.a)!=E(_QQ.a)){return false;}else{if(E(_QI.b)!=E(_QQ.b)){return false;}else{return new F(function(){return _QC(_QI.c,_QQ.c);});}}}else{return false;}}},_QR=function(_QS,_QT){return (!B(_QF(_QS,_QT)))?true:false;},_QU=new T2(0,_QF,_QR),_QV=function(_QW,_QX){while(1){var _QY=E(_QW);switch(_QY._){case 0:var _QZ=E(_QX);if(!_QZ._){return new F(function(){return _QC(_QY.a,_QZ.a);});}else{return false;}break;case 1:var _R0=E(_QX);if(_R0._==1){if(!B(_QV(_QY.a,_R0.a))){return false;}else{_QW=_QY.b;_QX=_R0.b;continue;}}else{return false;}break;case 2:var _R1=E(_QX);if(_R1._==2){if(!B(_QV(_QY.a,_R1.a))){return false;}else{_QW=_QY.b;_QX=_R1.b;continue;}}else{return false;}break;case 3:var _R2=E(_QX);if(_R2._==3){_QW=_QY.a;_QX=_R2.a;continue;}else{return false;}break;case 4:var _R3=E(_QX);if(_R3._==4){if(E(_QY.a)!=E(_R3.a)){return false;}else{if(E(_QY.b)!=E(_R3.b)){return false;}else{return new F(function(){return _QC(_QY.c,_R3.c);});}}}else{return false;}break;case 5:var _R4=E(_QX);if(_R4._==5){if(E(_QY.a)!=E(_R4.a)){return false;}else{return new F(function(){return _QC(_QY.b,_R4.b);});}}else{return false;}break;case 6:return (E(_QX)._==6)?true:false;default:return (E(_QX)._==7)?true:false;}}},_R5=function(_R6,_R7){while(1){var _R8=E(_R6);switch(_R8._){case 0:return (E(_R7)._==0)?true:false;case 1:var _R9=E(_R7);if(_R9._==1){if(E(_R8.a)!=E(_R9.a)){return false;}else{_R6=_R8.b;_R7=_R9.b;continue;}}else{return false;}break;case 2:var _Ra=E(_R7);if(_Ra._==2){if(E(_R8.a)!=E(_Ra.a)){return false;}else{if(E(_R8.b)!=E(_Ra.b)){return false;}else{if(E(_R8.c)!=E(_Ra.c)){return false;}else{if(E(_R8.d)!=E(_Ra.d)){return false;}else{if(E(_R8.e)!=E(_Ra.e)){return false;}else{_R6=_R8.f;_R7=_Ra.f;continue;}}}}}}else{return false;}break;case 3:var _Rb=E(_R7);if(_Rb._==3){if(!B(_R5(_R8.a,_Rb.a))){return false;}else{_R6=_R8.b;_R7=_Rb.b;continue;}}else{return false;}break;case 4:var _Rc=E(_R7);if(_Rc._==4){if(!B(_QV(_R8.a,_Rc.a))){return false;}else{if(!B(_R5(_R8.b,_Rc.b))){return false;}else{_R6=_R8.c;_R7=_Rc.c;continue;}}}else{return false;}break;case 5:var _Rd=E(_R7);if(_Rd._==5){if(E(_R8.a)!=E(_Rd.a)){return false;}else{if(E(_R8.b)!=E(_Rd.b)){return false;}else{if(E(_R8.c)!=E(_Rd.c)){return false;}else{if(E(_R8.d)!=E(_Rd.d)){return false;}else{if(E(_R8.e)!=E(_Rd.e)){return false;}else{_R6=_R8.f;_R7=_Rd.f;continue;}}}}}}else{return false;}break;default:var _Re=E(_R7);if(_Re._==6){if(!B(_QV(_R8.a,_Re.a))){return false;}else{if(E(_R8.b)!=E(_Re.b)){return false;}else{if(!B(_R5(_R8.c,_Re.c))){return false;}else{_R6=_R8.d;_R7=_Re.d;continue;}}}}else{return false;}}}},_Rf=function(_Rg,_Rh,_Ri,_Rj){return (_Rg!=_Ri)?true:(E(_Rh)!=E(_Rj))?true:false;},_Rk=function(_Rl,_Rm){var _Rn=E(_Rl),_Ro=E(_Rm);return new F(function(){return _Rf(E(_Rn.a),_Rn.b,E(_Ro.a),_Ro.b);});},_Rp=function(_Rq,_Rr,_Rs,_Rt){if(_Rq!=_Rs){return false;}else{return new F(function(){return _QC(_Rr,_Rt);});}},_Ru=function(_Rv,_Rw){var _Rx=E(_Rv),_Ry=E(_Rw);return new F(function(){return _Rp(E(_Rx.a),_Rx.b,E(_Ry.a),_Ry.b);});},_Rz=new T2(0,_Ru,_Rk),_RA=function(_RB,_RC){return E(_RB)!=E(_RC);},_RD=new T2(0,_QC,_RA),_RE=function(_RF,_RG,_RH,_RI,_RJ,_RK){return (!B(A3(_88,_RF,_RH,_RJ)))?true:(!B(A3(_88,_RG,_RI,_RK)))?true:false;},_RL=function(_RM,_RN,_RO,_RP){var _RQ=E(_RO),_RR=E(_RP);return new F(function(){return _RE(_RM,_RN,_RQ.a,_RQ.b,_RR.a,_RR.b);});},_RS=function(_RT,_RU,_RV,_RW,_RX,_RY){if(!B(A3(_88,_RT,_RV,_RX))){return false;}else{return new F(function(){return A3(_88,_RU,_RW,_RY);});}},_RZ=function(_S0,_S1,_S2,_S3){var _S4=E(_S2),_S5=E(_S3);return new F(function(){return _RS(_S0,_S1,_S4.a,_S4.b,_S5.a,_S5.b);});},_S6=function(_S7,_S8){return new T2(0,function(_S9,_Sa){return new F(function(){return _RZ(_S7,_S8,_S9,_Sa);});},function(_S9,_Sa){return new F(function(){return _RL(_S7,_S8,_S9,_Sa);});});},_Sb=function(_Sc,_Sd,_Se){while(1){var _Sf=E(_Sd);if(!_Sf._){return (E(_Se)._==0)?true:false;}else{var _Sg=E(_Se);if(!_Sg._){return false;}else{if(!B(A3(_88,_Sc,_Sf.a,_Sg.a))){return false;}else{_Sd=_Sf.b;_Se=_Sg.b;continue;}}}}},_Sh=function(_Si,_Sj){var _Sk=new T(function(){return B(_S6(_Si,_Sj));}),_Sl=function(_Sm,_Sn){var _So=function(_Sp){var _Sq=function(_Sr){if(_Sp!=_Sr){return false;}else{return new F(function(){return _Sb(_Sk,B(_GQ(_1I,_Sm)),B(_GQ(_1I,_Sn)));});}},_Ss=E(_Sn);if(!_Ss._){return new F(function(){return _Sq(_Ss.a);});}else{return new F(function(){return _Sq(0);});}},_St=E(_Sm);if(!_St._){return new F(function(){return _So(_St.a);});}else{return new F(function(){return _So(0);});}};return E(_Sl);},_Su=new T(function(){return B(_Sh(_Rz,_RD));}),_Sv=new T2(0,_QC,_RA),_Sw=function(_Sx,_Sy){var _Sz=E(_Sx);if(!_Sz._){var _SA=E(_Sy);if(!_SA._){if(E(_Sz.a)!=E(_SA.a)){return false;}else{return new F(function(){return _QC(_Sz.b,_SA.b);});}}else{return false;}}else{return (E(_Sy)._==0)?false:true;}},_SB=function(_SC,_SD,_SE,_SF){if(_SC!=_SE){return false;}else{return new F(function(){return _Sw(_SD,_SF);});}},_SG=function(_SH,_SI){var _SJ=E(_SH),_SK=E(_SI);return new F(function(){return _SB(E(_SJ.a),_SJ.b,E(_SK.a),_SK.b);});},_SL=function(_SM,_SN,_SO,_SP){if(_SM!=_SO){return true;}else{var _SQ=E(_SN);if(!_SQ._){var _SR=E(_SP);return (_SR._==0)?(E(_SQ.a)!=E(_SR.a))?true:(E(_SQ.b)!=E(_SR.b))?true:false:true;}else{return (E(_SP)._==0)?true:false;}}},_SS=function(_ST,_SU){var _SV=E(_ST),_SW=E(_SU);return new F(function(){return _SL(E(_SV.a),_SV.b,E(_SW.a),_SW.b);});},_SX=new T2(0,_SG,_SS),_SY=new T(function(){return B(_Sh(_Sv,_SX));}),_SZ=function(_T0,_T1){var _T2=E(_T0),_T3=E(_T1);return (_T2>_T3)?E(_T2):E(_T3);},_T4=function(_T5,_T6){var _T7=E(_T5),_T8=E(_T6);return (_T7>_T8)?E(_T8):E(_T7);},_T9=function(_Ta,_Tb){return (_Ta>=_Tb)?(_Ta!=_Tb)?2:1:0;},_Tc=function(_Td,_Te){return new F(function(){return _T9(E(_Td),E(_Te));});},_Tf=function(_Tg,_Th){return E(_Tg)>=E(_Th);},_Ti=function(_Tj,_Tk){return E(_Tj)>E(_Tk);},_Tl=function(_Tm,_Tn){return E(_Tm)<=E(_Tn);},_To=function(_Tp,_Tq){return E(_Tp)<E(_Tq);},_Tr={_:0,a:_Sv,b:_Tc,c:_To,d:_Tl,e:_Ti,f:_Tf,g:_SZ,h:_T4},_Ts=function(_Tt,_Tu,_Tv,_Tw,_Tx){while(1){var _Ty=E(_Tx);if(!_Ty._){var _Tz=_Ty.c,_TA=_Ty.d,_TB=E(_Ty.b),_TC=E(_TB.a);if(_Tt>=_TC){if(_Tt!=_TC){_Tu=_;_Tx=_TA;continue;}else{var _TD=E(_TB.b);if(_Tv>=_TD){if(_Tv!=_TD){_Tu=_;_Tx=_TA;continue;}else{var _TE=E(_TB.c);if(_Tw>=_TE){if(_Tw!=_TE){_Tu=_;_Tx=_TA;continue;}else{return true;}}else{_Tu=_;_Tx=_Tz;continue;}}}else{_Tu=_;_Tx=_Tz;continue;}}}else{_Tu=_;_Tx=_Tz;continue;}}else{return false;}}},_TF=function(_TG,_TH,_TI,_TJ,_TK){while(1){var _TL=E(_TK);if(!_TL._){var _TM=_TL.c,_TN=_TL.d,_TO=E(_TL.b),_TP=E(_TO.a);if(_TG>=_TP){if(_TG!=_TP){_TH=_;_TK=_TN;continue;}else{var _TQ=E(_TO.b);if(_TI>=_TQ){if(_TI!=_TQ){_TH=_;_TK=_TN;continue;}else{var _TR=E(_TJ),_TS=E(_TO.c);if(_TR>=_TS){if(_TR!=_TS){return new F(function(){return _Ts(_TG,_,_TI,_TR,_TN);});}else{return true;}}else{return new F(function(){return _Ts(_TG,_,_TI,_TR,_TM);});}}}else{_TH=_;_TK=_TM;continue;}}}else{_TH=_;_TK=_TM;continue;}}else{return false;}}},_TT=function(_TU,_TV,_TW,_TX,_TY){while(1){var _TZ=E(_TY);if(!_TZ._){var _U0=_TZ.c,_U1=_TZ.d,_U2=E(_TZ.b),_U3=E(_U2.a);if(_TU>=_U3){if(_TU!=_U3){_TV=_;_TY=_U1;continue;}else{var _U4=E(_TW),_U5=E(_U2.b);if(_U4>=_U5){if(_U4!=_U5){return new F(function(){return _TF(_TU,_,_U4,_TX,_U1);});}else{var _U6=E(_TX),_U7=E(_U2.c);if(_U6>=_U7){if(_U6!=_U7){return new F(function(){return _Ts(_TU,_,_U4,_U6,_U1);});}else{return true;}}else{return new F(function(){return _Ts(_TU,_,_U4,_U6,_U0);});}}}else{return new F(function(){return _TF(_TU,_,_U4,_TX,_U0);});}}}else{_TV=_;_TY=_U0;continue;}}else{return false;}}},_U8=function(_U9,_Ua,_Ub,_Uc){var _Ud=E(_Uc);if(!_Ud._){var _Ue=_Ud.c,_Uf=_Ud.d,_Ug=E(_Ud.b),_Uh=E(_U9),_Ui=E(_Ug.a);if(_Uh>=_Ui){if(_Uh!=_Ui){return new F(function(){return _TT(_Uh,_,_Ua,_Ub,_Uf);});}else{var _Uj=E(_Ua),_Uk=E(_Ug.b);if(_Uj>=_Uk){if(_Uj!=_Uk){return new F(function(){return _TF(_Uh,_,_Uj,_Ub,_Uf);});}else{var _Ul=E(_Ub),_Um=E(_Ug.c);if(_Ul>=_Um){if(_Ul!=_Um){return new F(function(){return _Ts(_Uh,_,_Uj,_Ul,_Uf);});}else{return true;}}else{return new F(function(){return _Ts(_Uh,_,_Uj,_Ul,_Ue);});}}}else{return new F(function(){return _TF(_Uh,_,_Uj,_Ub,_Ue);});}}}else{return new F(function(){return _TT(_Uh,_,_Ua,_Ub,_Ue);});}}else{return false;}},_Un=function(_Uo,_Up,_Uq,_Ur,_Us){var _Ut=E(_Us);if(!_Ut._){if(E(_Ut.b)>E(_Up)){return false;}else{return new F(function(){return _U8(_Uq,_Ur,_Ut.a,E(_Uo).b);});}}else{return false;}},_Uu=function(_Uv,_Uw,_Ux,_Uy,_Uz){var _UA=E(_Uz);if(!_UA._){var _UB=new T(function(){var _UC=B(_Uu(_UA.a,_UA.b,_UA.c,_UA.d,_UA.e));return new T2(0,_UC.a,_UC.b);});return new T2(0,new T(function(){return E(E(_UB).a);}),new T(function(){return B(_yV(_Uw,_Ux,_Uy,E(_UB).b));}));}else{return new T2(0,new T2(0,_Uw,_Ux),_Uy);}},_UD=function(_UE,_UF,_UG,_UH,_UI){var _UJ=E(_UH);if(!_UJ._){var _UK=new T(function(){var _UL=B(_UD(_UJ.a,_UJ.b,_UJ.c,_UJ.d,_UJ.e));return new T2(0,_UL.a,_UL.b);});return new T2(0,new T(function(){return E(E(_UK).a);}),new T(function(){return B(_y4(_UF,_UG,E(_UK).b,_UI));}));}else{return new T2(0,new T2(0,_UF,_UG),_UI);}},_UM=function(_UN,_UO){var _UP=E(_UN);if(!_UP._){var _UQ=_UP.a,_UR=E(_UO);if(!_UR._){var _US=_UR.a;if(_UQ<=_US){var _UT=B(_UD(_US,_UR.b,_UR.c,_UR.d,_UR.e)),_UU=E(_UT.a);return new F(function(){return _yV(_UU.a,_UU.b,_UP,_UT.b);});}else{var _UV=B(_Uu(_UQ,_UP.b,_UP.c,_UP.d,_UP.e)),_UW=E(_UV.a);return new F(function(){return _y4(_UW.a,_UW.b,_UV.b,_UR);});}}else{return E(_UP);}}else{return E(_UO);}},_UX=function(_UY,_UZ,_V0,_V1,_V2,_V3){var _V4=E(_UY);if(!_V4._){var _V5=_V4.a,_V6=_V4.b,_V7=_V4.c,_V8=_V4.d,_V9=_V4.e;if((imul(3,_V5)|0)>=_UZ){if((imul(3,_UZ)|0)>=_V5){return new F(function(){return _UM(_V4,new T5(0,_UZ,E(_V0),_V1,E(_V2),E(_V3)));});}else{return new F(function(){return _y4(_V6,_V7,_V8,B(_UX(_V9,_UZ,_V0,_V1,_V2,_V3)));});}}else{return new F(function(){return _yV(_V0,_V1,B(_Va(_V5,_V6,_V7,_V8,_V9,_V2)),_V3);});}}else{return new T5(0,_UZ,E(_V0),_V1,E(_V2),E(_V3));}},_Va=function(_Vb,_Vc,_Vd,_Ve,_Vf,_Vg){var _Vh=E(_Vg);if(!_Vh._){var _Vi=_Vh.a,_Vj=_Vh.b,_Vk=_Vh.c,_Vl=_Vh.d,_Vm=_Vh.e;if((imul(3,_Vb)|0)>=_Vi){if((imul(3,_Vi)|0)>=_Vb){return new F(function(){return _UM(new T5(0,_Vb,E(_Vc),_Vd,E(_Ve),E(_Vf)),_Vh);});}else{return new F(function(){return _y4(_Vc,_Vd,_Ve,B(_UX(_Vf,_Vi,_Vj,_Vk,_Vl,_Vm)));});}}else{return new F(function(){return _yV(_Vj,_Vk,B(_Va(_Vb,_Vc,_Vd,_Ve,_Vf,_Vl)),_Vm);});}}else{return new T5(0,_Vb,E(_Vc),_Vd,E(_Ve),E(_Vf));}},_Vn=function(_Vo,_Vp){var _Vq=E(_Vo);if(!_Vq._){var _Vr=_Vq.a,_Vs=_Vq.b,_Vt=_Vq.c,_Vu=_Vq.d,_Vv=_Vq.e,_Vw=E(_Vp);if(!_Vw._){var _Vx=_Vw.a,_Vy=_Vw.b,_Vz=_Vw.c,_VA=_Vw.d,_VB=_Vw.e;if((imul(3,_Vr)|0)>=_Vx){if((imul(3,_Vx)|0)>=_Vr){return new F(function(){return _UM(_Vq,_Vw);});}else{return new F(function(){return _y4(_Vs,_Vt,_Vu,B(_UX(_Vv,_Vx,_Vy,_Vz,_VA,_VB)));});}}else{return new F(function(){return _yV(_Vy,_Vz,B(_Va(_Vr,_Vs,_Vt,_Vu,_Vv,_VA)),_VB);});}}else{return E(_Vq);}}else{return E(_Vp);}},_VC=function(_VD,_VE){var _VF=E(_VE);if(!_VF._){var _VG=_VF.b,_VH=_VF.c,_VI=B(_VC(_VD,_VF.d)),_VJ=_VI.a,_VK=_VI.b,_VL=B(_VC(_VD,_VF.e)),_VM=_VL.a,_VN=_VL.b;return (!B(A2(_VD,_VG,_VH)))?new T2(0,B(_Vn(_VJ,_VM)),B(_Af(_VG,_VH,_VK,_VN))):new T2(0,B(_Af(_VG,_VH,_VJ,_VM)),B(_Vn(_VK,_VN)));}else{return new T2(0,_xZ,_xZ);}},_VO=__Z,_VP=function(_VQ,_VR){while(1){var _VS=B((function(_VT,_VU){var _VV=E(_VU);if(!_VV._){var _VW=_VV.e,_VX=new T(function(){var _VY=E(_VV.c),_VZ=E(_VY.b);if(!_VZ._){return new T2(1,new T3(5,_VV.b,_VY.a,_VZ.a),new T(function(){return B(_VP(_VT,_VW));}));}else{return B(_VP(_VT,_VW));}},1);_VQ=_VX;_VR=_VV.d;return __continue;}else{return E(_VT);}})(_VQ,_VR));if(_VS!=__continue){return _VS;}}},_W0=function(_W1,_W2){var _W3=E(_W2);return (_W3._==0)?new T5(0,_W3.a,E(_W3.b),new T(function(){return B(A1(_W1,_W3.c));}),E(B(_W0(_W1,_W3.d))),E(B(_W0(_W1,_W3.e)))):new T0(1);},_W4=new T0(1),_W5=function(_W6){var _W7=E(_W6),_W8=E(_W7.b);return new T2(0,_W7.a,_W4);},_W9=function(_Wa){return E(E(_Wa).b);},_Wb=function(_Wc,_Wd,_We){var _Wf=E(_Wd);if(!_Wf._){return E(_We);}else{var _Wg=function(_Wh,_Wi){while(1){var _Wj=E(_Wi);if(!_Wj._){var _Wk=_Wj.b,_Wl=_Wj.e;switch(B(A3(_W9,_Wc,_Wh,_Wk))){case 0:return new F(function(){return _Af(_Wk,_Wj.c,B(_Wg(_Wh,_Wj.d)),_Wl);});break;case 1:return E(_Wl);default:_Wi=_Wl;continue;}}else{return new T0(1);}}};return new F(function(){return _Wg(_Wf.a,_We);});}},_Wm=function(_Wn,_Wo,_Wp){var _Wq=E(_Wo);if(!_Wq._){return E(_Wp);}else{var _Wr=function(_Ws,_Wt){while(1){var _Wu=E(_Wt);if(!_Wu._){var _Wv=_Wu.b,_Ww=_Wu.d;switch(B(A3(_W9,_Wn,_Wv,_Ws))){case 0:return new F(function(){return _Af(_Wv,_Wu.c,_Ww,B(_Wr(_Ws,_Wu.e)));});break;case 1:return E(_Ww);default:_Wt=_Ww;continue;}}else{return new T0(1);}}};return new F(function(){return _Wr(_Wq.a,_Wp);});}},_Wx=function(_Wy,_Wz,_WA,_WB){var _WC=E(_Wz),_WD=E(_WB);if(!_WD._){var _WE=_WD.b,_WF=_WD.c,_WG=_WD.d,_WH=_WD.e;switch(B(A3(_W9,_Wy,_WC,_WE))){case 0:return new F(function(){return _yV(_WE,_WF,B(_Wx(_Wy,_WC,_WA,_WG)),_WH);});break;case 1:return E(_WD);default:return new F(function(){return _y4(_WE,_WF,_WG,B(_Wx(_Wy,_WC,_WA,_WH)));});}}else{return new T5(0,1,E(_WC),_WA,E(_xZ),E(_xZ));}},_WI=function(_WJ,_WK,_WL,_WM){return new F(function(){return _Wx(_WJ,_WK,_WL,_WM);});},_WN=function(_WO){return E(E(_WO).d);},_WP=function(_WQ){return E(E(_WQ).f);},_WR=function(_WS,_WT,_WU,_WV){var _WW=E(_WT);if(!_WW._){var _WX=E(_WU);if(!_WX._){return E(_WV);}else{var _WY=function(_WZ,_X0){while(1){var _X1=E(_X0);if(!_X1._){if(!B(A3(_WP,_WS,_X1.b,_WZ))){return E(_X1);}else{_X0=_X1.d;continue;}}else{return new T0(1);}}};return new F(function(){return _WY(_WX.a,_WV);});}}else{var _X2=_WW.a,_X3=E(_WU);if(!_X3._){var _X4=function(_X5,_X6){while(1){var _X7=E(_X6);if(!_X7._){if(!B(A3(_WN,_WS,_X7.b,_X5))){return E(_X7);}else{_X6=_X7.e;continue;}}else{return new T0(1);}}};return new F(function(){return _X4(_X2,_WV);});}else{var _X8=function(_X9,_Xa,_Xb){while(1){var _Xc=E(_Xb);if(!_Xc._){var _Xd=_Xc.b;if(!B(A3(_WN,_WS,_Xd,_X9))){if(!B(A3(_WP,_WS,_Xd,_Xa))){return E(_Xc);}else{_Xb=_Xc.d;continue;}}else{_Xb=_Xc.e;continue;}}else{return new T0(1);}}};return new F(function(){return _X8(_X2,_X3.a,_WV);});}}},_Xe=function(_Xf,_Xg,_Xh,_Xi,_Xj){var _Xk=E(_Xj);if(!_Xk._){var _Xl=_Xk.b,_Xm=_Xk.c,_Xn=_Xk.d,_Xo=_Xk.e,_Xp=E(_Xi);if(!_Xp._){var _Xq=_Xp.b,_Xr=function(_Xs){var _Xt=new T1(1,E(_Xq));return new F(function(){return _Af(_Xq,_Xp.c,B(_Xe(_Xf,_Xg,_Xt,_Xp.d,B(_WR(_Xf,_Xg,_Xt,_Xk)))),B(_Xe(_Xf,_Xt,_Xh,_Xp.e,B(_WR(_Xf,_Xt,_Xh,_Xk)))));});};if(!E(_Xn)._){return new F(function(){return _Xr(_);});}else{if(!E(_Xo)._){return new F(function(){return _Xr(_);});}else{return new F(function(){return _WI(_Xf,_Xl,_Xm,_Xp);});}}}else{return new F(function(){return _Af(_Xl,_Xm,B(_Wb(_Xf,_Xg,_Xn)),B(_Wm(_Xf,_Xh,_Xo)));});}}else{return E(_Xi);}},_Xu=function(_Xv,_Xw,_Xx,_Xy,_Xz,_XA,_XB,_XC,_XD,_XE,_XF,_XG,_XH){var _XI=function(_XJ){var _XK=new T1(1,E(_Xz));return new F(function(){return _Af(_Xz,_XA,B(_Xe(_Xv,_Xw,_XK,_XB,B(_WR(_Xv,_Xw,_XK,new T5(0,_XD,E(_XE),_XF,E(_XG),E(_XH)))))),B(_Xe(_Xv,_XK,_Xx,_XC,B(_WR(_Xv,_XK,_Xx,new T5(0,_XD,E(_XE),_XF,E(_XG),E(_XH)))))));});};if(!E(_XG)._){return new F(function(){return _XI(_);});}else{if(!E(_XH)._){return new F(function(){return _XI(_);});}else{return new F(function(){return _WI(_Xv,_XE,_XF,new T5(0,_Xy,E(_Xz),_XA,E(_XB),E(_XC)));});}}},_XL=function(_XM,_XN,_XO){var _XP=new T(function(){var _XQ=new T(function(){return E(E(_XO).b);}),_XR=B(_VC(function(_XS,_XT){var _XU=E(_XT);return new F(function(){return _Un(_XM,_XQ,_XS,_XU.a,_XU.b);});},_XN));return new T2(0,_XR.a,_XR.b);}),_XV=new T(function(){return E(E(_XP).a);});return new T2(0,new T(function(){var _XW=B(_W0(_W5,_XV));if(!_XW._){var _XX=E(E(_XP).b);if(!_XX._){return B(_Xu(_Tr,_VO,_VO,_XW.a,_XW.b,_XW.c,_XW.d,_XW.e,_XX.a,_XX.b,_XX.c,_XX.d,_XX.e));}else{return E(_XW);}}else{return E(E(_XP).b);}}),new T(function(){return B(_VP(_1I,_XV));}));},_XY=function(_XZ,_Y0,_Y1,_Y2){while(1){var _Y3=E(_Y2);if(!_Y3._){var _Y4=_Y3.d,_Y5=_Y3.e,_Y6=E(_Y3.b),_Y7=E(_Y6.a);if(_XZ>=_Y7){if(_XZ!=_Y7){_Y0=_;_Y2=_Y5;continue;}else{var _Y8=E(_Y6.b);if(_Y1>=_Y8){if(_Y1!=_Y8){_Y0=_;_Y2=_Y5;continue;}else{return true;}}else{_Y0=_;_Y2=_Y4;continue;}}}else{_Y0=_;_Y2=_Y4;continue;}}else{return false;}}},_Y9=function(_Ya,_Yb,_Yc,_Yd){while(1){var _Ye=E(_Yd);if(!_Ye._){var _Yf=_Ye.d,_Yg=_Ye.e,_Yh=E(_Ye.b),_Yi=E(_Yh.a);if(_Ya>=_Yi){if(_Ya!=_Yi){_Yb=_;_Yd=_Yg;continue;}else{var _Yj=E(_Yc),_Yk=E(_Yh.b);if(_Yj>=_Yk){if(_Yj!=_Yk){return new F(function(){return _XY(_Ya,_,_Yj,_Yg);});}else{return true;}}else{return new F(function(){return _XY(_Ya,_,_Yj,_Yf);});}}}else{_Yb=_;_Yd=_Yf;continue;}}else{return false;}}},_Yl=function(_Ym,_Yn,_Yo,_Yp,_Yq){var _Yr=E(_Yq);if(!_Yr._){var _Ys=_Yr.c,_Yt=_Yr.d,_Yu=_Yr.e,_Yv=E(_Yr.b),_Yw=E(_Yv.a);if(_Ym>=_Yw){if(_Ym!=_Yw){return new F(function(){return _y4(_Yv,_Ys,_Yt,B(_Yl(_Ym,_,_Yo,_Yp,_Yu)));});}else{var _Yx=E(_Yv.b);if(_Yo>=_Yx){if(_Yo!=_Yx){return new F(function(){return _y4(_Yv,_Ys,_Yt,B(_Yl(_Ym,_,_Yo,_Yp,_Yu)));});}else{return new T5(0,_Yr.a,E(new T2(0,_Ym,_Yo)),_Yp,E(_Yt),E(_Yu));}}else{return new F(function(){return _yV(_Yv,_Ys,B(_Yl(_Ym,_,_Yo,_Yp,_Yt)),_Yu);});}}}else{return new F(function(){return _yV(_Yv,_Ys,B(_Yl(_Ym,_,_Yo,_Yp,_Yt)),_Yu);});}}else{return new T5(0,1,E(new T2(0,_Ym,_Yo)),_Yp,E(_xZ),E(_xZ));}},_Yy=function(_Yz,_YA,_YB,_YC,_YD){var _YE=E(_YD);if(!_YE._){var _YF=_YE.c,_YG=_YE.d,_YH=_YE.e,_YI=E(_YE.b),_YJ=E(_YI.a);if(_Yz>=_YJ){if(_Yz!=_YJ){return new F(function(){return _y4(_YI,_YF,_YG,B(_Yy(_Yz,_,_YB,_YC,_YH)));});}else{var _YK=E(_YB),_YL=E(_YI.b);if(_YK>=_YL){if(_YK!=_YL){return new F(function(){return _y4(_YI,_YF,_YG,B(_Yl(_Yz,_,_YK,_YC,_YH)));});}else{return new T5(0,_YE.a,E(new T2(0,_Yz,_YK)),_YC,E(_YG),E(_YH));}}else{return new F(function(){return _yV(_YI,_YF,B(_Yl(_Yz,_,_YK,_YC,_YG)),_YH);});}}}else{return new F(function(){return _yV(_YI,_YF,B(_Yy(_Yz,_,_YB,_YC,_YG)),_YH);});}}else{return new T5(0,1,E(new T2(0,_Yz,_YB)),_YC,E(_xZ),E(_xZ));}},_YM=function(_YN,_YO,_YP,_YQ){var _YR=E(_YQ);if(!_YR._){var _YS=_YR.c,_YT=_YR.d,_YU=_YR.e,_YV=E(_YR.b),_YW=E(_YN),_YX=E(_YV.a);if(_YW>=_YX){if(_YW!=_YX){return new F(function(){return _y4(_YV,_YS,_YT,B(_Yy(_YW,_,_YO,_YP,_YU)));});}else{var _YY=E(_YO),_YZ=E(_YV.b);if(_YY>=_YZ){if(_YY!=_YZ){return new F(function(){return _y4(_YV,_YS,_YT,B(_Yl(_YW,_,_YY,_YP,_YU)));});}else{return new T5(0,_YR.a,E(new T2(0,_YW,_YY)),_YP,E(_YT),E(_YU));}}else{return new F(function(){return _yV(_YV,_YS,B(_Yl(_YW,_,_YY,_YP,_YT)),_YU);});}}}else{return new F(function(){return _yV(_YV,_YS,B(_Yy(_YW,_,_YO,_YP,_YT)),_YU);});}}else{return new T5(0,1,E(new T2(0,_YN,_YO)),_YP,E(_xZ),E(_xZ));}},_Z0=function(_Z1,_Z2,_Z3){while(1){var _Z4=B((function(_Z5,_Z6,_Z7){var _Z8=E(_Z7);if(!_Z8._){var _Z9=_Z8.c,_Za=_Z8.e,_Zb=E(_Z8.b),_Zc=_Zb.a,_Zd=_Zb.b,_Ze=B(_Z0(_Z5,_Z6,_Z8.d)),_Zf=_Ze.a,_Zg=_Ze.b,_Zh=function(_Zi){return new F(function(){return _Z0(new T(function(){return B(_YM(_Zc,_Zd,_Z9,_Zf));}),new T2(1,new T3(7,_Zc,_Zd,_Z9),_Zg),_Za);});},_Zj=E(_Zf);if(!_Zj._){var _Zk=_Zj.d,_Zl=_Zj.e,_Zm=E(_Zj.b),_Zn=E(_Zc),_Zo=E(_Zm.a);if(_Zn>=_Zo){if(_Zn!=_Zo){if(!B(_Y9(_Zn,_,_Zd,_Zl))){return new F(function(){return _Zh(_);});}else{_Z1=_Zj;_Z2=_Zg;_Z3=_Za;return __continue;}}else{var _Zp=E(_Zd),_Zq=E(_Zm.b);if(_Zp>=_Zq){if(_Zp!=_Zq){if(!B(_XY(_Zn,_,_Zp,_Zl))){return new F(function(){return _Zh(_);});}else{_Z1=_Zj;_Z2=_Zg;_Z3=_Za;return __continue;}}else{_Z1=_Zj;_Z2=_Zg;_Z3=_Za;return __continue;}}else{if(!B(_XY(_Zn,_,_Zp,_Zk))){return new F(function(){return _Zh(_);});}else{_Z1=_Zj;_Z2=_Zg;_Z3=_Za;return __continue;}}}}else{if(!B(_Y9(_Zn,_,_Zd,_Zk))){return new F(function(){return _Zh(_);});}else{_Z1=_Zj;_Z2=_Zg;_Z3=_Za;return __continue;}}}else{return new F(function(){return _Zh(_);});}}else{return new T2(0,_Z5,_Z6);}})(_Z1,_Z2,_Z3));if(_Z4!=__continue){return _Z4;}}},_Zr=0,_Zs=function(_Zt,_Zu,_Zv,_Zw){while(1){var _Zx=E(_Zw);if(!_Zx._){var _Zy=_Zx.d,_Zz=_Zx.e,_ZA=E(_Zx.b),_ZB=E(_ZA.a);if(_Zt>=_ZB){if(_Zt!=_ZB){_Zu=_;_Zw=_Zz;continue;}else{var _ZC=E(_ZA.b);if(_Zv>=_ZC){if(_Zv!=_ZC){_Zu=_;_Zw=_Zz;continue;}else{return new T1(1,_Zx.c);}}else{_Zu=_;_Zw=_Zy;continue;}}}else{_Zu=_;_Zw=_Zy;continue;}}else{return __Z;}}},_ZD=function(_ZE,_ZF,_ZG,_ZH){while(1){var _ZI=E(_ZH);if(!_ZI._){var _ZJ=_ZI.d,_ZK=_ZI.e,_ZL=E(_ZI.b),_ZM=E(_ZL.a);if(_ZE>=_ZM){if(_ZE!=_ZM){_ZF=_;_ZH=_ZK;continue;}else{var _ZN=E(_ZG),_ZO=E(_ZL.b);if(_ZN>=_ZO){if(_ZN!=_ZO){return new F(function(){return _Zs(_ZE,_,_ZN,_ZK);});}else{return new T1(1,_ZI.c);}}else{return new F(function(){return _Zs(_ZE,_,_ZN,_ZJ);});}}}else{_ZF=_;_ZH=_ZJ;continue;}}else{return __Z;}}},_ZP=function(_ZQ,_ZR,_ZS,_ZT,_ZU){while(1){var _ZV=E(_ZU);if(!_ZV._){var _ZW=_ZV.c,_ZX=_ZV.d,_ZY=E(_ZV.b),_ZZ=E(_ZQ),_100=E(_ZY.a);if(_ZZ>=_100){if(_ZZ!=_100){_ZQ=_ZZ;_ZU=_ZX;continue;}else{var _101=E(_ZR),_102=E(_ZY.b);if(_101>=_102){if(_101!=_102){_ZQ=_ZZ;_ZR=_101;_ZU=_ZX;continue;}else{var _103=E(_ZS),_104=E(_ZY.c);if(_103>=_104){if(_103!=_104){_ZQ=_ZZ;_ZR=_101;_ZS=_103;_ZU=_ZX;continue;}else{var _105=E(_ZY.d);if(_ZT>=_105){if(_ZT!=_105){_ZQ=_ZZ;_ZR=_101;_ZS=_103;_ZU=_ZX;continue;}else{return true;}}else{_ZQ=_ZZ;_ZR=_101;_ZS=_103;_ZU=_ZW;continue;}}}else{_ZQ=_ZZ;_ZR=_101;_ZS=_103;_ZU=_ZW;continue;}}}else{_ZQ=_ZZ;_ZR=_101;_ZU=_ZW;continue;}}}else{_ZQ=_ZZ;_ZU=_ZW;continue;}}else{return false;}}},_106=function(_107,_108){return E(_107)+E(_108)|0;},_109=function(_10a,_10b,_10c){var _10d=function(_10e,_10f){while(1){var _10g=B((function(_10h,_10i){var _10j=E(_10i);if(!_10j._){var _10k=new T(function(){return B(_10d(_10h,_10j.e));}),_10l=function(_10m){var _10n=E(_10j.c),_10o=E(_10n.b);if(!_10o._){if(E(_10n.a)!=E(_10b)){return new F(function(){return A1(_10k,_10m);});}else{if(E(_10o.b)>E(_10c)){return new F(function(){return A1(_10k,new T(function(){return B(_106(_10m,_10o.a));}));});}else{return new F(function(){return A1(_10k,_10m);});}}}else{return new F(function(){return A1(_10k,_10m);});}};_10e=_10l;_10f=_10j.d;return __continue;}else{return E(_10h);}})(_10e,_10f));if(_10g!=__continue){return _10g;}}};return new F(function(){return A3(_10d,_5r,_10a,_Zr);});},_10p=function(_10q,_10r){while(1){var _10s=E(_10r);if(!_10s._){var _10t=E(_10s.b);if(_10q>=_10t){if(_10q!=_10t){_10r=_10s.e;continue;}else{return new T1(1,_10s.c);}}else{_10r=_10s.d;continue;}}else{return __Z;}}},_10u=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_10v=new T(function(){return B(err(_10u));}),_10w=function(_10x,_10y){var _10z=E(_10y);if(!_10z._){return E(_10v);}else{var _10A=_10z.b,_10B=E(_10z.a),_10C=_10B.a,_10D=E(_10B.b),_10E=_10D.a,_10F=E(_10D.b);if(!_10F._){var _10G=_10F.b,_10H=E(_10F.a);return (_10x>_10H)?(_10H>=_10x)?E(_10A):new T2(1,new T2(0,_10C,new T2(0,_10E,new T2(0,_Zr,_10G))),new T(function(){return B(_10w(_10x-_10H|0,_10A));})):new T2(1,new T2(0,_10C,new T2(0,_10E,new T2(0,_10H-_10x|0,_10G))),_1I);}else{return E(_10A);}}},_10I=function(_10J,_10K){var _10L=E(_10K);if(!_10L._){return E(_10v);}else{var _10M=_10L.b,_10N=E(_10L.a),_10O=_10N.a,_10P=E(_10N.b),_10Q=_10P.a,_10R=E(_10P.b);if(!_10R._){var _10S=_10R.b,_10T=E(_10J),_10U=E(_10R.a);return (_10T>_10U)?(_10U>=_10T)?E(_10M):new T2(1,new T2(0,_10O,new T2(0,_10Q,new T2(0,_Zr,_10S))),new T(function(){return B(_10w(_10T-_10U|0,_10M));})):new T2(1,new T2(0,_10O,new T2(0,_10Q,new T2(0,_10U-_10T|0,_10S))),_1I);}else{return E(_10M);}}},_10V=function(_10W,_10X){var _10Y=E(_10X);if(!_10Y._){var _10Z=_10Y.b,_110=_10Y.c,_111=_10Y.d,_112=_10Y.e;if(!B(A2(_10W,_10Z,_110))){return new F(function(){return _Vn(B(_10V(_10W,_111)),B(_10V(_10W,_112)));});}else{return new F(function(){return _Af(_10Z,_110,B(_10V(_10W,_111)),B(_10V(_10W,_112)));});}}else{return new T0(1);}},_113=function(_114,_115){var _116=E(_114);if(!_116._){var _117=E(_115);if(!_117._){return new F(function(){return _Tc(_116.b,_117.b);});}else{return 0;}}else{return (E(_115)._==0)?2:1;}},_118=function(_119,_11a){return new F(function(){return _113(E(E(_119).b).b,E(E(_11a).b).b);});},_11b=new T2(1,_1I,_1I),_11c=function(_11d,_11e){var _11f=function(_11g,_11h){var _11i=E(_11g);if(!_11i._){return E(_11h);}else{var _11j=_11i.a,_11k=E(_11h);if(!_11k._){return E(_11i);}else{var _11l=_11k.a;return (B(A2(_11d,_11j,_11l))==2)?new T2(1,_11l,new T(function(){return B(_11f(_11i,_11k.b));})):new T2(1,_11j,new T(function(){return B(_11f(_11i.b,_11k));}));}}},_11m=function(_11n){var _11o=E(_11n);if(!_11o._){return __Z;}else{var _11p=E(_11o.b);return (_11p._==0)?E(_11o):new T2(1,new T(function(){return B(_11f(_11o.a,_11p.a));}),new T(function(){return B(_11m(_11p.b));}));}},_11q=new T(function(){return B(_11r(B(_11m(_1I))));}),_11r=function(_11s){while(1){var _11t=E(_11s);if(!_11t._){return E(_11q);}else{if(!E(_11t.b)._){return E(_11t.a);}else{_11s=B(_11m(_11t));continue;}}}},_11u=new T(function(){return B(_11v(_1I));}),_11w=function(_11x,_11y,_11z){while(1){var _11A=B((function(_11B,_11C,_11D){var _11E=E(_11D);if(!_11E._){return new T2(1,new T2(1,_11B,_11C),_11u);}else{var _11F=_11E.a;if(B(A2(_11d,_11B,_11F))==2){var _11G=new T2(1,_11B,_11C);_11x=_11F;_11y=_11G;_11z=_11E.b;return __continue;}else{return new T2(1,new T2(1,_11B,_11C),new T(function(){return B(_11v(_11E));}));}}})(_11x,_11y,_11z));if(_11A!=__continue){return _11A;}}},_11H=function(_11I,_11J,_11K){while(1){var _11L=B((function(_11M,_11N,_11O){var _11P=E(_11O);if(!_11P._){return new T2(1,new T(function(){return B(A1(_11N,new T2(1,_11M,_1I)));}),_11u);}else{var _11Q=_11P.a,_11R=_11P.b;switch(B(A2(_11d,_11M,_11Q))){case 0:_11I=_11Q;_11J=function(_11S){return new F(function(){return A1(_11N,new T2(1,_11M,_11S));});};_11K=_11R;return __continue;case 1:_11I=_11Q;_11J=function(_11T){return new F(function(){return A1(_11N,new T2(1,_11M,_11T));});};_11K=_11R;return __continue;default:return new T2(1,new T(function(){return B(A1(_11N,new T2(1,_11M,_1I)));}),new T(function(){return B(_11v(_11P));}));}}})(_11I,_11J,_11K));if(_11L!=__continue){return _11L;}}},_11v=function(_11U){var _11V=E(_11U);if(!_11V._){return E(_11b);}else{var _11W=_11V.a,_11X=E(_11V.b);if(!_11X._){return new T2(1,_11V,_1I);}else{var _11Y=_11X.a,_11Z=_11X.b;if(B(A2(_11d,_11W,_11Y))==2){return new F(function(){return _11w(_11Y,new T2(1,_11W,_1I),_11Z);});}else{return new F(function(){return _11H(_11Y,function(_120){return new T2(1,_11W,_120);},_11Z);});}}}};return new F(function(){return _11r(B(_11v(_11e)));});},_121=function(_122,_123,_124){var _125=B(_PE(B(_10I(_123,B(_11c(_118,B(_GQ(_1I,B(_10V(function(_126,_127){return new F(function(){return A1(_122,_127);});},_124))))))))));if(!_125._){var _128=E(_124);if(!_128._){return new F(function(){return _Xu(_Tr,_VO,_VO,_125.a,_125.b,_125.c,_125.d,_125.e,_128.a,_128.b,_128.c,_128.d,_128.e);});}else{return E(_125);}}else{return E(_124);}},_129=function(_12a,_12b,_12c,_12d){while(1){var _12e=E(_12d);if(!_12e._){var _12f=_12e.d,_12g=_12e.e,_12h=E(_12e.b),_12i=E(_12h.a);if(_12a>=_12i){if(_12a!=_12i){_12b=_;_12d=_12g;continue;}else{var _12j=E(_12h.b);if(_12c>=_12j){if(_12c!=_12j){_12b=_;_12d=_12g;continue;}else{return new T1(1,_12e.c);}}else{_12b=_;_12d=_12f;continue;}}}else{_12b=_;_12d=_12f;continue;}}else{return __Z;}}},_12k=function(_12l,_12m,_12n,_12o){while(1){var _12p=E(_12o);if(!_12p._){var _12q=_12p.d,_12r=_12p.e,_12s=E(_12p.b),_12t=E(_12s.a);if(_12l>=_12t){if(_12l!=_12t){_12m=_;_12o=_12r;continue;}else{var _12u=E(_12n),_12v=E(_12s.b);if(_12u>=_12v){if(_12u!=_12v){return new F(function(){return _129(_12l,_,_12u,_12r);});}else{return new T1(1,_12p.c);}}else{return new F(function(){return _129(_12l,_,_12u,_12q);});}}}else{_12m=_;_12o=_12q;continue;}}else{return __Z;}}},_12w=function(_12x,_12y,_12z){var _12A=E(_12z);if(!_12A._){var _12B=_12A.d,_12C=_12A.e,_12D=E(_12A.b),_12E=E(_12x),_12F=E(_12D.a);if(_12E>=_12F){if(_12E!=_12F){return new F(function(){return _Y9(_12E,_,_12y,_12C);});}else{var _12G=E(_12y),_12H=E(_12D.b);if(_12G>=_12H){if(_12G!=_12H){return new F(function(){return _XY(_12E,_,_12G,_12C);});}else{return true;}}else{return new F(function(){return _XY(_12E,_,_12G,_12B);});}}}else{return new F(function(){return _Y9(_12E,_,_12y,_12B);});}}else{return false;}},_12I=function(_12J,_12K,_12L){while(1){var _12M=E(_12K);switch(_12M._){case 0:return (E(_12M.a)>E(E(_12L).b))?true:false;case 1:if(!B(_12I(_12J,_12M.a,_12L))){return false;}else{_12K=_12M.b;continue;}break;case 2:if(!B(_12I(_12J,_12M.a,_12L))){_12K=_12M.b;continue;}else{return true;}break;case 3:return (!B(_12I(_12J,_12M.a,_12L)))?true:false;case 4:var _12N=_12M.b,_12O=_12M.c,_12P=E(E(_12J).b);if(!_12P._){var _12Q=_12P.d,_12R=_12P.e,_12S=E(_12P.b),_12T=E(_12M.a),_12U=E(_12S.a);if(_12T>=_12U){if(_12T!=_12U){var _12V=B(_12k(_12T,_,_12N,_12R));if(!_12V._){return false;}else{return new F(function(){return _QC(_12V.a,_12O);});}}else{var _12W=E(_12N),_12X=E(_12S.b);if(_12W>=_12X){if(_12W!=_12X){var _12Y=B(_129(_12T,_,_12W,_12R));if(!_12Y._){return false;}else{return new F(function(){return _QC(_12Y.a,_12O);});}}else{return new F(function(){return _QC(_12P.c,_12O);});}}else{var _12Z=B(_129(_12T,_,_12W,_12Q));if(!_12Z._){return false;}else{return new F(function(){return _QC(_12Z.a,_12O);});}}}}else{var _130=B(_12k(_12T,_,_12N,_12Q));if(!_130._){return false;}else{return new F(function(){return _QC(_130.a,_12O);});}}}else{return false;}break;case 5:return new F(function(){return _12w(_12M.a,_12M.b,E(_12J).b);});break;case 6:return true;default:return false;}}},_131=function(_132,_133,_134,_135){var _136=E(_134);switch(_136._){case 0:return new T3(0,_133,_j3,_1I);case 1:var _137=_136.b,_138=E(_133),_139=_138.a,_13a=E(_136.a),_13b=B(_10p(_13a,_139));if(!_13b._){return new T3(0,_138,_136,_1I);}else{var _13c=E(_13b.a),_13d=_13c.a,_13e=E(_13c.b);if(!_13e._){var _13f=_13e.a;return (!B(_TT(_13a,_,_13d,_13f,E(_132).b)))?new T3(0,_138,_136,_1I):new T3(0,new T2(0,new T(function(){return B(_OL(_13a,new T2(0,_13d,_W4),_139));}),_138.b),_137,new T2(1,new T3(4,_13a,_13d,_13f),_1I));}else{return new T3(0,_138,_137,new T2(1,new T2(6,_13a,_13d),_1I));}}break;case 2:var _13g=_136.a,_13h=_136.b,_13i=_136.c,_13j=_136.d,_13k=_136.f,_13l=E(E(_135).b);if(E(_136.e)>_13l){var _13m=function(_13n){var _13o=E(_13j);if(E(_13n)!=_13o){return new T3(0,_133,_136,_1I);}else{var _13p=E(_133),_13q=_13p.a;if(B(_109(_13q,_13h,_13l))<_13o){return new T3(0,_13p,_13k,new T2(1,new T4(2,_13g,_13h,_13i,_13o),_1I));}else{var _13r=new T(function(){return B(_121(function(_13s){var _13t=E(_13s),_13u=E(_13t.b);return (_13u._==0)?(E(_13t.a)!=E(_13h))?false:(E(_13u.b)>_13l)?true:false:false;},_13o,_13q));});return new T3(0,new T2(0,_13r,_13p.b),_13k,new T2(1,new T4(0,_13g,_13h,_13i,_13o),_1I));}}},_13v=E(E(_132).c);if(!_13v._){var _13w=_13v.d,_13x=_13v.e,_13y=E(_13v.b),_13z=E(_13g),_13A=E(_13y.a);if(_13z>=_13A){if(_13z!=_13A){var _13B=B(_ZD(_13z,_,_13i,_13x));if(!_13B._){return new T3(0,_133,_136,_1I);}else{return new F(function(){return _13m(_13B.a);});}}else{var _13C=E(_13i),_13D=E(_13y.b);if(_13C>=_13D){if(_13C!=_13D){var _13E=B(_Zs(_13z,_,_13C,_13x));if(!_13E._){return new T3(0,_133,_136,_1I);}else{return new F(function(){return _13m(_13E.a);});}}else{return new F(function(){return _13m(_13v.c);});}}else{var _13F=B(_Zs(_13z,_,_13C,_13w));if(!_13F._){return new T3(0,_133,_136,_1I);}else{return new F(function(){return _13m(_13F.a);});}}}}else{var _13G=B(_ZD(_13z,_,_13i,_13w));if(!_13G._){return new T3(0,_133,_136,_1I);}else{return new F(function(){return _13m(_13G.a);});}}}else{return new T3(0,_133,_136,_1I);}}else{return new T3(0,_133,_13k,new T2(1,new T4(1,_13g,_13h,_13i,_13j),_1I));}break;case 3:var _13H=new T(function(){var _13I=B(_131(_132,_133,_136.a,_135));return new T3(0,_13I.a,_13I.b,_13I.c);}),_13J=new T(function(){var _13K=B(_131(_132,new T(function(){return E(E(_13H).a);}),_136.b,_135));return new T3(0,_13K.a,_13K.b,_13K.c);}),_13L=new T(function(){return B(_2(E(_13H).c,new T(function(){return E(E(_13J).c);},1)));}),_13M=new T(function(){var _13N=E(_13H).b,_13O=E(_13J).b,_13P=function(_13Q){var _13R=E(_13O);switch(_13R._){case 0:return E(_13N);case 1:return new T2(3,_13N,_13R);case 2:return new T2(3,_13N,_13R);case 3:return new T2(3,_13N,_13R);case 4:return new T2(3,_13N,_13R);case 5:return new T2(3,_13N,_13R);default:return new T2(3,_13N,_13R);}};switch(E(_13N)._){case 0:return E(_13O);break;case 1:return B(_13P(_));break;case 2:return B(_13P(_));break;case 3:return B(_13P(_));break;case 4:return B(_13P(_));break;case 5:return B(_13P(_));break;default:return B(_13P(_));}});return new T3(0,new T(function(){return E(E(_13J).a);}),_13M,_13L);case 4:return (!B(_12I(_133,_136.a,_135)))?new T3(0,_133,_136.c,_1I):new T3(0,_133,_136.b,_1I);case 5:var _13S=_136.a,_13T=_136.b,_13U=_136.c,_13V=_136.f,_13W=E(_136.e),_13X=E(E(_135).b),_13Y=_13W<=_13X,_13Z=new T(function(){return E(_136.d)<=_13X;}),_140=new T(function(){return B(_OL(E(_13S),new T2(0,_13T,new T(function(){if(!E(_13Y)){if(!E(_13Z)){return new T2(0,_13U,_13W);}else{return new T0(1);}}else{return new T0(1);}})),E(_133).a));});return (!E(_13Y))?(!E(_13Z))?(!B(_ZP(_13S,_13T,_13U,_13W,E(_132).a)))?new T3(0,_133,_136,_1I):new T3(0,new T(function(){return new T2(0,_140,E(_133).b);}),_13V,new T2(1,new T3(3,_13S,_13T,_13U),_1I)):new T3(0,new T(function(){return new T2(0,_140,E(_133).b);}),_13V,new T2(1,new T3(3,_13S,_13T,_Zr),new T2(1,new T3(4,_13S,_13T,_Zr),_1I))):new T3(0,new T(function(){return new T2(0,_140,E(_133).b);}),_13V,new T2(1,new T3(3,_13S,_13T,_Zr),new T2(1,new T3(4,_13S,_13T,_Zr),_1I)));default:var _141=E(_135);return (E(_136.b)>E(_141.b))?(!B(_12I(_133,_136.a,_141)))?new T3(0,_133,_136,_1I):new T3(0,_133,_136.c,_1I):new T3(0,_133,_136.d,_1I);}},_142=function(_143,_144,_145,_146){var _147=new T(function(){var _148=B(_XL(_143,new T(function(){return E(E(_144).a);},1),_146));return new T2(0,_148.a,_148.b);}),_149=new T(function(){var _14a=B(_Z0(new T(function(){return E(E(_144).b);}),_1I,E(_143).d));return new T2(0,_14a.a,_14a.b);}),_14b=new T(function(){var _14c=new T(function(){var _14d=E(_144);return new T2(0,new T(function(){return E(E(_147).a);}),new T(function(){return E(E(_149).a);}));}),_14e=B(_131(_143,_14c,_145,_146));return new T3(0,_14e.a,_14e.b,_14e.c);}),_14f=new T(function(){var _14g=new T(function(){return B(_2(E(_147).b,new T(function(){return E(E(_14b).c);},1)));},1);return B(_2(E(_149).b,_14g));});return new T3(0,new T(function(){return E(E(_14b).a);}),new T(function(){return E(E(_14b).b);}),_14f);},_14h=function(_14i,_14j,_14k,_14l,_14m,_14n){var _14o=new T2(0,_14j,_14k),_14p=B(_142(_14i,_14o,_14l,_14m)),_14q=_14p.b,_14r=_14p.c,_14s=E(_14p.a),_14t=_14s.a,_14u=_14s.b,_14v=function(_14w){return new F(function(){return _14h(_14i,_14t,_14u,_14q,_14m,new T(function(){return B(_2(_14r,_14n));}));});};if(!B(A2(_SY,_14t,_14j))){return new F(function(){return _14v(_);});}else{if(!B(A2(_Su,_14u,_14k))){return new F(function(){return _14v(_);});}else{if(!B(_R5(_14q,_14l))){return new F(function(){return _14v(_);});}else{if(!B(_Sb(_QU,_14r,_1I))){return new F(function(){return _14v(_);});}else{return new T3(0,_14o,_14l,_14n);}}}}},_14x=new T(function(){return B(err(_1J));}),_14y=new T(function(){return B(err(_1T));}),_14z=new T(function(){return B(A3(_g9,_gC,_fE,_kL));}),_14A=new T(function(){return B(err(_1J));}),_14B=new T(function(){return B(err(_1T));}),_14C=function(_Jy){return new F(function(){return _fY(_gU,_Jy);});},_14D=function(_14E,_14F){return new F(function(){return _IO(_14C,_14F);});},_14G=new T(function(){return B(_IO(_14C,_4E));}),_14H=function(_Jy){return new F(function(){return _3h(_14G,_Jy);});},_14I=function(_14J){var _14K=new T(function(){return B(A3(_fY,_gU,_14J,_4E));});return function(_Jv){return new F(function(){return _3h(_14K,_Jv);});};},_14L=new T4(0,_14I,_14H,_14C,_14D),_14M=new T(function(){return B(unCStr("NotRedeemed"));}),_14N=function(_14O,_14P){var _14Q=new T(function(){var _14R=new T(function(){return B(A1(_14P,_W4));});return B(_f7(function(_14S){var _14T=E(_14S);return (_14T._==3)?(!B(_47(_14T.a,_NW)))?new T0(2):E(_14R):new T0(2);}));}),_14U=function(_14V){return E(_14Q);},_14W=new T(function(){if(E(_14O)>10){return new T0(2);}else{var _14X=new T(function(){var _14Y=new T(function(){var _14Z=function(_150){return new F(function(){return A3(_g9,_gC,_43,function(_151){return new F(function(){return A1(_14P,new T2(0,_150,_151));});});});};return B(A3(_g9,_gC,_43,_14Z));});return B(_f7(function(_152){var _153=E(_152);return (_153._==3)?(!B(_47(_153.a,_14M)))?new T0(2):E(_14Y):new T0(2);}));}),_154=function(_155){return E(_14X);};return new T1(1,function(_156){return new F(function(){return A2(_dO,_156,_154);});});}});return new F(function(){return _3r(new T1(1,function(_157){return new F(function(){return A2(_dO,_157,_14U);});}),_14W);});},_158=function(_Jy){return new F(function(){return _fY(_14N,_Jy);});},_159=function(_15a,_15b){return new F(function(){return _IO(_158,_15b);});},_15c=new T(function(){return B(_IO(_158,_4E));}),_15d=function(_Jy){return new F(function(){return _3h(_15c,_Jy);});},_15e=function(_15f){var _15g=new T(function(){return B(A3(_fY,_14N,_15f,_4E));});return function(_Jv){return new F(function(){return _3h(_15g,_Jv);});};},_15h=new T4(0,_15e,_15d,_158,_159),_15i=function(_15j,_15k){return new F(function(){return _K3(_Jw,_15h,_15k);});},_15l=new T(function(){return B(_IO(_15i,_4E));}),_15m=function(_Jy){return new F(function(){return _3h(_15l,_Jy);});},_15n=new T(function(){return B(_K3(_Jw,_15h,_4E));}),_15o=function(_Jy){return new F(function(){return _3h(_15n,_Jy);});},_15p=function(_15q,_Jy){return new F(function(){return _15o(_Jy);});},_15r=function(_15s,_15t){return new F(function(){return _IO(_15i,_15t);});},_15u=new T4(0,_15p,_15m,_15i,_15r),_15v=function(_15w,_15x){return new F(function(){return _K3(_14L,_15u,_15x);});},_15y=function(_15z,_15A){return new F(function(){return _IO(_15v,_15A);});},_15B=new T(function(){return B(_IO(_15y,_4E));}),_15C=function(_Ky){return new F(function(){return _3h(_15B,_Ky);});},_15D=function(_15E){return new F(function(){return _IO(_15y,_15E);});},_15F=function(_15G,_15H){return new F(function(){return _15D(_15H);});},_15I=new T(function(){return B(_IO(_15v,_4E));}),_15J=function(_Ky){return new F(function(){return _3h(_15I,_Ky);});},_15K=function(_15L,_Ky){return new F(function(){return _15J(_Ky);});},_15M=new T4(0,_15K,_15C,_15y,_15F),_15N=new T(function(){return B(_K3(_15M,_KI,_kL));}),_15O=new T(function(){return B(unAppCStr("[]",_1I));}),_15P=42,_15Q=new T2(1,_2o,_1I),_15R=function(_15S){var _15T=E(_15S);if(!_15T._){return E(_15Q);}else{var _15U=new T(function(){return B(_PZ(0,_15T.a,new T(function(){return B(_15R(_15T.b));})));});return new T2(1,_2n,_15U);}},_15V=function(_){var _15W=E(_Nb),_15X=eval(E(_pD)),_15Y=_15X,_15Z=__app1(E(_15Y),toJSStr(_15W)),_160=E(_NB),_161=__app1(E(_15Y),toJSStr(_160)),_162=__app0(E(_kR)),_163=E(_ND),_164=__app1(E(_15Y),toJSStr(_163)),_165=new T(function(){var _166=B(_kS(B(_3h(_14z,new T(function(){var _167=String(_164);return fromJSStr(_167);})))));if(!_166._){return E(_14y);}else{if(!E(_166.b)._){return E(_166.a);}else{return E(_14x);}}}),_168=B(_kS(B(_3h(_15N,new T(function(){var _169=String(_161);return fromJSStr(_169);})))));if(!_168._){return E(_14B);}else{if(!E(_168.b)._){var _16a=E(_168.a),_16b=new T(function(){var _16c=B(_kS(B(_3h(_kQ,new T(function(){var _16d=String(_162);return fromJSStr(_16d);})))));if(!_16c._){return E(_1U);}else{if(!E(_16c.b)._){return E(_16c.a);}else{return E(_1K);}}}),_16e=new T(function(){var _16f=B(_kS(B(_3h(_Na,new T(function(){var _16g=String(_15Z);return fromJSStr(_16g);})))));if(!_16f._){return E(_IK);}else{if(!E(_16f.b)._){var _16h=E(_16f.a);return new T4(0,new T(function(){return B(_tn(_16h.a));}),new T(function(){return B(_xK(_16h.b));}),new T(function(){return B(_GA(_16h.c));}),new T(function(){return B(_Dq(_16h.d));}));}else{return E(_IJ);}}}),_16i=B(_14h(_16e,new T(function(){return B(_PE(_16a.a));}),new T(function(){return B(_Dq(_16a.b));}),_16b,new T2(0,_15P,_165),_1I)),_16j=function(_,_16k){var _16l=B(_1O(_1L,B(_1a(0,_16i.b,_1I)),_)),_16m=E(_16i.a),_16n=new T(function(){var _16o=new T(function(){return B(_GQ(_1I,_16m.b));}),_16p=new T(function(){return B(_GQ(_1I,_16m.a));});return B(A3(_HD,_GX,new T2(1,function(_16q){return new F(function(){return _On(_16p,_16q);});},new T2(1,function(_16r){return new F(function(){return _Ik(_16o,_16r);});},_1I)),_In));}),_16s=B(_1O(_160,new T2(1,_b,_16n),_)),_16t=B(_1O(_15W,_Nz,_)),_16u=B(_1O(_163,B(_c(0,E(_165)+1|0,_1I)),_)),_16v=__app1(E(_15Y),toJSStr(E(_1L)));return new F(function(){return _pv(new T(function(){var _16w=String(_16v);return fromJSStr(_16w);}),_);});},_16x=E(_16i.c);if(!_16x._){var _16y=B(_1O(_Ny,_15O,_));return new F(function(){return _16j(_,_16y);});}else{var _16z=new T(function(){return B(_PZ(0,_16x.a,new T(function(){return B(_15R(_16x.b));})));}),_16A=B(_1O(_Ny,new T2(1,_2p,_16z),_));return new F(function(){return _16j(_,_16A);});}}else{return E(_14A);}}},_16B=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_16C=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_16D=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_16E=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_16F=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_16G=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_16H=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_16I=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_16J=function(_){return new F(function(){return __jsNull();});},_16K=function(_16L){var _16M=B(A1(_16L,_));return E(_16M);},_16N=new T(function(){return B(_16K(_16J));}),_16O=new T(function(){return E(_16N);}),_16P=function(_16Q,_16R,_16S,_){var _16T=E(_Nb),_16U=eval(E(_pD)),_16V=__app1(E(_16U),toJSStr(_16T)),_16W=B(_kS(B(_3h(_Na,new T(function(){var _16X=String(_16V);return fromJSStr(_16X);})))));if(!_16W._){return E(_IK);}else{if(!E(_16W.b)._){var _16Y=E(_16W.a),_16Z=B(_Iv(new T(function(){return B(_tn(_16Y.a));},1),new T(function(){return B(_vT(_16S,_16Q,_16R,B(_xK(_16Y.b))));},1),new T(function(){return B(_GA(_16Y.c));},1),new T(function(){return B(_Dq(_16Y.d));},1)));return new F(function(){return _1O(_16T,new T2(1,_16Z.a,_16Z.b),_);});}else{return E(_IJ);}}},_170=function(_){var _171=eval(E(_pD)),_172=__app1(E(_171),toJSStr(E(_1L))),_173=B(_pv(new T(function(){var _174=String(_172);return fromJSStr(_174);}),_)),_175=__createJSFunc(0,function(_){var _176=B(_NE(_));return _16O;}),_177=__app2(E(_16D),"clear_workspace",_175),_178=__createJSFunc(0,function(_){var _179=B(_kZ(_));return _16O;}),_17a=__app2(E(_16C),"b2c",_178),_17b=__createJSFunc(0,function(_){var _17c=B(_pE(_));return _16O;}),_17d=__app2(E(_16B),"c2b",_17b),_17e=function(_17f){var _17g=new T(function(){var _17h=Number(E(_17f));return jsTrunc(_17h);}),_17i=function(_17j){var _17k=new T(function(){var _17l=Number(E(_17j));return jsTrunc(_17l);}),_17m=function(_17n){var _17o=new T(function(){var _17p=Number(E(_17n));return jsTrunc(_17p);}),_17q=function(_17r,_){var _17s=B(_NK(_17g,_17k,_17o,new T(function(){var _17t=Number(E(_17r));return jsTrunc(_17t);}),_));return _16O;};return E(_17q);};return E(_17m);};return E(_17i);},_17u=__createJSFunc(5,E(_17e)),_17v=__app2(E(_16I),"commit",_17u),_17w=function(_17x){var _17y=new T(function(){var _17z=Number(E(_17x));return jsTrunc(_17z);}),_17A=function(_17B){var _17C=new T(function(){var _17D=Number(E(_17B));return jsTrunc(_17D);}),_17E=function(_17F,_){var _17G=B(_16P(_17y,_17C,new T(function(){var _17H=Number(E(_17F));return jsTrunc(_17H);}),_));return _16O;};return E(_17E);};return E(_17A);},_17I=__createJSFunc(4,E(_17w)),_17J=__app2(E(_16H),"redeem",_17I),_17K=function(_17L){var _17M=new T(function(){var _17N=Number(E(_17L));return jsTrunc(_17N);}),_17O=function(_17P){var _17Q=new T(function(){var _17R=Number(E(_17P));return jsTrunc(_17R);}),_17S=function(_17T,_){var _17U=B(_Nn(_17M,_17Q,new T(function(){var _17V=Number(E(_17T));return jsTrunc(_17V);}),_));return _16O;};return E(_17S);};return E(_17O);},_17W=__createJSFunc(4,E(_17K)),_17X=__app2(E(_16G),"claim",_17W),_17Y=function(_17Z){var _180=new T(function(){var _181=Number(E(_17Z));return jsTrunc(_181);}),_182=function(_183){var _184=new T(function(){var _185=Number(E(_183));return jsTrunc(_185);}),_186=function(_187,_){var _188=B(_Nc(_180,_184,new T(function(){var _189=Number(E(_187));return jsTrunc(_189);}),_));return _16O;};return E(_186);};return E(_182);},_18a=__createJSFunc(4,E(_17Y)),_18b=__app2(E(_16F),"choose",_18a),_18c=__createJSFunc(0,function(_){var _18d=B(_15V(_));return _16O;}),_18e=__app2(E(_16E),"execute",_18c);return _0;},_18f=function(_){return new F(function(){return _170(_);});};
var hasteMain = function() {B(A(_18f, [0]));};window.onload = hasteMain;