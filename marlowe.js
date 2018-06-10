"use strict";
var __haste_prog_id = '47f6f10a39d136247fdc5c9cec59657a196d8a85ea5ef09a8aa3e36b664e5f05';
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

var _0=new T0(1),_1=__Z,_2=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_3=function(_4){return new F(function(){return err(_2);});},_5=new T(function(){return B(_3(_));}),_6=function(_7,_8,_9,_a){var _b=E(_9);if(!_b._){var _c=_b.a,_d=E(_a);if(!_d._){var _e=_d.a,_f=_d.b,_g=_d.c;if(_e<=(imul(3,_c)|0)){return new T5(0,(1+_c|0)+_e|0,E(_7),_8,E(_b),E(_d));}else{var _h=E(_d.d);if(!_h._){var _i=_h.a,_j=_h.b,_k=_h.c,_l=_h.d,_m=E(_d.e);if(!_m._){var _n=_m.a;if(_i>=(imul(2,_n)|0)){var _o=function(_p){var _q=E(_7),_r=E(_h.e);return (_r._==0)?new T5(0,(1+_c|0)+_e|0,E(_j),_k,E(new T5(0,(1+_c|0)+_p|0,E(_q),_8,E(_b),E(_l))),E(new T5(0,(1+_n|0)+_r.a|0,E(_f),_g,E(_r),E(_m)))):new T5(0,(1+_c|0)+_e|0,E(_j),_k,E(new T5(0,(1+_c|0)+_p|0,E(_q),_8,E(_b),E(_l))),E(new T5(0,1+_n|0,E(_f),_g,E(_0),E(_m))));},_s=E(_l);if(!_s._){return new F(function(){return _o(_s.a);});}else{return new F(function(){return _o(0);});}}else{return new T5(0,(1+_c|0)+_e|0,E(_f),_g,E(new T5(0,(1+_c|0)+_i|0,E(_7),_8,E(_b),E(_h))),E(_m));}}else{return E(_5);}}else{return E(_5);}}}else{return new T5(0,1+_c|0,E(_7),_8,E(_b),E(_0));}}else{var _t=E(_a);if(!_t._){var _u=_t.a,_v=_t.b,_w=_t.c,_x=_t.e,_y=E(_t.d);if(!_y._){var _z=_y.a,_A=_y.b,_B=_y.c,_C=_y.d,_D=E(_x);if(!_D._){var _E=_D.a;if(_z>=(imul(2,_E)|0)){var _F=function(_G){var _H=E(_7),_I=E(_y.e);return (_I._==0)?new T5(0,1+_u|0,E(_A),_B,E(new T5(0,1+_G|0,E(_H),_8,E(_0),E(_C))),E(new T5(0,(1+_E|0)+_I.a|0,E(_v),_w,E(_I),E(_D)))):new T5(0,1+_u|0,E(_A),_B,E(new T5(0,1+_G|0,E(_H),_8,E(_0),E(_C))),E(new T5(0,1+_E|0,E(_v),_w,E(_0),E(_D))));},_J=E(_C);if(!_J._){return new F(function(){return _F(_J.a);});}else{return new F(function(){return _F(0);});}}else{return new T5(0,1+_u|0,E(_v),_w,E(new T5(0,1+_z|0,E(_7),_8,E(_0),E(_y))),E(_D));}}else{return new T5(0,3,E(_A),_B,E(new T5(0,1,E(_7),_8,E(_0),E(_0))),E(new T5(0,1,E(_v),_w,E(_0),E(_0))));}}else{var _K=E(_x);return (_K._==0)?new T5(0,3,E(_v),_w,E(new T5(0,1,E(_7),_8,E(_0),E(_0))),E(_K)):new T5(0,2,E(_7),_8,E(_0),E(_t));}}else{return new T5(0,1,E(_7),_8,E(_0),E(_0));}}},_L=function(_M,_N){return new T5(0,1,E(_M),_N,E(_0),E(_0));},_O=function(_P,_Q,_R){var _S=E(_R);if(!_S._){return new F(function(){return _6(_S.b,_S.c,_S.d,B(_O(_P,_Q,_S.e)));});}else{return new F(function(){return _L(_P,_Q);});}},_T=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_U=function(_V){return new F(function(){return err(_T);});},_W=new T(function(){return B(_U(_));}),_X=function(_Y,_Z,_10,_11){var _12=E(_11);if(!_12._){var _13=_12.a,_14=E(_10);if(!_14._){var _15=_14.a,_16=_14.b,_17=_14.c;if(_15<=(imul(3,_13)|0)){return new T5(0,(1+_15|0)+_13|0,E(_Y),_Z,E(_14),E(_12));}else{var _18=E(_14.d);if(!_18._){var _19=_18.a,_1a=E(_14.e);if(!_1a._){var _1b=_1a.a,_1c=_1a.b,_1d=_1a.c,_1e=_1a.d;if(_1b>=(imul(2,_19)|0)){var _1f=function(_1g){var _1h=E(_1a.e);return (_1h._==0)?new T5(0,(1+_15|0)+_13|0,E(_1c),_1d,E(new T5(0,(1+_19|0)+_1g|0,E(_16),_17,E(_18),E(_1e))),E(new T5(0,(1+_13|0)+_1h.a|0,E(_Y),_Z,E(_1h),E(_12)))):new T5(0,(1+_15|0)+_13|0,E(_1c),_1d,E(new T5(0,(1+_19|0)+_1g|0,E(_16),_17,E(_18),E(_1e))),E(new T5(0,1+_13|0,E(_Y),_Z,E(_0),E(_12))));},_1i=E(_1e);if(!_1i._){return new F(function(){return _1f(_1i.a);});}else{return new F(function(){return _1f(0);});}}else{return new T5(0,(1+_15|0)+_13|0,E(_16),_17,E(_18),E(new T5(0,(1+_13|0)+_1b|0,E(_Y),_Z,E(_1a),E(_12))));}}else{return E(_W);}}else{return E(_W);}}}else{return new T5(0,1+_13|0,E(_Y),_Z,E(_0),E(_12));}}else{var _1j=E(_10);if(!_1j._){var _1k=_1j.a,_1l=_1j.b,_1m=_1j.c,_1n=_1j.e,_1o=E(_1j.d);if(!_1o._){var _1p=_1o.a,_1q=E(_1n);if(!_1q._){var _1r=_1q.a,_1s=_1q.b,_1t=_1q.c,_1u=_1q.d;if(_1r>=(imul(2,_1p)|0)){var _1v=function(_1w){var _1x=E(_1q.e);return (_1x._==0)?new T5(0,1+_1k|0,E(_1s),_1t,E(new T5(0,(1+_1p|0)+_1w|0,E(_1l),_1m,E(_1o),E(_1u))),E(new T5(0,1+_1x.a|0,E(_Y),_Z,E(_1x),E(_0)))):new T5(0,1+_1k|0,E(_1s),_1t,E(new T5(0,(1+_1p|0)+_1w|0,E(_1l),_1m,E(_1o),E(_1u))),E(new T5(0,1,E(_Y),_Z,E(_0),E(_0))));},_1y=E(_1u);if(!_1y._){return new F(function(){return _1v(_1y.a);});}else{return new F(function(){return _1v(0);});}}else{return new T5(0,1+_1k|0,E(_1l),_1m,E(_1o),E(new T5(0,1+_1r|0,E(_Y),_Z,E(_1q),E(_0))));}}else{return new T5(0,3,E(_1l),_1m,E(_1o),E(new T5(0,1,E(_Y),_Z,E(_0),E(_0))));}}else{var _1z=E(_1n);return (_1z._==0)?new T5(0,3,E(_1z.b),_1z.c,E(new T5(0,1,E(_1l),_1m,E(_0),E(_0))),E(new T5(0,1,E(_Y),_Z,E(_0),E(_0)))):new T5(0,2,E(_Y),_Z,E(_1j),E(_0));}}else{return new T5(0,1,E(_Y),_Z,E(_0),E(_0));}}},_1A=function(_1B,_1C,_1D){var _1E=E(_1D);if(!_1E._){return new F(function(){return _X(_1E.b,_1E.c,B(_1A(_1B,_1C,_1E.d)),_1E.e);});}else{return new F(function(){return _L(_1B,_1C);});}},_1F=function(_1G,_1H,_1I,_1J,_1K,_1L,_1M){return new F(function(){return _X(_1J,_1K,B(_1A(_1G,_1H,_1L)),_1M);});},_1N=function(_1O,_1P,_1Q,_1R,_1S,_1T,_1U,_1V){var _1W=E(_1Q);if(!_1W._){var _1X=_1W.a,_1Y=_1W.b,_1Z=_1W.c,_20=_1W.d,_21=_1W.e;if((imul(3,_1X)|0)>=_1R){if((imul(3,_1R)|0)>=_1X){return new T5(0,(_1X+_1R|0)+1|0,E(_1O),_1P,E(_1W),E(new T5(0,_1R,E(_1S),_1T,E(_1U),E(_1V))));}else{return new F(function(){return _6(_1Y,_1Z,_20,B(_1N(_1O,_1P,_21,_1R,_1S,_1T,_1U,_1V)));});}}else{return new F(function(){return _X(_1S,_1T,B(_22(_1O,_1P,_1X,_1Y,_1Z,_20,_21,_1U)),_1V);});}}else{return new F(function(){return _1F(_1O,_1P,_1R,_1S,_1T,_1U,_1V);});}},_22=function(_23,_24,_25,_26,_27,_28,_29,_2a){var _2b=E(_2a);if(!_2b._){var _2c=_2b.a,_2d=_2b.b,_2e=_2b.c,_2f=_2b.d,_2g=_2b.e;if((imul(3,_25)|0)>=_2c){if((imul(3,_2c)|0)>=_25){return new T5(0,(_25+_2c|0)+1|0,E(_23),_24,E(new T5(0,_25,E(_26),_27,E(_28),E(_29))),E(_2b));}else{return new F(function(){return _6(_26,_27,_28,B(_1N(_23,_24,_29,_2c,_2d,_2e,_2f,_2g)));});}}else{return new F(function(){return _X(_2d,_2e,B(_22(_23,_24,_25,_26,_27,_28,_29,_2f)),_2g);});}}else{return new F(function(){return _O(_23,_24,new T5(0,_25,E(_26),_27,E(_28),E(_29)));});}},_2h=function(_2i,_2j,_2k,_2l){var _2m=E(_2k);if(!_2m._){var _2n=_2m.a,_2o=_2m.b,_2p=_2m.c,_2q=_2m.d,_2r=_2m.e,_2s=E(_2l);if(!_2s._){var _2t=_2s.a,_2u=_2s.b,_2v=_2s.c,_2w=_2s.d,_2x=_2s.e;if((imul(3,_2n)|0)>=_2t){if((imul(3,_2t)|0)>=_2n){return new T5(0,(_2n+_2t|0)+1|0,E(_2i),_2j,E(_2m),E(_2s));}else{return new F(function(){return _6(_2o,_2p,_2q,B(_1N(_2i,_2j,_2r,_2t,_2u,_2v,_2w,_2x)));});}}else{return new F(function(){return _X(_2u,_2v,B(_22(_2i,_2j,_2n,_2o,_2p,_2q,_2r,_2w)),_2x);});}}else{return new F(function(){return _O(_2i,_2j,_2m);});}}else{return new F(function(){return _1A(_2i,_2j,_2l);});}},_2y=function(_2z,_2A,_2B,_2C,_2D){var _2E=E(_2z);if(_2E==1){var _2F=E(_2D);if(!_2F._){return new T3(0,new T5(0,1,E(new T2(0,_2A,_2B)),_2C,E(_0),E(_0)),_1,_1);}else{var _2G=E(E(_2F.a).a),_2H=E(_2A),_2I=E(_2G.a);return (_2H>=_2I)?(_2H!=_2I)?new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_1,_2F):(_2B<E(_2G.b))?new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_2F,_1):new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_1,_2F):new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_2F,_1);}}else{var _2J=B(_2y(_2E>>1,_2A,_2B,_2C,_2D)),_2K=_2J.a,_2L=_2J.c,_2M=E(_2J.b);if(!_2M._){return new T3(0,_2K,_1,_2L);}else{var _2N=E(_2M.a),_2O=_2N.a,_2P=_2N.b,_2Q=E(_2M.b);if(!_2Q._){return new T3(0,new T(function(){return B(_O(_2O,_2P,_2K));}),_1,_2L);}else{var _2R=_2Q.b,_2S=E(_2Q.a),_2T=_2S.b,_2U=E(_2O),_2V=E(_2S.a),_2W=_2V.b,_2X=E(_2U.a),_2Y=E(_2V.a);if(_2X>=_2Y){if(_2X!=_2Y){return new T3(0,_2K,_1,_2M);}else{var _2Z=E(_2W);if(E(_2U.b)<_2Z){var _30=B(_2y(_2E>>1,_2Y,_2Z,_2T,_2R));return new T3(0,new T(function(){return B(_2h(_2U,_2P,_2K,_30.a));}),_30.b,_30.c);}else{return new T3(0,_2K,_1,_2M);}}}else{var _31=B(_32(_2E>>1,_2Y,_2W,_2T,_2R));return new T3(0,new T(function(){return B(_2h(_2U,_2P,_2K,_31.a));}),_31.b,_31.c);}}}}},_32=function(_33,_34,_35,_36,_37){var _38=E(_33);if(_38==1){var _39=E(_37);if(!_39._){return new T3(0,new T5(0,1,E(new T2(0,_34,_35)),_36,E(_0),E(_0)),_1,_1);}else{var _3a=E(E(_39.a).a),_3b=E(_34),_3c=E(_3a.a);if(_3b>=_3c){if(_3b!=_3c){return new T3(0,new T5(0,1,E(new T2(0,_3b,_35)),_36,E(_0),E(_0)),_1,_39);}else{var _3d=E(_35);return (_3d<E(_3a.b))?new T3(0,new T5(0,1,E(new T2(0,_3b,_3d)),_36,E(_0),E(_0)),_39,_1):new T3(0,new T5(0,1,E(new T2(0,_3b,_3d)),_36,E(_0),E(_0)),_1,_39);}}else{return new T3(0,new T5(0,1,E(new T2(0,_3b,_35)),_36,E(_0),E(_0)),_39,_1);}}}else{var _3e=B(_32(_38>>1,_34,_35,_36,_37)),_3f=_3e.a,_3g=_3e.c,_3h=E(_3e.b);if(!_3h._){return new T3(0,_3f,_1,_3g);}else{var _3i=E(_3h.a),_3j=_3i.a,_3k=_3i.b,_3l=E(_3h.b);if(!_3l._){return new T3(0,new T(function(){return B(_O(_3j,_3k,_3f));}),_1,_3g);}else{var _3m=_3l.b,_3n=E(_3l.a),_3o=_3n.b,_3p=E(_3j),_3q=E(_3n.a),_3r=_3q.b,_3s=E(_3p.a),_3t=E(_3q.a);if(_3s>=_3t){if(_3s!=_3t){return new T3(0,_3f,_1,_3h);}else{var _3u=E(_3r);if(E(_3p.b)<_3u){var _3v=B(_2y(_38>>1,_3t,_3u,_3o,_3m));return new T3(0,new T(function(){return B(_2h(_3p,_3k,_3f,_3v.a));}),_3v.b,_3v.c);}else{return new T3(0,_3f,_1,_3h);}}}else{var _3w=B(_32(_38>>1,_3t,_3r,_3o,_3m));return new T3(0,new T(function(){return B(_2h(_3p,_3k,_3f,_3w.a));}),_3w.b,_3w.c);}}}}},_3x=function(_3y,_3z,_3A,_3B,_3C){var _3D=E(_3C);if(!_3D._){var _3E=_3D.c,_3F=_3D.d,_3G=_3D.e,_3H=E(_3D.b),_3I=E(_3H.a);if(_3y>=_3I){if(_3y!=_3I){return new F(function(){return _6(_3H,_3E,_3F,B(_3x(_3y,_,_3A,_3B,_3G)));});}else{var _3J=E(_3H.b);if(_3A>=_3J){if(_3A!=_3J){return new F(function(){return _6(_3H,_3E,_3F,B(_3x(_3y,_,_3A,_3B,_3G)));});}else{return new T5(0,_3D.a,E(new T2(0,_3y,_3A)),_3B,E(_3F),E(_3G));}}else{return new F(function(){return _X(_3H,_3E,B(_3x(_3y,_,_3A,_3B,_3F)),_3G);});}}}else{return new F(function(){return _X(_3H,_3E,B(_3x(_3y,_,_3A,_3B,_3F)),_3G);});}}else{return new T5(0,1,E(new T2(0,_3y,_3A)),_3B,E(_0),E(_0));}},_3K=function(_3L,_3M,_3N,_3O,_3P){var _3Q=E(_3P);if(!_3Q._){var _3R=_3Q.c,_3S=_3Q.d,_3T=_3Q.e,_3U=E(_3Q.b),_3V=E(_3U.a);if(_3L>=_3V){if(_3L!=_3V){return new F(function(){return _6(_3U,_3R,_3S,B(_3K(_3L,_,_3N,_3O,_3T)));});}else{var _3W=E(_3N),_3X=E(_3U.b);if(_3W>=_3X){if(_3W!=_3X){return new F(function(){return _6(_3U,_3R,_3S,B(_3x(_3L,_,_3W,_3O,_3T)));});}else{return new T5(0,_3Q.a,E(new T2(0,_3L,_3W)),_3O,E(_3S),E(_3T));}}else{return new F(function(){return _X(_3U,_3R,B(_3x(_3L,_,_3W,_3O,_3S)),_3T);});}}}else{return new F(function(){return _X(_3U,_3R,B(_3K(_3L,_,_3N,_3O,_3S)),_3T);});}}else{return new T5(0,1,E(new T2(0,_3L,_3N)),_3O,E(_0),E(_0));}},_3Y=function(_3Z,_40,_41,_42){var _43=E(_42);if(!_43._){var _44=_43.c,_45=_43.d,_46=_43.e,_47=E(_43.b),_48=E(_3Z),_49=E(_47.a);if(_48>=_49){if(_48!=_49){return new F(function(){return _6(_47,_44,_45,B(_3K(_48,_,_40,_41,_46)));});}else{var _4a=E(_40),_4b=E(_47.b);if(_4a>=_4b){if(_4a!=_4b){return new F(function(){return _6(_47,_44,_45,B(_3x(_48,_,_4a,_41,_46)));});}else{return new T5(0,_43.a,E(new T2(0,_48,_4a)),_41,E(_45),E(_46));}}else{return new F(function(){return _X(_47,_44,B(_3x(_48,_,_4a,_41,_45)),_46);});}}}else{return new F(function(){return _X(_47,_44,B(_3K(_48,_,_40,_41,_45)),_46);});}}else{return new T5(0,1,E(new T2(0,_3Z,_40)),_41,E(_0),E(_0));}},_4c=function(_4d,_4e){while(1){var _4f=E(_4e);if(!_4f._){return E(_4d);}else{var _4g=E(_4f.a),_4h=E(_4g.a),_4i=B(_3Y(_4h.a,_4h.b,_4g.b,_4d));_4d=_4i;_4e=_4f.b;continue;}}},_4j=function(_4k,_4l,_4m,_4n,_4o){return new F(function(){return _4c(B(_3Y(_4l,_4m,_4n,_4k)),_4o);});},_4p=function(_4q,_4r,_4s){var _4t=E(_4r),_4u=E(_4t.a);return new F(function(){return _4c(B(_3Y(_4u.a,_4u.b,_4t.b,_4q)),_4s);});},_4v=function(_4w,_4x,_4y){var _4z=E(_4y);if(!_4z._){return E(_4x);}else{var _4A=E(_4z.a),_4B=_4A.a,_4C=_4A.b,_4D=E(_4z.b);if(!_4D._){return new F(function(){return _O(_4B,_4C,_4x);});}else{var _4E=E(_4D.a),_4F=E(_4B),_4G=_4F.b,_4H=E(_4E.a),_4I=_4H.b,_4J=E(_4F.a),_4K=E(_4H.a),_4L=function(_4M){var _4N=B(_32(_4w,_4K,_4I,_4E.b,_4D.b)),_4O=_4N.a,_4P=E(_4N.c);if(!_4P._){return new F(function(){return _4v(_4w<<1,B(_2h(_4F,_4C,_4x,_4O)),_4N.b);});}else{return new F(function(){return _4p(B(_2h(_4F,_4C,_4x,_4O)),_4P.a,_4P.b);});}};if(_4J>=_4K){if(_4J!=_4K){return new F(function(){return _4j(_4x,_4J,_4G,_4C,_4D);});}else{var _4Q=E(_4G);if(_4Q<E(_4I)){return new F(function(){return _4L(_);});}else{return new F(function(){return _4j(_4x,_4J,_4Q,_4C,_4D);});}}}else{return new F(function(){return _4L(_);});}}}},_4R=function(_4S,_4T,_4U,_4V,_4W,_4X){var _4Y=E(_4X);if(!_4Y._){return new F(function(){return _O(new T2(0,_4U,_4V),_4W,_4T);});}else{var _4Z=E(_4Y.a),_50=E(_4Z.a),_51=_50.b,_52=E(_4U),_53=E(_50.a),_54=function(_55){var _56=B(_32(_4S,_53,_51,_4Z.b,_4Y.b)),_57=_56.a,_58=E(_56.c);if(!_58._){return new F(function(){return _4v(_4S<<1,B(_2h(new T2(0,_52,_4V),_4W,_4T,_57)),_56.b);});}else{return new F(function(){return _4p(B(_2h(new T2(0,_52,_4V),_4W,_4T,_57)),_58.a,_58.b);});}};if(_52>=_53){if(_52!=_53){return new F(function(){return _4j(_4T,_52,_4V,_4W,_4Y);});}else{if(_4V<E(_51)){return new F(function(){return _54(_);});}else{return new F(function(){return _4j(_4T,_52,_4V,_4W,_4Y);});}}}else{return new F(function(){return _54(_);});}}},_59=function(_5a,_5b,_5c,_5d,_5e,_5f){var _5g=E(_5f);if(!_5g._){return new F(function(){return _O(new T2(0,_5c,_5d),_5e,_5b);});}else{var _5h=E(_5g.a),_5i=E(_5h.a),_5j=_5i.b,_5k=E(_5c),_5l=E(_5i.a),_5m=function(_5n){var _5o=B(_32(_5a,_5l,_5j,_5h.b,_5g.b)),_5p=_5o.a,_5q=E(_5o.c);if(!_5q._){return new F(function(){return _4v(_5a<<1,B(_2h(new T2(0,_5k,_5d),_5e,_5b,_5p)),_5o.b);});}else{return new F(function(){return _4p(B(_2h(new T2(0,_5k,_5d),_5e,_5b,_5p)),_5q.a,_5q.b);});}};if(_5k>=_5l){if(_5k!=_5l){return new F(function(){return _4j(_5b,_5k,_5d,_5e,_5g);});}else{var _5r=E(_5d);if(_5r<E(_5j)){return new F(function(){return _5m(_);});}else{return new F(function(){return _4j(_5b,_5k,_5r,_5e,_5g);});}}}else{return new F(function(){return _5m(_);});}}},_5s=function(_5t){var _5u=E(_5t);if(!_5u._){return new T0(1);}else{var _5v=E(_5u.a),_5w=_5v.a,_5x=_5v.b,_5y=E(_5u.b);if(!_5y._){return new T5(0,1,E(_5w),_5x,E(_0),E(_0));}else{var _5z=_5y.b,_5A=E(_5y.a),_5B=_5A.b,_5C=E(_5w),_5D=E(_5A.a),_5E=_5D.b,_5F=E(_5C.a),_5G=E(_5D.a);if(_5F>=_5G){if(_5F!=_5G){return new F(function(){return _4j(new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5E,_5B,_5z);});}else{var _5H=E(_5E);if(E(_5C.b)<_5H){return new F(function(){return _4R(1,new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5H,_5B,_5z);});}else{return new F(function(){return _4j(new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5H,_5B,_5z);});}}}else{return new F(function(){return _59(1,new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5E,_5B,_5z);});}}}},_5I=new T0(1),_5J=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_5K=function(_5L){return new F(function(){return err(_5J);});},_5M=new T(function(){return B(_5K(_));}),_5N=function(_5O,_5P,_5Q){var _5R=E(_5P);if(!_5R._){var _5S=_5R.a,_5T=E(_5Q);if(!_5T._){var _5U=_5T.a,_5V=_5T.b;if(_5U<=(imul(3,_5S)|0)){return new T4(0,(1+_5S|0)+_5U|0,E(_5O),E(_5R),E(_5T));}else{var _5W=E(_5T.c);if(!_5W._){var _5X=_5W.a,_5Y=_5W.b,_5Z=_5W.c,_60=E(_5T.d);if(!_60._){var _61=_60.a;if(_5X>=(imul(2,_61)|0)){var _62=function(_63){var _64=E(_5O),_65=E(_5W.d);return (_65._==0)?new T4(0,(1+_5S|0)+_5U|0,E(_5Y),E(new T4(0,(1+_5S|0)+_63|0,E(_64),E(_5R),E(_5Z))),E(new T4(0,(1+_61|0)+_65.a|0,E(_5V),E(_65),E(_60)))):new T4(0,(1+_5S|0)+_5U|0,E(_5Y),E(new T4(0,(1+_5S|0)+_63|0,E(_64),E(_5R),E(_5Z))),E(new T4(0,1+_61|0,E(_5V),E(_5I),E(_60))));},_66=E(_5Z);if(!_66._){return new F(function(){return _62(_66.a);});}else{return new F(function(){return _62(0);});}}else{return new T4(0,(1+_5S|0)+_5U|0,E(_5V),E(new T4(0,(1+_5S|0)+_5X|0,E(_5O),E(_5R),E(_5W))),E(_60));}}else{return E(_5M);}}else{return E(_5M);}}}else{return new T4(0,1+_5S|0,E(_5O),E(_5R),E(_5I));}}else{var _67=E(_5Q);if(!_67._){var _68=_67.a,_69=_67.b,_6a=_67.d,_6b=E(_67.c);if(!_6b._){var _6c=_6b.a,_6d=_6b.b,_6e=_6b.c,_6f=E(_6a);if(!_6f._){var _6g=_6f.a;if(_6c>=(imul(2,_6g)|0)){var _6h=function(_6i){var _6j=E(_5O),_6k=E(_6b.d);return (_6k._==0)?new T4(0,1+_68|0,E(_6d),E(new T4(0,1+_6i|0,E(_6j),E(_5I),E(_6e))),E(new T4(0,(1+_6g|0)+_6k.a|0,E(_69),E(_6k),E(_6f)))):new T4(0,1+_68|0,E(_6d),E(new T4(0,1+_6i|0,E(_6j),E(_5I),E(_6e))),E(new T4(0,1+_6g|0,E(_69),E(_5I),E(_6f))));},_6l=E(_6e);if(!_6l._){return new F(function(){return _6h(_6l.a);});}else{return new F(function(){return _6h(0);});}}else{return new T4(0,1+_68|0,E(_69),E(new T4(0,1+_6c|0,E(_5O),E(_5I),E(_6b))),E(_6f));}}else{return new T4(0,3,E(_6d),E(new T4(0,1,E(_5O),E(_5I),E(_5I))),E(new T4(0,1,E(_69),E(_5I),E(_5I))));}}else{var _6m=E(_6a);return (_6m._==0)?new T4(0,3,E(_69),E(new T4(0,1,E(_5O),E(_5I),E(_5I))),E(_6m)):new T4(0,2,E(_5O),E(_5I),E(_67));}}else{return new T4(0,1,E(_5O),E(_5I),E(_5I));}}},_6n=function(_6o){return new T4(0,1,E(_6o),E(_5I),E(_5I));},_6p=function(_6q,_6r){var _6s=E(_6r);if(!_6s._){return new F(function(){return _5N(_6s.b,_6s.c,B(_6p(_6q,_6s.d)));});}else{return new F(function(){return _6n(_6q);});}},_6t=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_6u=function(_6v){return new F(function(){return err(_6t);});},_6w=new T(function(){return B(_6u(_));}),_6x=function(_6y,_6z,_6A){var _6B=E(_6A);if(!_6B._){var _6C=_6B.a,_6D=E(_6z);if(!_6D._){var _6E=_6D.a,_6F=_6D.b;if(_6E<=(imul(3,_6C)|0)){return new T4(0,(1+_6E|0)+_6C|0,E(_6y),E(_6D),E(_6B));}else{var _6G=E(_6D.c);if(!_6G._){var _6H=_6G.a,_6I=E(_6D.d);if(!_6I._){var _6J=_6I.a,_6K=_6I.b,_6L=_6I.c;if(_6J>=(imul(2,_6H)|0)){var _6M=function(_6N){var _6O=E(_6I.d);return (_6O._==0)?new T4(0,(1+_6E|0)+_6C|0,E(_6K),E(new T4(0,(1+_6H|0)+_6N|0,E(_6F),E(_6G),E(_6L))),E(new T4(0,(1+_6C|0)+_6O.a|0,E(_6y),E(_6O),E(_6B)))):new T4(0,(1+_6E|0)+_6C|0,E(_6K),E(new T4(0,(1+_6H|0)+_6N|0,E(_6F),E(_6G),E(_6L))),E(new T4(0,1+_6C|0,E(_6y),E(_5I),E(_6B))));},_6P=E(_6L);if(!_6P._){return new F(function(){return _6M(_6P.a);});}else{return new F(function(){return _6M(0);});}}else{return new T4(0,(1+_6E|0)+_6C|0,E(_6F),E(_6G),E(new T4(0,(1+_6C|0)+_6J|0,E(_6y),E(_6I),E(_6B))));}}else{return E(_6w);}}else{return E(_6w);}}}else{return new T4(0,1+_6C|0,E(_6y),E(_5I),E(_6B));}}else{var _6Q=E(_6z);if(!_6Q._){var _6R=_6Q.a,_6S=_6Q.b,_6T=_6Q.d,_6U=E(_6Q.c);if(!_6U._){var _6V=_6U.a,_6W=E(_6T);if(!_6W._){var _6X=_6W.a,_6Y=_6W.b,_6Z=_6W.c;if(_6X>=(imul(2,_6V)|0)){var _70=function(_71){var _72=E(_6W.d);return (_72._==0)?new T4(0,1+_6R|0,E(_6Y),E(new T4(0,(1+_6V|0)+_71|0,E(_6S),E(_6U),E(_6Z))),E(new T4(0,1+_72.a|0,E(_6y),E(_72),E(_5I)))):new T4(0,1+_6R|0,E(_6Y),E(new T4(0,(1+_6V|0)+_71|0,E(_6S),E(_6U),E(_6Z))),E(new T4(0,1,E(_6y),E(_5I),E(_5I))));},_73=E(_6Z);if(!_73._){return new F(function(){return _70(_73.a);});}else{return new F(function(){return _70(0);});}}else{return new T4(0,1+_6R|0,E(_6S),E(_6U),E(new T4(0,1+_6X|0,E(_6y),E(_6W),E(_5I))));}}else{return new T4(0,3,E(_6S),E(_6U),E(new T4(0,1,E(_6y),E(_5I),E(_5I))));}}else{var _74=E(_6T);return (_74._==0)?new T4(0,3,E(_74.b),E(new T4(0,1,E(_6S),E(_5I),E(_5I))),E(new T4(0,1,E(_6y),E(_5I),E(_5I)))):new T4(0,2,E(_6y),E(_6Q),E(_5I));}}else{return new T4(0,1,E(_6y),E(_5I),E(_5I));}}},_75=function(_76,_77){var _78=E(_77);if(!_78._){return new F(function(){return _6x(_78.b,B(_75(_76,_78.c)),_78.d);});}else{return new F(function(){return _6n(_76);});}},_79=function(_7a,_7b,_7c,_7d,_7e){return new F(function(){return _5N(_7c,_7d,B(_6p(_7a,_7e)));});},_7f=function(_7g,_7h,_7i,_7j,_7k){return new F(function(){return _6x(_7i,B(_75(_7g,_7j)),_7k);});},_7l=function(_7m,_7n,_7o,_7p,_7q,_7r){var _7s=E(_7n);if(!_7s._){var _7t=_7s.a,_7u=_7s.b,_7v=_7s.c,_7w=_7s.d;if((imul(3,_7t)|0)>=_7o){if((imul(3,_7o)|0)>=_7t){return new T4(0,(_7t+_7o|0)+1|0,E(_7m),E(_7s),E(new T4(0,_7o,E(_7p),E(_7q),E(_7r))));}else{return new F(function(){return _5N(_7u,_7v,B(_7l(_7m,_7w,_7o,_7p,_7q,_7r)));});}}else{return new F(function(){return _6x(_7p,B(_7x(_7m,_7t,_7u,_7v,_7w,_7q)),_7r);});}}else{return new F(function(){return _7f(_7m,_7o,_7p,_7q,_7r);});}},_7x=function(_7y,_7z,_7A,_7B,_7C,_7D){var _7E=E(_7D);if(!_7E._){var _7F=_7E.a,_7G=_7E.b,_7H=_7E.c,_7I=_7E.d;if((imul(3,_7z)|0)>=_7F){if((imul(3,_7F)|0)>=_7z){return new T4(0,(_7z+_7F|0)+1|0,E(_7y),E(new T4(0,_7z,E(_7A),E(_7B),E(_7C))),E(_7E));}else{return new F(function(){return _5N(_7A,_7B,B(_7l(_7y,_7C,_7F,_7G,_7H,_7I)));});}}else{return new F(function(){return _6x(_7G,B(_7x(_7y,_7z,_7A,_7B,_7C,_7H)),_7I);});}}else{return new F(function(){return _79(_7y,_7z,_7A,_7B,_7C);});}},_7J=function(_7K,_7L,_7M){var _7N=E(_7L);if(!_7N._){var _7O=_7N.a,_7P=_7N.b,_7Q=_7N.c,_7R=_7N.d,_7S=E(_7M);if(!_7S._){var _7T=_7S.a,_7U=_7S.b,_7V=_7S.c,_7W=_7S.d;if((imul(3,_7O)|0)>=_7T){if((imul(3,_7T)|0)>=_7O){return new T4(0,(_7O+_7T|0)+1|0,E(_7K),E(_7N),E(_7S));}else{return new F(function(){return _5N(_7P,_7Q,B(_7l(_7K,_7R,_7T,_7U,_7V,_7W)));});}}else{return new F(function(){return _6x(_7U,B(_7x(_7K,_7O,_7P,_7Q,_7R,_7V)),_7W);});}}else{return new F(function(){return _79(_7K,_7O,_7P,_7Q,_7R);});}}else{return new F(function(){return _75(_7K,_7M);});}},_7X=function(_7Y,_7Z,_80,_81,_82){var _83=E(_7Y);if(_83==1){var _84=E(_82);if(!_84._){return new T3(0,new T4(0,1,E(new T3(0,_7Z,_80,_81)),E(_5I),E(_5I)),_1,_1);}else{var _85=E(_7Z),_86=E(_84.a),_87=E(_86.a);if(_85>=_87){if(_85!=_87){return new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_1,_84);}else{var _88=E(_86.b);return (_80>=_88)?(_80!=_88)?new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_1,_84):(_81<E(_86.c))?new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_84,_1):new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_1,_84):new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_84,_1);}}else{return new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_84,_1);}}}else{var _89=B(_7X(_83>>1,_7Z,_80,_81,_82)),_8a=_89.a,_8b=_89.c,_8c=E(_89.b);if(!_8c._){return new T3(0,_8a,_1,_8b);}else{var _8d=_8c.a,_8e=E(_8c.b);if(!_8e._){return new T3(0,new T(function(){return B(_6p(_8d,_8a));}),_1,_8b);}else{var _8f=_8e.b,_8g=E(_8d),_8h=E(_8g.a),_8i=E(_8e.a),_8j=_8i.b,_8k=_8i.c,_8l=E(_8i.a);if(_8h>=_8l){if(_8h!=_8l){return new T3(0,_8a,_1,_8c);}else{var _8m=E(_8g.b),_8n=E(_8j);if(_8m>=_8n){if(_8m!=_8n){return new T3(0,_8a,_1,_8c);}else{var _8o=E(_8k);if(E(_8g.c)<_8o){var _8p=B(_7X(_83>>1,_8l,_8n,_8o,_8f));return new T3(0,new T(function(){return B(_7J(_8g,_8a,_8p.a));}),_8p.b,_8p.c);}else{return new T3(0,_8a,_1,_8c);}}}else{var _8q=B(_8r(_83>>1,_8l,_8n,_8k,_8f));return new T3(0,new T(function(){return B(_7J(_8g,_8a,_8q.a));}),_8q.b,_8q.c);}}}else{var _8s=B(_8t(_83>>1,_8l,_8j,_8k,_8f));return new T3(0,new T(function(){return B(_7J(_8g,_8a,_8s.a));}),_8s.b,_8s.c);}}}}},_8r=function(_8u,_8v,_8w,_8x,_8y){var _8z=E(_8u);if(_8z==1){var _8A=E(_8y);if(!_8A._){return new T3(0,new T4(0,1,E(new T3(0,_8v,_8w,_8x)),E(_5I),E(_5I)),_1,_1);}else{var _8B=E(_8v),_8C=E(_8A.a),_8D=E(_8C.a);if(_8B>=_8D){if(_8B!=_8D){return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_1,_8A);}else{var _8E=E(_8C.b);if(_8w>=_8E){if(_8w!=_8E){return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_1,_8A);}else{var _8F=E(_8x);return (_8F<E(_8C.c))?new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8F)),E(_5I),E(_5I)),_8A,_1):new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8F)),E(_5I),E(_5I)),_1,_8A);}}else{return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_8A,_1);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_8A,_1);}}}else{var _8G=B(_8r(_8z>>1,_8v,_8w,_8x,_8y)),_8H=_8G.a,_8I=_8G.c,_8J=E(_8G.b);if(!_8J._){return new T3(0,_8H,_1,_8I);}else{var _8K=_8J.a,_8L=E(_8J.b);if(!_8L._){return new T3(0,new T(function(){return B(_6p(_8K,_8H));}),_1,_8I);}else{var _8M=_8L.b,_8N=E(_8K),_8O=E(_8N.a),_8P=E(_8L.a),_8Q=_8P.b,_8R=_8P.c,_8S=E(_8P.a);if(_8O>=_8S){if(_8O!=_8S){return new T3(0,_8H,_1,_8J);}else{var _8T=E(_8N.b),_8U=E(_8Q);if(_8T>=_8U){if(_8T!=_8U){return new T3(0,_8H,_1,_8J);}else{var _8V=E(_8R);if(E(_8N.c)<_8V){var _8W=B(_7X(_8z>>1,_8S,_8U,_8V,_8M));return new T3(0,new T(function(){return B(_7J(_8N,_8H,_8W.a));}),_8W.b,_8W.c);}else{return new T3(0,_8H,_1,_8J);}}}else{var _8X=B(_8r(_8z>>1,_8S,_8U,_8R,_8M));return new T3(0,new T(function(){return B(_7J(_8N,_8H,_8X.a));}),_8X.b,_8X.c);}}}else{var _8Y=B(_8t(_8z>>1,_8S,_8Q,_8R,_8M));return new T3(0,new T(function(){return B(_7J(_8N,_8H,_8Y.a));}),_8Y.b,_8Y.c);}}}}},_8t=function(_8Z,_90,_91,_92,_93){var _94=E(_8Z);if(_94==1){var _95=E(_93);if(!_95._){return new T3(0,new T4(0,1,E(new T3(0,_90,_91,_92)),E(_5I),E(_5I)),_1,_1);}else{var _96=E(_90),_97=E(_95.a),_98=E(_97.a);if(_96>=_98){if(_96!=_98){return new T3(0,new T4(0,1,E(new T3(0,_96,_91,_92)),E(_5I),E(_5I)),_1,_95);}else{var _99=E(_91),_9a=E(_97.b);if(_99>=_9a){if(_99!=_9a){return new T3(0,new T4(0,1,E(new T3(0,_96,_99,_92)),E(_5I),E(_5I)),_1,_95);}else{var _9b=E(_92);return (_9b<E(_97.c))?new T3(0,new T4(0,1,E(new T3(0,_96,_99,_9b)),E(_5I),E(_5I)),_95,_1):new T3(0,new T4(0,1,E(new T3(0,_96,_99,_9b)),E(_5I),E(_5I)),_1,_95);}}else{return new T3(0,new T4(0,1,E(new T3(0,_96,_99,_92)),E(_5I),E(_5I)),_95,_1);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_96,_91,_92)),E(_5I),E(_5I)),_95,_1);}}}else{var _9c=B(_8t(_94>>1,_90,_91,_92,_93)),_9d=_9c.a,_9e=_9c.c,_9f=E(_9c.b);if(!_9f._){return new T3(0,_9d,_1,_9e);}else{var _9g=_9f.a,_9h=E(_9f.b);if(!_9h._){return new T3(0,new T(function(){return B(_6p(_9g,_9d));}),_1,_9e);}else{var _9i=_9h.b,_9j=E(_9g),_9k=E(_9j.a),_9l=E(_9h.a),_9m=_9l.b,_9n=_9l.c,_9o=E(_9l.a);if(_9k>=_9o){if(_9k!=_9o){return new T3(0,_9d,_1,_9f);}else{var _9p=E(_9j.b),_9q=E(_9m);if(_9p>=_9q){if(_9p!=_9q){return new T3(0,_9d,_1,_9f);}else{var _9r=E(_9n);if(E(_9j.c)<_9r){var _9s=B(_7X(_94>>1,_9o,_9q,_9r,_9i));return new T3(0,new T(function(){return B(_7J(_9j,_9d,_9s.a));}),_9s.b,_9s.c);}else{return new T3(0,_9d,_1,_9f);}}}else{var _9t=B(_8r(_94>>1,_9o,_9q,_9n,_9i));return new T3(0,new T(function(){return B(_7J(_9j,_9d,_9t.a));}),_9t.b,_9t.c);}}}else{var _9u=B(_8t(_94>>1,_9o,_9m,_9n,_9i));return new T3(0,new T(function(){return B(_7J(_9j,_9d,_9u.a));}),_9u.b,_9u.c);}}}}},_9v=function(_9w,_9x,_9y,_9z,_9A){var _9B=E(_9A);if(!_9B._){var _9C=_9B.c,_9D=_9B.d,_9E=E(_9B.b),_9F=E(_9E.a);if(_9w>=_9F){if(_9w!=_9F){return new F(function(){return _5N(_9E,_9C,B(_9v(_9w,_,_9y,_9z,_9D)));});}else{var _9G=E(_9E.b);if(_9y>=_9G){if(_9y!=_9G){return new F(function(){return _5N(_9E,_9C,B(_9v(_9w,_,_9y,_9z,_9D)));});}else{var _9H=E(_9E.c);if(_9z>=_9H){if(_9z!=_9H){return new F(function(){return _5N(_9E,_9C,B(_9v(_9w,_,_9y,_9z,_9D)));});}else{return new T4(0,_9B.a,E(new T3(0,_9w,_9y,_9z)),E(_9C),E(_9D));}}else{return new F(function(){return _6x(_9E,B(_9v(_9w,_,_9y,_9z,_9C)),_9D);});}}}else{return new F(function(){return _6x(_9E,B(_9v(_9w,_,_9y,_9z,_9C)),_9D);});}}}else{return new F(function(){return _6x(_9E,B(_9v(_9w,_,_9y,_9z,_9C)),_9D);});}}else{return new T4(0,1,E(new T3(0,_9w,_9y,_9z)),E(_5I),E(_5I));}},_9I=function(_9J,_9K,_9L,_9M,_9N){var _9O=E(_9N);if(!_9O._){var _9P=_9O.c,_9Q=_9O.d,_9R=E(_9O.b),_9S=E(_9R.a);if(_9J>=_9S){if(_9J!=_9S){return new F(function(){return _5N(_9R,_9P,B(_9I(_9J,_,_9L,_9M,_9Q)));});}else{var _9T=E(_9R.b);if(_9L>=_9T){if(_9L!=_9T){return new F(function(){return _5N(_9R,_9P,B(_9I(_9J,_,_9L,_9M,_9Q)));});}else{var _9U=E(_9M),_9V=E(_9R.c);if(_9U>=_9V){if(_9U!=_9V){return new F(function(){return _5N(_9R,_9P,B(_9v(_9J,_,_9L,_9U,_9Q)));});}else{return new T4(0,_9O.a,E(new T3(0,_9J,_9L,_9U)),E(_9P),E(_9Q));}}else{return new F(function(){return _6x(_9R,B(_9v(_9J,_,_9L,_9U,_9P)),_9Q);});}}}else{return new F(function(){return _6x(_9R,B(_9I(_9J,_,_9L,_9M,_9P)),_9Q);});}}}else{return new F(function(){return _6x(_9R,B(_9I(_9J,_,_9L,_9M,_9P)),_9Q);});}}else{return new T4(0,1,E(new T3(0,_9J,_9L,_9M)),E(_5I),E(_5I));}},_9W=function(_9X,_9Y,_9Z,_a0,_a1){var _a2=E(_a1);if(!_a2._){var _a3=_a2.c,_a4=_a2.d,_a5=E(_a2.b),_a6=E(_a5.a);if(_9X>=_a6){if(_9X!=_a6){return new F(function(){return _5N(_a5,_a3,B(_9W(_9X,_,_9Z,_a0,_a4)));});}else{var _a7=E(_9Z),_a8=E(_a5.b);if(_a7>=_a8){if(_a7!=_a8){return new F(function(){return _5N(_a5,_a3,B(_9I(_9X,_,_a7,_a0,_a4)));});}else{var _a9=E(_a0),_aa=E(_a5.c);if(_a9>=_aa){if(_a9!=_aa){return new F(function(){return _5N(_a5,_a3,B(_9v(_9X,_,_a7,_a9,_a4)));});}else{return new T4(0,_a2.a,E(new T3(0,_9X,_a7,_a9)),E(_a3),E(_a4));}}else{return new F(function(){return _6x(_a5,B(_9v(_9X,_,_a7,_a9,_a3)),_a4);});}}}else{return new F(function(){return _6x(_a5,B(_9I(_9X,_,_a7,_a0,_a3)),_a4);});}}}else{return new F(function(){return _6x(_a5,B(_9W(_9X,_,_9Z,_a0,_a3)),_a4);});}}else{return new T4(0,1,E(new T3(0,_9X,_9Z,_a0)),E(_5I),E(_5I));}},_ab=function(_ac,_ad,_ae,_af){var _ag=E(_af);if(!_ag._){var _ah=_ag.c,_ai=_ag.d,_aj=E(_ag.b),_ak=E(_ac),_al=E(_aj.a);if(_ak>=_al){if(_ak!=_al){return new F(function(){return _5N(_aj,_ah,B(_9W(_ak,_,_ad,_ae,_ai)));});}else{var _am=E(_ad),_an=E(_aj.b);if(_am>=_an){if(_am!=_an){return new F(function(){return _5N(_aj,_ah,B(_9I(_ak,_,_am,_ae,_ai)));});}else{var _ao=E(_ae),_ap=E(_aj.c);if(_ao>=_ap){if(_ao!=_ap){return new F(function(){return _5N(_aj,_ah,B(_9v(_ak,_,_am,_ao,_ai)));});}else{return new T4(0,_ag.a,E(new T3(0,_ak,_am,_ao)),E(_ah),E(_ai));}}else{return new F(function(){return _6x(_aj,B(_9v(_ak,_,_am,_ao,_ah)),_ai);});}}}else{return new F(function(){return _6x(_aj,B(_9I(_ak,_,_am,_ae,_ah)),_ai);});}}}else{return new F(function(){return _6x(_aj,B(_9W(_ak,_,_ad,_ae,_ah)),_ai);});}}else{return new T4(0,1,E(new T3(0,_ac,_ad,_ae)),E(_5I),E(_5I));}},_aq=function(_ar,_as){while(1){var _at=E(_as);if(!_at._){return E(_ar);}else{var _au=E(_at.a),_av=B(_ab(_au.a,_au.b,_au.c,_ar));_ar=_av;_as=_at.b;continue;}}},_aw=function(_ax,_ay,_az,_aA,_aB){return new F(function(){return _aq(B(_ab(_ay,_az,_aA,_ax)),_aB);});},_aC=function(_aD,_aE,_aF){var _aG=E(_aE);return new F(function(){return _aq(B(_ab(_aG.a,_aG.b,_aG.c,_aD)),_aF);});},_aH=function(_aI,_aJ,_aK){var _aL=E(_aK);if(!_aL._){return E(_aJ);}else{var _aM=_aL.a,_aN=E(_aL.b);if(!_aN._){return new F(function(){return _6p(_aM,_aJ);});}else{var _aO=E(_aM),_aP=_aO.b,_aQ=_aO.c,_aR=E(_aO.a),_aS=E(_aN.a),_aT=_aS.b,_aU=_aS.c,_aV=E(_aS.a),_aW=function(_aX){var _aY=B(_8t(_aI,_aV,_aT,_aU,_aN.b)),_aZ=_aY.a,_b0=E(_aY.c);if(!_b0._){return new F(function(){return _aH(_aI<<1,B(_7J(_aO,_aJ,_aZ)),_aY.b);});}else{return new F(function(){return _aC(B(_7J(_aO,_aJ,_aZ)),_b0.a,_b0.b);});}};if(_aR>=_aV){if(_aR!=_aV){return new F(function(){return _aw(_aJ,_aR,_aP,_aQ,_aN);});}else{var _b1=E(_aP),_b2=E(_aT);if(_b1>=_b2){if(_b1!=_b2){return new F(function(){return _aw(_aJ,_aR,_b1,_aQ,_aN);});}else{var _b3=E(_aQ);if(_b3<E(_aU)){return new F(function(){return _aW(_);});}else{return new F(function(){return _aw(_aJ,_aR,_b1,_b3,_aN);});}}}else{return new F(function(){return _aW(_);});}}}else{return new F(function(){return _aW(_);});}}}},_b4=function(_b5,_b6,_b7,_b8,_b9,_ba){var _bb=E(_ba);if(!_bb._){return new F(function(){return _6p(new T3(0,_b7,_b8,_b9),_b6);});}else{var _bc=E(_b7),_bd=E(_bb.a),_be=_bd.b,_bf=_bd.c,_bg=E(_bd.a),_bh=function(_bi){var _bj=B(_8t(_b5,_bg,_be,_bf,_bb.b)),_bk=_bj.a,_bl=E(_bj.c);if(!_bl._){return new F(function(){return _aH(_b5<<1,B(_7J(new T3(0,_bc,_b8,_b9),_b6,_bk)),_bj.b);});}else{return new F(function(){return _aC(B(_7J(new T3(0,_bc,_b8,_b9),_b6,_bk)),_bl.a,_bl.b);});}};if(_bc>=_bg){if(_bc!=_bg){return new F(function(){return _aw(_b6,_bc,_b8,_b9,_bb);});}else{var _bm=E(_be);if(_b8>=_bm){if(_b8!=_bm){return new F(function(){return _aw(_b6,_bc,_b8,_b9,_bb);});}else{var _bn=E(_b9);if(_bn<E(_bf)){return new F(function(){return _bh(_);});}else{return new F(function(){return _aw(_b6,_bc,_b8,_bn,_bb);});}}}else{return new F(function(){return _bh(_);});}}}else{return new F(function(){return _bh(_);});}}},_bo=function(_bp,_bq,_br,_bs,_bt,_bu){var _bv=E(_bu);if(!_bv._){return new F(function(){return _6p(new T3(0,_br,_bs,_bt),_bq);});}else{var _bw=E(_br),_bx=E(_bv.a),_by=_bx.b,_bz=_bx.c,_bA=E(_bx.a),_bB=function(_bC){var _bD=B(_8t(_bp,_bA,_by,_bz,_bv.b)),_bE=_bD.a,_bF=E(_bD.c);if(!_bF._){return new F(function(){return _aH(_bp<<1,B(_7J(new T3(0,_bw,_bs,_bt),_bq,_bE)),_bD.b);});}else{return new F(function(){return _aC(B(_7J(new T3(0,_bw,_bs,_bt),_bq,_bE)),_bF.a,_bF.b);});}};if(_bw>=_bA){if(_bw!=_bA){return new F(function(){return _aw(_bq,_bw,_bs,_bt,_bv);});}else{var _bG=E(_by);if(_bs>=_bG){if(_bs!=_bG){return new F(function(){return _aw(_bq,_bw,_bs,_bt,_bv);});}else{if(_bt<E(_bz)){return new F(function(){return _bB(_);});}else{return new F(function(){return _aw(_bq,_bw,_bs,_bt,_bv);});}}}else{return new F(function(){return _bB(_);});}}}else{return new F(function(){return _bB(_);});}}},_bH=function(_bI,_bJ,_bK,_bL,_bM,_bN){var _bO=E(_bN);if(!_bO._){return new F(function(){return _6p(new T3(0,_bK,_bL,_bM),_bJ);});}else{var _bP=E(_bK),_bQ=E(_bO.a),_bR=_bQ.b,_bS=_bQ.c,_bT=E(_bQ.a),_bU=function(_bV){var _bW=B(_8t(_bI,_bT,_bR,_bS,_bO.b)),_bX=_bW.a,_bY=E(_bW.c);if(!_bY._){return new F(function(){return _aH(_bI<<1,B(_7J(new T3(0,_bP,_bL,_bM),_bJ,_bX)),_bW.b);});}else{return new F(function(){return _aC(B(_7J(new T3(0,_bP,_bL,_bM),_bJ,_bX)),_bY.a,_bY.b);});}};if(_bP>=_bT){if(_bP!=_bT){return new F(function(){return _aw(_bJ,_bP,_bL,_bM,_bO);});}else{var _bZ=E(_bL),_c0=E(_bR);if(_bZ>=_c0){if(_bZ!=_c0){return new F(function(){return _aw(_bJ,_bP,_bZ,_bM,_bO);});}else{var _c1=E(_bM);if(_c1<E(_bS)){return new F(function(){return _bU(_);});}else{return new F(function(){return _aw(_bJ,_bP,_bZ,_c1,_bO);});}}}else{return new F(function(){return _bU(_);});}}}else{return new F(function(){return _bU(_);});}}},_c2=function(_c3){var _c4=E(_c3);if(!_c4._){return new T0(1);}else{var _c5=_c4.a,_c6=E(_c4.b);if(!_c6._){return new T4(0,1,E(_c5),E(_5I),E(_5I));}else{var _c7=_c6.b,_c8=E(_c5),_c9=E(_c8.a),_ca=E(_c6.a),_cb=_ca.b,_cc=_ca.c,_cd=E(_ca.a);if(_c9>=_cd){if(_c9!=_cd){return new F(function(){return _aw(new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cb,_cc,_c7);});}else{var _ce=E(_c8.b),_cf=E(_cb);if(_ce>=_cf){if(_ce!=_cf){return new F(function(){return _aw(new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cc,_c7);});}else{var _cg=E(_cc);if(E(_c8.c)<_cg){return new F(function(){return _bo(1,new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cg,_c7);});}else{return new F(function(){return _aw(new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cg,_c7);});}}}else{return new F(function(){return _b4(1,new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cc,_c7);});}}}else{return new F(function(){return _bH(1,new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cb,_cc,_c7);});}}}},_ch=function(_ci,_cj,_ck,_cl,_cm){var _cn=E(_ci);if(_cn==1){var _co=E(_cm);if(!_co._){return new T3(0,new T5(0,1,E(new T2(0,_cj,_ck)),_cl,E(_0),E(_0)),_1,_1);}else{var _cp=E(E(_co.a).a),_cq=E(_cj),_cr=E(_cp.a);return (_cq>=_cr)?(_cq!=_cr)?new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_1,_co):(_ck<E(_cp.b))?new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_co,_1):new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_1,_co):new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_co,_1);}}else{var _cs=B(_ch(_cn>>1,_cj,_ck,_cl,_cm)),_ct=_cs.a,_cu=_cs.c,_cv=E(_cs.b);if(!_cv._){return new T3(0,_ct,_1,_cu);}else{var _cw=E(_cv.a),_cx=_cw.a,_cy=_cw.b,_cz=E(_cv.b);if(!_cz._){return new T3(0,new T(function(){return B(_O(_cx,_cy,_ct));}),_1,_cu);}else{var _cA=_cz.b,_cB=E(_cz.a),_cC=_cB.b,_cD=E(_cx),_cE=E(_cB.a),_cF=_cE.b,_cG=E(_cD.a),_cH=E(_cE.a);if(_cG>=_cH){if(_cG!=_cH){return new T3(0,_ct,_1,_cv);}else{var _cI=E(_cF);if(E(_cD.b)<_cI){var _cJ=B(_ch(_cn>>1,_cH,_cI,_cC,_cA));return new T3(0,new T(function(){return B(_2h(_cD,_cy,_ct,_cJ.a));}),_cJ.b,_cJ.c);}else{return new T3(0,_ct,_1,_cv);}}}else{var _cK=B(_cL(_cn>>1,_cH,_cF,_cC,_cA));return new T3(0,new T(function(){return B(_2h(_cD,_cy,_ct,_cK.a));}),_cK.b,_cK.c);}}}}},_cL=function(_cM,_cN,_cO,_cP,_cQ){var _cR=E(_cM);if(_cR==1){var _cS=E(_cQ);if(!_cS._){return new T3(0,new T5(0,1,E(new T2(0,_cN,_cO)),_cP,E(_0),E(_0)),_1,_1);}else{var _cT=E(E(_cS.a).a),_cU=E(_cN),_cV=E(_cT.a);if(_cU>=_cV){if(_cU!=_cV){return new T3(0,new T5(0,1,E(new T2(0,_cU,_cO)),_cP,E(_0),E(_0)),_1,_cS);}else{var _cW=E(_cO);return (_cW<E(_cT.b))?new T3(0,new T5(0,1,E(new T2(0,_cU,_cW)),_cP,E(_0),E(_0)),_cS,_1):new T3(0,new T5(0,1,E(new T2(0,_cU,_cW)),_cP,E(_0),E(_0)),_1,_cS);}}else{return new T3(0,new T5(0,1,E(new T2(0,_cU,_cO)),_cP,E(_0),E(_0)),_cS,_1);}}}else{var _cX=B(_cL(_cR>>1,_cN,_cO,_cP,_cQ)),_cY=_cX.a,_cZ=_cX.c,_d0=E(_cX.b);if(!_d0._){return new T3(0,_cY,_1,_cZ);}else{var _d1=E(_d0.a),_d2=_d1.a,_d3=_d1.b,_d4=E(_d0.b);if(!_d4._){return new T3(0,new T(function(){return B(_O(_d2,_d3,_cY));}),_1,_cZ);}else{var _d5=_d4.b,_d6=E(_d4.a),_d7=_d6.b,_d8=E(_d2),_d9=E(_d6.a),_da=_d9.b,_db=E(_d8.a),_dc=E(_d9.a);if(_db>=_dc){if(_db!=_dc){return new T3(0,_cY,_1,_d0);}else{var _dd=E(_da);if(E(_d8.b)<_dd){var _de=B(_ch(_cR>>1,_dc,_dd,_d7,_d5));return new T3(0,new T(function(){return B(_2h(_d8,_d3,_cY,_de.a));}),_de.b,_de.c);}else{return new T3(0,_cY,_1,_d0);}}}else{var _df=B(_cL(_cR>>1,_dc,_da,_d7,_d5));return new T3(0,new T(function(){return B(_2h(_d8,_d3,_cY,_df.a));}),_df.b,_df.c);}}}}},_dg=function(_dh,_di,_dj,_dk,_dl){var _dm=E(_dl);if(!_dm._){var _dn=_dm.c,_do=_dm.d,_dp=_dm.e,_dq=E(_dm.b),_dr=E(_dq.a);if(_dh>=_dr){if(_dh!=_dr){return new F(function(){return _6(_dq,_dn,_do,B(_dg(_dh,_,_dj,_dk,_dp)));});}else{var _ds=E(_dq.b);if(_dj>=_ds){if(_dj!=_ds){return new F(function(){return _6(_dq,_dn,_do,B(_dg(_dh,_,_dj,_dk,_dp)));});}else{return new T5(0,_dm.a,E(new T2(0,_dh,_dj)),_dk,E(_do),E(_dp));}}else{return new F(function(){return _X(_dq,_dn,B(_dg(_dh,_,_dj,_dk,_do)),_dp);});}}}else{return new F(function(){return _X(_dq,_dn,B(_dg(_dh,_,_dj,_dk,_do)),_dp);});}}else{return new T5(0,1,E(new T2(0,_dh,_dj)),_dk,E(_0),E(_0));}},_dt=function(_du,_dv,_dw,_dx,_dy){var _dz=E(_dy);if(!_dz._){var _dA=_dz.c,_dB=_dz.d,_dC=_dz.e,_dD=E(_dz.b),_dE=E(_dD.a);if(_du>=_dE){if(_du!=_dE){return new F(function(){return _6(_dD,_dA,_dB,B(_dt(_du,_,_dw,_dx,_dC)));});}else{var _dF=E(_dw),_dG=E(_dD.b);if(_dF>=_dG){if(_dF!=_dG){return new F(function(){return _6(_dD,_dA,_dB,B(_dg(_du,_,_dF,_dx,_dC)));});}else{return new T5(0,_dz.a,E(new T2(0,_du,_dF)),_dx,E(_dB),E(_dC));}}else{return new F(function(){return _X(_dD,_dA,B(_dg(_du,_,_dF,_dx,_dB)),_dC);});}}}else{return new F(function(){return _X(_dD,_dA,B(_dt(_du,_,_dw,_dx,_dB)),_dC);});}}else{return new T5(0,1,E(new T2(0,_du,_dw)),_dx,E(_0),E(_0));}},_dH=function(_dI,_dJ,_dK,_dL){var _dM=E(_dL);if(!_dM._){var _dN=_dM.c,_dO=_dM.d,_dP=_dM.e,_dQ=E(_dM.b),_dR=E(_dI),_dS=E(_dQ.a);if(_dR>=_dS){if(_dR!=_dS){return new F(function(){return _6(_dQ,_dN,_dO,B(_dt(_dR,_,_dJ,_dK,_dP)));});}else{var _dT=E(_dJ),_dU=E(_dQ.b);if(_dT>=_dU){if(_dT!=_dU){return new F(function(){return _6(_dQ,_dN,_dO,B(_dg(_dR,_,_dT,_dK,_dP)));});}else{return new T5(0,_dM.a,E(new T2(0,_dR,_dT)),_dK,E(_dO),E(_dP));}}else{return new F(function(){return _X(_dQ,_dN,B(_dg(_dR,_,_dT,_dK,_dO)),_dP);});}}}else{return new F(function(){return _X(_dQ,_dN,B(_dt(_dR,_,_dJ,_dK,_dO)),_dP);});}}else{return new T5(0,1,E(new T2(0,_dI,_dJ)),_dK,E(_0),E(_0));}},_dV=function(_dW,_dX){while(1){var _dY=E(_dX);if(!_dY._){return E(_dW);}else{var _dZ=E(_dY.a),_e0=E(_dZ.a),_e1=B(_dH(_e0.a,_e0.b,_dZ.b,_dW));_dW=_e1;_dX=_dY.b;continue;}}},_e2=function(_e3,_e4,_e5,_e6,_e7){return new F(function(){return _dV(B(_dH(_e4,_e5,_e6,_e3)),_e7);});},_e8=function(_e9,_ea,_eb){var _ec=E(_ea),_ed=E(_ec.a);return new F(function(){return _dV(B(_dH(_ed.a,_ed.b,_ec.b,_e9)),_eb);});},_ee=function(_ef,_eg,_eh){var _ei=E(_eh);if(!_ei._){return E(_eg);}else{var _ej=E(_ei.a),_ek=_ej.a,_el=_ej.b,_em=E(_ei.b);if(!_em._){return new F(function(){return _O(_ek,_el,_eg);});}else{var _en=E(_em.a),_eo=E(_ek),_ep=_eo.b,_eq=E(_en.a),_er=_eq.b,_es=E(_eo.a),_et=E(_eq.a),_eu=function(_ev){var _ew=B(_cL(_ef,_et,_er,_en.b,_em.b)),_ex=_ew.a,_ey=E(_ew.c);if(!_ey._){return new F(function(){return _ee(_ef<<1,B(_2h(_eo,_el,_eg,_ex)),_ew.b);});}else{return new F(function(){return _e8(B(_2h(_eo,_el,_eg,_ex)),_ey.a,_ey.b);});}};if(_es>=_et){if(_es!=_et){return new F(function(){return _e2(_eg,_es,_ep,_el,_em);});}else{var _ez=E(_ep);if(_ez<E(_er)){return new F(function(){return _eu(_);});}else{return new F(function(){return _e2(_eg,_es,_ez,_el,_em);});}}}else{return new F(function(){return _eu(_);});}}}},_eA=function(_eB,_eC,_eD,_eE,_eF,_eG){var _eH=E(_eG);if(!_eH._){return new F(function(){return _O(new T2(0,_eD,_eE),_eF,_eC);});}else{var _eI=E(_eH.a),_eJ=E(_eI.a),_eK=_eJ.b,_eL=E(_eD),_eM=E(_eJ.a),_eN=function(_eO){var _eP=B(_cL(_eB,_eM,_eK,_eI.b,_eH.b)),_eQ=_eP.a,_eR=E(_eP.c);if(!_eR._){return new F(function(){return _ee(_eB<<1,B(_2h(new T2(0,_eL,_eE),_eF,_eC,_eQ)),_eP.b);});}else{return new F(function(){return _e8(B(_2h(new T2(0,_eL,_eE),_eF,_eC,_eQ)),_eR.a,_eR.b);});}};if(_eL>=_eM){if(_eL!=_eM){return new F(function(){return _e2(_eC,_eL,_eE,_eF,_eH);});}else{var _eS=E(_eE);if(_eS<E(_eK)){return new F(function(){return _eN(_);});}else{return new F(function(){return _e2(_eC,_eL,_eS,_eF,_eH);});}}}else{return new F(function(){return _eN(_);});}}},_eT=function(_eU,_eV,_eW,_eX,_eY,_eZ){var _f0=E(_eZ);if(!_f0._){return new F(function(){return _O(new T2(0,_eW,_eX),_eY,_eV);});}else{var _f1=E(_f0.a),_f2=E(_f1.a),_f3=_f2.b,_f4=E(_eW),_f5=E(_f2.a),_f6=function(_f7){var _f8=B(_cL(_eU,_f5,_f3,_f1.b,_f0.b)),_f9=_f8.a,_fa=E(_f8.c);if(!_fa._){return new F(function(){return _ee(_eU<<1,B(_2h(new T2(0,_f4,_eX),_eY,_eV,_f9)),_f8.b);});}else{return new F(function(){return _e8(B(_2h(new T2(0,_f4,_eX),_eY,_eV,_f9)),_fa.a,_fa.b);});}};if(_f4>=_f5){if(_f4!=_f5){return new F(function(){return _e2(_eV,_f4,_eX,_eY,_f0);});}else{if(_eX<E(_f3)){return new F(function(){return _f6(_);});}else{return new F(function(){return _e2(_eV,_f4,_eX,_eY,_f0);});}}}else{return new F(function(){return _f6(_);});}}},_fb=function(_fc){var _fd=E(_fc);if(!_fd._){return new T0(1);}else{var _fe=E(_fd.a),_ff=_fe.a,_fg=_fe.b,_fh=E(_fd.b);if(!_fh._){return new T5(0,1,E(_ff),_fg,E(_0),E(_0));}else{var _fi=_fh.b,_fj=E(_fh.a),_fk=_fj.b,_fl=E(_ff),_fm=E(_fj.a),_fn=_fm.b,_fo=E(_fl.a),_fp=E(_fm.a);if(_fo>=_fp){if(_fo!=_fp){return new F(function(){return _e2(new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fn,_fk,_fi);});}else{var _fq=E(_fn);if(E(_fl.b)<_fq){return new F(function(){return _eT(1,new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fq,_fk,_fi);});}else{return new F(function(){return _e2(new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fq,_fk,_fi);});}}}else{return new F(function(){return _eA(1,new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fn,_fk,_fi);});}}}},_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=E(_fw);if(!_fx._){var _fy=_fx.c,_fz=_fx.d,_fA=E(_fx.b),_fB=E(_fs),_fC=E(_fA.a);if(_fB>=_fC){if(_fB!=_fC){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_ft,_fu,_fv,_fz)));});}else{var _fD=E(_ft),_fE=E(_fA.b);if(_fD>=_fE){if(_fD!=_fE){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_fD,_fu,_fv,_fz)));});}else{var _fF=E(_fu),_fG=E(_fA.c);if(_fF>=_fG){if(_fF!=_fG){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_fD,_fF,_fv,_fz)));});}else{var _fH=E(_fv),_fI=E(_fA.d);if(_fH>=_fI){if(_fH!=_fI){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_fD,_fF,_fH,_fz)));});}else{return new T4(0,_fx.a,E(new T4(0,_fB,_fD,_fF,_fH)),E(_fy),E(_fz));}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_fD,_fF,_fH,_fy)),_fz);});}}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_fD,_fF,_fv,_fy)),_fz);});}}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_fD,_fu,_fv,_fy)),_fz);});}}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_ft,_fu,_fv,_fy)),_fz);});}}else{return new T4(0,1,E(new T4(0,_fs,_ft,_fu,_fv)),E(_5I),E(_5I));}},_fJ=function(_fK,_fL){while(1){var _fM=E(_fL);if(!_fM._){return E(_fK);}else{var _fN=E(_fM.a),_fO=B(_fr(_fN.a,_fN.b,_fN.c,_fN.d,_fK));_fK=_fO;_fL=_fM.b;continue;}}},_fP=function(_fQ,_fR,_fS,_fT,_fU,_fV){return new F(function(){return _fJ(B(_fr(_fR,_fS,_fT,_fU,_fQ)),_fV);});},_fW=function(_fX,_fY){var _fZ=E(_fY);if(!_fZ._){return new T3(0,_5I,_1,_1);}else{var _g0=_fZ.a,_g1=E(_fX);if(_g1==1){var _g2=E(_fZ.b);if(!_g2._){return new T3(0,new T(function(){return new T4(0,1,E(_g0),E(_5I),E(_5I));}),_1,_1);}else{var _g3=E(_g0),_g4=E(_g3.a),_g5=E(_g2.a),_g6=E(_g5.a);if(_g4>=_g6){if(_g4!=_g6){return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2);}else{var _g7=E(_g3.b),_g8=E(_g5.b);if(_g7>=_g8){if(_g7!=_g8){return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2);}else{var _g9=E(_g3.c),_ga=E(_g5.c);return (_g9>=_ga)?(_g9!=_ga)?new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2):(E(_g3.d)<E(_g5.d))?new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1):new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2):new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1);}}else{return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1);}}}else{return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1);}}}else{var _gb=B(_fW(_g1>>1,_fZ)),_gc=_gb.a,_gd=_gb.c,_ge=E(_gb.b);if(!_ge._){return new T3(0,_gc,_1,_gd);}else{var _gf=_ge.a,_gg=E(_ge.b);if(!_gg._){return new T3(0,new T(function(){return B(_6p(_gf,_gc));}),_1,_gd);}else{var _gh=E(_gf),_gi=E(_gh.a),_gj=E(_gg.a),_gk=E(_gj.a);if(_gi>=_gk){if(_gi!=_gk){return new T3(0,_gc,_1,_ge);}else{var _gl=E(_gh.b),_gm=E(_gj.b);if(_gl>=_gm){if(_gl!=_gm){return new T3(0,_gc,_1,_ge);}else{var _gn=E(_gh.c),_go=E(_gj.c);if(_gn>=_go){if(_gn!=_go){return new T3(0,_gc,_1,_ge);}else{if(E(_gh.d)<E(_gj.d)){var _gp=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gp.a));}),_gp.b,_gp.c);}else{return new T3(0,_gc,_1,_ge);}}}else{var _gq=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gq.a));}),_gq.b,_gq.c);}}}else{var _gr=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gr.a));}),_gr.b,_gr.c);}}}else{var _gs=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gs.a));}),_gs.b,_gs.c);}}}}}},_gt=function(_gu,_gv,_gw){var _gx=E(_gw);if(!_gx._){return E(_gv);}else{var _gy=_gx.a,_gz=E(_gx.b);if(!_gz._){return new F(function(){return _6p(_gy,_gv);});}else{var _gA=E(_gy),_gB=_gA.b,_gC=_gA.c,_gD=_gA.d,_gE=E(_gA.a),_gF=E(_gz.a),_gG=E(_gF.a),_gH=function(_gI){var _gJ=B(_fW(_gu,_gz)),_gK=_gJ.a,_gL=E(_gJ.c);if(!_gL._){return new F(function(){return _gt(_gu<<1,B(_7J(_gA,_gv,_gK)),_gJ.b);});}else{return new F(function(){return _fJ(B(_7J(_gA,_gv,_gK)),_gL);});}};if(_gE>=_gG){if(_gE!=_gG){return new F(function(){return _fP(_gv,_gE,_gB,_gC,_gD,_gz);});}else{var _gM=E(_gB),_gN=E(_gF.b);if(_gM>=_gN){if(_gM!=_gN){return new F(function(){return _fP(_gv,_gE,_gM,_gC,_gD,_gz);});}else{var _gO=E(_gC),_gP=E(_gF.c);if(_gO>=_gP){if(_gO!=_gP){return new F(function(){return _fP(_gv,_gE,_gM,_gO,_gD,_gz);});}else{var _gQ=E(_gD);if(_gQ<E(_gF.d)){return new F(function(){return _gH(_);});}else{return new F(function(){return _fP(_gv,_gE,_gM,_gO,_gQ,_gz);});}}}else{return new F(function(){return _gH(_);});}}}else{return new F(function(){return _gH(_);});}}}else{return new F(function(){return _gH(_);});}}}},_gR=function(_gS){var _gT=E(_gS);if(!_gT._){return new T0(1);}else{var _gU=_gT.a,_gV=E(_gT.b);if(!_gV._){return new T4(0,1,E(_gU),E(_5I),E(_5I));}else{var _gW=_gV.b,_gX=E(_gU),_gY=E(_gX.a),_gZ=E(_gV.a),_h0=_gZ.b,_h1=_gZ.c,_h2=_gZ.d,_h3=E(_gZ.a);if(_gY>=_h3){if(_gY!=_h3){return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h0,_h1,_h2,_gW);});}else{var _h4=E(_gX.b),_h5=E(_h0);if(_h4>=_h5){if(_h4!=_h5){return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h5,_h1,_h2,_gW);});}else{var _h6=E(_gX.c),_h7=E(_h1);if(_h6>=_h7){if(_h6!=_h7){return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h5,_h7,_h2,_gW);});}else{var _h8=E(_h2);if(E(_gX.d)<_h8){return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}else{return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h5,_h7,_h8,_gW);});}}}else{return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}}}else{return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}}}else{return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}}}},_h9=0,_ha=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_hb=new T(function(){return B(err(_ha));}),_hc=function(_hd,_he){while(1){var _hf=B((function(_hg,_hh){var _hi=E(_hh);if(!_hi._){_hd=new T2(1,new T2(0,_hi.b,_hi.c),new T(function(){return B(_hc(_hg,_hi.e));}));_he=_hi.d;return __continue;}else{return E(_hg);}})(_hd,_he));if(_hf!=__continue){return _hf;}}},_hj=44,_hk=function(_hl,_hm,_hn){return new F(function(){return A1(_hl,new T2(1,_hj,new T(function(){return B(A1(_hm,_hn));})));});},_ho=new T(function(){return B(unCStr("CC "));}),_hp=new T(function(){return B(unCStr("IdentCC "));}),_hq=function(_hr,_hs){var _ht=E(_hr);return (_ht._==0)?E(_hs):new T2(1,_ht.a,new T(function(){return B(_hq(_ht.b,_hs));}));},_hu=function(_hv,_hw){var _hx=jsShowI(_hv);return new F(function(){return _hq(fromJSStr(_hx),_hw);});},_hy=41,_hz=40,_hA=function(_hB,_hC,_hD){if(_hC>=0){return new F(function(){return _hu(_hC,_hD);});}else{if(_hB<=6){return new F(function(){return _hu(_hC,_hD);});}else{return new T2(1,_hz,new T(function(){var _hE=jsShowI(_hC);return B(_hq(fromJSStr(_hE),new T2(1,_hy,_hD)));}));}}},_hF=function(_hG,_hH,_hI){if(_hG<11){return new F(function(){return _hq(_hp,new T(function(){return B(_hA(11,E(_hH),_hI));},1));});}else{var _hJ=new T(function(){return B(_hq(_hp,new T(function(){return B(_hA(11,E(_hH),new T2(1,_hy,_hI)));},1)));});return new T2(1,_hz,_hJ);}},_hK=32,_hL=function(_hM,_hN,_hO,_hP,_hQ,_hR){var _hS=function(_hT){var _hU=new T(function(){var _hV=new T(function(){return B(_hA(11,E(_hP),new T2(1,_hK,new T(function(){return B(_hA(11,E(_hQ),_hT));}))));});return B(_hA(11,E(_hO),new T2(1,_hK,_hV)));});return new F(function(){return _hF(11,_hN,new T2(1,_hK,_hU));});};if(_hM<11){return new F(function(){return _hq(_ho,new T(function(){return B(_hS(_hR));},1));});}else{var _hW=new T(function(){return B(_hq(_ho,new T(function(){return B(_hS(new T2(1,_hy,_hR)));},1)));});return new T2(1,_hz,_hW);}},_hX=function(_hY,_hZ){var _i0=E(_hY);return new F(function(){return _hL(0,_i0.a,_i0.b,_i0.c,_i0.d,_hZ);});},_i1=new T(function(){return B(unCStr("RC "));}),_i2=function(_i3,_i4,_i5,_i6,_i7){var _i8=function(_i9){var _ia=new T(function(){var _ib=new T(function(){return B(_hA(11,E(_i5),new T2(1,_hK,new T(function(){return B(_hA(11,E(_i6),_i9));}))));});return B(_hF(11,_i4,new T2(1,_hK,_ib)));},1);return new F(function(){return _hq(_i1,_ia);});};if(_i3<11){return new F(function(){return _i8(_i7);});}else{return new T2(1,_hz,new T(function(){return B(_i8(new T2(1,_hy,_i7)));}));}},_ic=function(_id,_ie){var _if=E(_id);return new F(function(){return _i2(0,_if.a,_if.b,_if.c,_ie);});},_ig=new T(function(){return B(unCStr("IdentPay "));}),_ih=function(_ii,_ij,_ik){if(_ii<11){return new F(function(){return _hq(_ig,new T(function(){return B(_hA(11,E(_ij),_ik));},1));});}else{var _il=new T(function(){return B(_hq(_ig,new T(function(){return B(_hA(11,E(_ij),new T2(1,_hy,_ik)));},1)));});return new T2(1,_hz,_il);}},_im=new T(function(){return B(unCStr(": empty list"));}),_in=new T(function(){return B(unCStr("Prelude."));}),_io=function(_ip){return new F(function(){return err(B(_hq(_in,new T(function(){return B(_hq(_ip,_im));},1))));});},_iq=new T(function(){return B(unCStr("foldr1"));}),_ir=new T(function(){return B(_io(_iq));}),_is=function(_it,_iu){var _iv=E(_iu);if(!_iv._){return E(_ir);}else{var _iw=_iv.a,_ix=E(_iv.b);if(!_ix._){return E(_iw);}else{return new F(function(){return A2(_it,_iw,new T(function(){return B(_is(_it,_ix));}));});}}},_iy=function(_iz,_iA,_iB){var _iC=new T(function(){var _iD=function(_iE){var _iF=E(_iz),_iG=new T(function(){return B(A3(_is,_hk,new T2(1,function(_iH){return new F(function(){return _ih(0,_iF.a,_iH);});},new T2(1,function(_iI){return new F(function(){return _hA(0,E(_iF.b),_iI);});},_1)),new T2(1,_hy,_iE)));});return new T2(1,_hz,_iG);};return B(A3(_is,_hk,new T2(1,_iD,new T2(1,function(_iJ){return new F(function(){return _hA(0,E(_iA),_iJ);});},_1)),new T2(1,_hy,_iB)));});return new T2(0,_hz,_iC);},_iK=function(_iL,_iM){var _iN=E(_iL),_iO=B(_iy(_iN.a,_iN.b,_iM));return new T2(1,_iO.a,_iO.b);},_iP=93,_iQ=91,_iR=function(_iS,_iT,_iU){var _iV=E(_iT);if(!_iV._){return new F(function(){return unAppCStr("[]",_iU);});}else{var _iW=new T(function(){var _iX=new T(function(){var _iY=function(_iZ){var _j0=E(_iZ);if(!_j0._){return E(new T2(1,_iP,_iU));}else{var _j1=new T(function(){return B(A2(_iS,_j0.a,new T(function(){return B(_iY(_j0.b));})));});return new T2(1,_hj,_j1);}};return B(_iY(_iV.b));});return B(A2(_iS,_iV.a,_iX));});return new T2(1,_iQ,_iW);}},_j2=function(_j3,_j4){return new F(function(){return _iR(_iK,_j3,_j4);});},_j5=new T(function(){return B(unCStr("IdentChoice "));}),_j6=function(_j7,_j8,_j9){if(_j7<11){return new F(function(){return _hq(_j5,new T(function(){return B(_hA(11,E(_j8),_j9));},1));});}else{var _ja=new T(function(){return B(_hq(_j5,new T(function(){return B(_hA(11,E(_j8),new T2(1,_hy,_j9)));},1)));});return new T2(1,_hz,_ja);}},_jb=function(_jc,_jd,_je){var _jf=new T(function(){var _jg=function(_jh){var _ji=E(_jc),_jj=new T(function(){return B(A3(_is,_hk,new T2(1,function(_jk){return new F(function(){return _j6(0,_ji.a,_jk);});},new T2(1,function(_jl){return new F(function(){return _hA(0,E(_ji.b),_jl);});},_1)),new T2(1,_hy,_jh)));});return new T2(1,_hz,_jj);};return B(A3(_is,_hk,new T2(1,_jg,new T2(1,function(_jm){return new F(function(){return _hA(0,E(_jd),_jm);});},_1)),new T2(1,_hy,_je)));});return new T2(0,_hz,_jf);},_jn=function(_jo,_jp){var _jq=E(_jo),_jr=B(_jb(_jq.a,_jq.b,_jp));return new T2(1,_jr.a,_jr.b);},_js=function(_jt,_ju){return new F(function(){return _iR(_jn,_jt,_ju);});},_jv=new T2(1,_hy,_1),_jw=function(_jx,_jy){while(1){var _jz=B((function(_jA,_jB){var _jC=E(_jB);if(!_jC._){_jx=new T2(1,_jC.b,new T(function(){return B(_jw(_jA,_jC.d));}));_jy=_jC.c;return __continue;}else{return E(_jA);}})(_jx,_jy));if(_jz!=__continue){return _jz;}}},_jD=function(_jE,_jF,_jG,_jH){var _jI=new T(function(){var _jJ=new T(function(){return B(_hc(_1,_jH));}),_jK=new T(function(){return B(_hc(_1,_jG));}),_jL=new T(function(){return B(_jw(_1,_jF));}),_jM=new T(function(){return B(_jw(_1,_jE));});return B(A3(_is,_hk,new T2(1,function(_jN){return new F(function(){return _iR(_hX,_jM,_jN);});},new T2(1,function(_jO){return new F(function(){return _iR(_ic,_jL,_jO);});},new T2(1,function(_jP){return new F(function(){return _j2(_jK,_jP);});},new T2(1,function(_jQ){return new F(function(){return _js(_jJ,_jQ);});},_1)))),_jv));});return new T2(0,_hz,_jI);},_jR=new T(function(){return B(err(_ha));}),_jS=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jT=new T(function(){return B(err(_jS));}),_jU=new T0(2),_jV=function(_jW){return new T2(3,_jW,_jU);},_jX=new T(function(){return B(unCStr("base"));}),_jY=new T(function(){return B(unCStr("Control.Exception.Base"));}),_jZ=new T(function(){return B(unCStr("PatternMatchFail"));}),_k0=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_jX,_jY,_jZ),_k1=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_k0,_1,_1),_k2=function(_k3){return E(_k1);},_k4=function(_k5){return E(E(_k5).a);},_k6=function(_k7,_k8,_k9){var _ka=B(A1(_k7,_)),_kb=B(A1(_k8,_)),_kc=hs_eqWord64(_ka.a,_kb.a);if(!_kc){return __Z;}else{var _kd=hs_eqWord64(_ka.b,_kb.b);return (!_kd)?__Z:new T1(1,_k9);}},_ke=function(_kf){var _kg=E(_kf);return new F(function(){return _k6(B(_k4(_kg.a)),_k2,_kg.b);});},_kh=function(_ki){return E(E(_ki).a);},_kj=function(_kk){return new T2(0,_kl,_kk);},_km=function(_kn,_ko){return new F(function(){return _hq(E(_kn).a,_ko);});},_kp=function(_kq,_kr){return new F(function(){return _iR(_km,_kq,_kr);});},_ks=function(_kt,_ku,_kv){return new F(function(){return _hq(E(_ku).a,_kv);});},_kw=new T3(0,_ks,_kh,_kp),_kl=new T(function(){return new T5(0,_k2,_kw,_kj,_ke,_kh);}),_kx=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_ky=function(_kz){return E(E(_kz).c);},_kA=function(_kB,_kC){return new F(function(){return die(new T(function(){return B(A2(_ky,_kC,_kB));}));});},_kD=function(_kE,_kF){return new F(function(){return _kA(_kE,_kF);});},_kG=function(_kH,_kI){var _kJ=E(_kI);if(!_kJ._){return new T2(0,_1,_1);}else{var _kK=_kJ.a;if(!B(A1(_kH,_kK))){return new T2(0,_1,_kJ);}else{var _kL=new T(function(){var _kM=B(_kG(_kH,_kJ.b));return new T2(0,_kM.a,_kM.b);});return new T2(0,new T2(1,_kK,new T(function(){return E(E(_kL).a);})),new T(function(){return E(E(_kL).b);}));}}},_kN=32,_kO=new T(function(){return B(unCStr("\n"));}),_kP=function(_kQ){return (E(_kQ)==124)?false:true;},_kR=function(_kS,_kT){var _kU=B(_kG(_kP,B(unCStr(_kS)))),_kV=_kU.a,_kW=function(_kX,_kY){var _kZ=new T(function(){var _l0=new T(function(){return B(_hq(_kT,new T(function(){return B(_hq(_kY,_kO));},1)));});return B(unAppCStr(": ",_l0));},1);return new F(function(){return _hq(_kX,_kZ);});},_l1=E(_kU.b);if(!_l1._){return new F(function(){return _kW(_kV,_1);});}else{if(E(_l1.a)==124){return new F(function(){return _kW(_kV,new T2(1,_kN,_l1.b));});}else{return new F(function(){return _kW(_kV,_1);});}}},_l2=function(_l3){return new F(function(){return _kD(new T1(0,new T(function(){return B(_kR(_l3,_kx));})),_kl);});},_l4=new T(function(){return B(_l2("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_l5=function(_l6,_l7){while(1){var _l8=B((function(_l9,_la){var _lb=E(_l9);switch(_lb._){case 0:var _lc=E(_la);if(!_lc._){return __Z;}else{_l6=B(A1(_lb.a,_lc.a));_l7=_lc.b;return __continue;}break;case 1:var _ld=B(A1(_lb.a,_la)),_le=_la;_l6=_ld;_l7=_le;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_lb.a,_la),new T(function(){return B(_l5(_lb.b,_la));}));default:return E(_lb.a);}})(_l6,_l7));if(_l8!=__continue){return _l8;}}},_lf=function(_lg,_lh){var _li=function(_lj){var _lk=E(_lh);if(_lk._==3){return new T2(3,_lk.a,new T(function(){return B(_lf(_lg,_lk.b));}));}else{var _ll=E(_lg);if(_ll._==2){return E(_lk);}else{var _lm=E(_lk);if(_lm._==2){return E(_ll);}else{var _ln=function(_lo){var _lp=E(_lm);if(_lp._==4){var _lq=function(_lr){return new T1(4,new T(function(){return B(_hq(B(_l5(_ll,_lr)),_lp.a));}));};return new T1(1,_lq);}else{var _ls=E(_ll);if(_ls._==1){var _lt=_ls.a,_lu=E(_lp);if(!_lu._){return new T1(1,function(_lv){return new F(function(){return _lf(B(A1(_lt,_lv)),_lu);});});}else{var _lw=function(_lx){return new F(function(){return _lf(B(A1(_lt,_lx)),new T(function(){return B(A1(_lu.a,_lx));}));});};return new T1(1,_lw);}}else{var _ly=E(_lp);if(!_ly._){return E(_l4);}else{var _lz=function(_lA){return new F(function(){return _lf(_ls,new T(function(){return B(A1(_ly.a,_lA));}));});};return new T1(1,_lz);}}}},_lB=E(_ll);switch(_lB._){case 1:var _lC=E(_lm);if(_lC._==4){var _lD=function(_lE){return new T1(4,new T(function(){return B(_hq(B(_l5(B(A1(_lB.a,_lE)),_lE)),_lC.a));}));};return new T1(1,_lD);}else{return new F(function(){return _ln(_);});}break;case 4:var _lF=_lB.a,_lG=E(_lm);switch(_lG._){case 0:var _lH=function(_lI){var _lJ=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(_lG,_lI));},1)));});return new T1(4,_lJ);};return new T1(1,_lH);case 1:var _lK=function(_lL){var _lM=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(B(A1(_lG.a,_lL)),_lL));},1)));});return new T1(4,_lM);};return new T1(1,_lK);default:return new T1(4,new T(function(){return B(_hq(_lF,_lG.a));}));}break;default:return new F(function(){return _ln(_);});}}}}},_lN=E(_lg);switch(_lN._){case 0:var _lO=E(_lh);if(!_lO._){var _lP=function(_lQ){return new F(function(){return _lf(B(A1(_lN.a,_lQ)),new T(function(){return B(A1(_lO.a,_lQ));}));});};return new T1(0,_lP);}else{return new F(function(){return _li(_);});}break;case 3:return new T2(3,_lN.a,new T(function(){return B(_lf(_lN.b,_lh));}));default:return new F(function(){return _li(_);});}},_lR=new T(function(){return B(unCStr("("));}),_lS=new T(function(){return B(unCStr(")"));}),_lT=function(_lU,_lV){while(1){var _lW=E(_lU);if(!_lW._){return (E(_lV)._==0)?true:false;}else{var _lX=E(_lV);if(!_lX._){return false;}else{if(E(_lW.a)!=E(_lX.a)){return false;}else{_lU=_lW.b;_lV=_lX.b;continue;}}}}},_lY=function(_lZ,_m0){return E(_lZ)!=E(_m0);},_m1=function(_m2,_m3){return E(_m2)==E(_m3);},_m4=new T2(0,_m1,_lY),_m5=function(_m6,_m7){while(1){var _m8=E(_m6);if(!_m8._){return (E(_m7)._==0)?true:false;}else{var _m9=E(_m7);if(!_m9._){return false;}else{if(E(_m8.a)!=E(_m9.a)){return false;}else{_m6=_m8.b;_m7=_m9.b;continue;}}}}},_ma=function(_mb,_mc){return (!B(_m5(_mb,_mc)))?true:false;},_md=new T2(0,_m5,_ma),_me=function(_mf,_mg){var _mh=E(_mf);switch(_mh._){case 0:return new T1(0,function(_mi){return new F(function(){return _me(B(A1(_mh.a,_mi)),_mg);});});case 1:return new T1(1,function(_mj){return new F(function(){return _me(B(A1(_mh.a,_mj)),_mg);});});case 2:return new T0(2);case 3:return new F(function(){return _lf(B(A1(_mg,_mh.a)),new T(function(){return B(_me(_mh.b,_mg));}));});break;default:var _mk=function(_ml){var _mm=E(_ml);if(!_mm._){return __Z;}else{var _mn=E(_mm.a);return new F(function(){return _hq(B(_l5(B(A1(_mg,_mn.a)),_mn.b)),new T(function(){return B(_mk(_mm.b));},1));});}},_mo=B(_mk(_mh.a));return (_mo._==0)?new T0(2):new T1(4,_mo);}},_mp=function(_mq,_mr){var _ms=E(_mq);if(!_ms){return new F(function(){return A1(_mr,_h9);});}else{var _mt=new T(function(){return B(_mp(_ms-1|0,_mr));});return new T1(0,function(_mu){return E(_mt);});}},_mv=function(_mw,_mx,_my){var _mz=new T(function(){return B(A1(_mw,_jV));}),_mA=function(_mB,_mC,_mD,_mE){while(1){var _mF=B((function(_mG,_mH,_mI,_mJ){var _mK=E(_mG);switch(_mK._){case 0:var _mL=E(_mH);if(!_mL._){return new F(function(){return A1(_mx,_mJ);});}else{var _mM=_mI+1|0,_mN=_mJ;_mB=B(A1(_mK.a,_mL.a));_mC=_mL.b;_mD=_mM;_mE=_mN;return __continue;}break;case 1:var _mO=B(A1(_mK.a,_mH)),_mP=_mH,_mM=_mI,_mN=_mJ;_mB=_mO;_mC=_mP;_mD=_mM;_mE=_mN;return __continue;case 2:return new F(function(){return A1(_mx,_mJ);});break;case 3:var _mQ=new T(function(){return B(_me(_mK,_mJ));});return new F(function(){return _mp(_mI,function(_mR){return E(_mQ);});});break;default:return new F(function(){return _me(_mK,_mJ);});}})(_mB,_mC,_mD,_mE));if(_mF!=__continue){return _mF;}}};return function(_mS){return new F(function(){return _mA(_mz,_mS,0,_my);});};},_mT=function(_mU){return new F(function(){return A1(_mU,_1);});},_mV=function(_mW,_mX){var _mY=function(_mZ){var _n0=E(_mZ);if(!_n0._){return E(_mT);}else{var _n1=_n0.a;if(!B(A1(_mW,_n1))){return E(_mT);}else{var _n2=new T(function(){return B(_mY(_n0.b));}),_n3=function(_n4){var _n5=new T(function(){return B(A1(_n2,function(_n6){return new F(function(){return A1(_n4,new T2(1,_n1,_n6));});}));});return new T1(0,function(_n7){return E(_n5);});};return E(_n3);}}};return function(_n8){return new F(function(){return A2(_mY,_n8,_mX);});};},_n9=new T0(6),_na=function(_nb){return E(_nb);},_nc=new T(function(){return B(unCStr("valDig: Bad base"));}),_nd=new T(function(){return B(err(_nc));}),_ne=function(_nf,_ng){var _nh=function(_ni,_nj){var _nk=E(_ni);if(!_nk._){var _nl=new T(function(){return B(A1(_nj,_1));});return function(_nm){return new F(function(){return A1(_nm,_nl);});};}else{var _nn=E(_nk.a),_no=function(_np){var _nq=new T(function(){return B(_nh(_nk.b,function(_nr){return new F(function(){return A1(_nj,new T2(1,_np,_nr));});}));}),_ns=function(_nt){var _nu=new T(function(){return B(A1(_nq,_nt));});return new T1(0,function(_nv){return E(_nu);});};return E(_ns);};switch(E(_nf)){case 8:if(48>_nn){var _nw=new T(function(){return B(A1(_nj,_1));});return function(_nx){return new F(function(){return A1(_nx,_nw);});};}else{if(_nn>55){var _ny=new T(function(){return B(A1(_nj,_1));});return function(_nz){return new F(function(){return A1(_nz,_ny);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 10:if(48>_nn){var _nA=new T(function(){return B(A1(_nj,_1));});return function(_nB){return new F(function(){return A1(_nB,_nA);});};}else{if(_nn>57){var _nC=new T(function(){return B(A1(_nj,_1));});return function(_nD){return new F(function(){return A1(_nD,_nC);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 16:if(48>_nn){if(97>_nn){if(65>_nn){var _nE=new T(function(){return B(A1(_nj,_1));});return function(_nF){return new F(function(){return A1(_nF,_nE);});};}else{if(_nn>70){var _nG=new T(function(){return B(A1(_nj,_1));});return function(_nH){return new F(function(){return A1(_nH,_nG);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nI=new T(function(){return B(A1(_nj,_1));});return function(_nJ){return new F(function(){return A1(_nJ,_nI);});};}else{if(_nn>70){var _nK=new T(function(){return B(A1(_nj,_1));});return function(_nL){return new F(function(){return A1(_nL,_nK);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{if(_nn>57){if(97>_nn){if(65>_nn){var _nM=new T(function(){return B(A1(_nj,_1));});return function(_nN){return new F(function(){return A1(_nN,_nM);});};}else{if(_nn>70){var _nO=new T(function(){return B(A1(_nj,_1));});return function(_nP){return new F(function(){return A1(_nP,_nO);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nQ=new T(function(){return B(A1(_nj,_1));});return function(_nR){return new F(function(){return A1(_nR,_nQ);});};}else{if(_nn>70){var _nS=new T(function(){return B(A1(_nj,_1));});return function(_nT){return new F(function(){return A1(_nT,_nS);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{return new F(function(){return _no(_nn-48|0);});}}break;default:return E(_nd);}}},_nU=function(_nV){var _nW=E(_nV);if(!_nW._){return new T0(2);}else{return new F(function(){return A1(_ng,_nW);});}};return function(_nX){return new F(function(){return A3(_nh,_nX,_na,_nU);});};},_nY=16,_nZ=8,_o0=function(_o1){var _o2=function(_o3){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nZ,_o3)));});},_o4=function(_o5){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nY,_o5)));});},_o6=function(_o7){switch(E(_o7)){case 79:return new T1(1,B(_ne(_nZ,_o2)));case 88:return new T1(1,B(_ne(_nY,_o4)));case 111:return new T1(1,B(_ne(_nZ,_o2)));case 120:return new T1(1,B(_ne(_nY,_o4)));default:return new T0(2);}};return function(_o8){return (E(_o8)==48)?E(new T1(0,_o6)):new T0(2);};},_o9=function(_oa){return new T1(0,B(_o0(_oa)));},_ob=__Z,_oc=function(_od){return new F(function(){return A1(_od,_ob);});},_oe=function(_of){return new F(function(){return A1(_of,_ob);});},_og=10,_oh=new T1(0,1),_oi=new T1(0,2147483647),_oj=function(_ok,_ol){while(1){var _om=E(_ok);if(!_om._){var _on=_om.a,_oo=E(_ol);if(!_oo._){var _op=_oo.a,_oq=addC(_on,_op);if(!E(_oq.b)){return new T1(0,_oq.a);}else{_ok=new T1(1,I_fromInt(_on));_ol=new T1(1,I_fromInt(_op));continue;}}else{_ok=new T1(1,I_fromInt(_on));_ol=_oo;continue;}}else{var _or=E(_ol);if(!_or._){_ok=_om;_ol=new T1(1,I_fromInt(_or.a));continue;}else{return new T1(1,I_add(_om.a,_or.a));}}}},_os=new T(function(){return B(_oj(_oi,_oh));}),_ot=function(_ou){var _ov=E(_ou);if(!_ov._){var _ow=E(_ov.a);return (_ow==( -2147483648))?E(_os):new T1(0, -_ow);}else{return new T1(1,I_negate(_ov.a));}},_ox=new T1(0,10),_oy=function(_oz,_oA){while(1){var _oB=E(_oz);if(!_oB._){return E(_oA);}else{var _oC=_oA+1|0;_oz=_oB.b;_oA=_oC;continue;}}},_oD=function(_oE,_oF){var _oG=E(_oF);return (_oG._==0)?__Z:new T2(1,new T(function(){return B(A1(_oE,_oG.a));}),new T(function(){return B(_oD(_oE,_oG.b));}));},_oH=function(_oI){return new T1(0,_oI);},_oJ=function(_oK){return new F(function(){return _oH(E(_oK));});},_oL=new T(function(){return B(unCStr("this should not happen"));}),_oM=new T(function(){return B(err(_oL));}),_oN=function(_oO,_oP){while(1){var _oQ=E(_oO);if(!_oQ._){var _oR=_oQ.a,_oS=E(_oP);if(!_oS._){var _oT=_oS.a;if(!(imul(_oR,_oT)|0)){return new T1(0,imul(_oR,_oT)|0);}else{_oO=new T1(1,I_fromInt(_oR));_oP=new T1(1,I_fromInt(_oT));continue;}}else{_oO=new T1(1,I_fromInt(_oR));_oP=_oS;continue;}}else{var _oU=E(_oP);if(!_oU._){_oO=_oQ;_oP=new T1(1,I_fromInt(_oU.a));continue;}else{return new T1(1,I_mul(_oQ.a,_oU.a));}}}},_oV=function(_oW,_oX){var _oY=E(_oX);if(!_oY._){return __Z;}else{var _oZ=E(_oY.b);return (_oZ._==0)?E(_oM):new T2(1,B(_oj(B(_oN(_oY.a,_oW)),_oZ.a)),new T(function(){return B(_oV(_oW,_oZ.b));}));}},_p0=new T1(0,0),_p1=function(_p2,_p3,_p4){while(1){var _p5=B((function(_p6,_p7,_p8){var _p9=E(_p8);if(!_p9._){return E(_p0);}else{if(!E(_p9.b)._){return E(_p9.a);}else{var _pa=E(_p7);if(_pa<=40){var _pb=function(_pc,_pd){while(1){var _pe=E(_pd);if(!_pe._){return E(_pc);}else{var _pf=B(_oj(B(_oN(_pc,_p6)),_pe.a));_pc=_pf;_pd=_pe.b;continue;}}};return new F(function(){return _pb(_p0,_p9);});}else{var _pg=B(_oN(_p6,_p6));if(!(_pa%2)){var _ph=B(_oV(_p6,_p9));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}else{var _ph=B(_oV(_p6,new T2(1,_p0,_p9)));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}}}}})(_p2,_p3,_p4));if(_p5!=__continue){return _p5;}}},_pi=function(_pj,_pk){return new F(function(){return _p1(_pj,new T(function(){return B(_oy(_pk,0));},1),B(_oD(_oJ,_pk)));});},_pl=function(_pm){var _pn=new T(function(){var _po=new T(function(){var _pp=function(_pq){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pq));})));});};return new T1(1,B(_ne(_og,_pp)));}),_pr=function(_ps){if(E(_ps)==43){var _pt=function(_pu){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pu));})));});};return new T1(1,B(_ne(_og,_pt)));}else{return new T0(2);}},_pv=function(_pw){if(E(_pw)==45){var _px=function(_py){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_ot(B(_pi(_ox,_py))));})));});};return new T1(1,B(_ne(_og,_px)));}else{return new T0(2);}};return B(_lf(B(_lf(new T1(0,_pv),new T1(0,_pr))),_po));});return new F(function(){return _lf(new T1(0,function(_pz){return (E(_pz)==101)?E(_pn):new T0(2);}),new T1(0,function(_pA){return (E(_pA)==69)?E(_pn):new T0(2);}));});},_pB=function(_pC){var _pD=function(_pE){return new F(function(){return A1(_pC,new T1(1,_pE));});};return function(_pF){return (E(_pF)==46)?new T1(1,B(_ne(_og,_pD))):new T0(2);};},_pG=function(_pH){return new T1(0,B(_pB(_pH)));},_pI=function(_pJ){var _pK=function(_pL){var _pM=function(_pN){return new T1(1,B(_mv(_pl,_oc,function(_pO){return new F(function(){return A1(_pJ,new T1(5,new T3(1,_pL,_pN,_pO)));});})));};return new T1(1,B(_mv(_pG,_oe,_pM)));};return new F(function(){return _ne(_og,_pK);});},_pP=function(_pQ){return new T1(1,B(_pI(_pQ)));},_pR=function(_pS){return E(E(_pS).a);},_pT=function(_pU,_pV,_pW){while(1){var _pX=E(_pW);if(!_pX._){return false;}else{if(!B(A3(_pR,_pU,_pV,_pX.a))){_pW=_pX.b;continue;}else{return true;}}}},_pY=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_pZ=function(_q0){return new F(function(){return _pT(_m4,_q0,_pY);});},_q1=false,_q2=true,_q3=function(_q4){var _q5=new T(function(){return B(A1(_q4,_nZ));}),_q6=new T(function(){return B(A1(_q4,_nY));});return function(_q7){switch(E(_q7)){case 79:return E(_q5);case 88:return E(_q6);case 111:return E(_q5);case 120:return E(_q6);default:return new T0(2);}};},_q8=function(_q9){return new T1(0,B(_q3(_q9)));},_qa=function(_qb){return new F(function(){return A1(_qb,_og);});},_qc=function(_qd){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_hA(9,_qd,_1));}))));});},_qe=function(_qf){var _qg=E(_qf);if(!_qg._){return E(_qg.a);}else{return new F(function(){return I_toInt(_qg.a);});}},_qh=function(_qi,_qj){var _qk=E(_qi);if(!_qk._){var _ql=_qk.a,_qm=E(_qj);return (_qm._==0)?_ql<=_qm.a:I_compareInt(_qm.a,_ql)>=0;}else{var _qn=_qk.a,_qo=E(_qj);return (_qo._==0)?I_compareInt(_qn,_qo.a)<=0:I_compare(_qn,_qo.a)<=0;}},_qp=function(_qq){return new T0(2);},_qr=function(_qs){var _qt=E(_qs);if(!_qt._){return E(_qp);}else{var _qu=_qt.a,_qv=E(_qt.b);if(!_qv._){return E(_qu);}else{var _qw=new T(function(){return B(_qr(_qv));}),_qx=function(_qy){return new F(function(){return _lf(B(A1(_qu,_qy)),new T(function(){return B(A1(_qw,_qy));}));});};return E(_qx);}}},_qz=function(_qA,_qB){var _qC=function(_qD,_qE,_qF){var _qG=E(_qD);if(!_qG._){return new F(function(){return A1(_qF,_qA);});}else{var _qH=E(_qE);if(!_qH._){return new T0(2);}else{if(E(_qG.a)!=E(_qH.a)){return new T0(2);}else{var _qI=new T(function(){return B(_qC(_qG.b,_qH.b,_qF));});return new T1(0,function(_qJ){return E(_qI);});}}}};return function(_qK){return new F(function(){return _qC(_qA,_qK,_qB);});};},_qL=new T(function(){return B(unCStr("SO"));}),_qM=14,_qN=function(_qO){var _qP=new T(function(){return B(A1(_qO,_qM));});return new T1(1,B(_qz(_qL,function(_qQ){return E(_qP);})));},_qR=new T(function(){return B(unCStr("SOH"));}),_qS=1,_qT=function(_qU){var _qV=new T(function(){return B(A1(_qU,_qS));});return new T1(1,B(_qz(_qR,function(_qW){return E(_qV);})));},_qX=function(_qY){return new T1(1,B(_mv(_qT,_qN,_qY)));},_qZ=new T(function(){return B(unCStr("NUL"));}),_r0=0,_r1=function(_r2){var _r3=new T(function(){return B(A1(_r2,_r0));});return new T1(1,B(_qz(_qZ,function(_r4){return E(_r3);})));},_r5=new T(function(){return B(unCStr("STX"));}),_r6=2,_r7=function(_r8){var _r9=new T(function(){return B(A1(_r8,_r6));});return new T1(1,B(_qz(_r5,function(_ra){return E(_r9);})));},_rb=new T(function(){return B(unCStr("ETX"));}),_rc=3,_rd=function(_re){var _rf=new T(function(){return B(A1(_re,_rc));});return new T1(1,B(_qz(_rb,function(_rg){return E(_rf);})));},_rh=new T(function(){return B(unCStr("EOT"));}),_ri=4,_rj=function(_rk){var _rl=new T(function(){return B(A1(_rk,_ri));});return new T1(1,B(_qz(_rh,function(_rm){return E(_rl);})));},_rn=new T(function(){return B(unCStr("ENQ"));}),_ro=5,_rp=function(_rq){var _rr=new T(function(){return B(A1(_rq,_ro));});return new T1(1,B(_qz(_rn,function(_rs){return E(_rr);})));},_rt=new T(function(){return B(unCStr("ACK"));}),_ru=6,_rv=function(_rw){var _rx=new T(function(){return B(A1(_rw,_ru));});return new T1(1,B(_qz(_rt,function(_ry){return E(_rx);})));},_rz=new T(function(){return B(unCStr("BEL"));}),_rA=7,_rB=function(_rC){var _rD=new T(function(){return B(A1(_rC,_rA));});return new T1(1,B(_qz(_rz,function(_rE){return E(_rD);})));},_rF=new T(function(){return B(unCStr("BS"));}),_rG=8,_rH=function(_rI){var _rJ=new T(function(){return B(A1(_rI,_rG));});return new T1(1,B(_qz(_rF,function(_rK){return E(_rJ);})));},_rL=new T(function(){return B(unCStr("HT"));}),_rM=9,_rN=function(_rO){var _rP=new T(function(){return B(A1(_rO,_rM));});return new T1(1,B(_qz(_rL,function(_rQ){return E(_rP);})));},_rR=new T(function(){return B(unCStr("LF"));}),_rS=10,_rT=function(_rU){var _rV=new T(function(){return B(A1(_rU,_rS));});return new T1(1,B(_qz(_rR,function(_rW){return E(_rV);})));},_rX=new T(function(){return B(unCStr("VT"));}),_rY=11,_rZ=function(_s0){var _s1=new T(function(){return B(A1(_s0,_rY));});return new T1(1,B(_qz(_rX,function(_s2){return E(_s1);})));},_s3=new T(function(){return B(unCStr("FF"));}),_s4=12,_s5=function(_s6){var _s7=new T(function(){return B(A1(_s6,_s4));});return new T1(1,B(_qz(_s3,function(_s8){return E(_s7);})));},_s9=new T(function(){return B(unCStr("CR"));}),_sa=13,_sb=function(_sc){var _sd=new T(function(){return B(A1(_sc,_sa));});return new T1(1,B(_qz(_s9,function(_se){return E(_sd);})));},_sf=new T(function(){return B(unCStr("SI"));}),_sg=15,_sh=function(_si){var _sj=new T(function(){return B(A1(_si,_sg));});return new T1(1,B(_qz(_sf,function(_sk){return E(_sj);})));},_sl=new T(function(){return B(unCStr("DLE"));}),_sm=16,_sn=function(_so){var _sp=new T(function(){return B(A1(_so,_sm));});return new T1(1,B(_qz(_sl,function(_sq){return E(_sp);})));},_sr=new T(function(){return B(unCStr("DC1"));}),_ss=17,_st=function(_su){var _sv=new T(function(){return B(A1(_su,_ss));});return new T1(1,B(_qz(_sr,function(_sw){return E(_sv);})));},_sx=new T(function(){return B(unCStr("DC2"));}),_sy=18,_sz=function(_sA){var _sB=new T(function(){return B(A1(_sA,_sy));});return new T1(1,B(_qz(_sx,function(_sC){return E(_sB);})));},_sD=new T(function(){return B(unCStr("DC3"));}),_sE=19,_sF=function(_sG){var _sH=new T(function(){return B(A1(_sG,_sE));});return new T1(1,B(_qz(_sD,function(_sI){return E(_sH);})));},_sJ=new T(function(){return B(unCStr("DC4"));}),_sK=20,_sL=function(_sM){var _sN=new T(function(){return B(A1(_sM,_sK));});return new T1(1,B(_qz(_sJ,function(_sO){return E(_sN);})));},_sP=new T(function(){return B(unCStr("NAK"));}),_sQ=21,_sR=function(_sS){var _sT=new T(function(){return B(A1(_sS,_sQ));});return new T1(1,B(_qz(_sP,function(_sU){return E(_sT);})));},_sV=new T(function(){return B(unCStr("SYN"));}),_sW=22,_sX=function(_sY){var _sZ=new T(function(){return B(A1(_sY,_sW));});return new T1(1,B(_qz(_sV,function(_t0){return E(_sZ);})));},_t1=new T(function(){return B(unCStr("ETB"));}),_t2=23,_t3=function(_t4){var _t5=new T(function(){return B(A1(_t4,_t2));});return new T1(1,B(_qz(_t1,function(_t6){return E(_t5);})));},_t7=new T(function(){return B(unCStr("CAN"));}),_t8=24,_t9=function(_ta){var _tb=new T(function(){return B(A1(_ta,_t8));});return new T1(1,B(_qz(_t7,function(_tc){return E(_tb);})));},_td=new T(function(){return B(unCStr("EM"));}),_te=25,_tf=function(_tg){var _th=new T(function(){return B(A1(_tg,_te));});return new T1(1,B(_qz(_td,function(_ti){return E(_th);})));},_tj=new T(function(){return B(unCStr("SUB"));}),_tk=26,_tl=function(_tm){var _tn=new T(function(){return B(A1(_tm,_tk));});return new T1(1,B(_qz(_tj,function(_to){return E(_tn);})));},_tp=new T(function(){return B(unCStr("ESC"));}),_tq=27,_tr=function(_ts){var _tt=new T(function(){return B(A1(_ts,_tq));});return new T1(1,B(_qz(_tp,function(_tu){return E(_tt);})));},_tv=new T(function(){return B(unCStr("FS"));}),_tw=28,_tx=function(_ty){var _tz=new T(function(){return B(A1(_ty,_tw));});return new T1(1,B(_qz(_tv,function(_tA){return E(_tz);})));},_tB=new T(function(){return B(unCStr("GS"));}),_tC=29,_tD=function(_tE){var _tF=new T(function(){return B(A1(_tE,_tC));});return new T1(1,B(_qz(_tB,function(_tG){return E(_tF);})));},_tH=new T(function(){return B(unCStr("RS"));}),_tI=30,_tJ=function(_tK){var _tL=new T(function(){return B(A1(_tK,_tI));});return new T1(1,B(_qz(_tH,function(_tM){return E(_tL);})));},_tN=new T(function(){return B(unCStr("US"));}),_tO=31,_tP=function(_tQ){var _tR=new T(function(){return B(A1(_tQ,_tO));});return new T1(1,B(_qz(_tN,function(_tS){return E(_tR);})));},_tT=new T(function(){return B(unCStr("SP"));}),_tU=32,_tV=function(_tW){var _tX=new T(function(){return B(A1(_tW,_tU));});return new T1(1,B(_qz(_tT,function(_tY){return E(_tX);})));},_tZ=new T(function(){return B(unCStr("DEL"));}),_u0=127,_u1=function(_u2){var _u3=new T(function(){return B(A1(_u2,_u0));});return new T1(1,B(_qz(_tZ,function(_u4){return E(_u3);})));},_u5=new T2(1,_u1,_1),_u6=new T2(1,_tV,_u5),_u7=new T2(1,_tP,_u6),_u8=new T2(1,_tJ,_u7),_u9=new T2(1,_tD,_u8),_ua=new T2(1,_tx,_u9),_ub=new T2(1,_tr,_ua),_uc=new T2(1,_tl,_ub),_ud=new T2(1,_tf,_uc),_ue=new T2(1,_t9,_ud),_uf=new T2(1,_t3,_ue),_ug=new T2(1,_sX,_uf),_uh=new T2(1,_sR,_ug),_ui=new T2(1,_sL,_uh),_uj=new T2(1,_sF,_ui),_uk=new T2(1,_sz,_uj),_ul=new T2(1,_st,_uk),_um=new T2(1,_sn,_ul),_un=new T2(1,_sh,_um),_uo=new T2(1,_sb,_un),_up=new T2(1,_s5,_uo),_uq=new T2(1,_rZ,_up),_ur=new T2(1,_rT,_uq),_us=new T2(1,_rN,_ur),_ut=new T2(1,_rH,_us),_uu=new T2(1,_rB,_ut),_uv=new T2(1,_rv,_uu),_uw=new T2(1,_rp,_uv),_ux=new T2(1,_rj,_uw),_uy=new T2(1,_rd,_ux),_uz=new T2(1,_r7,_uy),_uA=new T2(1,_r1,_uz),_uB=new T2(1,_qX,_uA),_uC=new T(function(){return B(_qr(_uB));}),_uD=34,_uE=new T1(0,1114111),_uF=92,_uG=39,_uH=function(_uI){var _uJ=new T(function(){return B(A1(_uI,_rA));}),_uK=new T(function(){return B(A1(_uI,_rG));}),_uL=new T(function(){return B(A1(_uI,_rM));}),_uM=new T(function(){return B(A1(_uI,_rS));}),_uN=new T(function(){return B(A1(_uI,_rY));}),_uO=new T(function(){return B(A1(_uI,_s4));}),_uP=new T(function(){return B(A1(_uI,_sa));}),_uQ=new T(function(){return B(A1(_uI,_uF));}),_uR=new T(function(){return B(A1(_uI,_uG));}),_uS=new T(function(){return B(A1(_uI,_uD));}),_uT=new T(function(){var _uU=function(_uV){var _uW=new T(function(){return B(_oH(E(_uV)));}),_uX=function(_uY){var _uZ=B(_pi(_uW,_uY));if(!B(_qh(_uZ,_uE))){return new T0(2);}else{return new F(function(){return A1(_uI,new T(function(){var _v0=B(_qe(_uZ));if(_v0>>>0>1114111){return B(_qc(_v0));}else{return _v0;}}));});}};return new T1(1,B(_ne(_uV,_uX)));},_v1=new T(function(){var _v2=new T(function(){return B(A1(_uI,_tO));}),_v3=new T(function(){return B(A1(_uI,_tI));}),_v4=new T(function(){return B(A1(_uI,_tC));}),_v5=new T(function(){return B(A1(_uI,_tw));}),_v6=new T(function(){return B(A1(_uI,_tq));}),_v7=new T(function(){return B(A1(_uI,_tk));}),_v8=new T(function(){return B(A1(_uI,_te));}),_v9=new T(function(){return B(A1(_uI,_t8));}),_va=new T(function(){return B(A1(_uI,_t2));}),_vb=new T(function(){return B(A1(_uI,_sW));}),_vc=new T(function(){return B(A1(_uI,_sQ));}),_vd=new T(function(){return B(A1(_uI,_sK));}),_ve=new T(function(){return B(A1(_uI,_sE));}),_vf=new T(function(){return B(A1(_uI,_sy));}),_vg=new T(function(){return B(A1(_uI,_ss));}),_vh=new T(function(){return B(A1(_uI,_sm));}),_vi=new T(function(){return B(A1(_uI,_sg));}),_vj=new T(function(){return B(A1(_uI,_qM));}),_vk=new T(function(){return B(A1(_uI,_ru));}),_vl=new T(function(){return B(A1(_uI,_ro));}),_vm=new T(function(){return B(A1(_uI,_ri));}),_vn=new T(function(){return B(A1(_uI,_rc));}),_vo=new T(function(){return B(A1(_uI,_r6));}),_vp=new T(function(){return B(A1(_uI,_qS));}),_vq=new T(function(){return B(A1(_uI,_r0));}),_vr=function(_vs){switch(E(_vs)){case 64:return E(_vq);case 65:return E(_vp);case 66:return E(_vo);case 67:return E(_vn);case 68:return E(_vm);case 69:return E(_vl);case 70:return E(_vk);case 71:return E(_uJ);case 72:return E(_uK);case 73:return E(_uL);case 74:return E(_uM);case 75:return E(_uN);case 76:return E(_uO);case 77:return E(_uP);case 78:return E(_vj);case 79:return E(_vi);case 80:return E(_vh);case 81:return E(_vg);case 82:return E(_vf);case 83:return E(_ve);case 84:return E(_vd);case 85:return E(_vc);case 86:return E(_vb);case 87:return E(_va);case 88:return E(_v9);case 89:return E(_v8);case 90:return E(_v7);case 91:return E(_v6);case 92:return E(_v5);case 93:return E(_v4);case 94:return E(_v3);case 95:return E(_v2);default:return new T0(2);}};return B(_lf(new T1(0,function(_vt){return (E(_vt)==94)?E(new T1(0,_vr)):new T0(2);}),new T(function(){return B(A1(_uC,_uI));})));});return B(_lf(new T1(1,B(_mv(_q8,_qa,_uU))),_v1));});return new F(function(){return _lf(new T1(0,function(_vu){switch(E(_vu)){case 34:return E(_uS);case 39:return E(_uR);case 92:return E(_uQ);case 97:return E(_uJ);case 98:return E(_uK);case 102:return E(_uO);case 110:return E(_uM);case 114:return E(_uP);case 116:return E(_uL);case 118:return E(_uN);default:return new T0(2);}}),_uT);});},_vv=function(_vw){return new F(function(){return A1(_vw,_h9);});},_vx=function(_vy){var _vz=E(_vy);if(!_vz._){return E(_vv);}else{var _vA=E(_vz.a),_vB=_vA>>>0,_vC=new T(function(){return B(_vx(_vz.b));});if(_vB>887){var _vD=u_iswspace(_vA);if(!E(_vD)){return E(_vv);}else{var _vE=function(_vF){var _vG=new T(function(){return B(A1(_vC,_vF));});return new T1(0,function(_vH){return E(_vG);});};return E(_vE);}}else{var _vI=E(_vB);if(_vI==32){var _vJ=function(_vK){var _vL=new T(function(){return B(A1(_vC,_vK));});return new T1(0,function(_vM){return E(_vL);});};return E(_vJ);}else{if(_vI-9>>>0>4){if(E(_vI)==160){var _vN=function(_vO){var _vP=new T(function(){return B(A1(_vC,_vO));});return new T1(0,function(_vQ){return E(_vP);});};return E(_vN);}else{return E(_vv);}}else{var _vR=function(_vS){var _vT=new T(function(){return B(A1(_vC,_vS));});return new T1(0,function(_vU){return E(_vT);});};return E(_vR);}}}}},_vV=function(_vW){var _vX=new T(function(){return B(_vV(_vW));}),_vY=function(_vZ){return (E(_vZ)==92)?E(_vX):new T0(2);},_w0=function(_w1){return E(new T1(0,_vY));},_w2=new T1(1,function(_w3){return new F(function(){return A2(_vx,_w3,_w0);});}),_w4=new T(function(){return B(_uH(function(_w5){return new F(function(){return A1(_vW,new T2(0,_w5,_q2));});}));}),_w6=function(_w7){var _w8=E(_w7);if(_w8==38){return E(_vX);}else{var _w9=_w8>>>0;if(_w9>887){var _wa=u_iswspace(_w8);return (E(_wa)==0)?new T0(2):E(_w2);}else{var _wb=E(_w9);return (_wb==32)?E(_w2):(_wb-9>>>0>4)?(E(_wb)==160)?E(_w2):new T0(2):E(_w2);}}};return new F(function(){return _lf(new T1(0,function(_wc){return (E(_wc)==92)?E(new T1(0,_w6)):new T0(2);}),new T1(0,function(_wd){var _we=E(_wd);if(E(_we)==92){return E(_w4);}else{return new F(function(){return A1(_vW,new T2(0,_we,_q1));});}}));});},_wf=function(_wg,_wh){var _wi=new T(function(){return B(A1(_wh,new T1(1,new T(function(){return B(A1(_wg,_1));}))));}),_wj=function(_wk){var _wl=E(_wk),_wm=E(_wl.a);if(E(_wm)==34){if(!E(_wl.b)){return E(_wi);}else{return new F(function(){return _wf(function(_wn){return new F(function(){return A1(_wg,new T2(1,_wm,_wn));});},_wh);});}}else{return new F(function(){return _wf(function(_wo){return new F(function(){return A1(_wg,new T2(1,_wm,_wo));});},_wh);});}};return new F(function(){return _vV(_wj);});},_wp=new T(function(){return B(unCStr("_\'"));}),_wq=function(_wr){var _ws=u_iswalnum(_wr);if(!E(_ws)){return new F(function(){return _pT(_m4,_wr,_wp);});}else{return true;}},_wt=function(_wu){return new F(function(){return _wq(E(_wu));});},_wv=new T(function(){return B(unCStr(",;()[]{}`"));}),_ww=new T(function(){return B(unCStr("=>"));}),_wx=new T2(1,_ww,_1),_wy=new T(function(){return B(unCStr("~"));}),_wz=new T2(1,_wy,_wx),_wA=new T(function(){return B(unCStr("@"));}),_wB=new T2(1,_wA,_wz),_wC=new T(function(){return B(unCStr("->"));}),_wD=new T2(1,_wC,_wB),_wE=new T(function(){return B(unCStr("<-"));}),_wF=new T2(1,_wE,_wD),_wG=new T(function(){return B(unCStr("|"));}),_wH=new T2(1,_wG,_wF),_wI=new T(function(){return B(unCStr("\\"));}),_wJ=new T2(1,_wI,_wH),_wK=new T(function(){return B(unCStr("="));}),_wL=new T2(1,_wK,_wJ),_wM=new T(function(){return B(unCStr("::"));}),_wN=new T2(1,_wM,_wL),_wO=new T(function(){return B(unCStr(".."));}),_wP=new T2(1,_wO,_wN),_wQ=function(_wR){var _wS=new T(function(){return B(A1(_wR,_n9));}),_wT=new T(function(){var _wU=new T(function(){var _wV=function(_wW){var _wX=new T(function(){return B(A1(_wR,new T1(0,_wW)));});return new T1(0,function(_wY){return (E(_wY)==39)?E(_wX):new T0(2);});};return B(_uH(_wV));}),_wZ=function(_x0){var _x1=E(_x0);switch(E(_x1)){case 39:return new T0(2);case 92:return E(_wU);default:var _x2=new T(function(){return B(A1(_wR,new T1(0,_x1)));});return new T1(0,function(_x3){return (E(_x3)==39)?E(_x2):new T0(2);});}},_x4=new T(function(){var _x5=new T(function(){return B(_wf(_na,_wR));}),_x6=new T(function(){var _x7=new T(function(){var _x8=new T(function(){var _x9=function(_xa){var _xb=E(_xa),_xc=u_iswalpha(_xb);return (E(_xc)==0)?(E(_xb)==95)?new T1(1,B(_mV(_wt,function(_xd){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xd)));});}))):new T0(2):new T1(1,B(_mV(_wt,function(_xe){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xe)));});})));};return B(_lf(new T1(0,_x9),new T(function(){return new T1(1,B(_mv(_o9,_pP,_wR)));})));}),_xf=function(_xg){return (!B(_pT(_m4,_xg,_pY)))?new T0(2):new T1(1,B(_mV(_pZ,function(_xh){var _xi=new T2(1,_xg,_xh);if(!B(_pT(_md,_xi,_wP))){return new F(function(){return A1(_wR,new T1(4,_xi));});}else{return new F(function(){return A1(_wR,new T1(2,_xi));});}})));};return B(_lf(new T1(0,_xf),_x8));});return B(_lf(new T1(0,function(_xj){if(!B(_pT(_m4,_xj,_wv))){return new T0(2);}else{return new F(function(){return A1(_wR,new T1(2,new T2(1,_xj,_1)));});}}),_x7));});return B(_lf(new T1(0,function(_xk){return (E(_xk)==34)?E(_x5):new T0(2);}),_x6));});return B(_lf(new T1(0,function(_xl){return (E(_xl)==39)?E(new T1(0,_wZ)):new T0(2);}),_x4));});return new F(function(){return _lf(new T1(1,function(_xm){return (E(_xm)._==0)?E(_wS):new T0(2);}),_wT);});},_xn=0,_xo=function(_xp,_xq){var _xr=new T(function(){var _xs=new T(function(){var _xt=function(_xu){var _xv=new T(function(){var _xw=new T(function(){return B(A1(_xq,_xu));});return B(_wQ(function(_xx){var _xy=E(_xx);return (_xy._==2)?(!B(_lT(_xy.a,_lS)))?new T0(2):E(_xw):new T0(2);}));}),_xz=function(_xA){return E(_xv);};return new T1(1,function(_xB){return new F(function(){return A2(_vx,_xB,_xz);});});};return B(A2(_xp,_xn,_xt));});return B(_wQ(function(_xC){var _xD=E(_xC);return (_xD._==2)?(!B(_lT(_xD.a,_lR)))?new T0(2):E(_xs):new T0(2);}));}),_xE=function(_xF){return E(_xr);};return function(_xG){return new F(function(){return A2(_vx,_xG,_xE);});};},_xH=function(_xI,_xJ){var _xK=function(_xL){var _xM=new T(function(){return B(A1(_xI,_xL));}),_xN=function(_xO){return new F(function(){return _lf(B(A1(_xM,_xO)),new T(function(){return new T1(1,B(_xo(_xK,_xO)));}));});};return E(_xN);},_xP=new T(function(){return B(A1(_xI,_xJ));}),_xQ=function(_xR){return new F(function(){return _lf(B(A1(_xP,_xR)),new T(function(){return new T1(1,B(_xo(_xK,_xR)));}));});};return E(_xQ);},_xS=function(_xT,_xU){var _xV=function(_xW,_xX){var _xY=function(_xZ){return new F(function(){return A1(_xX,new T(function(){return  -E(_xZ);}));});},_y0=new T(function(){return B(_wQ(function(_y1){return new F(function(){return A3(_xT,_y1,_xW,_xY);});}));}),_y2=function(_y3){return E(_y0);},_y4=function(_y5){return new F(function(){return A2(_vx,_y5,_y2);});},_y6=new T(function(){return B(_wQ(function(_y7){var _y8=E(_y7);if(_y8._==4){var _y9=E(_y8.a);if(!_y9._){return new F(function(){return A3(_xT,_y8,_xW,_xX);});}else{if(E(_y9.a)==45){if(!E(_y9.b)._){return E(new T1(1,_y4));}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}));}),_ya=function(_yb){return E(_y6);};return new T1(1,function(_yc){return new F(function(){return A2(_vx,_yc,_ya);});});};return new F(function(){return _xH(_xV,_xU);});},_yd=function(_ye){var _yf=E(_ye);if(!_yf._){var _yg=_yf.b,_yh=new T(function(){return B(_p1(new T(function(){return B(_oH(E(_yf.a)));}),new T(function(){return B(_oy(_yg,0));},1),B(_oD(_oJ,_yg))));});return new T1(1,_yh);}else{return (E(_yf.b)._==0)?(E(_yf.c)._==0)?new T1(1,new T(function(){return B(_pi(_ox,_yf.a));})):__Z:__Z;}},_yi=function(_yj,_yk){return new T0(2);},_yl=function(_ym){var _yn=E(_ym);if(_yn._==5){var _yo=B(_yd(_yn.a));if(!_yo._){return E(_yi);}else{var _yp=new T(function(){return B(_qe(_yo.a));});return function(_yq,_yr){return new F(function(){return A1(_yr,_yp);});};}}else{return E(_yi);}},_ys=function(_yt){return new F(function(){return _xS(_yl,_yt);});},_yu=new T(function(){return B(unCStr("["));}),_yv=function(_yw,_yx){var _yy=function(_yz,_yA){var _yB=new T(function(){return B(A1(_yA,_1));}),_yC=new T(function(){var _yD=function(_yE){return new F(function(){return _yy(_q2,function(_yF){return new F(function(){return A1(_yA,new T2(1,_yE,_yF));});});});};return B(A2(_yw,_xn,_yD));}),_yG=new T(function(){return B(_wQ(function(_yH){var _yI=E(_yH);if(_yI._==2){var _yJ=E(_yI.a);if(!_yJ._){return new T0(2);}else{var _yK=_yJ.b;switch(E(_yJ.a)){case 44:return (E(_yK)._==0)?(!E(_yz))?new T0(2):E(_yC):new T0(2);case 93:return (E(_yK)._==0)?E(_yB):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_yL=function(_yM){return E(_yG);};return new T1(1,function(_yN){return new F(function(){return A2(_vx,_yN,_yL);});});},_yO=function(_yP,_yQ){return new F(function(){return _yR(_yQ);});},_yR=function(_yS){var _yT=new T(function(){var _yU=new T(function(){var _yV=new T(function(){var _yW=function(_yX){return new F(function(){return _yy(_q2,function(_yY){return new F(function(){return A1(_yS,new T2(1,_yX,_yY));});});});};return B(A2(_yw,_xn,_yW));});return B(_lf(B(_yy(_q1,_yS)),_yV));});return B(_wQ(function(_yZ){var _z0=E(_yZ);return (_z0._==2)?(!B(_lT(_z0.a,_yu)))?new T0(2):E(_yU):new T0(2);}));}),_z1=function(_z2){return E(_yT);};return new F(function(){return _lf(new T1(1,function(_z3){return new F(function(){return A2(_vx,_z3,_z1);});}),new T(function(){return new T1(1,B(_xo(_yO,_yS)));}));});};return new F(function(){return _yR(_yx);});},_z4=function(_z5,_z6){return new F(function(){return _yv(_ys,_z6);});},_z7=new T(function(){return B(_yv(_ys,_jV));}),_z8=function(_yt){return new F(function(){return _l5(_z7,_yt);});},_z9=function(_za){var _zb=new T(function(){return B(A3(_xS,_yl,_za,_jV));});return function(_zc){return new F(function(){return _l5(_zb,_zc);});};},_zd=new T4(0,_z9,_z8,_ys,_z4),_ze=11,_zf=new T(function(){return B(unCStr("IdentChoice"));}),_zg=function(_zh,_zi){if(_zh>10){return new T0(2);}else{var _zj=new T(function(){var _zk=new T(function(){return B(A3(_xS,_yl,_ze,function(_zl){return new F(function(){return A1(_zi,_zl);});}));});return B(_wQ(function(_zm){var _zn=E(_zm);return (_zn._==3)?(!B(_lT(_zn.a,_zf)))?new T0(2):E(_zk):new T0(2);}));}),_zo=function(_zp){return E(_zj);};return new T1(1,function(_zq){return new F(function(){return A2(_vx,_zq,_zo);});});}},_zr=function(_zs,_zt){return new F(function(){return _zg(E(_zs),_zt);});},_zu=function(_zv){return new F(function(){return _xH(_zr,_zv);});},_zw=function(_zx,_zy){return new F(function(){return _yv(_zu,_zy);});},_zz=new T(function(){return B(_yv(_zu,_jV));}),_zA=function(_zv){return new F(function(){return _l5(_zz,_zv);});},_zB=function(_zC){var _zD=new T(function(){return B(A3(_xH,_zr,_zC,_jV));});return function(_zc){return new F(function(){return _l5(_zD,_zc);});};},_zE=new T4(0,_zB,_zA,_zu,_zw),_zF=new T(function(){return B(unCStr(","));}),_zG=function(_zH){return E(E(_zH).c);},_zI=function(_zJ,_zK,_zL){var _zM=new T(function(){return B(_zG(_zK));}),_zN=new T(function(){return B(A2(_zG,_zJ,_zL));}),_zO=function(_zP){var _zQ=function(_zR){var _zS=new T(function(){var _zT=new T(function(){return B(A2(_zM,_zL,function(_zU){return new F(function(){return A1(_zP,new T2(0,_zR,_zU));});}));});return B(_wQ(function(_zV){var _zW=E(_zV);return (_zW._==2)?(!B(_lT(_zW.a,_zF)))?new T0(2):E(_zT):new T0(2);}));}),_zX=function(_zY){return E(_zS);};return new T1(1,function(_zZ){return new F(function(){return A2(_vx,_zZ,_zX);});});};return new F(function(){return A1(_zN,_zQ);});};return E(_zO);},_A0=function(_A1,_A2,_A3){var _A4=function(_yt){return new F(function(){return _zI(_A1,_A2,_yt);});},_A5=function(_A6,_A7){return new F(function(){return _A8(_A7);});},_A8=function(_A9){return new F(function(){return _lf(new T1(1,B(_xo(_A4,_A9))),new T(function(){return new T1(1,B(_xo(_A5,_A9)));}));});};return new F(function(){return _A8(_A3);});},_Aa=function(_Ab,_Ac){return new F(function(){return _A0(_zE,_zd,_Ac);});},_Ad=new T(function(){return B(_yv(_Aa,_jV));}),_Ae=function(_zv){return new F(function(){return _l5(_Ad,_zv);});},_Af=new T(function(){return B(_A0(_zE,_zd,_jV));}),_Ag=function(_zv){return new F(function(){return _l5(_Af,_zv);});},_Ah=function(_Ai,_zv){return new F(function(){return _Ag(_zv);});},_Aj=function(_Ak,_Al){return new F(function(){return _yv(_Aa,_Al);});},_Am=new T4(0,_Ah,_Ae,_Aa,_Aj),_An=function(_Ao,_Ap){return new F(function(){return _A0(_Am,_zd,_Ap);});},_Aq=function(_Ar,_As){return new F(function(){return _yv(_An,_As);});},_At=new T(function(){return B(_yv(_Aq,_jV));}),_Au=function(_Av){return new F(function(){return _l5(_At,_Av);});},_Aw=function(_Ax){return new F(function(){return _yv(_Aq,_Ax);});},_Ay=function(_Az,_AA){return new F(function(){return _Aw(_AA);});},_AB=new T(function(){return B(_yv(_An,_jV));}),_AC=function(_Av){return new F(function(){return _l5(_AB,_Av);});},_AD=function(_AE,_Av){return new F(function(){return _AC(_Av);});},_AF=new T4(0,_AD,_Au,_Aq,_Ay),_AG=new T(function(){return B(unCStr("IdentPay"));}),_AH=function(_AI,_AJ){if(_AI>10){return new T0(2);}else{var _AK=new T(function(){var _AL=new T(function(){return B(A3(_xS,_yl,_ze,function(_AM){return new F(function(){return A1(_AJ,_AM);});}));});return B(_wQ(function(_AN){var _AO=E(_AN);return (_AO._==3)?(!B(_lT(_AO.a,_AG)))?new T0(2):E(_AL):new T0(2);}));}),_AP=function(_AQ){return E(_AK);};return new T1(1,function(_AR){return new F(function(){return A2(_vx,_AR,_AP);});});}},_AS=function(_AT,_AU){return new F(function(){return _AH(E(_AT),_AU);});},_AV=function(_zv){return new F(function(){return _xH(_AS,_zv);});},_AW=function(_AX,_AY){return new F(function(){return _yv(_AV,_AY);});},_AZ=new T(function(){return B(_yv(_AV,_jV));}),_B0=function(_zv){return new F(function(){return _l5(_AZ,_zv);});},_B1=function(_B2){var _B3=new T(function(){return B(A3(_xH,_AS,_B2,_jV));});return function(_zc){return new F(function(){return _l5(_B3,_zc);});};},_B4=new T4(0,_B1,_B0,_AV,_AW),_B5=function(_B6,_B7){return new F(function(){return _A0(_B4,_zd,_B7);});},_B8=new T(function(){return B(_yv(_B5,_jV));}),_B9=function(_zv){return new F(function(){return _l5(_B8,_zv);});},_Ba=new T(function(){return B(_A0(_B4,_zd,_jV));}),_Bb=function(_zv){return new F(function(){return _l5(_Ba,_zv);});},_Bc=function(_Bd,_zv){return new F(function(){return _Bb(_zv);});},_Be=function(_Bf,_Bg){return new F(function(){return _yv(_B5,_Bg);});},_Bh=new T4(0,_Bc,_B9,_B5,_Be),_Bi=function(_Bj,_Bk){return new F(function(){return _A0(_Bh,_zd,_Bk);});},_Bl=function(_Bm,_Bn){return new F(function(){return _yv(_Bi,_Bn);});},_Bo=new T(function(){return B(_yv(_Bl,_jV));}),_Bp=function(_Av){return new F(function(){return _l5(_Bo,_Av);});},_Bq=function(_Br){return new F(function(){return _yv(_Bl,_Br);});},_Bs=function(_Bt,_Bu){return new F(function(){return _Bq(_Bu);});},_Bv=new T(function(){return B(_yv(_Bi,_jV));}),_Bw=function(_Av){return new F(function(){return _l5(_Bv,_Av);});},_Bx=function(_By,_Av){return new F(function(){return _Bw(_Av);});},_Bz=new T4(0,_Bx,_Bp,_Bl,_Bs),_BA=new T(function(){return B(unCStr("IdentCC"));}),_BB=function(_BC,_BD){if(_BC>10){return new T0(2);}else{var _BE=new T(function(){var _BF=new T(function(){return B(A3(_xS,_yl,_ze,function(_BG){return new F(function(){return A1(_BD,_BG);});}));});return B(_wQ(function(_BH){var _BI=E(_BH);return (_BI._==3)?(!B(_lT(_BI.a,_BA)))?new T0(2):E(_BF):new T0(2);}));}),_BJ=function(_BK){return E(_BE);};return new T1(1,function(_BL){return new F(function(){return A2(_vx,_BL,_BJ);});});}},_BM=function(_BN,_BO){return new F(function(){return _BB(E(_BN),_BO);});},_BP=new T(function(){return B(unCStr("RC"));}),_BQ=function(_BR,_BS){if(_BR>10){return new T0(2);}else{var _BT=new T(function(){var _BU=new T(function(){var _BV=function(_BW){var _BX=function(_BY){return new F(function(){return A3(_xS,_yl,_ze,function(_BZ){return new F(function(){return A1(_BS,new T3(0,_BW,_BY,_BZ));});});});};return new F(function(){return A3(_xS,_yl,_ze,_BX);});};return B(A3(_xH,_BM,_ze,_BV));});return B(_wQ(function(_C0){var _C1=E(_C0);return (_C1._==3)?(!B(_lT(_C1.a,_BP)))?new T0(2):E(_BU):new T0(2);}));}),_C2=function(_C3){return E(_BT);};return new T1(1,function(_C4){return new F(function(){return A2(_vx,_C4,_C2);});});}},_C5=function(_C6,_C7){return new F(function(){return _BQ(E(_C6),_C7);});},_C8=function(_zv){return new F(function(){return _xH(_C5,_zv);});},_C9=function(_Ca,_Cb){return new F(function(){return _yv(_C8,_Cb);});},_Cc=new T(function(){return B(_yv(_C9,_jV));}),_Cd=function(_Av){return new F(function(){return _l5(_Cc,_Av);});},_Ce=new T(function(){return B(_yv(_C8,_jV));}),_Cf=function(_Av){return new F(function(){return _l5(_Ce,_Av);});},_Cg=function(_Ch,_Av){return new F(function(){return _Cf(_Av);});},_Ci=function(_Cj,_Ck){return new F(function(){return _yv(_C9,_Ck);});},_Cl=new T4(0,_Cg,_Cd,_C9,_Ci),_Cm=new T(function(){return B(unCStr("CC"));}),_Cn=function(_Co,_Cp){if(_Co>10){return new T0(2);}else{var _Cq=new T(function(){var _Cr=new T(function(){var _Cs=function(_Ct){var _Cu=function(_Cv){var _Cw=function(_Cx){return new F(function(){return A3(_xS,_yl,_ze,function(_Cy){return new F(function(){return A1(_Cp,new T4(0,_Ct,_Cv,_Cx,_Cy));});});});};return new F(function(){return A3(_xS,_yl,_ze,_Cw);});};return new F(function(){return A3(_xS,_yl,_ze,_Cu);});};return B(A3(_xH,_BM,_ze,_Cs));});return B(_wQ(function(_Cz){var _CA=E(_Cz);return (_CA._==3)?(!B(_lT(_CA.a,_Cm)))?new T0(2):E(_Cr):new T0(2);}));}),_CB=function(_CC){return E(_Cq);};return new T1(1,function(_CD){return new F(function(){return A2(_vx,_CD,_CB);});});}},_CE=function(_CF,_CG){return new F(function(){return _Cn(E(_CF),_CG);});},_CH=function(_zv){return new F(function(){return _xH(_CE,_zv);});},_CI=function(_CJ,_CK){return new F(function(){return _yv(_CH,_CK);});},_CL=new T(function(){return B(_yv(_CI,_jV));}),_CM=function(_Av){return new F(function(){return _l5(_CL,_Av);});},_CN=new T(function(){return B(_yv(_CH,_jV));}),_CO=function(_Av){return new F(function(){return _l5(_CN,_Av);});},_CP=function(_CQ,_Av){return new F(function(){return _CO(_Av);});},_CR=function(_CS,_CT){return new F(function(){return _yv(_CI,_CT);});},_CU=new T4(0,_CP,_CM,_CI,_CR),_CV=function(_CW,_CX,_CY,_CZ,_D0){var _D1=new T(function(){return B(_zI(_CW,_CX,_D0));}),_D2=new T(function(){return B(_zG(_CZ));}),_D3=function(_D4){var _D5=function(_D6){var _D7=E(_D6),_D8=new T(function(){var _D9=new T(function(){var _Da=function(_Db){var _Dc=new T(function(){var _Dd=new T(function(){return B(A2(_D2,_D0,function(_De){return new F(function(){return A1(_D4,new T4(0,_D7.a,_D7.b,_Db,_De));});}));});return B(_wQ(function(_Df){var _Dg=E(_Df);return (_Dg._==2)?(!B(_lT(_Dg.a,_zF)))?new T0(2):E(_Dd):new T0(2);}));}),_Dh=function(_Di){return E(_Dc);};return new T1(1,function(_Dj){return new F(function(){return A2(_vx,_Dj,_Dh);});});};return B(A3(_zG,_CY,_D0,_Da));});return B(_wQ(function(_Dk){var _Dl=E(_Dk);return (_Dl._==2)?(!B(_lT(_Dl.a,_zF)))?new T0(2):E(_D9):new T0(2);}));}),_Dm=function(_Dn){return E(_D8);};return new T1(1,function(_Do){return new F(function(){return A2(_vx,_Do,_Dm);});});};return new F(function(){return A1(_D1,_D5);});};return E(_D3);},_Dp=function(_Dq,_Dr,_Ds,_Dt,_Du){var _Dv=function(_yt){return new F(function(){return _CV(_Dq,_Dr,_Ds,_Dt,_yt);});},_Dw=function(_Dx,_Dy){return new F(function(){return _Dz(_Dy);});},_Dz=function(_DA){return new F(function(){return _lf(new T1(1,B(_xo(_Dv,_DA))),new T(function(){return new T1(1,B(_xo(_Dw,_DA)));}));});};return new F(function(){return _Dz(_Du);});},_DB=function(_DC){var _DD=function(_DE){return E(new T2(3,_DC,_jU));};return new T1(1,function(_DF){return new F(function(){return A2(_vx,_DF,_DD);});});},_DG=new T(function(){return B(_Dp(_CU,_Cl,_Bz,_AF,_DB));}),_DH=function(_DI,_DJ,_DK,_DL){var _DM=E(_DI);if(_DM==1){var _DN=E(_DL);if(!_DN._){return new T3(0,new T(function(){var _DO=E(_DJ);return new T5(0,1,E(_DO),_DK,E(_0),E(_0));}),_1,_1);}else{var _DP=E(_DJ);return (_DP<E(E(_DN.a).a))?new T3(0,new T5(0,1,E(_DP),_DK,E(_0),E(_0)),_DN,_1):new T3(0,new T5(0,1,E(_DP),_DK,E(_0),E(_0)),_1,_DN);}}else{var _DQ=B(_DH(_DM>>1,_DJ,_DK,_DL)),_DR=_DQ.a,_DS=_DQ.c,_DT=E(_DQ.b);if(!_DT._){return new T3(0,_DR,_1,_DS);}else{var _DU=E(_DT.a),_DV=_DU.a,_DW=_DU.b,_DX=E(_DT.b);if(!_DX._){return new T3(0,new T(function(){return B(_O(_DV,_DW,_DR));}),_1,_DS);}else{var _DY=E(_DX.a),_DZ=E(_DV),_E0=E(_DY.a);if(_DZ<_E0){var _E1=B(_DH(_DM>>1,_E0,_DY.b,_DX.b));return new T3(0,new T(function(){return B(_2h(_DZ,_DW,_DR,_E1.a));}),_E1.b,_E1.c);}else{return new T3(0,_DR,_1,_DT);}}}}},_E2=function(_E3,_E4,_E5){var _E6=E(_E5);if(!_E6._){var _E7=_E6.c,_E8=_E6.d,_E9=_E6.e,_Ea=E(_E6.b);if(_E3>=_Ea){if(_E3!=_Ea){return new F(function(){return _6(_Ea,_E7,_E8,B(_E2(_E3,_E4,_E9)));});}else{return new T5(0,_E6.a,E(_E3),_E4,E(_E8),E(_E9));}}else{return new F(function(){return _X(_Ea,_E7,B(_E2(_E3,_E4,_E8)),_E9);});}}else{return new T5(0,1,E(_E3),_E4,E(_0),E(_0));}},_Eb=function(_Ec,_Ed){while(1){var _Ee=E(_Ed);if(!_Ee._){return E(_Ec);}else{var _Ef=E(_Ee.a),_Eg=B(_E2(E(_Ef.a),_Ef.b,_Ec));_Ec=_Eg;_Ed=_Ee.b;continue;}}},_Eh=function(_Ei,_Ej,_Ek,_El){return new F(function(){return _Eb(B(_E2(E(_Ej),_Ek,_Ei)),_El);});},_Em=function(_En,_Eo,_Ep){var _Eq=E(_Eo);return new F(function(){return _Eb(B(_E2(E(_Eq.a),_Eq.b,_En)),_Ep);});},_Er=function(_Es,_Et,_Eu){while(1){var _Ev=E(_Eu);if(!_Ev._){return E(_Et);}else{var _Ew=E(_Ev.a),_Ex=_Ew.a,_Ey=_Ew.b,_Ez=E(_Ev.b);if(!_Ez._){return new F(function(){return _O(_Ex,_Ey,_Et);});}else{var _EA=E(_Ez.a),_EB=E(_Ex),_EC=E(_EA.a);if(_EB<_EC){var _ED=B(_DH(_Es,_EC,_EA.b,_Ez.b)),_EE=_ED.a,_EF=E(_ED.c);if(!_EF._){var _EG=_Es<<1,_EH=B(_2h(_EB,_Ey,_Et,_EE));_Es=_EG;_Et=_EH;_Eu=_ED.b;continue;}else{return new F(function(){return _Em(B(_2h(_EB,_Ey,_Et,_EE)),_EF.a,_EF.b);});}}else{return new F(function(){return _Eh(_Et,_EB,_Ey,_Ez);});}}}}},_EI=function(_EJ,_EK,_EL,_EM,_EN){var _EO=E(_EN);if(!_EO._){return new F(function(){return _O(_EL,_EM,_EK);});}else{var _EP=E(_EO.a),_EQ=E(_EL),_ER=E(_EP.a);if(_EQ<_ER){var _ES=B(_DH(_EJ,_ER,_EP.b,_EO.b)),_ET=_ES.a,_EU=E(_ES.c);if(!_EU._){return new F(function(){return _Er(_EJ<<1,B(_2h(_EQ,_EM,_EK,_ET)),_ES.b);});}else{return new F(function(){return _Em(B(_2h(_EQ,_EM,_EK,_ET)),_EU.a,_EU.b);});}}else{return new F(function(){return _Eh(_EK,_EQ,_EM,_EO);});}}},_EV=function(_EW){var _EX=E(_EW);if(!_EX._){return new T0(1);}else{var _EY=E(_EX.a),_EZ=_EY.a,_F0=_EY.b,_F1=E(_EX.b);if(!_F1._){var _F2=E(_EZ);return new T5(0,1,E(_F2),_F0,E(_0),E(_0));}else{var _F3=_F1.b,_F4=E(_F1.a),_F5=_F4.b,_F6=E(_EZ),_F7=E(_F4.a);if(_F6<_F7){return new F(function(){return _EI(1,new T5(0,1,E(_F6),_F0,E(_0),E(_0)),_F7,_F5,_F3);});}else{return new F(function(){return _Eh(new T5(0,1,E(_F6),_F0,E(_0),E(_0)),_F7,_F5,_F3);});}}}},_F8=function(_){return _h9;},_F9=new T(function(){return B(unCStr(": Choose"));}),_Fa=new T(function(){return eval("(function (x, y, z) {var a = document.getElementById(\'actions\'); var r = a.insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x + \' \')); var input = document.createElement(\'input\'); input.type = \'number\'; var ch = \'ibox\' + a.childNodes.length; input.id = ch; input.value = 0; input.style.setProperty(\'width\', \'5em\'); c1.appendChild(input); c1.appendChild(document.createTextNode(\' \' + y)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addActionWithNum(z, document.getElementById(ch).value);};})");}),_Fb=function(_Fc,_Fd,_){var _Fe=new T(function(){return B(A3(_is,_hk,new T2(1,function(_Ff){return new F(function(){return _j6(0,_Fc,_Ff);});},new T2(1,function(_Fg){return new F(function(){return _hA(0,E(_Fd),_Fg);});},_1)),_jv));}),_Fh=__app3(E(_Fa),toJSStr(B(unAppCStr("P",new T(function(){return B(_hq(B(_hA(0,E(_Fd),_1)),_F9));})))),toJSStr(B(unAppCStr("for choice with id ",new T(function(){return B(_hA(0,E(_Fc),_1));})))),toJSStr(new T2(1,_hz,_Fe)));return new F(function(){return _F8(_);});},_Fi=function(_Fj,_Fk,_){while(1){var _Fl=B((function(_Fm,_Fn,_){var _Fo=E(_Fn);if(!_Fo._){var _Fp=E(_Fo.b);_Fj=function(_){var _Fq=B(_Fb(_Fp.a,_Fp.b,_));return new F(function(){return _Fi(_Fm,_Fo.e,_);});};_Fk=_Fo.d;return __continue;}else{return new F(function(){return A1(_Fm,_);});}})(_Fj,_Fk,_));if(_Fl!=__continue){return _Fl;}}},_Fr=new T(function(){return B(unCStr("SIP "));}),_Fs=new T(function(){return B(unCStr("SIRC "));}),_Ft=new T(function(){return B(unCStr("SICC "));}),_Fu=function(_Fv,_Fw,_Fx){var _Fy=E(_Fw);switch(_Fy._){case 0:var _Fz=function(_FA){var _FB=new T(function(){var _FC=new T(function(){return B(_hA(11,E(_Fy.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.d),_FA));}))));});return B(_hA(11,E(_Fy.b),new T2(1,_hK,_FC)));});return new F(function(){return _hF(11,_Fy.a,new T2(1,_hK,_FB));});};if(_Fv<11){return new F(function(){return _hq(_Ft,new T(function(){return B(_Fz(_Fx));},1));});}else{var _FD=new T(function(){return B(_hq(_Ft,new T(function(){return B(_Fz(new T2(1,_hy,_Fx)));},1)));});return new T2(1,_hz,_FD);}break;case 1:var _FE=function(_FF){var _FG=new T(function(){var _FH=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FF));}))));});return B(_hF(11,_Fy.a,new T2(1,_hK,_FH)));},1);return new F(function(){return _hq(_Fs,_FG);});};if(_Fv<11){return new F(function(){return _FE(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FE(new T2(1,_hy,_Fx)));}));}break;default:var _FI=function(_FJ){var _FK=new T(function(){var _FL=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FJ));}))));});return B(_ih(11,_Fy.a,new T2(1,_hK,_FL)));},1);return new F(function(){return _hq(_Fr,_FK);});};if(_Fv<11){return new F(function(){return _FI(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FI(new T2(1,_hy,_Fx)));}));}}},_FM=new T(function(){return B(unCStr(" ADA"));}),_FN=new T(function(){return eval("(function (x, y) {var r = document.getElementById(\'actions\').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addAction(y);};})");}),_FO=function(_FP,_FQ,_FR,_){var _FS=new T(function(){var _FT=new T(function(){var _FU=new T(function(){var _FV=new T(function(){return B(unAppCStr(") of ",new T(function(){return B(_hq(B(_hA(0,E(_FR),_1)),_FM));})));},1);return B(_hq(B(_hA(0,E(_FP),_1)),_FV));});return B(unAppCStr(": Claim payment (with id: ",_FU));},1);return B(_hq(B(_hA(0,E(_FQ),_1)),_FT));}),_FW=__app2(E(_FN),toJSStr(B(unAppCStr("P",_FS))),toJSStr(B(_Fu(0,new T3(2,_FP,_FQ,_FR),_1))));return new F(function(){return _F8(_);});},_FX=function(_FY,_FZ,_){while(1){var _G0=B((function(_G1,_G2,_){var _G3=E(_G2);if(!_G3._){var _G4=E(_G3.b);_FY=function(_){var _G5=B(_FO(_G4.a,_G4.b,_G3.c,_));return new F(function(){return _FX(_G1,_G3.e,_);});};_FZ=_G3.d;return __continue;}else{return new F(function(){return A1(_G1,_);});}})(_FY,_FZ,_));if(_G0!=__continue){return _G0;}}},_G6=new T(function(){return B(unCStr(")"));}),_G7=function(_G8,_G9,_Ga,_){var _Gb=new T(function(){var _Gc=new T(function(){var _Gd=new T(function(){var _Ge=new T(function(){return B(unAppCStr(" ADA from commit (with id: ",new T(function(){return B(_hq(B(_hA(0,E(_G8),_1)),_G6));})));},1);return B(_hq(B(_hA(0,E(_Ga),_1)),_Ge));});return B(unAppCStr(": Redeem ",_Gd));},1);return B(_hq(B(_hA(0,E(_G9),_1)),_Gc));}),_Gf=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gb))),toJSStr(B(_Fu(0,new T3(1,_G8,_G9,_Ga),_1))));return new F(function(){return _F8(_);});},_Gg=function(_Gh,_Gi,_){while(1){var _Gj=B((function(_Gk,_Gl,_){var _Gm=E(_Gl);if(!_Gm._){var _Gn=E(_Gm.b);_Gh=function(_){var _Go=B(_G7(_Gn.a,_Gn.b,_Gn.c,_));return new F(function(){return _Gg(_Gk,_Gm.d,_);});};_Gi=_Gm.c;return __continue;}else{return new F(function(){return A1(_Gk,_);});}})(_Gh,_Gi,_));if(_Gj!=__continue){return _Gj;}}},_Gp=function(_){return _h9;},_Gq=function(_Gr,_Gs,_Gt,_Gu,_){var _Gv=new T(function(){var _Gw=new T(function(){var _Gx=new T(function(){var _Gy=new T(function(){var _Gz=new T(function(){var _GA=new T(function(){return B(unAppCStr(" ADA expiring on: ",new T(function(){return B(_hA(0,E(_Gu),_1));})));},1);return B(_hq(B(_hA(0,E(_Gt),_1)),_GA));});return B(unAppCStr(") of ",_Gz));},1);return B(_hq(B(_hA(0,E(_Gr),_1)),_Gy));});return B(unAppCStr(": Make commit (with id: ",_Gx));},1);return B(_hq(B(_hA(0,E(_Gs),_1)),_Gw));}),_GB=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gv))),toJSStr(B(_Fu(0,new T4(0,_Gr,_Gs,_Gt,_Gu),_1))));return new F(function(){return _F8(_);});},_GC=function(_GD,_GE,_){while(1){var _GF=B((function(_GG,_GH,_){var _GI=E(_GH);if(!_GI._){var _GJ=E(_GI.b);_GD=function(_){var _GK=B(_Gq(_GJ.a,_GJ.b,_GJ.c,_GJ.d,_));return new F(function(){return _GC(_GG,_GI.d,_);});};_GE=_GI.c;return __continue;}else{return new F(function(){return A1(_GG,_);});}})(_GD,_GE,_));if(_GF!=__continue){return _GF;}}},_GL=function(_GM,_GN,_GO,_GP,_){var _GQ=B(_GC(_Gp,_GM,_)),_GR=B(_Gg(_Gp,_GN,_)),_GS=B(_FX(_Gp,_GO,_));return new F(function(){return _Fi(_Gp,_GP,_);});},_GT=function(_GU,_GV){var _GW=E(_GU),_GX=E(_GV);return (E(_GW.a)!=E(_GX.a))?true:(E(_GW.b)!=E(_GX.b))?true:(E(_GW.c)!=E(_GX.c))?true:(E(_GW.d)!=E(_GX.d))?true:false;},_GY=function(_GZ,_H0){return E(_GZ)==E(_H0);},_H1=function(_H2,_H3,_H4,_H5,_H6,_H7,_H8,_H9){if(_H2!=_H6){return false;}else{if(E(_H3)!=E(_H7)){return false;}else{if(E(_H4)!=E(_H8)){return false;}else{return new F(function(){return _GY(_H5,_H9);});}}}},_Ha=function(_Hb,_Hc){var _Hd=E(_Hb),_He=E(_Hc);return new F(function(){return _H1(E(_Hd.a),_Hd.b,_Hd.c,_Hd.d,E(_He.a),_He.b,_He.c,_He.d);});},_Hf=new T2(0,_Ha,_GT),_Hg=function(_Hh,_Hi){return E(_Hh)<E(_Hi);},_Hj=function(_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr){if(_Hk>=_Ho){if(_Hk!=_Ho){return false;}else{var _Hs=E(_Hl),_Ht=E(_Hp);if(_Hs>=_Ht){if(_Hs!=_Ht){return false;}else{var _Hu=E(_Hm),_Hv=E(_Hq);if(_Hu>=_Hv){if(_Hu!=_Hv){return false;}else{return new F(function(){return _Hg(_Hn,_Hr);});}}else{return true;}}}else{return true;}}}else{return true;}},_Hw=function(_Hx,_Hy){var _Hz=E(_Hx),_HA=E(_Hy);return new F(function(){return _Hj(E(_Hz.a),_Hz.b,_Hz.c,_Hz.d,E(_HA.a),_HA.b,_HA.c,_HA.d);});},_HB=function(_HC,_HD){return E(_HC)<=E(_HD);},_HE=function(_HF,_HG,_HH,_HI,_HJ,_HK,_HL,_HM){if(_HF>=_HJ){if(_HF!=_HJ){return false;}else{var _HN=E(_HG),_HO=E(_HK);if(_HN>=_HO){if(_HN!=_HO){return false;}else{var _HP=E(_HH),_HQ=E(_HL);if(_HP>=_HQ){if(_HP!=_HQ){return false;}else{return new F(function(){return _HB(_HI,_HM);});}}else{return true;}}}else{return true;}}}else{return true;}},_HR=function(_HS,_HT){var _HU=E(_HS),_HV=E(_HT);return new F(function(){return _HE(E(_HU.a),_HU.b,_HU.c,_HU.d,E(_HV.a),_HV.b,_HV.c,_HV.d);});},_HW=function(_HX,_HY){return E(_HX)>E(_HY);},_HZ=function(_I0,_I1,_I2,_I3,_I4,_I5,_I6,_I7){if(_I0>=_I4){if(_I0!=_I4){return true;}else{var _I8=E(_I1),_I9=E(_I5);if(_I8>=_I9){if(_I8!=_I9){return true;}else{var _Ia=E(_I2),_Ib=E(_I6);if(_Ia>=_Ib){if(_Ia!=_Ib){return true;}else{return new F(function(){return _HW(_I3,_I7);});}}else{return false;}}}else{return false;}}}else{return false;}},_Ic=function(_Id,_Ie){var _If=E(_Id),_Ig=E(_Ie);return new F(function(){return _HZ(E(_If.a),_If.b,_If.c,_If.d,E(_Ig.a),_Ig.b,_Ig.c,_Ig.d);});},_Ih=function(_Ii,_Ij){return E(_Ii)>=E(_Ij);},_Ik=function(_Il,_Im,_In,_Io,_Ip,_Iq,_Ir,_Is){if(_Il>=_Ip){if(_Il!=_Ip){return true;}else{var _It=E(_Im),_Iu=E(_Iq);if(_It>=_Iu){if(_It!=_Iu){return true;}else{var _Iv=E(_In),_Iw=E(_Ir);if(_Iv>=_Iw){if(_Iv!=_Iw){return true;}else{return new F(function(){return _Ih(_Io,_Is);});}}else{return false;}}}else{return false;}}}else{return false;}},_Ix=function(_Iy,_Iz){var _IA=E(_Iy),_IB=E(_Iz);return new F(function(){return _Ik(E(_IA.a),_IA.b,_IA.c,_IA.d,E(_IB.a),_IB.b,_IB.c,_IB.d);});},_IC=function(_ID,_IE){return (_ID>=_IE)?(_ID!=_IE)?2:1:0;},_IF=function(_IG,_IH){return new F(function(){return _IC(E(_IG),E(_IH));});},_II=function(_IJ,_IK,_IL,_IM,_IN,_IO,_IP,_IQ){if(_IJ>=_IN){if(_IJ!=_IN){return 2;}else{var _IR=E(_IK),_IS=E(_IO);if(_IR>=_IS){if(_IR!=_IS){return 2;}else{var _IT=E(_IL),_IU=E(_IP);if(_IT>=_IU){if(_IT!=_IU){return 2;}else{return new F(function(){return _IF(_IM,_IQ);});}}else{return 0;}}}else{return 0;}}}else{return 0;}},_IV=function(_IW,_IX){var _IY=E(_IW),_IZ=E(_IX);return new F(function(){return _II(E(_IY.a),_IY.b,_IY.c,_IY.d,E(_IZ.a),_IZ.b,_IZ.c,_IZ.d);});},_J0=function(_J1,_J2){var _J3=E(_J1),_J4=E(_J3.a),_J5=E(_J2),_J6=E(_J5.a);if(_J4>=_J6){if(_J4!=_J6){return E(_J3);}else{var _J7=E(_J3.b),_J8=E(_J5.b);if(_J7>=_J8){if(_J7!=_J8){return E(_J3);}else{var _J9=E(_J3.c),_Ja=E(_J5.c);return (_J9>=_Ja)?(_J9!=_Ja)?E(_J3):(E(_J3.d)>E(_J5.d))?E(_J3):E(_J5):E(_J5);}}else{return E(_J5);}}}else{return E(_J5);}},_Jb=function(_Jc,_Jd){var _Je=E(_Jc),_Jf=E(_Je.a),_Jg=E(_Jd),_Jh=E(_Jg.a);if(_Jf>=_Jh){if(_Jf!=_Jh){return E(_Jg);}else{var _Ji=E(_Je.b),_Jj=E(_Jg.b);if(_Ji>=_Jj){if(_Ji!=_Jj){return E(_Jg);}else{var _Jk=E(_Je.c),_Jl=E(_Jg.c);return (_Jk>=_Jl)?(_Jk!=_Jl)?E(_Jg):(E(_Je.d)>E(_Jg.d))?E(_Jg):E(_Je):E(_Je);}}else{return E(_Je);}}}else{return E(_Je);}},_Jm={_:0,a:_Hf,b:_IV,c:_Hw,d:_HR,e:_Ic,f:_Ix,g:_J0,h:_Jb},_Jn=function(_Jo,_Jp,_Jq,_Jr){if(_Jo!=_Jq){return false;}else{return new F(function(){return _GY(_Jp,_Jr);});}},_Js=function(_Jt,_Ju){var _Jv=E(_Jt),_Jw=E(_Ju);return new F(function(){return _Jn(E(_Jv.a),_Jv.b,E(_Jw.a),_Jw.b);});},_Jx=function(_Jy,_Jz,_JA,_JB){return (_Jy!=_JA)?true:(E(_Jz)!=E(_JB))?true:false;},_JC=function(_JD,_JE){var _JF=E(_JD),_JG=E(_JE);return new F(function(){return _Jx(E(_JF.a),_JF.b,E(_JG.a),_JG.b);});},_JH=new T2(0,_Js,_JC),_JI=function(_JJ,_JK,_JL,_JM){if(_JJ>=_JL){if(_JJ!=_JL){return 2;}else{return new F(function(){return _IF(_JK,_JM);});}}else{return 0;}},_JN=function(_JO,_JP){var _JQ=E(_JO),_JR=E(_JP);return new F(function(){return _JI(E(_JQ.a),_JQ.b,E(_JR.a),_JR.b);});},_JS=function(_JT,_JU,_JV,_JW){if(_JT>=_JV){if(_JT!=_JV){return false;}else{return new F(function(){return _Hg(_JU,_JW);});}}else{return true;}},_JX=function(_JY,_JZ){var _K0=E(_JY),_K1=E(_JZ);return new F(function(){return _JS(E(_K0.a),_K0.b,E(_K1.a),_K1.b);});},_K2=function(_K3,_K4,_K5,_K6){if(_K3>=_K5){if(_K3!=_K5){return false;}else{return new F(function(){return _HB(_K4,_K6);});}}else{return true;}},_K7=function(_K8,_K9){var _Ka=E(_K8),_Kb=E(_K9);return new F(function(){return _K2(E(_Ka.a),_Ka.b,E(_Kb.a),_Kb.b);});},_Kc=function(_Kd,_Ke,_Kf,_Kg){if(_Kd>=_Kf){if(_Kd!=_Kf){return true;}else{return new F(function(){return _HW(_Ke,_Kg);});}}else{return false;}},_Kh=function(_Ki,_Kj){var _Kk=E(_Ki),_Kl=E(_Kj);return new F(function(){return _Kc(E(_Kk.a),_Kk.b,E(_Kl.a),_Kl.b);});},_Km=function(_Kn,_Ko,_Kp,_Kq){if(_Kn>=_Kp){if(_Kn!=_Kp){return true;}else{return new F(function(){return _Ih(_Ko,_Kq);});}}else{return false;}},_Kr=function(_Ks,_Kt){var _Ku=E(_Ks),_Kv=E(_Kt);return new F(function(){return _Km(E(_Ku.a),_Ku.b,E(_Kv.a),_Kv.b);});},_Kw=function(_Kx,_Ky){var _Kz=E(_Kx),_KA=_Kz.b,_KB=E(_Kz.a),_KC=E(_Ky),_KD=_KC.b,_KE=E(_KC.a);if(_KB>=_KE){if(_KB!=_KE){return new T2(0,_KB,_KA);}else{var _KF=E(_KA),_KG=E(_KD);return (_KF>_KG)?new T2(0,_KB,_KF):new T2(0,_KE,_KG);}}else{return new T2(0,_KE,_KD);}},_KH=function(_KI,_KJ){var _KK=E(_KI),_KL=_KK.b,_KM=E(_KK.a),_KN=E(_KJ),_KO=_KN.b,_KP=E(_KN.a);if(_KM>=_KP){if(_KM!=_KP){return new T2(0,_KP,_KO);}else{var _KQ=E(_KL),_KR=E(_KO);return (_KQ>_KR)?new T2(0,_KP,_KR):new T2(0,_KM,_KQ);}}else{return new T2(0,_KM,_KL);}},_KS={_:0,a:_JH,b:_JN,c:_JX,d:_K7,e:_Kh,f:_Kr,g:_Kw,h:_KH},_KT=function(_KU,_KV,_KW,_KX){if(_KU!=_KW){return false;}else{return new F(function(){return _GY(_KV,_KX);});}},_KY=function(_KZ,_L0){var _L1=E(_KZ),_L2=E(_L0);return new F(function(){return _KT(E(_L1.a),_L1.b,E(_L2.a),_L2.b);});},_L3=function(_L4,_L5,_L6,_L7){return (_L4!=_L6)?true:(E(_L5)!=E(_L7))?true:false;},_L8=function(_L9,_La){var _Lb=E(_L9),_Lc=E(_La);return new F(function(){return _L3(E(_Lb.a),_Lb.b,E(_Lc.a),_Lc.b);});},_Ld=new T2(0,_KY,_L8),_Le=function(_Lf,_Lg,_Lh,_Li){if(_Lf>=_Lh){if(_Lf!=_Lh){return 2;}else{return new F(function(){return _IF(_Lg,_Li);});}}else{return 0;}},_Lj=function(_Lk,_Ll){var _Lm=E(_Lk),_Ln=E(_Ll);return new F(function(){return _Le(E(_Lm.a),_Lm.b,E(_Ln.a),_Ln.b);});},_Lo=function(_Lp,_Lq,_Lr,_Ls){if(_Lp>=_Lr){if(_Lp!=_Lr){return false;}else{return new F(function(){return _Hg(_Lq,_Ls);});}}else{return true;}},_Lt=function(_Lu,_Lv){var _Lw=E(_Lu),_Lx=E(_Lv);return new F(function(){return _Lo(E(_Lw.a),_Lw.b,E(_Lx.a),_Lx.b);});},_Ly=function(_Lz,_LA,_LB,_LC){if(_Lz>=_LB){if(_Lz!=_LB){return false;}else{return new F(function(){return _HB(_LA,_LC);});}}else{return true;}},_LD=function(_LE,_LF){var _LG=E(_LE),_LH=E(_LF);return new F(function(){return _Ly(E(_LG.a),_LG.b,E(_LH.a),_LH.b);});},_LI=function(_LJ,_LK,_LL,_LM){if(_LJ>=_LL){if(_LJ!=_LL){return true;}else{return new F(function(){return _HW(_LK,_LM);});}}else{return false;}},_LN=function(_LO,_LP){var _LQ=E(_LO),_LR=E(_LP);return new F(function(){return _LI(E(_LQ.a),_LQ.b,E(_LR.a),_LR.b);});},_LS=function(_LT,_LU,_LV,_LW){if(_LT>=_LV){if(_LT!=_LV){return true;}else{return new F(function(){return _Ih(_LU,_LW);});}}else{return false;}},_LX=function(_LY,_LZ){var _M0=E(_LY),_M1=E(_LZ);return new F(function(){return _LS(E(_M0.a),_M0.b,E(_M1.a),_M1.b);});},_M2=function(_M3,_M4){var _M5=E(_M3),_M6=_M5.b,_M7=E(_M5.a),_M8=E(_M4),_M9=_M8.b,_Ma=E(_M8.a);if(_M7>=_Ma){if(_M7!=_Ma){return new T2(0,_M7,_M6);}else{var _Mb=E(_M6),_Mc=E(_M9);return (_Mb>_Mc)?new T2(0,_M7,_Mb):new T2(0,_Ma,_Mc);}}else{return new T2(0,_Ma,_M9);}},_Md=function(_Me,_Mf){var _Mg=E(_Me),_Mh=_Mg.b,_Mi=E(_Mg.a),_Mj=E(_Mf),_Mk=_Mj.b,_Ml=E(_Mj.a);if(_Mi>=_Ml){if(_Mi!=_Ml){return new T2(0,_Ml,_Mk);}else{var _Mm=E(_Mh),_Mn=E(_Mk);return (_Mm>_Mn)?new T2(0,_Ml,_Mn):new T2(0,_Mi,_Mm);}}else{return new T2(0,_Mi,_Mh);}},_Mo={_:0,a:_Ld,b:_Lj,c:_Lt,d:_LD,e:_LN,f:_LX,g:_M2,h:_Md},_Mp=function(_Mq,_Mr){var _Ms=E(_Mq),_Mt=E(_Mr);return (E(_Ms.a)!=E(_Mt.a))?true:(E(_Ms.b)!=E(_Mt.b))?true:(E(_Ms.c)!=E(_Mt.c))?true:false;},_Mu=function(_Mv,_Mw,_Mx,_My,_Mz,_MA){if(_Mv!=_My){return false;}else{if(E(_Mw)!=E(_Mz)){return false;}else{return new F(function(){return _GY(_Mx,_MA);});}}},_MB=function(_MC,_MD){var _ME=E(_MC),_MF=E(_MD);return new F(function(){return _Mu(E(_ME.a),_ME.b,_ME.c,E(_MF.a),_MF.b,_MF.c);});},_MG=new T2(0,_MB,_Mp),_MH=function(_MI,_MJ,_MK,_ML,_MM,_MN){if(_MI>=_ML){if(_MI!=_ML){return false;}else{var _MO=E(_MJ),_MP=E(_MM);if(_MO>=_MP){if(_MO!=_MP){return false;}else{return new F(function(){return _Hg(_MK,_MN);});}}else{return true;}}}else{return true;}},_MQ=function(_MR,_MS){var _MT=E(_MR),_MU=E(_MS);return new F(function(){return _MH(E(_MT.a),_MT.b,_MT.c,E(_MU.a),_MU.b,_MU.c);});},_MV=function(_MW,_MX,_MY,_MZ,_N0,_N1){if(_MW>=_MZ){if(_MW!=_MZ){return false;}else{var _N2=E(_MX),_N3=E(_N0);if(_N2>=_N3){if(_N2!=_N3){return false;}else{return new F(function(){return _HB(_MY,_N1);});}}else{return true;}}}else{return true;}},_N4=function(_N5,_N6){var _N7=E(_N5),_N8=E(_N6);return new F(function(){return _MV(E(_N7.a),_N7.b,_N7.c,E(_N8.a),_N8.b,_N8.c);});},_N9=function(_Na,_Nb,_Nc,_Nd,_Ne,_Nf){if(_Na>=_Nd){if(_Na!=_Nd){return true;}else{var _Ng=E(_Nb),_Nh=E(_Ne);if(_Ng>=_Nh){if(_Ng!=_Nh){return true;}else{return new F(function(){return _HW(_Nc,_Nf);});}}else{return false;}}}else{return false;}},_Ni=function(_Nj,_Nk){var _Nl=E(_Nj),_Nm=E(_Nk);return new F(function(){return _N9(E(_Nl.a),_Nl.b,_Nl.c,E(_Nm.a),_Nm.b,_Nm.c);});},_Nn=function(_No,_Np,_Nq,_Nr,_Ns,_Nt){if(_No>=_Nr){if(_No!=_Nr){return true;}else{var _Nu=E(_Np),_Nv=E(_Ns);if(_Nu>=_Nv){if(_Nu!=_Nv){return true;}else{return new F(function(){return _Ih(_Nq,_Nt);});}}else{return false;}}}else{return false;}},_Nw=function(_Nx,_Ny){var _Nz=E(_Nx),_NA=E(_Ny);return new F(function(){return _Nn(E(_Nz.a),_Nz.b,_Nz.c,E(_NA.a),_NA.b,_NA.c);});},_NB=function(_NC,_ND,_NE,_NF,_NG,_NH){if(_NC>=_NF){if(_NC!=_NF){return 2;}else{var _NI=E(_ND),_NJ=E(_NG);if(_NI>=_NJ){if(_NI!=_NJ){return 2;}else{return new F(function(){return _IF(_NE,_NH);});}}else{return 0;}}}else{return 0;}},_NK=function(_NL,_NM){var _NN=E(_NL),_NO=E(_NM);return new F(function(){return _NB(E(_NN.a),_NN.b,_NN.c,E(_NO.a),_NO.b,_NO.c);});},_NP=function(_NQ,_NR){var _NS=E(_NQ),_NT=E(_NS.a),_NU=E(_NR),_NV=E(_NU.a);if(_NT>=_NV){if(_NT!=_NV){return E(_NS);}else{var _NW=E(_NS.b),_NX=E(_NU.b);return (_NW>=_NX)?(_NW!=_NX)?E(_NS):(E(_NS.c)>E(_NU.c))?E(_NS):E(_NU):E(_NU);}}else{return E(_NU);}},_NY=function(_NZ,_O0){var _O1=E(_NZ),_O2=E(_O1.a),_O3=E(_O0),_O4=E(_O3.a);if(_O2>=_O4){if(_O2!=_O4){return E(_O3);}else{var _O5=E(_O1.b),_O6=E(_O3.b);return (_O5>=_O6)?(_O5!=_O6)?E(_O3):(E(_O1.c)>E(_O3.c))?E(_O3):E(_O1):E(_O1);}}else{return E(_O1);}},_O7={_:0,a:_MG,b:_NK,c:_MQ,d:_N4,e:_Ni,f:_Nw,g:_NP,h:_NY},_O8=__Z,_O9=__Z,_Oa=function(_Ob){return E(E(_Ob).b);},_Oc=function(_Od,_Oe,_Of){var _Og=E(_Oe);if(!_Og._){return E(_Of);}else{var _Oh=function(_Oi,_Oj){while(1){var _Ok=E(_Oj);if(!_Ok._){var _Ol=_Ok.b,_Om=_Ok.e;switch(B(A3(_Oa,_Od,_Oi,_Ol))){case 0:return new F(function(){return _2h(_Ol,_Ok.c,B(_Oh(_Oi,_Ok.d)),_Om);});break;case 1:return E(_Om);default:_Oj=_Om;continue;}}else{return new T0(1);}}};return new F(function(){return _Oh(_Og.a,_Of);});}},_On=function(_Oo,_Op,_Oq){var _Or=E(_Op);if(!_Or._){return E(_Oq);}else{var _Os=function(_Ot,_Ou){while(1){var _Ov=E(_Ou);if(!_Ov._){var _Ow=_Ov.b,_Ox=_Ov.d;switch(B(A3(_Oa,_Oo,_Ow,_Ot))){case 0:return new F(function(){return _2h(_Ow,_Ov.c,_Ox,B(_Os(_Ot,_Ov.e)));});break;case 1:return E(_Ox);default:_Ou=_Ox;continue;}}else{return new T0(1);}}};return new F(function(){return _Os(_Or.a,_Oq);});}},_Oy=function(_Oz,_OA,_OB,_OC){var _OD=E(_OA),_OE=E(_OC);if(!_OE._){var _OF=_OE.b,_OG=_OE.c,_OH=_OE.d,_OI=_OE.e;switch(B(A3(_Oa,_Oz,_OD,_OF))){case 0:return new F(function(){return _X(_OF,_OG,B(_Oy(_Oz,_OD,_OB,_OH)),_OI);});break;case 1:return E(_OE);default:return new F(function(){return _6(_OF,_OG,_OH,B(_Oy(_Oz,_OD,_OB,_OI)));});}}else{return new T5(0,1,E(_OD),_OB,E(_0),E(_0));}},_OJ=function(_OK,_OL,_OM,_ON){return new F(function(){return _Oy(_OK,_OL,_OM,_ON);});},_OO=function(_OP){return E(E(_OP).d);},_OQ=function(_OR){return E(E(_OR).f);},_OS=function(_OT,_OU,_OV,_OW){var _OX=E(_OU);if(!_OX._){var _OY=E(_OV);if(!_OY._){return E(_OW);}else{var _OZ=function(_P0,_P1){while(1){var _P2=E(_P1);if(!_P2._){if(!B(A3(_OQ,_OT,_P2.b,_P0))){return E(_P2);}else{_P1=_P2.d;continue;}}else{return new T0(1);}}};return new F(function(){return _OZ(_OY.a,_OW);});}}else{var _P3=_OX.a,_P4=E(_OV);if(!_P4._){var _P5=function(_P6,_P7){while(1){var _P8=E(_P7);if(!_P8._){if(!B(A3(_OO,_OT,_P8.b,_P6))){return E(_P8);}else{_P7=_P8.e;continue;}}else{return new T0(1);}}};return new F(function(){return _P5(_P3,_OW);});}else{var _P9=function(_Pa,_Pb,_Pc){while(1){var _Pd=E(_Pc);if(!_Pd._){var _Pe=_Pd.b;if(!B(A3(_OO,_OT,_Pe,_Pa))){if(!B(A3(_OQ,_OT,_Pe,_Pb))){return E(_Pd);}else{_Pc=_Pd.d;continue;}}else{_Pc=_Pd.e;continue;}}else{return new T0(1);}}};return new F(function(){return _P9(_P3,_P4.a,_OW);});}}},_Pf=function(_Pg,_Ph,_Pi,_Pj,_Pk){var _Pl=E(_Pk);if(!_Pl._){var _Pm=_Pl.b,_Pn=_Pl.c,_Po=_Pl.d,_Pp=_Pl.e,_Pq=E(_Pj);if(!_Pq._){var _Pr=_Pq.b,_Ps=function(_Pt){var _Pu=new T1(1,E(_Pr));return new F(function(){return _2h(_Pr,_Pq.c,B(_Pf(_Pg,_Ph,_Pu,_Pq.d,B(_OS(_Pg,_Ph,_Pu,_Pl)))),B(_Pf(_Pg,_Pu,_Pi,_Pq.e,B(_OS(_Pg,_Pu,_Pi,_Pl)))));});};if(!E(_Po)._){return new F(function(){return _Ps(_);});}else{if(!E(_Pp)._){return new F(function(){return _Ps(_);});}else{return new F(function(){return _OJ(_Pg,_Pm,_Pn,_Pq);});}}}else{return new F(function(){return _2h(_Pm,_Pn,B(_Oc(_Pg,_Ph,_Po)),B(_On(_Pg,_Pi,_Pp)));});}}else{return E(_Pj);}},_Pv=function(_Pw,_Px,_Py,_Pz,_PA,_PB,_PC,_PD,_PE,_PF,_PG,_PH,_PI){var _PJ=function(_PK){var _PL=new T1(1,E(_PA));return new F(function(){return _2h(_PA,_PB,B(_Pf(_Pw,_Px,_PL,_PC,B(_OS(_Pw,_Px,_PL,new T5(0,_PE,E(_PF),_PG,E(_PH),E(_PI)))))),B(_Pf(_Pw,_PL,_Py,_PD,B(_OS(_Pw,_PL,_Py,new T5(0,_PE,E(_PF),_PG,E(_PH),E(_PI)))))));});};if(!E(_PH)._){return new F(function(){return _PJ(_);});}else{if(!E(_PI)._){return new F(function(){return _PJ(_);});}else{return new F(function(){return _OJ(_Pw,_PF,_PG,new T5(0,_Pz,E(_PA),_PB,E(_PC),E(_PD)));});}}},_PM=function(_PN,_PO,_PP){var _PQ=E(_PO);if(!_PQ._){return E(_PP);}else{var _PR=function(_PS,_PT){while(1){var _PU=E(_PT);if(!_PU._){var _PV=_PU.b,_PW=_PU.d;switch(B(A3(_Oa,_PN,_PS,_PV))){case 0:return new F(function(){return _7J(_PV,B(_PR(_PS,_PU.c)),_PW);});break;case 1:return E(_PW);default:_PT=_PW;continue;}}else{return new T0(1);}}};return new F(function(){return _PR(_PQ.a,_PP);});}},_PX=function(_PY,_PZ,_Q0){var _Q1=E(_PZ);if(!_Q1._){return E(_Q0);}else{var _Q2=function(_Q3,_Q4){while(1){var _Q5=E(_Q4);if(!_Q5._){var _Q6=_Q5.b,_Q7=_Q5.c;switch(B(A3(_Oa,_PY,_Q6,_Q3))){case 0:return new F(function(){return _7J(_Q6,_Q7,B(_Q2(_Q3,_Q5.d)));});break;case 1:return E(_Q7);default:_Q4=_Q7;continue;}}else{return new T0(1);}}};return new F(function(){return _Q2(_Q1.a,_Q0);});}},_Q8=function(_Q9,_Qa,_Qb){var _Qc=E(_Qa),_Qd=E(_Qb);if(!_Qd._){var _Qe=_Qd.b,_Qf=_Qd.c,_Qg=_Qd.d;switch(B(A3(_Oa,_Q9,_Qc,_Qe))){case 0:return new F(function(){return _6x(_Qe,B(_Q8(_Q9,_Qc,_Qf)),_Qg);});break;case 1:return E(_Qd);default:return new F(function(){return _5N(_Qe,_Qf,B(_Q8(_Q9,_Qc,_Qg)));});}}else{return new T4(0,1,E(_Qc),E(_5I),E(_5I));}},_Qh=function(_Qi,_Qj,_Qk){return new F(function(){return _Q8(_Qi,_Qj,_Qk);});},_Ql=function(_Qm,_Qn,_Qo,_Qp){var _Qq=E(_Qn);if(!_Qq._){var _Qr=E(_Qo);if(!_Qr._){return E(_Qp);}else{var _Qs=function(_Qt,_Qu){while(1){var _Qv=E(_Qu);if(!_Qv._){if(!B(A3(_OQ,_Qm,_Qv.b,_Qt))){return E(_Qv);}else{_Qu=_Qv.c;continue;}}else{return new T0(1);}}};return new F(function(){return _Qs(_Qr.a,_Qp);});}}else{var _Qw=_Qq.a,_Qx=E(_Qo);if(!_Qx._){var _Qy=function(_Qz,_QA){while(1){var _QB=E(_QA);if(!_QB._){if(!B(A3(_OO,_Qm,_QB.b,_Qz))){return E(_QB);}else{_QA=_QB.d;continue;}}else{return new T0(1);}}};return new F(function(){return _Qy(_Qw,_Qp);});}else{var _QC=function(_QD,_QE,_QF){while(1){var _QG=E(_QF);if(!_QG._){var _QH=_QG.b;if(!B(A3(_OO,_Qm,_QH,_QD))){if(!B(A3(_OQ,_Qm,_QH,_QE))){return E(_QG);}else{_QF=_QG.c;continue;}}else{_QF=_QG.d;continue;}}else{return new T0(1);}}};return new F(function(){return _QC(_Qw,_Qx.a,_Qp);});}}},_QI=function(_QJ,_QK,_QL,_QM,_QN){var _QO=E(_QN);if(!_QO._){var _QP=_QO.b,_QQ=_QO.c,_QR=_QO.d,_QS=E(_QM);if(!_QS._){var _QT=_QS.b,_QU=function(_QV){var _QW=new T1(1,E(_QT));return new F(function(){return _7J(_QT,B(_QI(_QJ,_QK,_QW,_QS.c,B(_Ql(_QJ,_QK,_QW,_QO)))),B(_QI(_QJ,_QW,_QL,_QS.d,B(_Ql(_QJ,_QW,_QL,_QO)))));});};if(!E(_QQ)._){return new F(function(){return _QU(_);});}else{if(!E(_QR)._){return new F(function(){return _QU(_);});}else{return new F(function(){return _Qh(_QJ,_QP,_QS);});}}}else{return new F(function(){return _7J(_QP,B(_PM(_QJ,_QK,_QQ)),B(_PX(_QJ,_QL,_QR)));});}}else{return E(_QM);}},_QX=function(_QY,_QZ,_R0,_R1,_R2,_R3,_R4,_R5,_R6,_R7,_R8){var _R9=function(_Ra){var _Rb=new T1(1,E(_R2));return new F(function(){return _7J(_R2,B(_QI(_QY,_QZ,_Rb,_R3,B(_Ql(_QY,_QZ,_Rb,new T4(0,_R5,E(_R6),E(_R7),E(_R8)))))),B(_QI(_QY,_Rb,_R0,_R4,B(_Ql(_QY,_Rb,_R0,new T4(0,_R5,E(_R6),E(_R7),E(_R8)))))));});};if(!E(_R7)._){return new F(function(){return _R9(_);});}else{if(!E(_R8)._){return new F(function(){return _R9(_);});}else{return new F(function(){return _Qh(_QY,_R6,new T4(0,_R1,E(_R2),E(_R3),E(_R4)));});}}},_Rc=function(_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj,_Rk){return new T4(0,new T(function(){var _Rl=E(_Rd);if(!_Rl._){var _Rm=E(_Rh);if(!_Rm._){return B(_QX(_Jm,_O9,_O9,_Rl.a,_Rl.b,_Rl.c,_Rl.d,_Rm.a,_Rm.b,_Rm.c,_Rm.d));}else{return E(_Rl);}}else{return E(_Rh);}}),new T(function(){var _Rn=E(_Re);if(!_Rn._){var _Ro=E(_Ri);if(!_Ro._){return B(_QX(_O7,_O9,_O9,_Rn.a,_Rn.b,_Rn.c,_Rn.d,_Ro.a,_Ro.b,_Ro.c,_Ro.d));}else{return E(_Rn);}}else{return E(_Ri);}}),new T(function(){var _Rp=E(_Rf);if(!_Rp._){var _Rq=E(_Rj);if(!_Rq._){return B(_Pv(_Mo,_O8,_O8,_Rp.a,_Rp.b,_Rp.c,_Rp.d,_Rp.e,_Rq.a,_Rq.b,_Rq.c,_Rq.d,_Rq.e));}else{return E(_Rp);}}else{return E(_Rj);}}),new T(function(){var _Rr=E(_Rg);if(!_Rr._){var _Rs=E(_Rk);if(!_Rs._){return B(_Pv(_KS,_O8,_O8,_Rr.a,_Rr.b,_Rr.c,_Rr.d,_Rr.e,_Rs.a,_Rs.b,_Rs.c,_Rs.d,_Rs.e));}else{return E(_Rr);}}else{return E(_Rk);}}));},_Rt=0,_Ru=function(_Rv,_Rw,_Rx,_Ry){while(1){var _Rz=E(_Ry);if(!_Rz._){var _RA=_Rz.d,_RB=_Rz.e,_RC=E(_Rz.b),_RD=E(_RC.a);if(_Rv>=_RD){if(_Rv!=_RD){_Rw=_;_Ry=_RB;continue;}else{var _RE=E(_RC.b);if(_Rx>=_RE){if(_Rx!=_RE){_Rw=_;_Ry=_RB;continue;}else{return new T1(1,_Rz.c);}}else{_Rw=_;_Ry=_RA;continue;}}}else{_Rw=_;_Ry=_RA;continue;}}else{return __Z;}}},_RF=function(_RG,_RH,_RI,_RJ){while(1){var _RK=E(_RJ);if(!_RK._){var _RL=_RK.d,_RM=_RK.e,_RN=E(_RK.b),_RO=E(_RN.a);if(_RG>=_RO){if(_RG!=_RO){_RH=_;_RJ=_RM;continue;}else{var _RP=E(_RI),_RQ=E(_RN.b);if(_RP>=_RQ){if(_RP!=_RQ){return new F(function(){return _Ru(_RG,_,_RP,_RM);});}else{return new T1(1,_RK.c);}}else{return new F(function(){return _Ru(_RG,_,_RP,_RL);});}}}else{_RH=_;_RJ=_RL;continue;}}else{return __Z;}}},_RR=function(_RS,_RT){while(1){var _RU=E(_RT);if(!_RU._){var _RV=E(_RU.b);if(_RS>=_RV){if(_RS!=_RV){_RT=_RU.e;continue;}else{return new T1(1,_RU.c);}}else{_RT=_RU.d;continue;}}else{return __Z;}}},_RW=function(_RX,_RY,_RZ){while(1){var _S0=E(_RZ);switch(_S0._){case 0:var _S1=B(_RR(E(_S0.a),_RX));if(!_S1._){return E(_Rt);}else{var _S2=E(E(_S1.a).b);return (_S2._==0)?E(_S2.a):E(_Rt);}break;case 1:return B(_RW(_RX,_RY,_S0.a))+B(_RW(_RX,_RY,_S0.b))|0;case 2:return E(_S0.a);default:var _S3=_S0.b,_S4=_S0.c,_S5=E(_RY);if(!_S5._){var _S6=_S5.d,_S7=_S5.e,_S8=E(_S5.b),_S9=E(_S0.a),_Sa=E(_S8.a);if(_S9>=_Sa){if(_S9!=_Sa){var _Sb=B(_RF(_S9,_,_S3,_S7));if(!_Sb._){_RY=_S5;_RZ=_S4;continue;}else{return E(_Sb.a);}}else{var _Sc=E(_S3),_Sd=E(_S8.b);if(_Sc>=_Sd){if(_Sc!=_Sd){var _Se=B(_Ru(_S9,_,_Sc,_S7));if(!_Se._){_RY=_S5;_RZ=_S4;continue;}else{return E(_Se.a);}}else{return E(_S5.c);}}else{var _Sf=B(_Ru(_S9,_,_Sc,_S6));if(!_Sf._){_RY=_S5;_RZ=_S4;continue;}else{return E(_Sf.a);}}}}else{var _Sg=B(_RF(_S9,_,_S3,_S6));if(!_Sg._){_RY=_S5;_RZ=_S4;continue;}else{return E(_Sg.a);}}}else{_RY=_0;_RZ=_S4;continue;}}}},_Sh=function(_Si,_Sj){while(1){var _Sk=E(_Sj);if(!_Sk._){var _Sl=E(_Sk.b);if(_Si>=_Sl){if(_Si!=_Sl){_Sj=_Sk.e;continue;}else{return true;}}else{_Sj=_Sk.d;continue;}}else{return false;}}},_Sm=function(_Sn,_So){while(1){var _Sp=E(_So);if(!_Sp._){var _Sq=E(_Sp.b);if(_Sn>=_Sq){if(_Sn!=_Sq){_So=_Sp.e;continue;}else{return new T1(1,_Sp.c);}}else{_So=_Sp.d;continue;}}else{return __Z;}}},_Sr=function(_Ss,_St){var _Su=E(_Ss);return new F(function(){return _RW(_Su.a,_Su.b,_St);});},_Sv=function(_Sw,_Sx){var _Sy=E(_Sw);switch(_Sy._){case 1:var _Sz=E(_Sx),_SA=_Sz.a,_SB=E(_Sy.a);return (!B(_Sh(_SB,_SA)))?new T4(0,new T4(0,1,E(new T4(0,_SB,_Sy.b,new T(function(){return B(_RW(_SA,_Sz.b,_Sy.c));}),_Sy.e)),E(_5I),E(_5I)),_5I,_0,_0):new T4(0,_5I,_5I,_0,_0);case 2:var _SC=E(_Sy.a),_SD=B(_Sm(_SC,E(_Sx).a));if(!_SD._){return new T4(0,_5I,_5I,_0,_0);}else{var _SE=E(_SD.a),_SF=E(_SE.b);return (_SF._==0)?new T4(0,_5I,new T4(0,1,E(new T3(0,_SC,_SE.a,_SF.a)),E(_5I),E(_5I)),_0,_0):new T4(0,_5I,_5I,_0,_0);}break;case 3:return new T4(0,_5I,_5I,new T5(0,1,E(new T2(0,_Sy.a,_Sy.c)),new T(function(){return B(_Sr(_Sx,_Sy.d));}),E(_0),E(_0)),_0);case 4:var _SG=B(_Sv(_Sy.a,_Sx)),_SH=B(_Sv(_Sy.b,_Sx));return new F(function(){return _Rc(_SG.a,_SG.b,_SG.c,_SG.d,_SH.a,_SH.b,_SH.c,_SH.d);});break;default:return new T4(0,_5I,_5I,_0,_0);}},_SI=function(_SJ,_SK){var _SL=new T(function(){var _SM=function(_SN,_SO){while(1){var _SP=B((function(_SQ,_SR){var _SS=E(_SR);if(!_SS._){var _ST=_SS.e,_SU=new T(function(){var _SV=E(_SS.c),_SW=E(_SV.b);if(!_SW._){var _SX=E(E(_SJ).b);if(E(_SW.b)>_SX){var _SY=function(_SZ,_T0){while(1){var _T1=B((function(_T2,_T3){var _T4=E(_T3);if(!_T4._){var _T5=_T4.e,_T6=new T(function(){var _T7=E(_T4.c),_T8=E(_T7.b);if(!_T8._){if(E(_T8.b)>_SX){return B(_SY(_T2,_T5));}else{return new T2(1,new T3(0,_T4.b,_T7.a,_T8.a),new T(function(){return B(_SY(_T2,_T5));}));}}else{return B(_SY(_T2,_T5));}},1);_SZ=_T6;_T0=_T4.d;return __continue;}else{return E(_T2);}})(_SZ,_T0));if(_T1!=__continue){return _T1;}}};return B(_SY(_SQ,_ST));}else{var _T9=new T(function(){var _Ta=function(_Tb,_Tc){while(1){var _Td=B((function(_Te,_Tf){var _Tg=E(_Tf);if(!_Tg._){var _Th=_Tg.e,_Ti=new T(function(){var _Tj=E(_Tg.c),_Tk=E(_Tj.b);if(!_Tk._){if(E(_Tk.b)>_SX){return B(_Ta(_Te,_Th));}else{return new T2(1,new T3(0,_Tg.b,_Tj.a,_Tk.a),new T(function(){return B(_Ta(_Te,_Th));}));}}else{return B(_Ta(_Te,_Th));}},1);_Tb=_Ti;_Tc=_Tg.d;return __continue;}else{return E(_Te);}})(_Tb,_Tc));if(_Td!=__continue){return _Td;}}};return B(_Ta(_SQ,_ST));});return new T2(1,new T3(0,_SS.b,_SV.a,_SW.a),_T9);}}else{return B(_SM(_SQ,_ST));}},1);_SN=_SU;_SO=_SS.d;return __continue;}else{return E(_SQ);}})(_SN,_SO));if(_SP!=__continue){return _SP;}}};return B(_c2(B(_SM(_1,_SK))));});return new T4(0,_5I,_SL,_0,_0);},_Tl=function(_Tm,_Tn,_To,_Tp,_Tq){while(1){var _Tr=E(_Tm);if(!_Tr._){return new T4(0,_Tn,_To,_Tp,_Tq);}else{var _Ts=E(_Tr.a),_Tt=B(_Rc(_Tn,_To,_Tp,_Tq,_Ts.a,_Ts.b,_Ts.c,_Ts.d));_Tm=_Tr.b;_Tn=_Tt.a;_To=_Tt.b;_Tp=_Tt.c;_Tq=_Tt.d;continue;}}},_Tu=function(_Tv,_Tw,_Tx,_Ty,_Tz,_TA){var _TB=E(_Tv),_TC=B(_Rc(_Tx,_Ty,_Tz,_TA,_TB.a,_TB.b,_TB.c,_TB.d));return new F(function(){return _Tl(_Tw,_TC.a,_TC.b,_TC.c,_TC.d);});},_TD=0,_TE=function(_TF){var _TG=E(_TF);switch(_TG._){case 1:var _TH=B(_TE(_TG.a));return new F(function(){return _Tu(new T(function(){var _TI=B(_TE(_TG.b));return new T4(0,_TI.a,_TI.b,_TI.c,_TI.d);}),_1,_TH.a,_TH.b,_TH.c,_TH.d);});break;case 3:var _TJ=B(_TE(_TG.c));return new F(function(){return _Rc(_5I,_5I,_0,new T5(0,1,E(new T2(0,_TG.a,_TG.b)),_TD,E(_0),E(_0)),_TJ.a,_TJ.b,_TJ.c,_TJ.d);});break;default:return new T4(0,_5I,_5I,_0,_0);}},_TK=function(_TL,_TM,_TN,_TO){while(1){var _TP=E(_TO);if(!_TP._){var _TQ=_TP.d,_TR=_TP.e,_TS=E(_TP.b),_TT=E(_TS.a);if(_TL>=_TT){if(_TL!=_TT){_TM=_;_TO=_TR;continue;}else{var _TU=E(_TS.b);if(_TN>=_TU){if(_TN!=_TU){_TM=_;_TO=_TR;continue;}else{return true;}}else{_TM=_;_TO=_TQ;continue;}}}else{_TM=_;_TO=_TQ;continue;}}else{return false;}}},_TV=function(_TW,_TX,_TY,_TZ){while(1){var _U0=E(_TZ);if(!_U0._){var _U1=_U0.d,_U2=_U0.e,_U3=E(_U0.b),_U4=E(_U3.a);if(_TW>=_U4){if(_TW!=_U4){_TX=_;_TZ=_U2;continue;}else{var _U5=E(_TY),_U6=E(_U3.b);if(_U5>=_U6){if(_U5!=_U6){return new F(function(){return _TK(_TW,_,_U5,_U2);});}else{return true;}}else{return new F(function(){return _TK(_TW,_,_U5,_U1);});}}}else{_TX=_;_TZ=_U1;continue;}}else{return false;}}},_U7=function(_U8,_U9,_Ua,_Ub,_Uc){while(1){var _Ud=E(_U8);if(!_Ud._){return new T4(0,_U9,_Ua,_Ub,_Uc);}else{var _Ue=E(_Ud.a),_Uf=B(_Rc(_U9,_Ua,_Ub,_Uc,_Ue.a,_Ue.b,_Ue.c,_Ue.d));_U8=_Ud.b;_U9=_Uf.a;_Ua=_Uf.b;_Ub=_Uf.c;_Uc=_Uf.d;continue;}}},_Ug=function(_Uh,_Ui,_Uj,_Uk,_Ul){while(1){var _Um=E(_Uh);if(!_Um._){return new T4(0,_Ui,_Uj,_Uk,_Ul);}else{var _Un=E(_Um.a),_Uo=B(_Rc(_Ui,_Uj,_Uk,_Ul,_Un.a,_Un.b,_Un.c,_Un.d));_Uh=_Um.b;_Ui=_Uo.a;_Uj=_Uo.b;_Uk=_Uo.c;_Ul=_Uo.d;continue;}}},_Up=function(_Uq,_Ur,_Us,_Ut,_Uu){while(1){var _Uv=E(_Uq);if(!_Uv._){return new T4(0,_Ur,_Us,_Ut,_Uu);}else{var _Uw=E(_Uv.a),_Ux=B(_Rc(_Ur,_Us,_Ut,_Uu,_Uw.a,_Uw.b,_Uw.c,_Uw.d));_Uq=_Uv.b;_Ur=_Ux.a;_Us=_Ux.b;_Ut=_Ux.c;_Uu=_Ux.d;continue;}}},_Uy=function(_Uz,_UA){var _UB=B(_TE(_UA));return new T4(0,_UB.a,_UB.b,_UB.c,_UB.d);},_UC=function(_UD,_UE){var _UF=B(_UG(_UD,_UE));return new T4(0,_UF.a,_UF.b,_UF.c,_UF.d);},_UG=function(_UH,_UI){while(1){var _UJ=B((function(_UK,_UL){var _UM=E(_UL);switch(_UM._){case 1:var _UN=B(_UG(_UK,_UM.a));return new F(function(){return _Up(new T2(1,new T(function(){return B(_UC(_UK,_UM.b));}),_1),_UN.a,_UN.b,_UN.c,_UN.d);});break;case 2:var _UO=B(_UG(_UK,_UM.a));return new F(function(){return _Ug(new T2(1,new T(function(){return B(_UC(_UK,_UM.b));}),_1),_UO.a,_UO.b,_UO.c,_UO.d);});break;case 3:var _UP=_UK;_UH=_UP;_UI=_UM.a;return __continue;case 4:var _UQ=_UM.a,_UR=_UM.b,_US=E(E(_UK).b);if(!_US._){var _UT=_US.d,_UU=_US.e,_UV=E(_US.b),_UW=E(_UQ),_UX=E(_UV.a);if(_UW>=_UX){if(_UW!=_UX){return (!B(_TV(_UW,_,_UR,_UU)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_UW,_UR)),_TD,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}else{var _UY=E(_UR),_UZ=E(_UV.b);return (_UY>=_UZ)?(_UY!=_UZ)?(!B(_TK(_UW,_,_UY,_UU)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_UW,_UY)),_TD,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0):new T4(0,_5I,_5I,_0,_0):(!B(_TK(_UW,_,_UY,_UT)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_UW,_UY)),_TD,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return (!B(_TV(_UW,_,_UR,_UT)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_UW,_UR)),_TD,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_UQ,_UR)),_TD,E(_0),E(_0)));}break;case 5:var _V0=_UM.a,_V1=_UM.b,_V2=E(E(_UK).b);if(!_V2._){var _V3=_V2.d,_V4=_V2.e,_V5=E(_V2.b),_V6=E(_V0),_V7=E(_V5.a);if(_V6>=_V7){if(_V6!=_V7){return (!B(_TV(_V6,_,_V1,_V4)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_V6,_V1)),_TD,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}else{var _V8=E(_V1),_V9=E(_V5.b);return (_V8>=_V9)?(_V8!=_V9)?(!B(_TK(_V6,_,_V8,_V4)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_V6,_V8)),_TD,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0):new T4(0,_5I,_5I,_0,_0):(!B(_TK(_V6,_,_V8,_V3)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_V6,_V8)),_TD,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return (!B(_TV(_V6,_,_V1,_V3)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_V6,_V1)),_TD,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_V0,_V1)),_TD,E(_0),E(_0)));}break;case 6:var _Va=B(_TE(_UM.a));return new F(function(){return _U7(new T2(1,new T(function(){return B(_Uy(_UK,_UM.b));}),_1),_Va.a,_Va.b,_Va.c,_Va.d);});break;default:return new T4(0,_5I,_5I,_0,_0);}})(_UH,_UI));if(_UJ!=__continue){return _UJ;}}},_Vb=function(_Vc,_Vd,_Ve,_Vf,_Vg){while(1){var _Vh=E(_Vc);if(!_Vh._){return new T4(0,_Vd,_Ve,_Vf,_Vg);}else{var _Vi=E(_Vh.a),_Vj=B(_Rc(_Vd,_Ve,_Vf,_Vg,_Vi.a,_Vi.b,_Vi.c,_Vi.d));_Vc=_Vh.b;_Vd=_Vj.a;_Ve=_Vj.b;_Vf=_Vj.c;_Vg=_Vj.d;continue;}}},_Vk=function(_Vl,_Vm){var _Vn=B(_Vo(_Vl,_Vm));return new T4(0,_Vn.a,_Vn.b,_Vn.c,_Vn.d);},_Vo=function(_Vp,_Vq){while(1){var _Vr=B((function(_Vs,_Vt){var _Vu=E(_Vt);switch(_Vu._){case 0:return new T4(0,_5I,_5I,_0,_0);case 1:var _Vv=B(_TE(_Vu.c)),_Vw=B(_Vo(_Vs,_Vu.f)),_Vx=B(_Rc(_Vv.a,_Vv.b,_Vv.c,_Vv.d,_Vw.a,_Vw.b,_Vw.c,_Vw.d)),_Vy=B(_Vo(_Vs,_Vu.g));return new F(function(){return _Rc(_Vx.a,_Vx.b,_Vx.c,_Vx.d,_Vy.a,_Vy.b,_Vy.c,_Vy.d);});break;case 2:var _Vz=_Vs;_Vp=_Vz;_Vq=_Vu.b;return __continue;case 3:var _VA=B(_TE(_Vu.d)),_VB=B(_Vo(_Vs,_Vu.f));return new F(function(){return _Rc(_VA.a,_VA.b,_VA.c,_VA.d,_VB.a,_VB.b,_VB.c,_VB.d);});break;case 4:var _VC=B(_Vo(_Vs,_Vu.a));return new F(function(){return _Vb(new T2(1,new T(function(){return B(_Vk(_Vs,_Vu.b));}),_1),_VC.a,_VC.b,_VC.c,_VC.d);});break;case 5:var _VD=B(_UG(_Vs,_Vu.a)),_VE=B(_Vo(_Vs,_Vu.b)),_VF=B(_Rc(_VD.a,_VD.b,_VD.c,_VD.d,_VE.a,_VE.b,_VE.c,_VE.d)),_VG=B(_Vo(_Vs,_Vu.c));return new F(function(){return _Rc(_VF.a,_VF.b,_VF.c,_VF.d,_VG.a,_VG.b,_VG.c,_VG.d);});break;default:var _VH=B(_UG(_Vs,_Vu.a)),_VI=B(_Vo(_Vs,_Vu.c)),_VJ=B(_Rc(_VH.a,_VH.b,_VH.c,_VH.d,_VI.a,_VI.b,_VI.c,_VI.d)),_VK=B(_Vo(_Vs,_Vu.d));return new F(function(){return _Rc(_VJ.a,_VJ.b,_VJ.c,_VJ.d,_VK.a,_VK.b,_VK.c,_VK.d);});}})(_Vp,_Vq));if(_Vr!=__continue){return _Vr;}}},_VL=function(_VM,_VN){return E(_VM)!=E(_VN);},_VO=new T2(0,_GY,_VL),_VP=function(_VQ,_VR){var _VS=E(_VQ),_VT=E(_VR);return (_VS>_VT)?E(_VS):E(_VT);},_VU=function(_VV,_VW){var _VX=E(_VV),_VY=E(_VW);return (_VX>_VY)?E(_VY):E(_VX);},_VZ={_:0,a:_VO,b:_IF,c:_Hg,d:_HB,e:_HW,f:_Ih,g:_VP,h:_VU},_W0=function(_W1,_W2,_W3,_W4,_W5){while(1){var _W6=E(_W5);if(!_W6._){var _W7=_W6.c,_W8=_W6.d,_W9=E(_W6.b),_Wa=E(_W9.a);if(_W1>=_Wa){if(_W1!=_Wa){_W2=_;_W5=_W8;continue;}else{var _Wb=E(_W9.b);if(_W3>=_Wb){if(_W3!=_Wb){_W2=_;_W5=_W8;continue;}else{var _Wc=E(_W9.c);if(_W4>=_Wc){if(_W4!=_Wc){_W2=_;_W5=_W8;continue;}else{return true;}}else{_W2=_;_W5=_W7;continue;}}}else{_W2=_;_W5=_W7;continue;}}}else{_W2=_;_W5=_W7;continue;}}else{return false;}}},_Wd=function(_We,_Wf,_Wg,_Wh,_Wi){while(1){var _Wj=E(_Wi);if(!_Wj._){var _Wk=_Wj.c,_Wl=_Wj.d,_Wm=E(_Wj.b),_Wn=E(_Wm.a);if(_We>=_Wn){if(_We!=_Wn){_Wf=_;_Wi=_Wl;continue;}else{var _Wo=E(_Wm.b);if(_Wg>=_Wo){if(_Wg!=_Wo){_Wf=_;_Wi=_Wl;continue;}else{var _Wp=E(_Wh),_Wq=E(_Wm.c);if(_Wp>=_Wq){if(_Wp!=_Wq){return new F(function(){return _W0(_We,_,_Wg,_Wp,_Wl);});}else{return true;}}else{return new F(function(){return _W0(_We,_,_Wg,_Wp,_Wk);});}}}else{_Wf=_;_Wi=_Wk;continue;}}}else{_Wf=_;_Wi=_Wk;continue;}}else{return false;}}},_Wr=function(_Ws,_Wt,_Wu,_Wv,_Ww){while(1){var _Wx=E(_Ww);if(!_Wx._){var _Wy=_Wx.c,_Wz=_Wx.d,_WA=E(_Wx.b),_WB=E(_WA.a);if(_Ws>=_WB){if(_Ws!=_WB){_Wt=_;_Ww=_Wz;continue;}else{var _WC=E(_Wu),_WD=E(_WA.b);if(_WC>=_WD){if(_WC!=_WD){return new F(function(){return _Wd(_Ws,_,_WC,_Wv,_Wz);});}else{var _WE=E(_Wv),_WF=E(_WA.c);if(_WE>=_WF){if(_WE!=_WF){return new F(function(){return _W0(_Ws,_,_WC,_WE,_Wz);});}else{return true;}}else{return new F(function(){return _W0(_Ws,_,_WC,_WE,_Wy);});}}}else{return new F(function(){return _Wd(_Ws,_,_WC,_Wv,_Wy);});}}}else{_Wt=_;_Ww=_Wy;continue;}}else{return false;}}},_WG=function(_WH,_WI,_WJ,_WK){var _WL=E(_WK);if(!_WL._){var _WM=_WL.c,_WN=_WL.d,_WO=E(_WL.b),_WP=E(_WH),_WQ=E(_WO.a);if(_WP>=_WQ){if(_WP!=_WQ){return new F(function(){return _Wr(_WP,_,_WI,_WJ,_WN);});}else{var _WR=E(_WI),_WS=E(_WO.b);if(_WR>=_WS){if(_WR!=_WS){return new F(function(){return _Wd(_WP,_,_WR,_WJ,_WN);});}else{var _WT=E(_WJ),_WU=E(_WO.c);if(_WT>=_WU){if(_WT!=_WU){return new F(function(){return _W0(_WP,_,_WR,_WT,_WN);});}else{return true;}}else{return new F(function(){return _W0(_WP,_,_WR,_WT,_WM);});}}}else{return new F(function(){return _Wd(_WP,_,_WR,_WJ,_WM);});}}}else{return new F(function(){return _Wr(_WP,_,_WI,_WJ,_WM);});}}else{return false;}},_WV=function(_WW,_WX,_WY,_WZ,_X0){var _X1=E(_X0);if(!_X1._){if(E(_X1.b)>E(_WX)){return false;}else{return new F(function(){return _WG(_WY,_WZ,_X1.a,E(_WW).b);});}}else{return false;}},_X2=function(_X3,_X4,_X5,_X6,_X7){var _X8=E(_X7);if(!_X8._){var _X9=new T(function(){var _Xa=B(_X2(_X8.a,_X8.b,_X8.c,_X8.d,_X8.e));return new T2(0,_Xa.a,_Xa.b);});return new T2(0,new T(function(){return E(E(_X9).a);}),new T(function(){return B(_X(_X4,_X5,_X6,E(_X9).b));}));}else{return new T2(0,new T2(0,_X4,_X5),_X6);}},_Xb=function(_Xc,_Xd,_Xe,_Xf,_Xg){var _Xh=E(_Xf);if(!_Xh._){var _Xi=new T(function(){var _Xj=B(_Xb(_Xh.a,_Xh.b,_Xh.c,_Xh.d,_Xh.e));return new T2(0,_Xj.a,_Xj.b);});return new T2(0,new T(function(){return E(E(_Xi).a);}),new T(function(){return B(_6(_Xd,_Xe,E(_Xi).b,_Xg));}));}else{return new T2(0,new T2(0,_Xd,_Xe),_Xg);}},_Xk=function(_Xl,_Xm){var _Xn=E(_Xl);if(!_Xn._){var _Xo=_Xn.a,_Xp=E(_Xm);if(!_Xp._){var _Xq=_Xp.a;if(_Xo<=_Xq){var _Xr=B(_Xb(_Xq,_Xp.b,_Xp.c,_Xp.d,_Xp.e)),_Xs=E(_Xr.a);return new F(function(){return _X(_Xs.a,_Xs.b,_Xn,_Xr.b);});}else{var _Xt=B(_X2(_Xo,_Xn.b,_Xn.c,_Xn.d,_Xn.e)),_Xu=E(_Xt.a);return new F(function(){return _6(_Xu.a,_Xu.b,_Xt.b,_Xp);});}}else{return E(_Xn);}}else{return E(_Xm);}},_Xv=function(_Xw,_Xx,_Xy,_Xz,_XA,_XB){var _XC=E(_Xw);if(!_XC._){var _XD=_XC.a,_XE=_XC.b,_XF=_XC.c,_XG=_XC.d,_XH=_XC.e;if((imul(3,_XD)|0)>=_Xx){if((imul(3,_Xx)|0)>=_XD){return new F(function(){return _Xk(_XC,new T5(0,_Xx,E(_Xy),_Xz,E(_XA),E(_XB)));});}else{return new F(function(){return _6(_XE,_XF,_XG,B(_Xv(_XH,_Xx,_Xy,_Xz,_XA,_XB)));});}}else{return new F(function(){return _X(_Xy,_Xz,B(_XI(_XD,_XE,_XF,_XG,_XH,_XA)),_XB);});}}else{return new T5(0,_Xx,E(_Xy),_Xz,E(_XA),E(_XB));}},_XI=function(_XJ,_XK,_XL,_XM,_XN,_XO){var _XP=E(_XO);if(!_XP._){var _XQ=_XP.a,_XR=_XP.b,_XS=_XP.c,_XT=_XP.d,_XU=_XP.e;if((imul(3,_XJ)|0)>=_XQ){if((imul(3,_XQ)|0)>=_XJ){return new F(function(){return _Xk(new T5(0,_XJ,E(_XK),_XL,E(_XM),E(_XN)),_XP);});}else{return new F(function(){return _6(_XK,_XL,_XM,B(_Xv(_XN,_XQ,_XR,_XS,_XT,_XU)));});}}else{return new F(function(){return _X(_XR,_XS,B(_XI(_XJ,_XK,_XL,_XM,_XN,_XT)),_XU);});}}else{return new T5(0,_XJ,E(_XK),_XL,E(_XM),E(_XN));}},_XV=function(_XW,_XX){var _XY=E(_XW);if(!_XY._){var _XZ=_XY.a,_Y0=_XY.b,_Y1=_XY.c,_Y2=_XY.d,_Y3=_XY.e,_Y4=E(_XX);if(!_Y4._){var _Y5=_Y4.a,_Y6=_Y4.b,_Y7=_Y4.c,_Y8=_Y4.d,_Y9=_Y4.e;if((imul(3,_XZ)|0)>=_Y5){if((imul(3,_Y5)|0)>=_XZ){return new F(function(){return _Xk(_XY,_Y4);});}else{return new F(function(){return _6(_Y0,_Y1,_Y2,B(_Xv(_Y3,_Y5,_Y6,_Y7,_Y8,_Y9)));});}}else{return new F(function(){return _X(_Y6,_Y7,B(_XI(_XZ,_Y0,_Y1,_Y2,_Y3,_Y8)),_Y9);});}}else{return E(_XY);}}else{return E(_XX);}},_Ya=function(_Yb,_Yc){var _Yd=E(_Yc);if(!_Yd._){var _Ye=_Yd.b,_Yf=_Yd.c,_Yg=B(_Ya(_Yb,_Yd.d)),_Yh=_Yg.a,_Yi=_Yg.b,_Yj=B(_Ya(_Yb,_Yd.e)),_Yk=_Yj.a,_Yl=_Yj.b;return (!B(A2(_Yb,_Ye,_Yf)))?new T2(0,B(_XV(_Yh,_Yk)),B(_2h(_Ye,_Yf,_Yi,_Yl))):new T2(0,B(_2h(_Ye,_Yf,_Yh,_Yk)),B(_XV(_Yi,_Yl)));}else{return new T2(0,_0,_0);}},_Ym=function(_Yn,_Yo){while(1){var _Yp=B((function(_Yq,_Yr){var _Ys=E(_Yr);if(!_Ys._){var _Yt=_Ys.e,_Yu=new T(function(){var _Yv=E(_Ys.c),_Yw=E(_Yv.b);if(!_Yw._){return new T2(1,new T3(5,_Ys.b,_Yv.a,_Yw.a),new T(function(){return B(_Ym(_Yq,_Yt));}));}else{return B(_Ym(_Yq,_Yt));}},1);_Yn=_Yu;_Yo=_Ys.d;return __continue;}else{return E(_Yq);}})(_Yn,_Yo));if(_Yp!=__continue){return _Yp;}}},_Yx=function(_Yy,_Yz){var _YA=E(_Yz);return (_YA._==0)?new T5(0,_YA.a,E(_YA.b),new T(function(){return B(A1(_Yy,_YA.c));}),E(B(_Yx(_Yy,_YA.d))),E(B(_Yx(_Yy,_YA.e)))):new T0(1);},_YB=new T0(1),_YC=function(_YD){var _YE=E(_YD),_YF=E(_YE.b);return new T2(0,_YE.a,_YB);},_YG=function(_YH,_YI,_YJ){var _YK=new T(function(){var _YL=new T(function(){return E(E(_YJ).b);}),_YM=B(_Ya(function(_YN,_YO){var _YP=E(_YO);return new F(function(){return _WV(_YH,_YL,_YN,_YP.a,_YP.b);});},_YI));return new T2(0,_YM.a,_YM.b);}),_YQ=new T(function(){return E(E(_YK).a);});return new T2(0,new T(function(){var _YR=B(_Yx(_YC,_YQ));if(!_YR._){var _YS=E(E(_YK).b);if(!_YS._){return B(_Pv(_VZ,_O8,_O8,_YR.a,_YR.b,_YR.c,_YR.d,_YR.e,_YS.a,_YS.b,_YS.c,_YS.d,_YS.e));}else{return E(_YR);}}else{return E(E(_YK).b);}}),new T(function(){return B(_Ym(_1,_YQ));}));},_YT=function(_YU,_YV,_YW,_YX){while(1){var _YY=E(_YX);if(!_YY._){var _YZ=_YY.d,_Z0=_YY.e,_Z1=E(_YY.b),_Z2=E(_Z1.a);if(_YU>=_Z2){if(_YU!=_Z2){_YV=_;_YX=_Z0;continue;}else{var _Z3=E(_Z1.b);if(_YW>=_Z3){if(_YW!=_Z3){_YV=_;_YX=_Z0;continue;}else{return true;}}else{_YV=_;_YX=_YZ;continue;}}}else{_YV=_;_YX=_YZ;continue;}}else{return false;}}},_Z4=function(_Z5,_Z6,_Z7,_Z8){while(1){var _Z9=E(_Z8);if(!_Z9._){var _Za=_Z9.d,_Zb=_Z9.e,_Zc=E(_Z9.b),_Zd=E(_Zc.a);if(_Z5>=_Zd){if(_Z5!=_Zd){_Z6=_;_Z8=_Zb;continue;}else{var _Ze=E(_Z7),_Zf=E(_Zc.b);if(_Ze>=_Zf){if(_Ze!=_Zf){return new F(function(){return _YT(_Z5,_,_Ze,_Zb);});}else{return true;}}else{return new F(function(){return _YT(_Z5,_,_Ze,_Za);});}}}else{_Z6=_;_Z8=_Za;continue;}}else{return false;}}},_Zg=function(_Zh,_Zi,_Zj,_Zk,_Zl){var _Zm=E(_Zl);if(!_Zm._){var _Zn=_Zm.c,_Zo=_Zm.d,_Zp=_Zm.e,_Zq=E(_Zm.b),_Zr=E(_Zq.a);if(_Zh>=_Zr){if(_Zh!=_Zr){return new F(function(){return _6(_Zq,_Zn,_Zo,B(_Zg(_Zh,_,_Zj,_Zk,_Zp)));});}else{var _Zs=E(_Zq.b);if(_Zj>=_Zs){if(_Zj!=_Zs){return new F(function(){return _6(_Zq,_Zn,_Zo,B(_Zg(_Zh,_,_Zj,_Zk,_Zp)));});}else{return new T5(0,_Zm.a,E(new T2(0,_Zh,_Zj)),_Zk,E(_Zo),E(_Zp));}}else{return new F(function(){return _X(_Zq,_Zn,B(_Zg(_Zh,_,_Zj,_Zk,_Zo)),_Zp);});}}}else{return new F(function(){return _X(_Zq,_Zn,B(_Zg(_Zh,_,_Zj,_Zk,_Zo)),_Zp);});}}else{return new T5(0,1,E(new T2(0,_Zh,_Zj)),_Zk,E(_0),E(_0));}},_Zt=function(_Zu,_Zv,_Zw,_Zx,_Zy){var _Zz=E(_Zy);if(!_Zz._){var _ZA=_Zz.c,_ZB=_Zz.d,_ZC=_Zz.e,_ZD=E(_Zz.b),_ZE=E(_ZD.a);if(_Zu>=_ZE){if(_Zu!=_ZE){return new F(function(){return _6(_ZD,_ZA,_ZB,B(_Zt(_Zu,_,_Zw,_Zx,_ZC)));});}else{var _ZF=E(_Zw),_ZG=E(_ZD.b);if(_ZF>=_ZG){if(_ZF!=_ZG){return new F(function(){return _6(_ZD,_ZA,_ZB,B(_Zg(_Zu,_,_ZF,_Zx,_ZC)));});}else{return new T5(0,_Zz.a,E(new T2(0,_Zu,_ZF)),_Zx,E(_ZB),E(_ZC));}}else{return new F(function(){return _X(_ZD,_ZA,B(_Zg(_Zu,_,_ZF,_Zx,_ZB)),_ZC);});}}}else{return new F(function(){return _X(_ZD,_ZA,B(_Zt(_Zu,_,_Zw,_Zx,_ZB)),_ZC);});}}else{return new T5(0,1,E(new T2(0,_Zu,_Zw)),_Zx,E(_0),E(_0));}},_ZH=function(_ZI,_ZJ,_ZK,_ZL){var _ZM=E(_ZL);if(!_ZM._){var _ZN=_ZM.c,_ZO=_ZM.d,_ZP=_ZM.e,_ZQ=E(_ZM.b),_ZR=E(_ZI),_ZS=E(_ZQ.a);if(_ZR>=_ZS){if(_ZR!=_ZS){return new F(function(){return _6(_ZQ,_ZN,_ZO,B(_Zt(_ZR,_,_ZJ,_ZK,_ZP)));});}else{var _ZT=E(_ZJ),_ZU=E(_ZQ.b);if(_ZT>=_ZU){if(_ZT!=_ZU){return new F(function(){return _6(_ZQ,_ZN,_ZO,B(_Zg(_ZR,_,_ZT,_ZK,_ZP)));});}else{return new T5(0,_ZM.a,E(new T2(0,_ZR,_ZT)),_ZK,E(_ZO),E(_ZP));}}else{return new F(function(){return _X(_ZQ,_ZN,B(_Zg(_ZR,_,_ZT,_ZK,_ZO)),_ZP);});}}}else{return new F(function(){return _X(_ZQ,_ZN,B(_Zt(_ZR,_,_ZJ,_ZK,_ZO)),_ZP);});}}else{return new T5(0,1,E(new T2(0,_ZI,_ZJ)),_ZK,E(_0),E(_0));}},_ZV=function(_ZW,_ZX,_ZY){while(1){var _ZZ=B((function(_100,_101,_102){var _103=E(_102);if(!_103._){var _104=_103.c,_105=_103.e,_106=E(_103.b),_107=_106.a,_108=_106.b,_109=B(_ZV(_100,_101,_103.d)),_10a=_109.a,_10b=_109.b,_10c=function(_10d){return new F(function(){return _ZV(new T(function(){return B(_ZH(_107,_108,_104,_10a));}),new T2(1,new T3(7,_107,_108,_104),_10b),_105);});},_10e=E(_10a);if(!_10e._){var _10f=_10e.d,_10g=_10e.e,_10h=E(_10e.b),_10i=E(_107),_10j=E(_10h.a);if(_10i>=_10j){if(_10i!=_10j){if(!B(_Z4(_10i,_,_108,_10g))){return new F(function(){return _10c(_);});}else{_ZW=_10e;_ZX=_10b;_ZY=_105;return __continue;}}else{var _10k=E(_108),_10l=E(_10h.b);if(_10k>=_10l){if(_10k!=_10l){if(!B(_YT(_10i,_,_10k,_10g))){return new F(function(){return _10c(_);});}else{_ZW=_10e;_ZX=_10b;_ZY=_105;return __continue;}}else{_ZW=_10e;_ZX=_10b;_ZY=_105;return __continue;}}else{if(!B(_YT(_10i,_,_10k,_10f))){return new F(function(){return _10c(_);});}else{_ZW=_10e;_ZX=_10b;_ZY=_105;return __continue;}}}}else{if(!B(_Z4(_10i,_,_108,_10f))){return new F(function(){return _10c(_);});}else{_ZW=_10e;_ZX=_10b;_ZY=_105;return __continue;}}}else{return new F(function(){return _10c(_);});}}else{return new T2(0,_100,_101);}})(_ZW,_ZX,_ZY));if(_ZZ!=__continue){return _ZZ;}}},_10m=function(_10n,_10o){while(1){var _10p=E(_10n);switch(_10p._){case 0:var _10q=E(_10o);if(!_10q._){return new F(function(){return _GY(_10p.a,_10q.a);});}else{return false;}break;case 1:var _10r=E(_10o);if(_10r._==1){if(!B(_10m(_10p.a,_10r.a))){return false;}else{_10n=_10p.b;_10o=_10r.b;continue;}}else{return false;}break;case 2:var _10s=E(_10o);if(_10s._==2){return new F(function(){return _GY(_10p.a,_10s.a);});}else{return false;}break;default:var _10t=E(_10o);if(_10t._==3){if(E(_10p.a)!=E(_10t.a)){return false;}else{if(E(_10p.b)!=E(_10t.b)){return false;}else{_10n=_10p.c;_10o=_10t.c;continue;}}}else{return false;}}}},_10u=function(_10v,_10w){while(1){var _10x=E(_10v);switch(_10x._){case 0:var _10y=E(_10w);if(!_10y._){return new F(function(){return _GY(_10x.a,_10y.a);});}else{return false;}break;case 1:var _10z=E(_10w);if(_10z._==1){if(!B(_10u(_10x.a,_10z.a))){return false;}else{_10v=_10x.b;_10w=_10z.b;continue;}}else{return false;}break;case 2:var _10A=E(_10w);if(_10A._==2){if(!B(_10u(_10x.a,_10A.a))){return false;}else{_10v=_10x.b;_10w=_10A.b;continue;}}else{return false;}break;case 3:var _10B=E(_10w);if(_10B._==3){_10v=_10x.a;_10w=_10B.a;continue;}else{return false;}break;case 4:var _10C=E(_10w);if(_10C._==4){if(E(_10x.a)!=E(_10C.a)){return false;}else{if(E(_10x.b)!=E(_10C.b)){return false;}else{return new F(function(){return _GY(_10x.c,_10C.c);});}}}else{return false;}break;case 5:var _10D=E(_10w);if(_10D._==5){if(E(_10x.a)!=E(_10D.a)){return false;}else{return new F(function(){return _GY(_10x.b,_10D.b);});}}else{return false;}break;case 6:var _10E=E(_10w);if(_10E._==6){if(!B(_10m(_10x.a,_10E.a))){return false;}else{return new F(function(){return _10m(_10x.b,_10E.b);});}}else{return false;}break;case 7:return (E(_10w)._==7)?true:false;default:return (E(_10w)._==8)?true:false;}}},_10F=function(_10G,_10H){while(1){var _10I=E(_10G);switch(_10I._){case 0:return (E(_10H)._==0)?true:false;case 1:var _10J=E(_10H);if(_10J._==1){if(E(_10I.a)!=E(_10J.a)){return false;}else{if(E(_10I.b)!=E(_10J.b)){return false;}else{if(!B(_10m(_10I.c,_10J.c))){return false;}else{if(E(_10I.d)!=E(_10J.d)){return false;}else{if(E(_10I.e)!=E(_10J.e)){return false;}else{if(!B(_10F(_10I.f,_10J.f))){return false;}else{_10G=_10I.g;_10H=_10J.g;continue;}}}}}}}else{return false;}break;case 2:var _10K=E(_10H);if(_10K._==2){if(E(_10I.a)!=E(_10K.a)){return false;}else{_10G=_10I.b;_10H=_10K.b;continue;}}else{return false;}break;case 3:var _10L=E(_10H);if(_10L._==3){if(E(_10I.a)!=E(_10L.a)){return false;}else{if(E(_10I.b)!=E(_10L.b)){return false;}else{if(E(_10I.c)!=E(_10L.c)){return false;}else{if(!B(_10m(_10I.d,_10L.d))){return false;}else{if(E(_10I.e)!=E(_10L.e)){return false;}else{_10G=_10I.f;_10H=_10L.f;continue;}}}}}}else{return false;}break;case 4:var _10M=E(_10H);if(_10M._==4){if(!B(_10F(_10I.a,_10M.a))){return false;}else{_10G=_10I.b;_10H=_10M.b;continue;}}else{return false;}break;case 5:var _10N=E(_10H);if(_10N._==5){if(!B(_10u(_10I.a,_10N.a))){return false;}else{if(!B(_10F(_10I.b,_10N.b))){return false;}else{_10G=_10I.c;_10H=_10N.c;continue;}}}else{return false;}break;default:var _10O=E(_10H);if(_10O._==6){if(!B(_10u(_10I.a,_10O.a))){return false;}else{if(E(_10I.b)!=E(_10O.b)){return false;}else{if(!B(_10F(_10I.c,_10O.c))){return false;}else{_10G=_10I.d;_10H=_10O.d;continue;}}}}else{return false;}}}},_10P=new T2(0,_GY,_VL),_10Q=function(_10R,_10S,_10T,_10U,_10V,_10W){return (!B(A3(_pR,_10R,_10T,_10V)))?true:(!B(A3(_pR,_10S,_10U,_10W)))?true:false;},_10X=function(_10Y,_10Z,_110,_111){var _112=E(_110),_113=E(_111);return new F(function(){return _10Q(_10Y,_10Z,_112.a,_112.b,_113.a,_113.b);});},_114=function(_115,_116,_117,_118,_119,_11a){if(!B(A3(_pR,_115,_117,_119))){return false;}else{return new F(function(){return A3(_pR,_116,_118,_11a);});}},_11b=function(_11c,_11d,_11e,_11f){var _11g=E(_11e),_11h=E(_11f);return new F(function(){return _114(_11c,_11d,_11g.a,_11g.b,_11h.a,_11h.b);});},_11i=function(_11j,_11k){return new T2(0,function(_11l,_11m){return new F(function(){return _11b(_11j,_11k,_11l,_11m);});},function(_11l,_11m){return new F(function(){return _10X(_11j,_11k,_11l,_11m);});});},_11n=function(_11o,_11p,_11q){while(1){var _11r=E(_11p);if(!_11r._){return (E(_11q)._==0)?true:false;}else{var _11s=E(_11q);if(!_11s._){return false;}else{if(!B(A3(_pR,_11o,_11r.a,_11s.a))){return false;}else{_11p=_11r.b;_11q=_11s.b;continue;}}}}},_11t=function(_11u,_11v){var _11w=new T(function(){return B(_11i(_11u,_11v));}),_11x=function(_11y,_11z){var _11A=function(_11B){var _11C=function(_11D){if(_11B!=_11D){return false;}else{return new F(function(){return _11n(_11w,B(_hc(_1,_11y)),B(_hc(_1,_11z)));});}},_11E=E(_11z);if(!_11E._){return new F(function(){return _11C(_11E.a);});}else{return new F(function(){return _11C(0);});}},_11F=E(_11y);if(!_11F._){return new F(function(){return _11A(_11F.a);});}else{return new F(function(){return _11A(0);});}};return E(_11x);},_11G=new T(function(){return B(_11t(_JH,_10P));}),_11H=function(_11I,_11J){var _11K=E(_11I);if(!_11K._){var _11L=E(_11J);if(!_11L._){if(E(_11K.a)!=E(_11L.a)){return false;}else{return new F(function(){return _GY(_11K.b,_11L.b);});}}else{return false;}}else{return (E(_11J)._==0)?false:true;}},_11M=function(_11N,_11O,_11P,_11Q){if(_11N!=_11P){return false;}else{return new F(function(){return _11H(_11O,_11Q);});}},_11R=function(_11S,_11T){var _11U=E(_11S),_11V=E(_11T);return new F(function(){return _11M(E(_11U.a),_11U.b,E(_11V.a),_11V.b);});},_11W=function(_11X,_11Y,_11Z,_120){if(_11X!=_11Z){return true;}else{var _121=E(_11Y);if(!_121._){var _122=E(_120);return (_122._==0)?(E(_121.a)!=E(_122.a))?true:(E(_121.b)!=E(_122.b))?true:false:true;}else{return (E(_120)._==0)?true:false;}}},_123=function(_124,_125){var _126=E(_124),_127=E(_125);return new F(function(){return _11W(E(_126.a),_126.b,E(_127.a),_127.b);});},_128=new T2(0,_11R,_123),_129=new T(function(){return B(_11t(_VO,_128));}),_12a=function(_12b,_12c,_12d,_12e){while(1){var _12f=E(_12e);if(!_12f._){var _12g=_12f.d,_12h=_12f.e,_12i=E(_12f.b),_12j=E(_12i.a);if(_12b>=_12j){if(_12b!=_12j){_12c=_;_12e=_12h;continue;}else{var _12k=E(_12i.b);if(_12d>=_12k){if(_12d!=_12k){_12c=_;_12e=_12h;continue;}else{return new T1(1,_12f.c);}}else{_12c=_;_12e=_12g;continue;}}}else{_12c=_;_12e=_12g;continue;}}else{return __Z;}}},_12l=function(_12m,_12n,_12o,_12p){while(1){var _12q=E(_12p);if(!_12q._){var _12r=_12q.d,_12s=_12q.e,_12t=E(_12q.b),_12u=E(_12t.a);if(_12m>=_12u){if(_12m!=_12u){_12n=_;_12p=_12s;continue;}else{var _12v=E(_12o),_12w=E(_12t.b);if(_12v>=_12w){if(_12v!=_12w){return new F(function(){return _12a(_12m,_,_12v,_12s);});}else{return new T1(1,_12q.c);}}else{return new F(function(){return _12a(_12m,_,_12v,_12r);});}}}else{_12n=_;_12p=_12r;continue;}}else{return __Z;}}},_12x=function(_12y,_12z,_12A,_12B,_12C){while(1){var _12D=E(_12C);if(!_12D._){var _12E=_12D.c,_12F=_12D.d,_12G=E(_12D.b),_12H=E(_12y),_12I=E(_12G.a);if(_12H>=_12I){if(_12H!=_12I){_12y=_12H;_12C=_12F;continue;}else{var _12J=E(_12z),_12K=E(_12G.b);if(_12J>=_12K){if(_12J!=_12K){_12y=_12H;_12z=_12J;_12C=_12F;continue;}else{var _12L=E(_12A),_12M=E(_12G.c);if(_12L>=_12M){if(_12L!=_12M){_12y=_12H;_12z=_12J;_12A=_12L;_12C=_12F;continue;}else{var _12N=E(_12G.d);if(_12B>=_12N){if(_12B!=_12N){_12y=_12H;_12z=_12J;_12A=_12L;_12C=_12F;continue;}else{return true;}}else{_12y=_12H;_12z=_12J;_12A=_12L;_12C=_12E;continue;}}}else{_12y=_12H;_12z=_12J;_12A=_12L;_12C=_12E;continue;}}}else{_12y=_12H;_12z=_12J;_12C=_12E;continue;}}}else{_12y=_12H;_12C=_12E;continue;}}else{return false;}}},_12O=function(_12P,_12Q){return E(_12P)+E(_12Q)|0;},_12R=function(_12S,_12T,_12U){var _12V=function(_12W,_12X){while(1){var _12Y=B((function(_12Z,_130){var _131=E(_130);if(!_131._){var _132=new T(function(){return B(_12V(_12Z,_131.e));}),_133=function(_134){var _135=E(_131.c),_136=E(_135.b);if(!_136._){if(E(_135.a)!=E(_12T)){return new F(function(){return A1(_132,_134);});}else{if(E(_136.b)>E(_12U)){return new F(function(){return A1(_132,new T(function(){return B(_12O(_134,_136.a));}));});}else{return new F(function(){return A1(_132,_134);});}}}else{return new F(function(){return A1(_132,_134);});}};_12W=_133;_12X=_131.d;return __continue;}else{return E(_12Z);}})(_12W,_12X));if(_12Y!=__continue){return _12Y;}}};return new F(function(){return A3(_12V,_na,_12S,_Rt);});},_137=__Z,_138=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_139=new T(function(){return B(err(_138));}),_13a=function(_13b,_13c){var _13d=E(_13c);if(!_13d._){return (E(_13b)==0)?__Z:E(_139);}else{var _13e=_13d.b,_13f=E(_13d.a),_13g=_13f.a,_13h=E(_13f.b),_13i=_13h.a,_13j=E(_13h.b);if(!_13j._){var _13k=_13j.b,_13l=E(_13j.a);return (_13b>_13l)?(_13l>=_13b)?E(_13e):new T2(1,new T2(0,_13g,new T2(0,_13i,new T2(0,_Rt,_13k))),new T(function(){return B(_13a(_13b-_13l|0,_13e));})):new T2(1,new T2(0,_13g,new T2(0,_13i,new T2(0,_13l-_13b|0,_13k))),_1);}else{return E(_13e);}}},_13m=function(_13n,_13o){var _13p=E(_13o);if(!_13p._){return (E(_13n)==0)?__Z:E(_139);}else{var _13q=_13p.b,_13r=E(_13p.a),_13s=_13r.a,_13t=E(_13r.b),_13u=_13t.a,_13v=E(_13t.b);if(!_13v._){var _13w=_13v.b,_13x=E(_13n),_13y=E(_13v.a);return (_13x>_13y)?(_13y>=_13x)?E(_13q):new T2(1,new T2(0,_13s,new T2(0,_13u,new T2(0,_Rt,_13w))),new T(function(){return B(_13a(_13x-_13y|0,_13q));})):new T2(1,new T2(0,_13s,new T2(0,_13u,new T2(0,_13y-_13x|0,_13w))),_1);}else{return E(_13q);}}},_13z=function(_13A,_13B){var _13C=E(_13B);if(!_13C._){var _13D=_13C.b,_13E=_13C.c,_13F=_13C.d,_13G=_13C.e;if(!B(A2(_13A,_13D,_13E))){return new F(function(){return _XV(B(_13z(_13A,_13F)),B(_13z(_13A,_13G)));});}else{return new F(function(){return _2h(_13D,_13E,B(_13z(_13A,_13F)),B(_13z(_13A,_13G)));});}}else{return new T0(1);}},_13H=function(_13I,_13J){var _13K=E(_13I);if(!_13K._){var _13L=E(_13J);if(!_13L._){return new F(function(){return _IF(_13K.b,_13L.b);});}else{return 0;}}else{return (E(_13J)._==0)?2:1;}},_13M=function(_13N,_13O){return new F(function(){return _13H(E(E(_13N).b).b,E(E(_13O).b).b);});},_13P=new T2(1,_1,_1),_13Q=function(_13R,_13S){var _13T=function(_13U,_13V){var _13W=E(_13U);if(!_13W._){return E(_13V);}else{var _13X=_13W.a,_13Y=E(_13V);if(!_13Y._){return E(_13W);}else{var _13Z=_13Y.a;return (B(A2(_13R,_13X,_13Z))==2)?new T2(1,_13Z,new T(function(){return B(_13T(_13W,_13Y.b));})):new T2(1,_13X,new T(function(){return B(_13T(_13W.b,_13Y));}));}}},_140=function(_141){var _142=E(_141);if(!_142._){return __Z;}else{var _143=E(_142.b);return (_143._==0)?E(_142):new T2(1,new T(function(){return B(_13T(_142.a,_143.a));}),new T(function(){return B(_140(_143.b));}));}},_144=new T(function(){return B(_145(B(_140(_1))));}),_145=function(_146){while(1){var _147=E(_146);if(!_147._){return E(_144);}else{if(!E(_147.b)._){return E(_147.a);}else{_146=B(_140(_147));continue;}}}},_148=new T(function(){return B(_149(_1));}),_14a=function(_14b,_14c,_14d){while(1){var _14e=B((function(_14f,_14g,_14h){var _14i=E(_14h);if(!_14i._){return new T2(1,new T2(1,_14f,_14g),_148);}else{var _14j=_14i.a;if(B(A2(_13R,_14f,_14j))==2){var _14k=new T2(1,_14f,_14g);_14b=_14j;_14c=_14k;_14d=_14i.b;return __continue;}else{return new T2(1,new T2(1,_14f,_14g),new T(function(){return B(_149(_14i));}));}}})(_14b,_14c,_14d));if(_14e!=__continue){return _14e;}}},_14l=function(_14m,_14n,_14o){while(1){var _14p=B((function(_14q,_14r,_14s){var _14t=E(_14s);if(!_14t._){return new T2(1,new T(function(){return B(A1(_14r,new T2(1,_14q,_1)));}),_148);}else{var _14u=_14t.a,_14v=_14t.b;switch(B(A2(_13R,_14q,_14u))){case 0:_14m=_14u;_14n=function(_14w){return new F(function(){return A1(_14r,new T2(1,_14q,_14w));});};_14o=_14v;return __continue;case 1:_14m=_14u;_14n=function(_14x){return new F(function(){return A1(_14r,new T2(1,_14q,_14x));});};_14o=_14v;return __continue;default:return new T2(1,new T(function(){return B(A1(_14r,new T2(1,_14q,_1)));}),new T(function(){return B(_149(_14t));}));}}})(_14m,_14n,_14o));if(_14p!=__continue){return _14p;}}},_149=function(_14y){var _14z=E(_14y);if(!_14z._){return E(_13P);}else{var _14A=_14z.a,_14B=E(_14z.b);if(!_14B._){return new T2(1,_14z,_1);}else{var _14C=_14B.a,_14D=_14B.b;if(B(A2(_13R,_14A,_14C))==2){return new F(function(){return _14a(_14C,new T2(1,_14A,_1),_14D);});}else{return new F(function(){return _14l(_14C,function(_14E){return new T2(1,_14A,_14E);},_14D);});}}}};return new F(function(){return _145(B(_149(_13S)));});},_14F=function(_14G,_14H,_14I){var _14J=B(_EV(B(_13m(_14H,B(_13Q(_13M,B(_hc(_1,B(_13z(function(_14K,_14L){return new F(function(){return A1(_14G,_14L);});},_14I))))))))));if(!_14J._){var _14M=E(_14I);if(!_14M._){return new F(function(){return _Pv(_VZ,_O8,_O8,_14J.a,_14J.b,_14J.c,_14J.d,_14J.e,_14M.a,_14M.b,_14M.c,_14M.d,_14M.e);});}else{return E(_14J);}}else{return E(_14I);}},_14N=function(_14O,_14P,_14Q){var _14R=E(_14Q);if(!_14R._){var _14S=_14R.d,_14T=_14R.e,_14U=E(_14R.b),_14V=E(_14O),_14W=E(_14U.a);if(_14V>=_14W){if(_14V!=_14W){return new F(function(){return _Z4(_14V,_,_14P,_14T);});}else{var _14X=E(_14P),_14Y=E(_14U.b);if(_14X>=_14Y){if(_14X!=_14Y){return new F(function(){return _YT(_14V,_,_14X,_14T);});}else{return true;}}else{return new F(function(){return _YT(_14V,_,_14X,_14S);});}}}else{return new F(function(){return _Z4(_14V,_,_14P,_14S);});}}else{return false;}},_14Z=function(_150,_151,_152){while(1){var _153=E(_151);switch(_153._){case 0:return (E(_153.a)>E(E(_152).b))?true:false;case 1:if(!B(_14Z(_150,_153.a,_152))){return false;}else{_151=_153.b;continue;}break;case 2:if(!B(_14Z(_150,_153.a,_152))){_151=_153.b;continue;}else{return true;}break;case 3:return (!B(_14Z(_150,_153.a,_152)))?true:false;case 4:var _154=_153.b,_155=_153.c,_156=E(E(_150).b);if(!_156._){var _157=_156.d,_158=_156.e,_159=E(_156.b),_15a=E(_153.a),_15b=E(_159.a);if(_15a>=_15b){if(_15a!=_15b){var _15c=B(_RF(_15a,_,_154,_158));if(!_15c._){return false;}else{return new F(function(){return _GY(_15c.a,_155);});}}else{var _15d=E(_154),_15e=E(_159.b);if(_15d>=_15e){if(_15d!=_15e){var _15f=B(_Ru(_15a,_,_15d,_158));if(!_15f._){return false;}else{return new F(function(){return _GY(_15f.a,_155);});}}else{return new F(function(){return _GY(_156.c,_155);});}}else{var _15g=B(_Ru(_15a,_,_15d,_157));if(!_15g._){return false;}else{return new F(function(){return _GY(_15g.a,_155);});}}}}else{var _15h=B(_RF(_15a,_,_154,_157));if(!_15h._){return false;}else{return new F(function(){return _GY(_15h.a,_155);});}}}else{return false;}break;case 5:return new F(function(){return _14N(_153.a,_153.b,E(_150).b);});break;case 6:var _15i=E(_150),_15j=_15i.a,_15k=_15i.b;return B(_RW(_15j,_15k,_153.a))>=B(_RW(_15j,_15k,_153.b));case 7:return true;default:return false;}}},_15l=function(_15m,_15n,_15o,_15p){var _15q=E(_15o);switch(_15q._){case 0:return new T3(0,_15n,_137,_1);case 1:var _15r=_15q.a,_15s=_15q.b,_15t=_15q.g,_15u=E(_15q.e),_15v=E(E(_15p).b),_15w=_15u<=_15v,_15x=new T(function(){var _15y=E(_15n);return B(_RW(_15y.a,_15y.b,_15q.c));}),_15z=new T(function(){return E(_15q.d)<=_15v;}),_15A=new T(function(){return B(_E2(E(_15r),new T2(0,_15s,new T(function(){if(!E(_15w)){if(!E(_15z)){return new T2(0,_15x,_15u);}else{return new T0(1);}}else{return new T0(1);}})),E(_15n).a));});return (!E(_15w))?(!E(_15z))?(!B(_12x(_15r,_15s,_15x,_15u,E(_15m).a)))?new T3(0,_15n,_15q,_1):new T3(0,new T(function(){return new T2(0,_15A,E(_15n).b);}),_15q.f,new T2(1,new T3(3,_15r,_15s,_15x),_1)):new T3(0,new T(function(){return new T2(0,_15A,E(_15n).b);}),_15t,_1):new T3(0,new T(function(){return new T2(0,_15A,E(_15n).b);}),_15t,_1);case 2:var _15B=_15q.b,_15C=E(_15n),_15D=_15C.a,_15E=E(_15q.a),_15F=B(_RR(_15E,_15D));if(!_15F._){return new T3(0,_15C,_15q,_1);}else{var _15G=E(_15F.a),_15H=_15G.a,_15I=E(_15G.b);if(!_15I._){var _15J=_15I.a;return (!B(_Wr(_15E,_,_15H,_15J,E(_15m).b)))?new T3(0,_15C,_15q,_1):new T3(0,new T2(0,new T(function(){return B(_E2(_15E,new T2(0,_15H,_YB),_15D));}),_15C.b),_15B,new T2(1,new T3(4,_15E,_15H,_15J),_1));}else{return new T3(0,_15C,_15B,new T2(1,new T2(6,_15E,_15H),_1));}}break;case 3:var _15K=_15q.a,_15L=_15q.b,_15M=_15q.c,_15N=_15q.d,_15O=_15q.f,_15P=E(E(_15p).b);if(E(_15q.e)>_15P){var _15Q=function(_15R){var _15S=E(_15n),_15T=_15S.a,_15U=_15S.b,_15V=B(_RW(_15T,_15U,_15N));if(E(_15R)!=_15V){return new T3(0,_15S,_15q,_1);}else{if(B(_12R(_15T,_15L,_15P))<_15V){return new T3(0,_15S,_15O,new T2(1,new T4(2,_15K,_15L,_15M,_15V),_1));}else{var _15W=new T(function(){return B(_14F(function(_15X){var _15Y=E(_15X),_15Z=E(_15Y.b);return (_15Z._==0)?(E(_15Y.a)!=E(_15L))?false:(E(_15Z.b)>_15P)?true:false:false;},_15V,_15T));});return new T3(0,new T2(0,_15W,_15U),_15O,new T2(1,new T4(0,_15K,_15L,_15M,_15V),_1));}}},_160=E(E(_15m).c);if(!_160._){var _161=_160.d,_162=_160.e,_163=E(_160.b),_164=E(_15K),_165=E(_163.a);if(_164>=_165){if(_164!=_165){var _166=B(_12l(_164,_,_15M,_162));if(!_166._){return new T3(0,_15n,_15q,_1);}else{return new F(function(){return _15Q(_166.a);});}}else{var _167=E(_15M),_168=E(_163.b);if(_167>=_168){if(_167!=_168){var _169=B(_12a(_164,_,_167,_162));if(!_169._){return new T3(0,_15n,_15q,_1);}else{return new F(function(){return _15Q(_169.a);});}}else{return new F(function(){return _15Q(_160.c);});}}else{var _16a=B(_12a(_164,_,_167,_161));if(!_16a._){return new T3(0,_15n,_15q,_1);}else{return new F(function(){return _15Q(_16a.a);});}}}}else{var _16b=B(_12l(_164,_,_15M,_161));if(!_16b._){return new T3(0,_15n,_15q,_1);}else{return new F(function(){return _15Q(_16b.a);});}}}else{return new T3(0,_15n,_15q,_1);}}else{return new T3(0,_15n,_15O,new T2(1,new T4(1,_15K,_15L,_15M,new T(function(){return B(_Sr(_15n,_15N));})),_1));}break;case 4:var _16c=new T(function(){var _16d=B(_15l(_15m,_15n,_15q.a,_15p));return new T3(0,_16d.a,_16d.b,_16d.c);}),_16e=new T(function(){var _16f=B(_15l(_15m,new T(function(){return E(E(_16c).a);}),_15q.b,_15p));return new T3(0,_16f.a,_16f.b,_16f.c);}),_16g=new T(function(){return B(_hq(E(_16c).c,new T(function(){return E(E(_16e).c);},1)));}),_16h=new T(function(){var _16i=E(_16c).b,_16j=E(_16e).b,_16k=function(_16l){var _16m=E(_16j);switch(_16m._){case 0:return E(_16i);case 1:return new T2(4,_16i,_16m);case 2:return new T2(4,_16i,_16m);case 3:return new T2(4,_16i,_16m);case 4:return new T2(4,_16i,_16m);case 5:return new T2(4,_16i,_16m);default:return new T2(4,_16i,_16m);}};switch(E(_16i)._){case 0:return E(_16j);break;case 1:return B(_16k(_));break;case 2:return B(_16k(_));break;case 3:return B(_16k(_));break;case 4:return B(_16k(_));break;case 5:return B(_16k(_));break;default:return B(_16k(_));}});return new T3(0,new T(function(){return E(E(_16e).a);}),_16h,_16g);case 5:return (!B(_14Z(_15n,_15q.a,_15p)))?new T3(0,_15n,_15q.c,_1):new T3(0,_15n,_15q.b,_1);default:var _16n=E(_15p);return (E(_15q.b)>E(_16n.b))?(!B(_14Z(_15n,_15q.a,_16n)))?new T3(0,_15n,_15q,_1):new T3(0,_15n,_15q.c,_1):new T3(0,_15n,_15q.d,_1);}},_16o=function(_16p,_16q,_16r,_16s,_16t){var _16u=E(_16s);switch(_16u._){case 0:return new T3(0,new T2(0,_16q,_16r),_137,_1);case 1:var _16v=_16u.a,_16w=_16u.b,_16x=_16u.g,_16y=E(_16u.e),_16z=E(E(_16t).b),_16A=_16y<=_16z,_16B=new T(function(){return B(_RW(_16q,_16r,_16u.c));}),_16C=new T(function(){return E(_16u.d)<=_16z;}),_16D=new T(function(){return B(_E2(E(_16v),new T2(0,_16w,new T(function(){if(!E(_16A)){if(!E(_16C)){return new T2(0,_16B,_16y);}else{return new T0(1);}}else{return new T0(1);}})),_16q));});return (!E(_16A))?(!E(_16C))?(!B(_12x(_16v,_16w,_16B,_16y,E(_16p).a)))?new T3(0,new T2(0,_16q,_16r),_16u,_1):new T3(0,new T2(0,_16D,_16r),_16u.f,new T2(1,new T3(3,_16v,_16w,_16B),_1)):new T3(0,new T2(0,_16D,_16r),_16x,_1):new T3(0,new T2(0,_16D,_16r),_16x,_1);case 2:var _16E=_16u.b,_16F=E(_16u.a),_16G=B(_RR(_16F,_16q));if(!_16G._){return new T3(0,new T2(0,_16q,_16r),_16u,_1);}else{var _16H=E(_16G.a),_16I=_16H.a,_16J=E(_16H.b);if(!_16J._){var _16K=_16J.a;return (!B(_Wr(_16F,_,_16I,_16K,E(_16p).b)))?new T3(0,new T2(0,_16q,_16r),_16u,_1):new T3(0,new T2(0,new T(function(){return B(_E2(_16F,new T2(0,_16I,_YB),_16q));}),_16r),_16E,new T2(1,new T3(4,_16F,_16I,_16K),_1));}else{return new T3(0,new T2(0,_16q,_16r),_16E,new T2(1,new T2(6,_16F,_16I),_1));}}break;case 3:var _16L=_16u.a,_16M=_16u.b,_16N=_16u.c,_16O=_16u.d,_16P=_16u.f,_16Q=E(E(_16t).b);if(E(_16u.e)>_16Q){var _16R=function(_16S){var _16T=B(_RW(_16q,_16r,_16O));if(E(_16S)!=_16T){return new T3(0,new T2(0,_16q,_16r),_16u,_1);}else{if(B(_12R(_16q,_16M,_16Q))<_16T){return new T3(0,new T2(0,_16q,_16r),_16P,new T2(1,new T4(2,_16L,_16M,_16N,_16T),_1));}else{var _16U=new T(function(){return B(_14F(function(_16V){var _16W=E(_16V),_16X=E(_16W.b);return (_16X._==0)?(E(_16W.a)!=E(_16M))?false:(E(_16X.b)>_16Q)?true:false:false;},_16T,_16q));});return new T3(0,new T2(0,_16U,_16r),_16P,new T2(1,new T4(0,_16L,_16M,_16N,_16T),_1));}}},_16Y=E(E(_16p).c);if(!_16Y._){var _16Z=_16Y.d,_170=_16Y.e,_171=E(_16Y.b),_172=E(_16L),_173=E(_171.a);if(_172>=_173){if(_172!=_173){var _174=B(_12l(_172,_,_16N,_170));if(!_174._){return new T3(0,new T2(0,_16q,_16r),_16u,_1);}else{return new F(function(){return _16R(_174.a);});}}else{var _175=E(_16N),_176=E(_171.b);if(_175>=_176){if(_175!=_176){var _177=B(_12a(_172,_,_175,_170));if(!_177._){return new T3(0,new T2(0,_16q,_16r),_16u,_1);}else{return new F(function(){return _16R(_177.a);});}}else{return new F(function(){return _16R(_16Y.c);});}}else{var _178=B(_12a(_172,_,_175,_16Z));if(!_178._){return new T3(0,new T2(0,_16q,_16r),_16u,_1);}else{return new F(function(){return _16R(_178.a);});}}}}else{var _179=B(_12l(_172,_,_16N,_16Z));if(!_179._){return new T3(0,new T2(0,_16q,_16r),_16u,_1);}else{return new F(function(){return _16R(_179.a);});}}}else{return new T3(0,new T2(0,_16q,_16r),_16u,_1);}}else{return new T3(0,new T2(0,_16q,_16r),_16P,new T2(1,new T4(1,_16L,_16M,_16N,new T(function(){return B(_RW(_16q,_16r,_16O));})),_1));}break;case 4:var _17a=new T(function(){var _17b=B(_16o(_16p,_16q,_16r,_16u.a,_16t));return new T3(0,_17b.a,_17b.b,_17b.c);}),_17c=new T(function(){var _17d=B(_15l(_16p,new T(function(){return E(E(_17a).a);}),_16u.b,_16t));return new T3(0,_17d.a,_17d.b,_17d.c);}),_17e=new T(function(){return B(_hq(E(_17a).c,new T(function(){return E(E(_17c).c);},1)));}),_17f=new T(function(){var _17g=E(_17a).b,_17h=E(_17c).b,_17i=function(_17j){var _17k=E(_17h);switch(_17k._){case 0:return E(_17g);case 1:return new T2(4,_17g,_17k);case 2:return new T2(4,_17g,_17k);case 3:return new T2(4,_17g,_17k);case 4:return new T2(4,_17g,_17k);case 5:return new T2(4,_17g,_17k);default:return new T2(4,_17g,_17k);}};switch(E(_17g)._){case 0:return E(_17h);break;case 1:return B(_17i(_));break;case 2:return B(_17i(_));break;case 3:return B(_17i(_));break;case 4:return B(_17i(_));break;case 5:return B(_17i(_));break;default:return B(_17i(_));}});return new T3(0,new T(function(){return E(E(_17c).a);}),_17f,_17e);case 5:return (!B(_14Z(new T2(0,_16q,_16r),_16u.a,_16t)))?new T3(0,new T2(0,_16q,_16r),_16u.c,_1):new T3(0,new T2(0,_16q,_16r),_16u.b,_1);default:var _17l=E(_16t);return (E(_16u.b)>E(_17l.b))?(!B(_14Z(new T2(0,_16q,_16r),_16u.a,_17l)))?new T3(0,new T2(0,_16q,_16r),_16u,_1):new T3(0,new T2(0,_16q,_16r),_16u.c,_1):new T3(0,new T2(0,_16q,_16r),_16u.d,_1);}},_17m=function(_17n,_17o,_17p,_17q,_17r,_17s){var _17t=B(_16o(_17n,_17o,_17p,_17q,_17r)),_17u=_17t.b,_17v=_17t.c,_17w=E(_17t.a),_17x=_17w.a,_17y=_17w.b,_17z=function(_17A){return new F(function(){return _17m(_17n,_17x,_17y,_17u,_17r,new T(function(){return B(_hq(_17v,_17s));}));});};if(!B(A2(_129,_17x,_17o))){return new F(function(){return _17z(_);});}else{if(!B(A2(_11G,_17y,_17p))){return new F(function(){return _17z(_);});}else{if(!B(_10F(_17u,_17q))){return new F(function(){return _17z(_);});}else{if(!E(_17v)._){return new T3(0,new T2(0,_17o,_17p),_17q,_17s);}else{return new F(function(){return _17z(_);});}}}}},_17B=function(_17C,_17D,_17E,_17F){var _17G=new T(function(){var _17H=B(_YG(_17C,new T(function(){return E(E(_17D).a);},1),_17F));return new T2(0,_17H.a,_17H.b);}),_17I=new T(function(){var _17J=B(_ZV(new T(function(){return E(E(_17D).b);}),_1,E(_17C).d));return new T2(0,_17J.a,_17J.b);}),_17K=new T(function(){var _17L=E(_17D),_17M=B(_17m(_17C,new T(function(){return E(E(_17G).a);}),new T(function(){return E(E(_17I).a);}),_17E,_17F,_1));return new T3(0,_17M.a,_17M.b,_17M.c);}),_17N=new T(function(){var _17O=new T(function(){return B(_hq(E(_17G).b,new T(function(){return E(E(_17K).c);},1)));},1);return B(_hq(E(_17I).b,_17O));});return new T3(0,new T(function(){return E(E(_17K).a);}),new T(function(){return E(E(_17K).b);}),_17N);},_17P=function(_17Q,_17R,_17S,_17T,_17U){while(1){var _17V=E(_17Q);if(!_17V._){return new T4(0,_17R,_17S,_17T,_17U);}else{var _17W=E(_17V.a),_17X=B(_Rc(_17R,_17S,_17T,_17U,_17W.a,_17W.b,_17W.c,_17W.d));_17Q=_17V.b;_17R=_17X.a;_17S=_17X.b;_17T=_17X.c;_17U=_17X.d;continue;}}},_17Y=function(_17Z,_180,_181,_182,_183,_184){var _185=E(_17Z),_186=B(_Rc(_181,_182,_183,_184,_185.a,_185.b,_185.c,_185.d));return new F(function(){return _17P(_180,_186.a,_186.b,_186.c,_186.d);});},_187=function(_188,_189,_18a,_18b){var _18c=B(_17B(_189,_18b,_18a,_188)),_18d=_18c.a,_18e=_18c.b,_18f=B(_Sv(_18e,_18d));return new F(function(){return _17Y(new T(function(){var _18g=B(_SI(_188,E(_18d).a));return new T4(0,_18g.a,_18g.b,_18g.c,_18g.d);}),new T2(1,new T(function(){var _18h=B(_Vo(_18d,_18e));return new T4(0,_18h.a,_18h.b,_18h.c,_18h.d);}),_1),_18f.a,_18f.b,_18f.c,_18f.d);});},_18i="(function (t) {return window[t].getValue()})",_18j=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_18k=new T(function(){return B(unCStr("contractState"));}),_18l=new T(function(){return B(unCStr("currBlock"));}),_18m=new T(function(){return eval("(function (x) { var node = document.getElementById(x); while (node.hasChildNodes()) { node.removeChild(node.lastChild); } })");}),_18n=new T(function(){return B(err(_ha));}),_18o=new T(function(){return B(err(_jS));}),_18p=new T(function(){return B(A3(_xS,_yl,_xn,_DB));}),_18q="(function (t) {return document.getElementById(t).value})",_18r=new T(function(){return B(err(_ha));}),_18s=new T(function(){return B(err(_jS));}),_18t=function(_zv){return new F(function(){return _xH(_BM,_zv);});},_18u=function(_18v,_18w){return new F(function(){return _yv(_18t,_18w);});},_18x=new T(function(){return B(_yv(_18t,_jV));}),_18y=function(_zv){return new F(function(){return _l5(_18x,_zv);});},_18z=function(_18A){var _18B=new T(function(){return B(A3(_xH,_BM,_18A,_jV));});return function(_zc){return new F(function(){return _l5(_18B,_zc);});};},_18C=new T4(0,_18z,_18y,_18t,_18u),_18D=new T(function(){return B(unCStr("NotRedeemed"));}),_18E=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_18F=function(_18G,_18H){var _18I=new T(function(){var _18J=new T(function(){return B(A1(_18H,_YB));});return B(_wQ(function(_18K){var _18L=E(_18K);return (_18L._==3)?(!B(_lT(_18L.a,_18E)))?new T0(2):E(_18J):new T0(2);}));}),_18M=function(_18N){return E(_18I);},_18O=new T(function(){if(E(_18G)>10){return new T0(2);}else{var _18P=new T(function(){var _18Q=new T(function(){var _18R=function(_18S){return new F(function(){return A3(_xS,_yl,_ze,function(_18T){return new F(function(){return A1(_18H,new T2(0,_18S,_18T));});});});};return B(A3(_xS,_yl,_ze,_18R));});return B(_wQ(function(_18U){var _18V=E(_18U);return (_18V._==3)?(!B(_lT(_18V.a,_18D)))?new T0(2):E(_18Q):new T0(2);}));}),_18W=function(_18X){return E(_18P);};return new T1(1,function(_18Y){return new F(function(){return A2(_vx,_18Y,_18W);});});}});return new F(function(){return _lf(new T1(1,function(_18Z){return new F(function(){return A2(_vx,_18Z,_18M);});}),_18O);});},_190=function(_zv){return new F(function(){return _xH(_18F,_zv);});},_191=function(_192,_193){return new F(function(){return _yv(_190,_193);});},_194=new T(function(){return B(_yv(_190,_jV));}),_195=function(_zv){return new F(function(){return _l5(_194,_zv);});},_196=function(_197){var _198=new T(function(){return B(A3(_xH,_18F,_197,_jV));});return function(_zc){return new F(function(){return _l5(_198,_zc);});};},_199=new T4(0,_196,_195,_190,_191),_19a=function(_19b,_19c){return new F(function(){return _A0(_zd,_199,_19c);});},_19d=new T(function(){return B(_yv(_19a,_jV));}),_19e=function(_zv){return new F(function(){return _l5(_19d,_zv);});},_19f=new T(function(){return B(_A0(_zd,_199,_jV));}),_19g=function(_zv){return new F(function(){return _l5(_19f,_zv);});},_19h=function(_19i,_zv){return new F(function(){return _19g(_zv);});},_19j=function(_19k,_19l){return new F(function(){return _yv(_19a,_19l);});},_19m=new T4(0,_19h,_19e,_19a,_19j),_19n=function(_19o,_19p){return new F(function(){return _A0(_18C,_19m,_19p);});},_19q=function(_19r,_19s){return new F(function(){return _yv(_19n,_19s);});},_19t=new T(function(){return B(_yv(_19q,_jV));}),_19u=function(_Av){return new F(function(){return _l5(_19t,_Av);});},_19v=function(_19w){return new F(function(){return _yv(_19q,_19w);});},_19x=function(_19y,_19z){return new F(function(){return _19v(_19z);});},_19A=new T(function(){return B(_yv(_19n,_jV));}),_19B=function(_Av){return new F(function(){return _l5(_19A,_Av);});},_19C=function(_19D,_Av){return new F(function(){return _19B(_Av);});},_19E=new T4(0,_19C,_19u,_19q,_19x),_19F=new T(function(){return B(_A0(_19E,_AF,_DB));}),_19G=42,_19H=new T(function(){return B(unCStr("actions"));}),_19I=function(_19J){while(1){var _19K=B((function(_19L){var _19M=E(_19L);if(!_19M._){return __Z;}else{var _19N=_19M.b,_19O=E(_19M.a);if(!E(_19O.b)._){return new T2(1,_19O.a,new T(function(){return B(_19I(_19N));}));}else{_19J=_19N;return __continue;}}})(_19J));if(_19K!=__continue){return _19K;}}},_19P=new T(function(){return B(err(_ha));}),_19Q=new T(function(){return B(err(_jS));}),_19R=new T(function(){return B(unCStr("ConstMoney"));}),_19S=new T(function(){return B(unCStr("AvailableMoney"));}),_19T=new T(function(){return B(unCStr("AddMoney"));}),_19U=new T(function(){return B(unCStr("MoneyFromChoice"));}),_19V=function(_19W,_19X){var _19Y=new T(function(){var _19Z=new T(function(){var _1a0=new T(function(){if(_19W>10){return new T0(2);}else{var _1a1=new T(function(){var _1a2=new T(function(){var _1a3=function(_1a4){var _1a5=function(_1a6){return new F(function(){return A3(_xH,_1a7,_ze,function(_1a8){return new F(function(){return A1(_19X,new T3(3,_1a4,_1a6,_1a8));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1a5);});};return B(A3(_xH,_zr,_ze,_1a3));});return B(_wQ(function(_1a9){var _1aa=E(_1a9);return (_1aa._==3)?(!B(_lT(_1aa.a,_19U)))?new T0(2):E(_1a2):new T0(2);}));}),_1ab=function(_1ac){return E(_1a1);};return new T1(1,function(_1ad){return new F(function(){return A2(_vx,_1ad,_1ab);});});}});if(_19W>10){return B(_lf(_jU,_1a0));}else{var _1ae=new T(function(){var _1af=new T(function(){return B(A3(_xS,_yl,_ze,function(_1ag){return new F(function(){return A1(_19X,new T1(2,_1ag));});}));});return B(_wQ(function(_1ah){var _1ai=E(_1ah);return (_1ai._==3)?(!B(_lT(_1ai.a,_19R)))?new T0(2):E(_1af):new T0(2);}));}),_1aj=function(_1ak){return E(_1ae);};return B(_lf(new T1(1,function(_1al){return new F(function(){return A2(_vx,_1al,_1aj);});}),_1a0));}});if(_19W>10){return B(_lf(_jU,_19Z));}else{var _1am=new T(function(){var _1an=new T(function(){var _1ao=function(_1ap){return new F(function(){return A3(_xH,_1a7,_ze,function(_1aq){return new F(function(){return A1(_19X,new T2(1,_1ap,_1aq));});});});};return B(A3(_xH,_1a7,_ze,_1ao));});return B(_wQ(function(_1ar){var _1as=E(_1ar);return (_1as._==3)?(!B(_lT(_1as.a,_19T)))?new T0(2):E(_1an):new T0(2);}));}),_1at=function(_1au){return E(_1am);};return B(_lf(new T1(1,function(_1av){return new F(function(){return A2(_vx,_1av,_1at);});}),_19Z));}});if(_19W>10){return new F(function(){return _lf(_jU,_19Y);});}else{var _1aw=new T(function(){var _1ax=new T(function(){return B(A3(_xH,_BM,_ze,function(_1ay){return new F(function(){return A1(_19X,new T1(0,_1ay));});}));});return B(_wQ(function(_1az){var _1aA=E(_1az);return (_1aA._==3)?(!B(_lT(_1aA.a,_19S)))?new T0(2):E(_1ax):new T0(2);}));}),_1aB=function(_1aC){return E(_1aw);};return new F(function(){return _lf(new T1(1,function(_1aD){return new F(function(){return A2(_vx,_1aD,_1aB);});}),_19Y);});}},_1a7=function(_1aE,_1aF){return new F(function(){return _19V(E(_1aE),_1aF);});},_1aG=new T0(7),_1aH=function(_1aI,_1aJ){return new F(function(){return A1(_1aJ,_1aG);});},_1aK=new T(function(){return B(unCStr("TrueObs"));}),_1aL=new T2(0,_1aK,_1aH),_1aM=new T0(8),_1aN=function(_1aO,_1aP){return new F(function(){return A1(_1aP,_1aM);});},_1aQ=new T(function(){return B(unCStr("FalseObs"));}),_1aR=new T2(0,_1aQ,_1aN),_1aS=new T2(1,_1aR,_1),_1aT=new T2(1,_1aL,_1aS),_1aU=function(_1aV,_1aW,_1aX){var _1aY=E(_1aV);if(!_1aY._){return new T0(2);}else{var _1aZ=E(_1aY.a),_1b0=_1aZ.a,_1b1=new T(function(){return B(A2(_1aZ.b,_1aW,_1aX));}),_1b2=new T(function(){return B(_wQ(function(_1b3){var _1b4=E(_1b3);switch(_1b4._){case 3:return (!B(_lT(_1b0,_1b4.a)))?new T0(2):E(_1b1);case 4:return (!B(_lT(_1b0,_1b4.a)))?new T0(2):E(_1b1);default:return new T0(2);}}));}),_1b5=function(_1b6){return E(_1b2);};return new F(function(){return _lf(new T1(1,function(_1b7){return new F(function(){return A2(_vx,_1b7,_1b5);});}),new T(function(){return B(_1aU(_1aY.b,_1aW,_1aX));}));});}},_1b8=new T(function(){return B(unCStr("ValueGE"));}),_1b9=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1ba=new T(function(){return B(unCStr("PersonChoseThis"));}),_1bb=new T(function(){return B(unCStr("BelowTimeout"));}),_1bc=new T(function(){return B(unCStr("AndObs"));}),_1bd=new T(function(){return B(unCStr("OrObs"));}),_1be=new T(function(){return B(unCStr("NotObs"));}),_1bf=function(_1bg,_1bh){var _1bi=new T(function(){var _1bj=E(_1bg),_1bk=new T(function(){var _1bl=new T(function(){var _1bm=new T(function(){var _1bn=new T(function(){var _1bo=new T(function(){var _1bp=new T(function(){if(_1bj>10){return new T0(2);}else{var _1bq=new T(function(){var _1br=new T(function(){var _1bs=function(_1bt){return new F(function(){return A3(_xH,_1a7,_ze,function(_1bu){return new F(function(){return A1(_1bh,new T2(6,_1bt,_1bu));});});});};return B(A3(_xH,_1a7,_ze,_1bs));});return B(_wQ(function(_1bv){var _1bw=E(_1bv);return (_1bw._==3)?(!B(_lT(_1bw.a,_1b8)))?new T0(2):E(_1br):new T0(2);}));}),_1bx=function(_1by){return E(_1bq);};return new T1(1,function(_1bz){return new F(function(){return A2(_vx,_1bz,_1bx);});});}});if(_1bj>10){return B(_lf(_jU,_1bp));}else{var _1bA=new T(function(){var _1bB=new T(function(){var _1bC=function(_1bD){return new F(function(){return A3(_xS,_yl,_ze,function(_1bE){return new F(function(){return A1(_1bh,new T2(5,_1bD,_1bE));});});});};return B(A3(_xH,_zr,_ze,_1bC));});return B(_wQ(function(_1bF){var _1bG=E(_1bF);return (_1bG._==3)?(!B(_lT(_1bG.a,_1b9)))?new T0(2):E(_1bB):new T0(2);}));}),_1bH=function(_1bI){return E(_1bA);};return B(_lf(new T1(1,function(_1bJ){return new F(function(){return A2(_vx,_1bJ,_1bH);});}),_1bp));}});if(_1bj>10){return B(_lf(_jU,_1bo));}else{var _1bK=new T(function(){var _1bL=new T(function(){var _1bM=function(_1bN){var _1bO=function(_1bP){return new F(function(){return A3(_xS,_yl,_ze,function(_1bQ){return new F(function(){return A1(_1bh,new T3(4,_1bN,_1bP,_1bQ));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1bO);});};return B(A3(_xH,_zr,_ze,_1bM));});return B(_wQ(function(_1bR){var _1bS=E(_1bR);return (_1bS._==3)?(!B(_lT(_1bS.a,_1ba)))?new T0(2):E(_1bL):new T0(2);}));}),_1bT=function(_1bU){return E(_1bK);};return B(_lf(new T1(1,function(_1bV){return new F(function(){return A2(_vx,_1bV,_1bT);});}),_1bo));}});if(_1bj>10){return B(_lf(_jU,_1bn));}else{var _1bW=new T(function(){var _1bX=new T(function(){return B(A3(_xH,_1bf,_ze,function(_1bY){return new F(function(){return A1(_1bh,new T1(3,_1bY));});}));});return B(_wQ(function(_1bZ){var _1c0=E(_1bZ);return (_1c0._==3)?(!B(_lT(_1c0.a,_1be)))?new T0(2):E(_1bX):new T0(2);}));}),_1c1=function(_1c2){return E(_1bW);};return B(_lf(new T1(1,function(_1c3){return new F(function(){return A2(_vx,_1c3,_1c1);});}),_1bn));}});if(_1bj>10){return B(_lf(_jU,_1bm));}else{var _1c4=new T(function(){var _1c5=new T(function(){var _1c6=function(_1c7){return new F(function(){return A3(_xH,_1bf,_ze,function(_1c8){return new F(function(){return A1(_1bh,new T2(2,_1c7,_1c8));});});});};return B(A3(_xH,_1bf,_ze,_1c6));});return B(_wQ(function(_1c9){var _1ca=E(_1c9);return (_1ca._==3)?(!B(_lT(_1ca.a,_1bd)))?new T0(2):E(_1c5):new T0(2);}));}),_1cb=function(_1cc){return E(_1c4);};return B(_lf(new T1(1,function(_1cd){return new F(function(){return A2(_vx,_1cd,_1cb);});}),_1bm));}});if(_1bj>10){return B(_lf(_jU,_1bl));}else{var _1ce=new T(function(){var _1cf=new T(function(){var _1cg=function(_1ch){return new F(function(){return A3(_xH,_1bf,_ze,function(_1ci){return new F(function(){return A1(_1bh,new T2(1,_1ch,_1ci));});});});};return B(A3(_xH,_1bf,_ze,_1cg));});return B(_wQ(function(_1cj){var _1ck=E(_1cj);return (_1ck._==3)?(!B(_lT(_1ck.a,_1bc)))?new T0(2):E(_1cf):new T0(2);}));}),_1cl=function(_1cm){return E(_1ce);};return B(_lf(new T1(1,function(_1cn){return new F(function(){return A2(_vx,_1cn,_1cl);});}),_1bl));}});if(_1bj>10){return B(_lf(_jU,_1bk));}else{var _1co=new T(function(){var _1cp=new T(function(){return B(A3(_xS,_yl,_ze,function(_1cq){return new F(function(){return A1(_1bh,new T1(0,_1cq));});}));});return B(_wQ(function(_1cr){var _1cs=E(_1cr);return (_1cs._==3)?(!B(_lT(_1cs.a,_1bb)))?new T0(2):E(_1cp):new T0(2);}));}),_1ct=function(_1cu){return E(_1co);};return B(_lf(new T1(1,function(_1cv){return new F(function(){return A2(_vx,_1cv,_1ct);});}),_1bk));}});return new F(function(){return _lf(B(_1aU(_1aT,_1bg,_1bh)),_1bi);});},_1cw=new T(function(){return B(unCStr("Null"));}),_1cx=new T(function(){return B(unCStr("CommitCash"));}),_1cy=new T(function(){return B(unCStr("RedeemCC"));}),_1cz=new T(function(){return B(unCStr("Pay"));}),_1cA=new T(function(){return B(unCStr("Both"));}),_1cB=new T(function(){return B(unCStr("Choice"));}),_1cC=new T(function(){return B(unCStr("When"));}),_1cD=function(_1cE,_1cF){var _1cG=new T(function(){var _1cH=new T(function(){return B(A1(_1cF,_137));});return B(_wQ(function(_1cI){var _1cJ=E(_1cI);return (_1cJ._==3)?(!B(_lT(_1cJ.a,_1cw)))?new T0(2):E(_1cH):new T0(2);}));}),_1cK=function(_1cL){return E(_1cG);},_1cM=new T(function(){var _1cN=E(_1cE),_1cO=new T(function(){var _1cP=new T(function(){var _1cQ=new T(function(){var _1cR=new T(function(){var _1cS=new T(function(){if(_1cN>10){return new T0(2);}else{var _1cT=new T(function(){var _1cU=new T(function(){var _1cV=function(_1cW){var _1cX=function(_1cY){var _1cZ=function(_1d0){return new F(function(){return A3(_xH,_1cD,_ze,function(_1d1){return new F(function(){return A1(_1cF,new T4(6,_1cW,_1cY,_1d0,_1d1));});});});};return new F(function(){return A3(_xH,_1cD,_ze,_1cZ);});};return new F(function(){return A3(_xS,_yl,_ze,_1cX);});};return B(A3(_xH,_1bf,_ze,_1cV));});return B(_wQ(function(_1d2){var _1d3=E(_1d2);return (_1d3._==3)?(!B(_lT(_1d3.a,_1cC)))?new T0(2):E(_1cU):new T0(2);}));}),_1d4=function(_1d5){return E(_1cT);};return new T1(1,function(_1d6){return new F(function(){return A2(_vx,_1d6,_1d4);});});}});if(_1cN>10){return B(_lf(_jU,_1cS));}else{var _1d7=new T(function(){var _1d8=new T(function(){var _1d9=function(_1da){var _1db=function(_1dc){return new F(function(){return A3(_xH,_1cD,_ze,function(_1dd){return new F(function(){return A1(_1cF,new T3(5,_1da,_1dc,_1dd));});});});};return new F(function(){return A3(_xH,_1cD,_ze,_1db);});};return B(A3(_xH,_1bf,_ze,_1d9));});return B(_wQ(function(_1de){var _1df=E(_1de);return (_1df._==3)?(!B(_lT(_1df.a,_1cB)))?new T0(2):E(_1d8):new T0(2);}));}),_1dg=function(_1dh){return E(_1d7);};return B(_lf(new T1(1,function(_1di){return new F(function(){return A2(_vx,_1di,_1dg);});}),_1cS));}});if(_1cN>10){return B(_lf(_jU,_1cR));}else{var _1dj=new T(function(){var _1dk=new T(function(){var _1dl=function(_1dm){return new F(function(){return A3(_xH,_1cD,_ze,function(_1dn){return new F(function(){return A1(_1cF,new T2(4,_1dm,_1dn));});});});};return B(A3(_xH,_1cD,_ze,_1dl));});return B(_wQ(function(_1do){var _1dp=E(_1do);return (_1dp._==3)?(!B(_lT(_1dp.a,_1cA)))?new T0(2):E(_1dk):new T0(2);}));}),_1dq=function(_1dr){return E(_1dj);};return B(_lf(new T1(1,function(_1ds){return new F(function(){return A2(_vx,_1ds,_1dq);});}),_1cR));}});if(_1cN>10){return B(_lf(_jU,_1cQ));}else{var _1dt=new T(function(){var _1du=new T(function(){var _1dv=function(_1dw){var _1dx=function(_1dy){var _1dz=function(_1dA){var _1dB=function(_1dC){var _1dD=function(_1dE){return new F(function(){return A3(_xH,_1cD,_ze,function(_1dF){return new F(function(){return A1(_1cF,new T6(3,_1dw,_1dy,_1dA,_1dC,_1dE,_1dF));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1dD);});};return new F(function(){return A3(_xH,_1a7,_ze,_1dB);});};return new F(function(){return A3(_xS,_yl,_ze,_1dz);});};return new F(function(){return A3(_xS,_yl,_ze,_1dx);});};return B(A3(_xH,_AS,_ze,_1dv));});return B(_wQ(function(_1dG){var _1dH=E(_1dG);return (_1dH._==3)?(!B(_lT(_1dH.a,_1cz)))?new T0(2):E(_1du):new T0(2);}));}),_1dI=function(_1dJ){return E(_1dt);};return B(_lf(new T1(1,function(_1dK){return new F(function(){return A2(_vx,_1dK,_1dI);});}),_1cQ));}});if(_1cN>10){return B(_lf(_jU,_1cP));}else{var _1dL=new T(function(){var _1dM=new T(function(){var _1dN=function(_1dO){return new F(function(){return A3(_xH,_1cD,_ze,function(_1dP){return new F(function(){return A1(_1cF,new T2(2,_1dO,_1dP));});});});};return B(A3(_xH,_BM,_ze,_1dN));});return B(_wQ(function(_1dQ){var _1dR=E(_1dQ);return (_1dR._==3)?(!B(_lT(_1dR.a,_1cy)))?new T0(2):E(_1dM):new T0(2);}));}),_1dS=function(_1dT){return E(_1dL);};return B(_lf(new T1(1,function(_1dU){return new F(function(){return A2(_vx,_1dU,_1dS);});}),_1cP));}});if(_1cN>10){return B(_lf(_jU,_1cO));}else{var _1dV=new T(function(){var _1dW=new T(function(){var _1dX=function(_1dY){var _1dZ=function(_1e0){var _1e1=function(_1e2){var _1e3=function(_1e4){var _1e5=function(_1e6){var _1e7=function(_1e8){return new F(function(){return A3(_xH,_1cD,_ze,function(_1e9){return new F(function(){return A1(_1cF,{_:1,a:_1dY,b:_1e0,c:_1e2,d:_1e4,e:_1e6,f:_1e8,g:_1e9});});});});};return new F(function(){return A3(_xH,_1cD,_ze,_1e7);});};return new F(function(){return A3(_xS,_yl,_ze,_1e5);});};return new F(function(){return A3(_xS,_yl,_ze,_1e3);});};return new F(function(){return A3(_xH,_1a7,_ze,_1e1);});};return new F(function(){return A3(_xS,_yl,_ze,_1dZ);});};return B(A3(_xH,_BM,_ze,_1dX));});return B(_wQ(function(_1ea){var _1eb=E(_1ea);return (_1eb._==3)?(!B(_lT(_1eb.a,_1cx)))?new T0(2):E(_1dW):new T0(2);}));}),_1ec=function(_1ed){return E(_1dV);};return B(_lf(new T1(1,function(_1ee){return new F(function(){return A2(_vx,_1ee,_1ec);});}),_1cO));}});return new F(function(){return _lf(new T1(1,function(_1ef){return new F(function(){return A2(_vx,_1ef,_1cK);});}),_1cM);});},_1eg=new T(function(){return B(A3(_xH,_1cD,_xn,_DB));}),_1eh=function(_1ei,_){var _1ej=__app0(E(_18j)),_1ek=eval(E(_18q)),_1el=__app1(E(_1ek),toJSStr(E(_18l))),_1em=eval(E(_18i)),_1en=__app1(E(_1em),toJSStr(E(_18k))),_1eo=__app1(E(_18m),toJSStr(_19H)),_1ep=new T(function(){var _1eq=B(_19I(B(_l5(_19F,new T(function(){var _1er=String(_1en);return fromJSStr(_1er);})))));if(!_1eq._){return E(_18s);}else{if(!E(_1eq.b)._){var _1es=E(_1eq.a);return new T2(0,new T(function(){return B(_EV(_1es.a));}),new T(function(){return B(_5s(_1es.b));}));}else{return E(_18r);}}}),_1et=new T(function(){var _1eu=B(_19I(B(_l5(_1eg,new T(function(){var _1ev=String(_1ej);return fromJSStr(_1ev);})))));if(!_1eu._){return E(_19Q);}else{if(!E(_1eu.b)._){return E(_1eu.a);}else{return E(_19P);}}}),_1ew=new T(function(){var _1ex=B(_19I(B(_l5(_18p,new T(function(){var _1ey=String(_1el);return fromJSStr(_1ey);})))));if(!_1ex._){return E(_18o);}else{if(!E(_1ex.b)._){return E(_1ex.a);}else{return E(_18n);}}}),_1ez=B(_187(new T2(0,_19G,_1ew),_1ei,_1et,_1ep));return new F(function(){return _GL(_1ez.a,_1ez.b,_1ez.c,_1ez.d,_);});},_1eA=new T(function(){return B(unCStr("contractInput"));}),_1eB="(function (t, s) {window[t].setValue(s)})",_1eC=function(_1eD,_1eE,_){var _1eF=eval(E(_1eB)),_1eG=__app2(E(_1eF),toJSStr(E(_1eD)),toJSStr(E(_1eE)));return new F(function(){return _F8(_);});},_1eH=function(_1eI,_1eJ,_1eK,_){var _1eL=E(_1eA),_1eM=toJSStr(_1eL),_1eN=eval(E(_18i)),_1eO=__app1(E(_1eN),_1eM),_1eP=B(_19I(B(_l5(_DG,new T(function(){var _1eQ=String(_1eO);return fromJSStr(_1eQ);})))));if(!_1eP._){return E(_jT);}else{if(!E(_1eP.b)._){var _1eR=E(_1eP.a),_1eS=B(_jD(new T(function(){return B(_gR(_1eR.a));},1),new T(function(){return B(_c2(_1eR.b));},1),new T(function(){return B(_dH(_1eK,_1eI,_1eJ,B(_fb(_1eR.c))));},1),new T(function(){return B(_5s(_1eR.d));},1))),_1eT=B(_1eC(_1eL,new T2(1,_1eS.a,_1eS.b),_)),_1eU=__app1(E(_1eN),_1eM),_1eV=new T(function(){var _1eW=B(_19I(B(_l5(_DG,new T(function(){var _1eX=String(_1eU);return fromJSStr(_1eX);})))));if(!_1eW._){return E(_jT);}else{if(!E(_1eW.b)._){var _1eY=E(_1eW.a);return new T4(0,new T(function(){return B(_gR(_1eY.a));}),new T(function(){return B(_c2(_1eY.b));}),new T(function(){return B(_fb(_1eY.c));}),new T(function(){return B(_5s(_1eY.d));}));}else{return E(_jR);}}});return new F(function(){return _1eh(_1eV,_);});}else{return E(_jR);}}},_1eZ=function(_1f0,_1f1,_1f2,_1f3,_1f4){var _1f5=E(_1f4);if(!_1f5._){var _1f6=_1f5.c,_1f7=_1f5.d,_1f8=E(_1f5.b),_1f9=E(_1f8.a);if(_1f0>=_1f9){if(_1f0!=_1f9){return new F(function(){return _5N(_1f8,_1f6,B(_1eZ(_1f0,_,_1f2,_1f3,_1f7)));});}else{var _1fa=E(_1f8.b);if(_1f2>=_1fa){if(_1f2!=_1fa){return new F(function(){return _5N(_1f8,_1f6,B(_1eZ(_1f0,_,_1f2,_1f3,_1f7)));});}else{var _1fb=E(_1f8.c);if(_1f3>=_1fb){if(_1f3!=_1fb){return new F(function(){return _5N(_1f8,_1f6,B(_1eZ(_1f0,_,_1f2,_1f3,_1f7)));});}else{return new T4(0,_1f5.a,E(new T3(0,_1f0,_1f2,_1f3)),E(_1f6),E(_1f7));}}else{return new F(function(){return _6x(_1f8,B(_1eZ(_1f0,_,_1f2,_1f3,_1f6)),_1f7);});}}}else{return new F(function(){return _6x(_1f8,B(_1eZ(_1f0,_,_1f2,_1f3,_1f6)),_1f7);});}}}else{return new F(function(){return _6x(_1f8,B(_1eZ(_1f0,_,_1f2,_1f3,_1f6)),_1f7);});}}else{return new T4(0,1,E(new T3(0,_1f0,_1f2,_1f3)),E(_5I),E(_5I));}},_1fc=function(_1fd,_1fe,_1ff,_1fg,_1fh){var _1fi=E(_1fh);if(!_1fi._){var _1fj=_1fi.c,_1fk=_1fi.d,_1fl=E(_1fi.b),_1fm=E(_1fl.a);if(_1fd>=_1fm){if(_1fd!=_1fm){return new F(function(){return _5N(_1fl,_1fj,B(_1fc(_1fd,_,_1ff,_1fg,_1fk)));});}else{var _1fn=E(_1fl.b);if(_1ff>=_1fn){if(_1ff!=_1fn){return new F(function(){return _5N(_1fl,_1fj,B(_1fc(_1fd,_,_1ff,_1fg,_1fk)));});}else{var _1fo=E(_1fg),_1fp=E(_1fl.c);if(_1fo>=_1fp){if(_1fo!=_1fp){return new F(function(){return _5N(_1fl,_1fj,B(_1eZ(_1fd,_,_1ff,_1fo,_1fk)));});}else{return new T4(0,_1fi.a,E(new T3(0,_1fd,_1ff,_1fo)),E(_1fj),E(_1fk));}}else{return new F(function(){return _6x(_1fl,B(_1eZ(_1fd,_,_1ff,_1fo,_1fj)),_1fk);});}}}else{return new F(function(){return _6x(_1fl,B(_1fc(_1fd,_,_1ff,_1fg,_1fj)),_1fk);});}}}else{return new F(function(){return _6x(_1fl,B(_1fc(_1fd,_,_1ff,_1fg,_1fj)),_1fk);});}}else{return new T4(0,1,E(new T3(0,_1fd,_1ff,_1fg)),E(_5I),E(_5I));}},_1fq=function(_1fr,_1fs,_1ft,_1fu,_1fv){var _1fw=E(_1fv);if(!_1fw._){var _1fx=_1fw.c,_1fy=_1fw.d,_1fz=E(_1fw.b),_1fA=E(_1fz.a);if(_1fr>=_1fA){if(_1fr!=_1fA){return new F(function(){return _5N(_1fz,_1fx,B(_1fq(_1fr,_,_1ft,_1fu,_1fy)));});}else{var _1fB=E(_1ft),_1fC=E(_1fz.b);if(_1fB>=_1fC){if(_1fB!=_1fC){return new F(function(){return _5N(_1fz,_1fx,B(_1fc(_1fr,_,_1fB,_1fu,_1fy)));});}else{var _1fD=E(_1fu),_1fE=E(_1fz.c);if(_1fD>=_1fE){if(_1fD!=_1fE){return new F(function(){return _5N(_1fz,_1fx,B(_1eZ(_1fr,_,_1fB,_1fD,_1fy)));});}else{return new T4(0,_1fw.a,E(new T3(0,_1fr,_1fB,_1fD)),E(_1fx),E(_1fy));}}else{return new F(function(){return _6x(_1fz,B(_1eZ(_1fr,_,_1fB,_1fD,_1fx)),_1fy);});}}}else{return new F(function(){return _6x(_1fz,B(_1fc(_1fr,_,_1fB,_1fu,_1fx)),_1fy);});}}}else{return new F(function(){return _6x(_1fz,B(_1fq(_1fr,_,_1ft,_1fu,_1fx)),_1fy);});}}else{return new T4(0,1,E(new T3(0,_1fr,_1ft,_1fu)),E(_5I),E(_5I));}},_1fF=function(_1fG,_1fH,_1fI,_1fJ){var _1fK=E(_1fJ);if(!_1fK._){var _1fL=_1fK.c,_1fM=_1fK.d,_1fN=E(_1fK.b),_1fO=E(_1fG),_1fP=E(_1fN.a);if(_1fO>=_1fP){if(_1fO!=_1fP){return new F(function(){return _5N(_1fN,_1fL,B(_1fq(_1fO,_,_1fH,_1fI,_1fM)));});}else{var _1fQ=E(_1fH),_1fR=E(_1fN.b);if(_1fQ>=_1fR){if(_1fQ!=_1fR){return new F(function(){return _5N(_1fN,_1fL,B(_1fc(_1fO,_,_1fQ,_1fI,_1fM)));});}else{var _1fS=E(_1fI),_1fT=E(_1fN.c);if(_1fS>=_1fT){if(_1fS!=_1fT){return new F(function(){return _5N(_1fN,_1fL,B(_1eZ(_1fO,_,_1fQ,_1fS,_1fM)));});}else{return new T4(0,_1fK.a,E(new T3(0,_1fO,_1fQ,_1fS)),E(_1fL),E(_1fM));}}else{return new F(function(){return _6x(_1fN,B(_1eZ(_1fO,_,_1fQ,_1fS,_1fL)),_1fM);});}}}else{return new F(function(){return _6x(_1fN,B(_1fc(_1fO,_,_1fQ,_1fI,_1fL)),_1fM);});}}}else{return new F(function(){return _6x(_1fN,B(_1fq(_1fO,_,_1fH,_1fI,_1fL)),_1fM);});}}else{return new T4(0,1,E(new T3(0,_1fG,_1fH,_1fI)),E(_5I),E(_5I));}},_1fU=function(_1fV,_1fW,_1fX,_){var _1fY=E(_1eA),_1fZ=toJSStr(_1fY),_1g0=eval(E(_18i)),_1g1=__app1(E(_1g0),_1fZ),_1g2=B(_19I(B(_l5(_DG,new T(function(){var _1g3=String(_1g1);return fromJSStr(_1g3);})))));if(!_1g2._){return E(_jT);}else{if(!E(_1g2.b)._){var _1g4=E(_1g2.a),_1g5=B(_jD(new T(function(){return B(_gR(_1g4.a));},1),new T(function(){return B(_1fF(_1fX,_1fV,_1fW,B(_c2(_1g4.b))));},1),new T(function(){return B(_fb(_1g4.c));},1),new T(function(){return B(_5s(_1g4.d));},1))),_1g6=B(_1eC(_1fY,new T2(1,_1g5.a,_1g5.b),_)),_1g7=__app1(E(_1g0),_1fZ),_1g8=new T(function(){var _1g9=B(_19I(B(_l5(_DG,new T(function(){var _1ga=String(_1g7);return fromJSStr(_1ga);})))));if(!_1g9._){return E(_jT);}else{if(!E(_1g9.b)._){var _1gb=E(_1g9.a);return new T4(0,new T(function(){return B(_gR(_1gb.a));}),new T(function(){return B(_c2(_1gb.b));}),new T(function(){return B(_fb(_1gb.c));}),new T(function(){return B(_5s(_1gb.d));}));}else{return E(_jR);}}});return new F(function(){return _1eh(_1g8,_);});}else{return E(_jR);}}},_1gc=function(_1gd,_1ge,_1gf,_1gg,_){var _1gh=E(_1eA),_1gi=toJSStr(_1gh),_1gj=eval(E(_18i)),_1gk=__app1(E(_1gj),_1gi),_1gl=B(_19I(B(_l5(_DG,new T(function(){var _1gm=String(_1gk);return fromJSStr(_1gm);})))));if(!_1gl._){return E(_jT);}else{if(!E(_1gl.b)._){var _1gn=E(_1gl.a),_1go=B(_jD(new T(function(){return B(_fr(_1gf,_1gd,_1ge,_1gg,B(_gR(_1gn.a))));},1),new T(function(){return B(_c2(_1gn.b));},1),new T(function(){return B(_fb(_1gn.c));},1),new T(function(){return B(_5s(_1gn.d));},1))),_1gp=B(_1eC(_1gh,new T2(1,_1go.a,_1go.b),_)),_1gq=__app1(E(_1gj),_1gi),_1gr=new T(function(){var _1gs=B(_19I(B(_l5(_DG,new T(function(){var _1gt=String(_1gq);return fromJSStr(_1gt);})))));if(!_1gs._){return E(_jT);}else{if(!E(_1gs.b)._){var _1gu=E(_1gs.a);return new T4(0,new T(function(){return B(_gR(_1gu.a));}),new T(function(){return B(_c2(_1gu.b));}),new T(function(){return B(_fb(_1gu.c));}),new T(function(){return B(_5s(_1gu.d));}));}else{return E(_jR);}}});return new F(function(){return _1eh(_1gr,_);});}else{return E(_jR);}}},_1gv=new T(function(){return B(err(_jS));}),_1gw=new T(function(){return B(unCStr("SICC"));}),_1gx=new T(function(){return B(unCStr("SIRC"));}),_1gy=new T(function(){return B(unCStr("SIP"));}),_1gz=11,_1gA=function(_1gB,_1gC){var _1gD=new T(function(){var _1gE=new T(function(){if(_1gB>10){return new T0(2);}else{var _1gF=new T(function(){var _1gG=new T(function(){var _1gH=function(_1gI){var _1gJ=function(_1gK){return new F(function(){return A3(_xS,_yl,_1gz,function(_1gL){return new F(function(){return A1(_1gC,new T3(2,_1gI,_1gK,_1gL));});});});};return new F(function(){return A3(_xS,_yl,_1gz,_1gJ);});};return B(A3(_xH,_AS,_1gz,_1gH));});return B(_wQ(function(_1gM){var _1gN=E(_1gM);return (_1gN._==3)?(!B(_lT(_1gN.a,_1gy)))?new T0(2):E(_1gG):new T0(2);}));}),_1gO=function(_1gP){return E(_1gF);};return new T1(1,function(_1gQ){return new F(function(){return A2(_vx,_1gQ,_1gO);});});}});if(_1gB>10){return B(_lf(_jU,_1gE));}else{var _1gR=new T(function(){var _1gS=new T(function(){var _1gT=function(_1gU){var _1gV=function(_1gW){return new F(function(){return A3(_xS,_yl,_1gz,function(_1gX){return new F(function(){return A1(_1gC,new T3(1,_1gU,_1gW,_1gX));});});});};return new F(function(){return A3(_xS,_yl,_1gz,_1gV);});};return B(A3(_xH,_BM,_1gz,_1gT));});return B(_wQ(function(_1gY){var _1gZ=E(_1gY);return (_1gZ._==3)?(!B(_lT(_1gZ.a,_1gx)))?new T0(2):E(_1gS):new T0(2);}));}),_1h0=function(_1h1){return E(_1gR);};return B(_lf(new T1(1,function(_1h2){return new F(function(){return A2(_vx,_1h2,_1h0);});}),_1gE));}});if(_1gB>10){return new F(function(){return _lf(_jU,_1gD);});}else{var _1h3=new T(function(){var _1h4=new T(function(){var _1h5=function(_1h6){var _1h7=function(_1h8){var _1h9=function(_1ha){return new F(function(){return A3(_xS,_yl,_1gz,function(_1hb){return new F(function(){return A1(_1gC,new T4(0,_1h6,_1h8,_1ha,_1hb));});});});};return new F(function(){return A3(_xS,_yl,_1gz,_1h9);});};return new F(function(){return A3(_xS,_yl,_1gz,_1h7);});};return B(A3(_xH,_BM,_1gz,_1h5));});return B(_wQ(function(_1hc){var _1hd=E(_1hc);return (_1hd._==3)?(!B(_lT(_1hd.a,_1gw)))?new T0(2):E(_1h4):new T0(2);}));}),_1he=function(_1hf){return E(_1h3);};return new F(function(){return _lf(new T1(1,function(_1hg){return new F(function(){return A2(_vx,_1hg,_1he);});}),_1gD);});}},_1hh=function(_1hi,_1hj){return new F(function(){return _1gA(E(_1hi),_1hj);});},_1hk=new T(function(){return B(A3(_xH,_1hh,_xn,_DB));}),_1hl=function(_1hm,_){var _1hn=B(_19I(B(_l5(_1hk,_1hm))));if(!_1hn._){return E(_1gv);}else{if(!E(_1hn.b)._){var _1ho=E(_1hn.a);switch(_1ho._){case 0:return new F(function(){return _1gc(_1ho.b,_1ho.c,_1ho.a,_1ho.d,_);});break;case 1:return new F(function(){return _1fU(_1ho.b,_1ho.c,_1ho.a,_);});break;default:return new F(function(){return _1eH(_1ho.b,_1ho.c,_1ho.a,_);});}}else{return E(_hb);}}},_1hp=function(_1hq,_1hr,_1hs,_){var _1ht=E(_1eA),_1hu=toJSStr(_1ht),_1hv=eval(E(_18i)),_1hw=__app1(E(_1hv),_1hu),_1hx=B(_19I(B(_l5(_DG,new T(function(){var _1hy=String(_1hw);return fromJSStr(_1hy);})))));if(!_1hx._){return E(_jT);}else{if(!E(_1hx.b)._){var _1hz=E(_1hx.a),_1hA=B(_jD(new T(function(){return B(_gR(_1hz.a));},1),new T(function(){return B(_c2(_1hz.b));},1),new T(function(){return B(_fb(_1hz.c));},1),new T(function(){return B(_3Y(_1hs,_1hq,_1hr,B(_5s(_1hz.d))));},1))),_1hB=B(_1eC(_1ht,new T2(1,_1hA.a,_1hA.b),_)),_1hC=__app1(E(_1hv),_1hu),_1hD=new T(function(){var _1hE=B(_19I(B(_l5(_DG,new T(function(){var _1hF=String(_1hC);return fromJSStr(_1hF);})))));if(!_1hE._){return E(_jT);}else{if(!E(_1hE.b)._){var _1hG=E(_1hE.a);return new T4(0,new T(function(){return B(_gR(_1hG.a));}),new T(function(){return B(_c2(_1hG.b));}),new T(function(){return B(_fb(_1hG.c));}),new T(function(){return B(_5s(_1hG.d));}));}else{return E(_jR);}}});return new F(function(){return _1eh(_1hD,_);});}else{return E(_jR);}}},_1hH=new T(function(){return B(err(_ha));}),_1hI=new T(function(){return B(err(_jS));}),_1hJ=new T(function(){return B(_A0(_zE,_zd,_DB));}),_1hK=function(_1hL,_1hM,_){var _1hN=new T(function(){var _1hO=B(_19I(B(_l5(_1hJ,_1hL))));if(!_1hO._){return E(_1hI);}else{if(!E(_1hO.b)._){var _1hP=E(_1hO.a);return new T2(0,_1hP.a,_1hP.b);}else{return E(_1hH);}}});return new F(function(){return _1hp(new T(function(){return E(E(_1hN).b);}),_1hM,new T(function(){return E(E(_1hN).a);}),_);});},_1hQ=new T(function(){return B(unCStr("When"));}),_1hR=new T(function(){return B(unCStr("Choice"));}),_1hS=new T(function(){return B(unCStr("Both"));}),_1hT=new T(function(){return B(unCStr("Pay"));}),_1hU=new T(function(){return B(unCStr("RedeemCC"));}),_1hV=new T(function(){return B(unCStr("CommitCash"));}),_1hW=new T(function(){return B(unCStr("Null"));}),_1hX=32,_1hY=new T2(1,_1hX,_1),_1hZ=function(_1i0){var _1i1=E(_1i0);return (_1i1==1)?E(_1hY):new T2(1,_1hX,new T(function(){return B(_1hZ(_1i1-1|0));}));},_1i2=new T(function(){return B(unCStr("head"));}),_1i3=new T(function(){return B(_io(_1i2));}),_1i4=function(_1i5){return new F(function(){return _hA(0,E(_1i5),_1);});},_1i6=new T(function(){return B(unCStr("IdentPay"));}),_1i7=new T(function(){return B(unCStr("ValueGE"));}),_1i8=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1i9=new T(function(){return B(unCStr("PersonChoseThis"));}),_1ia=new T(function(){return B(unCStr("NotObs"));}),_1ib=new T(function(){return B(unCStr("OrObs"));}),_1ic=new T(function(){return B(unCStr("AndObs"));}),_1id=new T(function(){return B(unCStr("BelowTimeout"));}),_1ie=new T(function(){return B(unCStr("IdentChoice"));}),_1if=new T(function(){return B(unCStr("IdentCC"));}),_1ig=new T(function(){return B(unCStr("MoneyFromChoice"));}),_1ih=new T(function(){return B(unCStr("ConstMoney"));}),_1ii=new T(function(){return B(unCStr("AddMoney"));}),_1ij=new T(function(){return B(unCStr("AvailableMoney"));}),_1ik=new T(function(){return B(unCStr("FalseObs"));}),_1il=new T(function(){return B(unCStr("TrueObs"));}),_1im=function(_1in){var _1io=E(_1in);switch(_1io._){case 0:var _1ip=E(_1io.a);switch(_1ip._){case 0:return new T2(0,_1hW,_1);case 1:return new T2(0,_1hV,new T2(1,new T1(3,_1ip.a),new T2(1,new T1(6,_1ip.b),new T2(1,new T1(2,_1ip.c),new T2(1,new T1(6,_1ip.d),new T2(1,new T1(6,_1ip.e),new T2(1,new T1(0,_1ip.f),new T2(1,new T1(0,_1ip.g),_1))))))));case 2:return new T2(0,_1hU,new T2(1,new T1(3,_1ip.a),new T2(1,new T1(0,_1ip.b),_1)));case 3:return new T2(0,_1hT,new T2(1,new T1(5,_1ip.a),new T2(1,new T1(6,_1ip.b),new T2(1,new T1(6,_1ip.c),new T2(1,new T1(2,_1ip.d),new T2(1,new T1(6,_1ip.e),new T2(1,new T1(0,_1ip.f),_1)))))));case 4:return new T2(0,_1hS,new T2(1,new T1(0,_1ip.a),new T2(1,new T1(0,_1ip.b),_1)));case 5:return new T2(0,_1hR,new T2(1,new T1(1,_1ip.a),new T2(1,new T1(0,_1ip.b),new T2(1,new T1(0,_1ip.c),_1))));default:return new T2(0,_1hQ,new T2(1,new T1(1,_1ip.a),new T2(1,new T1(6,_1ip.b),new T2(1,new T1(0,_1ip.c),new T2(1,new T1(0,_1ip.d),_1)))));}break;case 1:var _1iq=E(_1io.a);switch(_1iq._){case 0:return new T2(0,_1id,new T2(1,new T1(6,_1iq.a),_1));case 1:return new T2(0,_1ic,new T2(1,new T1(1,_1iq.a),new T2(1,new T1(1,_1iq.b),_1)));case 2:return new T2(0,_1ib,new T2(1,new T1(1,_1iq.a),new T2(1,new T1(1,_1iq.b),_1)));case 3:return new T2(0,_1ia,new T2(1,new T1(1,_1iq.a),_1));case 4:return new T2(0,_1i9,new T2(1,new T1(4,_1iq.a),new T2(1,new T1(6,_1iq.b),new T2(1,new T1(6,_1iq.c),_1))));case 5:return new T2(0,_1i8,new T2(1,new T1(4,_1iq.a),new T2(1,new T1(6,_1iq.b),_1)));case 6:return new T2(0,_1i7,new T2(1,new T1(2,_1iq.a),new T2(1,new T1(2,_1iq.b),_1)));case 7:return new T2(0,_1il,_1);default:return new T2(0,_1ik,_1);}break;case 2:var _1ir=E(_1io.a);switch(_1ir._){case 0:return new T2(0,_1ij,new T2(1,new T1(3,_1ir.a),_1));case 1:return new T2(0,_1ii,new T2(1,new T1(2,_1ir.a),new T2(1,new T1(2,_1ir.b),_1)));case 2:return new T2(0,_1ih,new T2(1,new T1(6,_1ir.a),_1));default:return new T2(0,_1ig,new T2(1,new T1(4,_1ir.a),new T2(1,new T1(6,_1ir.b),new T2(1,new T1(2,_1ir.c),_1))));}break;case 3:return new T2(0,_1if,new T2(1,new T1(6,_1io.a),_1));case 4:return new T2(0,_1ie,new T2(1,new T1(6,_1io.a),_1));case 5:return new T2(0,_1i6,new T2(1,new T1(6,_1io.a),_1));default:return new T2(0,new T(function(){return B(_1i4(_1io.a));}),_1);}},_1is=function(_1it){var _1iu=B(_1im(_1it)),_1iv=_1iu.a,_1iw=E(_1iu.b);if(!_1iw._){return new T1(0,new T2(0,_1iv,_1));}else{switch(E(_1it)._){case 0:return new T1(2,new T2(0,_1iv,_1iw));case 1:return new T1(2,new T2(0,_1iv,_1iw));case 2:return new T1(2,new T2(0,_1iv,_1iw));default:return new T1(1,new T2(0,_1iv,_1iw));}}},_1ix=function(_1iy,_1iz){var _1iA=E(_1iz);if(!_1iA._){return __Z;}else{var _1iB=_1iA.a,_1iC=new T(function(){var _1iD=B(_kG(new T(function(){return B(A1(_1iy,_1iB));}),_1iA.b));return new T2(0,_1iD.a,_1iD.b);});return new T2(1,new T2(1,_1iB,new T(function(){return E(E(_1iC).a);})),new T(function(){return B(_1ix(_1iy,E(_1iC).b));}));}},_1iE=function(_1iF){var _1iG=E(_1iF);if(!_1iG._){return __Z;}else{return new F(function(){return _hq(_1iG.a,new T(function(){return B(_1iE(_1iG.b));},1));});}},_1iH=function(_1iI,_1iJ){return (E(_1iI)._==2)?false:(E(_1iJ)._==2)?false:true;},_1iK=function(_1iL,_1iM){var _1iN=E(_1iM);return (_1iN._==0)?__Z:new T2(1,_1iL,new T2(1,_1iN.a,new T(function(){return B(_1iK(_1iL,_1iN.b));})));},_1iO=new T(function(){return B(unCStr("\n"));}),_1iP=new T(function(){return B(unCStr("tail"));}),_1iQ=new T(function(){return B(_io(_1iP));}),_1iR=function(_1iS,_1iT,_1iU){var _1iV=E(_1iU);if(!_1iV._){return E(_1iT);}else{var _1iW=new T(function(){return (E(_1iS)+B(_oy(_1iT,0))|0)+1|0;}),_1iX=new T(function(){return B(_1ix(_1iH,B(_oD(_1is,_1iV))));}),_1iY=new T(function(){var _1iZ=E(_1iX);if(!_1iZ._){return E(_1iQ);}else{var _1j0=new T(function(){var _1j1=E(_1iW);if(0>=_1j1){return __Z;}else{return B(_1hZ(_1j1));}}),_1j2=function(_1j3){var _1j4=new T(function(){var _1j5=function(_1j6){var _1j7=E(_1j6);if(!_1j7._){return __Z;}else{var _1j8=new T(function(){return B(_hq(B(_1j9(_1iW,_1j7.a)),new T(function(){return B(_1j5(_1j7.b));},1)));});return new T2(1,_1hX,_1j8);}},_1ja=B(_1j5(_1j3));if(!_1ja._){return __Z;}else{return E(_1ja.b);}},1);return new F(function(){return _hq(_1j0,_1j4);});};return B(_1iK(_1iO,B(_oD(_1j2,_1iZ.b))));}}),_1jb=new T(function(){var _1jc=new T(function(){var _1jd=E(_1iX);if(!_1jd._){return E(_1i3);}else{var _1je=function(_1jf){var _1jg=E(_1jf);if(!_1jg._){return __Z;}else{var _1jh=new T(function(){return B(_hq(B(_1j9(_1iW,_1jg.a)),new T(function(){return B(_1je(_1jg.b));},1)));});return new T2(1,_1hX,_1jh);}};return B(_1je(_1jd.a));}},1);return B(_hq(_1iT,_1jc));});return new F(function(){return _1iE(new T2(1,_1jb,_1iY));});}},_1ji=new T(function(){return B(unCStr(")"));}),_1j9=function(_1jj,_1jk){var _1jl=E(_1jk);switch(_1jl._){case 0:var _1jm=E(_1jl.a);return new F(function(){return _1jn(0,_1jm.a,_1jm.b);});break;case 1:return new F(function(){return unAppCStr("(",new T(function(){var _1jo=E(_1jl.a);return B(_hq(B(_1jn(0,_1jo.a,_1jo.b)),_1ji));}));});break;default:var _1jp=new T(function(){var _1jq=E(_1jl.a);return B(_hq(B(_1iR(new T(function(){return E(_1jj)+1|0;},1),_1jq.a,_1jq.b)),_1ji));});return new F(function(){return unAppCStr("(",_1jp);});}},_1jn=function(_1jr,_1js,_1jt){var _1ju=E(_1jt);if(!_1ju._){return E(_1js);}else{var _1jv=new T(function(){return (_1jr+B(_oy(_1js,0))|0)+1|0;}),_1jw=new T(function(){return B(_1ix(_1iH,B(_oD(_1is,_1ju))));}),_1jx=new T(function(){var _1jy=E(_1jw);if(!_1jy._){return E(_1iQ);}else{var _1jz=new T(function(){var _1jA=E(_1jv);if(0>=_1jA){return __Z;}else{return B(_1hZ(_1jA));}}),_1jB=function(_1jC){var _1jD=new T(function(){var _1jE=function(_1jF){var _1jG=E(_1jF);if(!_1jG._){return __Z;}else{var _1jH=new T(function(){return B(_hq(B(_1j9(_1jv,_1jG.a)),new T(function(){return B(_1jE(_1jG.b));},1)));});return new T2(1,_1hX,_1jH);}},_1jI=B(_1jE(_1jC));if(!_1jI._){return __Z;}else{return E(_1jI.b);}},1);return new F(function(){return _hq(_1jz,_1jD);});};return B(_1iK(_1iO,B(_oD(_1jB,_1jy.b))));}}),_1jJ=new T(function(){var _1jK=new T(function(){var _1jL=E(_1jw);if(!_1jL._){return E(_1i3);}else{var _1jM=function(_1jN){var _1jO=E(_1jN);if(!_1jO._){return __Z;}else{var _1jP=new T(function(){return B(_hq(B(_1j9(_1jv,_1jO.a)),new T(function(){return B(_1jM(_1jO.b));},1)));});return new T2(1,_1hX,_1jP);}};return B(_1jM(_1jL.a));}},1);return B(_hq(_1js,_1jK));});return new F(function(){return _1iE(new T2(1,_1jJ,_1jx));});}},_1jQ=new T(function(){return B(_1jn(0,_1hW,_1));}),_1jR=function(_1jS,_){return new T(function(){var _1jT=B(_19I(B(_l5(_1eg,_1jS))));if(!_1jT._){return E(_19Q);}else{if(!E(_1jT.b)._){var _1jU=E(_1jT.a);switch(_1jU._){case 0:return E(_1jQ);break;case 1:return B(_1jn(0,_1hV,new T2(1,new T1(3,_1jU.a),new T2(1,new T1(6,_1jU.b),new T2(1,new T1(2,_1jU.c),new T2(1,new T1(6,_1jU.d),new T2(1,new T1(6,_1jU.e),new T2(1,new T1(0,_1jU.f),new T2(1,new T1(0,_1jU.g),_1)))))))));break;case 2:return B(_1jn(0,_1hU,new T2(1,new T1(3,_1jU.a),new T2(1,new T1(0,_1jU.b),_1))));break;case 3:return B(_1jn(0,_1hT,new T2(1,new T1(5,_1jU.a),new T2(1,new T1(6,_1jU.b),new T2(1,new T1(6,_1jU.c),new T2(1,new T1(2,_1jU.d),new T2(1,new T1(6,_1jU.e),new T2(1,new T1(0,_1jU.f),_1))))))));break;case 4:return B(_1jn(0,_1hS,new T2(1,new T1(0,_1jU.a),new T2(1,new T1(0,_1jU.b),_1))));break;case 5:return B(_1jn(0,_1hR,new T2(1,new T1(1,_1jU.a),new T2(1,new T1(0,_1jU.b),new T2(1,new T1(0,_1jU.c),_1)))));break;default:return B(_1jn(0,_1hQ,new T2(1,new T1(1,_1jU.a),new T2(1,new T1(6,_1jU.b),new T2(1,new T1(0,_1jU.c),new T2(1,new T1(0,_1jU.d),_1))))));}}else{return E(_19P);}}});},_1jV=new T(function(){return B(unCStr("codeArea"));}),_1jW=function(_){var _1jX=__app0(E(_18j)),_1jY=B(_1jR(new T(function(){var _1jZ=String(_1jX);return fromJSStr(_1jZ);}),_)),_1k0=B(_1eC(_1jV,_1jY,_)),_1k1=eval(E(_18i)),_1k2=__app1(E(_1k1),toJSStr(E(_1eA))),_1k3=new T(function(){var _1k4=B(_19I(B(_l5(_DG,new T(function(){var _1k5=String(_1k2);return fromJSStr(_1k5);})))));if(!_1k4._){return E(_jT);}else{if(!E(_1k4.b)._){var _1k6=E(_1k4.a);return new T4(0,new T(function(){return B(_gR(_1k6.a));}),new T(function(){return B(_c2(_1k6.b));}),new T(function(){return B(_fb(_1k6.c));}),new T(function(){return B(_5s(_1k6.d));}));}else{return E(_jR);}}});return new F(function(){return _1eh(_1k3,_);});},_1k7="(function (b) { return (b.inputList.length); })",_1k8="(function (b, x) { return (b.inputList[x]); })",_1k9=function(_1ka,_1kb,_){var _1kc=eval(E(_1k8)),_1kd=__app2(E(_1kc),_1ka,_1kb);return new T1(0,_1kd);},_1ke=function(_1kf,_1kg,_1kh,_){var _1ki=E(_1kh);if(!_1ki._){return _1;}else{var _1kj=B(_1k9(_1kf,E(_1ki.a),_)),_1kk=B(_1ke(_1kf,_,_1ki.b,_));return new T2(1,_1kj,_1kk);}},_1kl=function(_1km,_1kn){if(_1km<=_1kn){var _1ko=function(_1kp){return new T2(1,_1kp,new T(function(){if(_1kp!=_1kn){return B(_1ko(_1kp+1|0));}else{return __Z;}}));};return new F(function(){return _1ko(_1km);});}else{return __Z;}},_1kq=function(_1kr,_){var _1ks=eval(E(_1k7)),_1kt=__app1(E(_1ks),_1kr),_1ku=Number(_1kt),_1kv=jsTrunc(_1ku);return new F(function(){return _1ke(_1kr,_,new T(function(){return B(_1kl(0,_1kv-1|0));}),_);});},_1kw="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_1kx="(function (x) { return x.name; })",_1ky=new T(function(){return B(unCStr("\""));}),_1kz=function(_1kA){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_hq(_1kA,_1ky));}))));});},_1kB=function(_1kC,_1kD,_){var _1kE=E(_1kD);if(!_1kE._){return new F(function(){return _1kz(_1kC);});}else{var _1kF=E(_1kE.a),_1kG=E(_1kx),_1kH=eval(_1kG),_1kI=__app1(E(_1kH),E(_1kF.a)),_1kJ=String(_1kI);if(!B(_lT(fromJSStr(_1kJ),_1kC))){var _1kK=function(_1kL,_1kM,_){while(1){var _1kN=E(_1kM);if(!_1kN._){return new F(function(){return _1kz(_1kL);});}else{var _1kO=E(_1kN.a),_1kP=eval(_1kG),_1kQ=__app1(E(_1kP),E(_1kO.a)),_1kR=String(_1kQ);if(!B(_lT(fromJSStr(_1kR),_1kL))){_1kM=_1kN.b;continue;}else{return _1kO;}}}};return new F(function(){return _1kK(_1kC,_1kE.b,_);});}else{return _1kF;}}},_1kS=function(_1kT,_1kU,_1kV,_){var _1kW=B(_1kq(_1kU,_)),_1kX=B(_1kB(_1kT,_1kW,_)),_1kY=eval(E(_1kw)),_1kZ=__app2(E(_1kY),E(E(_1kV).a),E(E(_1kX).a));return new F(function(){return _F8(_);});},_1l0="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_1l1=function(_1l2,_1l3,_1l4,_){var _1l5=B(_1kq(_1l3,_)),_1l6=B(_1kB(_1l2,_1l5,_)),_1l7=eval(E(_1l0)),_1l8=__app2(E(_1l7),E(E(_1l4).a),E(E(_1l6).a));return new F(function(){return _F8(_);});},_1l9=function(_1la){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_hq(_1la,_1ky));}))));});},_1lb=function(_1lc,_1ld,_){var _1le=E(_1ld);if(!_1le._){return new F(function(){return _1l9(_1lc);});}else{var _1lf=E(_1le.a),_1lg=E(_1kx),_1lh=eval(_1lg),_1li=__app1(E(_1lh),E(_1lf.a)),_1lj=String(_1li);if(!B(_lT(fromJSStr(_1lj),_1lc))){var _1lk=function(_1ll,_1lm,_){while(1){var _1ln=E(_1lm);if(!_1ln._){return new F(function(){return _1l9(_1ll);});}else{var _1lo=E(_1ln.a),_1lp=eval(_1lg),_1lq=__app1(E(_1lp),E(_1lo.a)),_1lr=String(_1lq);if(!B(_lT(fromJSStr(_1lr),_1ll))){_1lm=_1ln.b;continue;}else{return _1lo;}}}};return new F(function(){return _1lk(_1lc,_1le.b,_);});}else{return _1lf;}}},_1ls="(function (b) { return (b.fieldRow.length); })",_1lt="(function (b, x) { return (b.fieldRow[x]); })",_1lu=function(_1lv,_1lw,_){var _1lx=eval(E(_1lt)),_1ly=__app2(E(_1lx),_1lv,_1lw);return new T1(0,_1ly);},_1lz=function(_1lA,_1lB,_1lC,_){var _1lD=E(_1lC);if(!_1lD._){return _1;}else{var _1lE=B(_1lu(_1lA,E(_1lD.a),_)),_1lF=B(_1lz(_1lA,_,_1lD.b,_));return new T2(1,_1lE,_1lF);}},_1lG=function(_1lH,_){var _1lI=eval(E(_1ls)),_1lJ=__app1(E(_1lI),_1lH),_1lK=Number(_1lJ),_1lL=jsTrunc(_1lK);return new F(function(){return _1lz(_1lH,_,new T(function(){return B(_1kl(0,_1lL-1|0));}),_);});},_1lM=function(_1lN,_){var _1lO=E(_1lN);if(!_1lO._){return _1;}else{var _1lP=B(_1lG(E(E(_1lO.a).a),_)),_1lQ=B(_1lM(_1lO.b,_));return new T2(1,_1lP,_1lQ);}},_1lR=function(_1lS){var _1lT=E(_1lS);if(!_1lT._){return __Z;}else{return new F(function(){return _hq(_1lT.a,new T(function(){return B(_1lR(_1lT.b));},1));});}},_1lU=function(_1lV,_1lW,_){var _1lX=B(_1kq(_1lW,_)),_1lY=B(_1lM(_1lX,_));return new F(function(){return _1lb(_1lV,B(_1lR(_1lY)),_);});},_1lZ=function(_1m0,_1m1,_1m2,_){var _1m3=B(_1kq(_1m1,_)),_1m4=B(_1kB(_1m0,_1m3,_)),_1m5=eval(E(_1l0)),_1m6=__app2(E(_1m5),E(E(_1m2).a),E(E(_1m4).a));return new F(function(){return _F8(_);});},_1m7=new T(function(){return B(unCStr("contract_commitcash"));}),_1m8=new T(function(){return B(unCStr("contract_redeemcc"));}),_1m9=new T(function(){return B(unCStr("contract_pay"));}),_1ma=new T(function(){return B(unCStr("contract_both"));}),_1mb=new T(function(){return B(unCStr("contract_choice"));}),_1mc=new T(function(){return B(unCStr("contract_when"));}),_1md="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_1me=function(_1mf,_){var _1mg=eval(E(_1md)),_1mh=__app1(E(_1mg),toJSStr(E(_1mf)));return new T1(0,_1mh);},_1mi=new T(function(){return B(unCStr("payer_id"));}),_1mj=new T(function(){return B(unCStr("pay_id"));}),_1mk=new T(function(){return B(unCStr("ccommit_id"));}),_1ml=new T(function(){return B(unCStr("end_expiration"));}),_1mm=new T(function(){return B(unCStr("start_expiration"));}),_1mn=new T(function(){return B(unCStr("person_id"));}),_1mo=new T(function(){return B(unCStr("contract_null"));}),_1mp=new T(function(){return B(unCStr("contract2"));}),_1mq=new T(function(){return B(unCStr("contract1"));}),_1mr=new T(function(){return B(unCStr("observation"));}),_1ms=new T(function(){return B(unCStr("timeout"));}),_1mt=new T(function(){return B(unCStr("contract"));}),_1mu=new T(function(){return B(unCStr("expiration"));}),_1mv=new T(function(){return B(unCStr("ammount"));}),_1mw=new T(function(){return B(unCStr("payee_id"));}),_1mx=new T(function(){return B(unCStr("value_available_money"));}),_1my=new T(function(){return B(unCStr("value_add_money"));}),_1mz=new T(function(){return B(unCStr("value_const_money"));}),_1mA=new T(function(){return B(unCStr("money_from_choice"));}),_1mB=new T(function(){return B(unCStr("value2"));}),_1mC=new T(function(){return B(unCStr("value1"));}),_1mD=new T(function(){return B(unCStr("choice_id"));}),_1mE=new T(function(){return B(unCStr("default"));}),_1mF=new T(function(){return B(unCStr("money"));}),_1mG=new T(function(){return B(unCStr("commit_id"));}),_1mH="(function (b, s) { return (b.setText(s)); })",_1mI=function(_1mJ,_){var _1mK=E(_1mJ);switch(_1mK._){case 0:var _1mL=B(_1me(_1mx,_)),_1mM=E(_1mL),_1mN=B(_1lU(_1mG,E(_1mM.a),_)),_1mO=eval(E(_1mH)),_1mP=__app2(E(_1mO),E(E(_1mN).a),toJSStr(B(_hA(0,E(_1mK.a),_1))));return _1mM;case 1:var _1mQ=B(_1mI(_1mK.a,_)),_1mR=B(_1mI(_1mK.b,_)),_1mS=B(_1me(_1my,_)),_1mT=E(_1mS),_1mU=E(_1mT.a),_1mV=B(_1l1(_1mC,_1mU,_1mQ,_)),_1mW=B(_1l1(_1mB,_1mU,_1mR,_));return _1mT;case 2:var _1mX=B(_1me(_1mz,_)),_1mY=E(_1mX),_1mZ=B(_1lU(_1mF,E(_1mY.a),_)),_1n0=eval(E(_1mH)),_1n1=__app2(E(_1n0),E(E(_1mZ).a),toJSStr(B(_hA(0,E(_1mK.a),_1))));return _1mY;default:var _1n2=B(_1mI(_1mK.c,_)),_1n3=B(_1me(_1mA,_)),_1n4=E(_1n3),_1n5=E(_1n4.a),_1n6=B(_1lU(_1mD,_1n5,_)),_1n7=eval(E(_1mH)),_1n8=__app2(E(_1n7),E(E(_1n6).a),toJSStr(B(_hA(0,E(_1mK.a),_1)))),_1n9=B(_1lU(_1mn,_1n5,_)),_1na=__app2(E(_1n7),E(E(_1n9).a),toJSStr(B(_hA(0,E(_1mK.b),_1)))),_1nb=B(_1l1(_1mE,_1n5,_1n2,_));return _1n4;}},_1nc=new T(function(){return B(unCStr("observation_personchosethis"));}),_1nd=new T(function(){return B(unCStr("observation_personchosesomething"));}),_1ne=new T(function(){return B(unCStr("observation_value_ge"));}),_1nf=new T(function(){return B(unCStr("observation_trueobs"));}),_1ng=new T(function(){return B(unCStr("observation_falseobs"));}),_1nh=new T(function(){return B(unCStr("observation_belowtimeout"));}),_1ni=new T(function(){return B(unCStr("observation_andobs"));}),_1nj=new T(function(){return B(unCStr("observation_orobs"));}),_1nk=new T(function(){return B(unCStr("observation_notobs"));}),_1nl=new T(function(){return B(unCStr("person"));}),_1nm=new T(function(){return B(unCStr("choice_value"));}),_1nn=new T(function(){return B(unCStr("observation2"));}),_1no=new T(function(){return B(unCStr("observation1"));}),_1np=new T(function(){return B(unCStr("block_number"));}),_1nq=function(_1nr,_){var _1ns=E(_1nr);switch(_1ns._){case 0:var _1nt=B(_1me(_1nh,_)),_1nu=E(_1nt),_1nv=B(_1lU(_1np,E(_1nu.a),_)),_1nw=eval(E(_1mH)),_1nx=__app2(E(_1nw),E(E(_1nv).a),toJSStr(B(_hA(0,E(_1ns.a),_1))));return _1nu;case 1:var _1ny=B(_1nq(_1ns.a,_)),_1nz=B(_1nq(_1ns.b,_)),_1nA=B(_1me(_1ni,_)),_1nB=E(_1nA),_1nC=E(_1nB.a),_1nD=B(_1lZ(_1no,_1nC,_1ny,_)),_1nE=B(_1lZ(_1nn,_1nC,_1nz,_));return _1nB;case 2:var _1nF=B(_1nq(_1ns.a,_)),_1nG=B(_1nq(_1ns.b,_)),_1nH=B(_1me(_1nj,_)),_1nI=E(_1nH),_1nJ=E(_1nI.a),_1nK=B(_1lZ(_1no,_1nJ,_1nF,_)),_1nL=B(_1lZ(_1nn,_1nJ,_1nG,_));return _1nI;case 3:var _1nM=B(_1nq(_1ns.a,_)),_1nN=B(_1me(_1nk,_)),_1nO=E(_1nN),_1nP=B(_1lZ(_1mr,E(_1nO.a),_1nM,_));return _1nO;case 4:var _1nQ=B(_1me(_1nc,_)),_1nR=E(_1nQ),_1nS=E(_1nR.a),_1nT=B(_1lU(_1mD,_1nS,_)),_1nU=eval(E(_1mH)),_1nV=__app2(E(_1nU),E(E(_1nT).a),toJSStr(B(_hA(0,E(_1ns.a),_1)))),_1nW=B(_1lU(_1nl,_1nS,_)),_1nX=__app2(E(_1nU),E(E(_1nW).a),toJSStr(B(_hA(0,E(_1ns.b),_1)))),_1nY=B(_1lU(_1nm,_1nS,_)),_1nZ=__app2(E(_1nU),E(E(_1nY).a),toJSStr(B(_hA(0,E(_1ns.c),_1))));return _1nR;case 5:var _1o0=B(_1me(_1nd,_)),_1o1=E(_1o0),_1o2=E(_1o1.a),_1o3=B(_1lU(_1mD,_1o2,_)),_1o4=eval(E(_1mH)),_1o5=__app2(E(_1o4),E(E(_1o3).a),toJSStr(B(_hA(0,E(_1ns.a),_1)))),_1o6=B(_1lU(_1nl,_1o2,_)),_1o7=__app2(E(_1o4),E(E(_1o6).a),toJSStr(B(_hA(0,E(_1ns.b),_1))));return _1o1;case 6:var _1o8=B(_1mI(_1ns.a,_)),_1o9=B(_1mI(_1ns.b,_)),_1oa=B(_1me(_1ne,_)),_1ob=E(_1oa),_1oc=E(_1ob.a),_1od=B(_1l1(_1mC,_1oc,_1o8,_)),_1oe=B(_1l1(_1mB,_1oc,_1o9,_));return _1ob;case 7:return new F(function(){return _1me(_1nf,_);});break;default:return new F(function(){return _1me(_1ng,_);});}},_1of=function(_1og,_){var _1oh=E(_1og);switch(_1oh._){case 0:return new F(function(){return _1me(_1mo,_);});break;case 1:var _1oi=B(_1of(_1oh.f,_)),_1oj=B(_1of(_1oh.g,_)),_1ok=B(_1mI(_1oh.c,_)),_1ol=B(_1me(_1m7,_)),_1om=E(_1ol),_1on=E(_1om.a),_1oo=B(_1lU(_1mk,_1on,_)),_1op=eval(E(_1mH)),_1oq=__app2(E(_1op),E(E(_1oo).a),toJSStr(B(_hA(0,E(_1oh.a),_1)))),_1or=B(_1lU(_1mn,_1on,_)),_1os=__app2(E(_1op),E(E(_1or).a),toJSStr(B(_hA(0,E(_1oh.b),_1)))),_1ot=B(_1l1(_1mv,_1on,_1ok,_)),_1ou=B(_1lU(_1mm,_1on,_)),_1ov=__app2(E(_1op),E(E(_1ou).a),toJSStr(B(_hA(0,E(_1oh.d),_1)))),_1ow=B(_1lU(_1ml,_1on,_)),_1ox=__app2(E(_1op),E(E(_1ow).a),toJSStr(B(_hA(0,E(_1oh.e),_1)))),_1oy=B(_1kS(_1mq,_1on,_1oi,_)),_1oz=B(_1kS(_1mp,_1on,_1oj,_));return _1om;case 2:var _1oA=B(_1of(_1oh.b,_)),_1oB=B(_1me(_1m8,_)),_1oC=E(_1oB),_1oD=E(_1oC.a),_1oE=B(_1lU(_1mk,_1oD,_)),_1oF=eval(E(_1mH)),_1oG=__app2(E(_1oF),E(E(_1oE).a),toJSStr(B(_hA(0,E(_1oh.a),_1)))),_1oH=B(_1kS(_1mt,_1oD,_1oA,_));return _1oC;case 3:var _1oI=B(_1of(_1oh.f,_)),_1oJ=B(_1me(_1m9,_)),_1oK=B(_1mI(_1oh.d,_)),_1oL=E(_1oJ),_1oM=E(_1oL.a),_1oN=B(_1lU(_1mj,_1oM,_)),_1oO=eval(E(_1mH)),_1oP=__app2(E(_1oO),E(E(_1oN).a),toJSStr(B(_hA(0,E(_1oh.a),_1)))),_1oQ=B(_1lU(_1mi,_1oM,_)),_1oR=__app2(E(_1oO),E(E(_1oQ).a),toJSStr(B(_hA(0,E(_1oh.b),_1)))),_1oS=B(_1lU(_1mw,_1oM,_)),_1oT=__app2(E(_1oO),E(E(_1oS).a),toJSStr(B(_hA(0,E(_1oh.c),_1)))),_1oU=B(_1l1(_1mv,_1oM,_1oK,_)),_1oV=B(_1lU(_1mu,_1oM,_)),_1oW=__app2(E(_1oO),E(E(_1oV).a),toJSStr(B(_hA(0,E(_1oh.e),_1)))),_1oX=B(_1kS(_1mt,_1oM,_1oI,_));return _1oL;case 4:var _1oY=B(_1of(_1oh.a,_)),_1oZ=B(_1of(_1oh.b,_)),_1p0=B(_1me(_1ma,_)),_1p1=E(_1p0),_1p2=E(_1p1.a),_1p3=B(_1kS(_1mq,_1p2,_1oY,_)),_1p4=B(_1kS(_1mp,_1p2,_1oZ,_));return _1p1;case 5:var _1p5=B(_1nq(_1oh.a,_)),_1p6=B(_1of(_1oh.b,_)),_1p7=B(_1of(_1oh.c,_)),_1p8=B(_1me(_1mb,_)),_1p9=E(_1p8),_1pa=E(_1p9.a),_1pb=B(_1lZ(_1mr,_1pa,_1p5,_)),_1pc=B(_1kS(_1mq,_1pa,_1p6,_)),_1pd=B(_1kS(_1mp,_1pa,_1p7,_));return _1p9;default:var _1pe=B(_1nq(_1oh.a,_)),_1pf=B(_1of(_1oh.c,_)),_1pg=B(_1of(_1oh.d,_)),_1ph=B(_1me(_1mc,_)),_1pi=E(_1ph),_1pj=E(_1pi.a),_1pk=B(_1lU(_1ms,_1pj,_)),_1pl=eval(E(_1mH)),_1pm=__app2(E(_1pl),E(E(_1pk).a),toJSStr(B(_hA(0,E(_1oh.b),_1)))),_1pn=B(_1lZ(_1mr,_1pj,_1pe,_)),_1po=B(_1kS(_1mq,_1pj,_1pf,_)),_1pp=B(_1kS(_1mp,_1pj,_1pg,_));return _1pi;}},_1pq=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_1pr=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_1ps=new T(function(){return B(unCStr("base_contract"));}),_1pt=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_1pu=function(_1pv,_){var _1pw=__app0(E(_1pq)),_1px=__app0(E(_1pr)),_1py=B(_19I(B(_l5(_1eg,_1pv))));if(!_1py._){return E(_19Q);}else{if(!E(_1py.b)._){var _1pz=B(_1of(_1py.a,_)),_1pA=B(_1kS(_1ps,_1px,_1pz,_)),_1pB=__app0(E(_1pt)),_1pC=eval(E(_18i)),_1pD=__app1(E(_1pC),toJSStr(E(_1eA))),_1pE=new T(function(){var _1pF=B(_19I(B(_l5(_DG,new T(function(){var _1pG=String(_1pD);return fromJSStr(_1pG);})))));if(!_1pF._){return E(_jT);}else{if(!E(_1pF.b)._){var _1pH=E(_1pF.a);return new T4(0,new T(function(){return B(_gR(_1pH.a));}),new T(function(){return B(_c2(_1pH.b));}),new T(function(){return B(_fb(_1pH.c));}),new T(function(){return B(_5s(_1pH.d));}));}else{return E(_jR);}}});return new F(function(){return _1eh(_1pE,_);});}else{return E(_19P);}}},_1pI=function(_){var _1pJ=eval(E(_18i)),_1pK=__app1(E(_1pJ),toJSStr(E(_1jV)));return new F(function(){return _1pu(new T(function(){var _1pL=String(_1pK);return fromJSStr(_1pL);}),_);});},_1pM=new T(function(){return B(unCStr("contractOutput"));}),_1pN=new T(function(){return B(unCStr("([], [], [], [])"));}),_1pO=new T(function(){return B(unCStr("([], [])"));}),_1pP=new T(function(){return B(_hA(0,0,_1));}),_1pQ="(function (t, s) {document.getElementById(t).value = s})",_1pR=function(_1pS,_1pT,_){var _1pU=eval(E(_1pQ)),_1pV=__app2(E(_1pU),toJSStr(E(_1pS)),toJSStr(E(_1pT)));return new F(function(){return _F8(_);});},_1pW=function(_){var _1pX=__app0(E(_1pq)),_1pY=B(_1eC(_1jV,_1,_)),_1pZ=B(_1pR(_18l,_1pP,_)),_1q0=B(_1eC(_18k,_1pO,_)),_1q1=B(_1eC(_1eA,_1pN,_));return new F(function(){return _1eC(_1pM,_1,_);});},_1q2=1000,_1q3=new T1(2,_1q2),_1q4=3,_1q5=new T1(0,_1q4),_1q6=4,_1q7=new T1(0,_1q6),_1q8=new T2(1,_1q5,_1q7),_1q9=2,_1qa=new T1(0,_1q9),_1qb=1,_1qc=new T1(0,_1qb),_1qd=new T2(1,_1qc,_1qa),_1qe=new T2(1,_1qd,_1q8),_1qf=new T2(6,_1qe,_1q3),_1qg=20,_1qh=5,_1qi=new T6(3,_1q9,_1q9,_1qh,_1qa,_1qg,_137),_1qj=new T6(3,_1qb,_1qb,_1qh,_1qc,_1qg,_137),_1qk=new T2(4,_1qj,_1qi),_1ql=new T6(3,_1q4,_1q4,_1qh,_1q5,_1qg,_137),_1qm=new T6(3,_1q6,_1q6,_1qh,_1q7,_1qg,_137),_1qn=new T2(4,_1ql,_1qm),_1qo=new T2(4,_1qk,_1qn),_1qp=new T3(5,_1qf,_1qo,_137),_1qq=10,_1qr=new T4(6,_1aM,_1qq,_137,_1qp),_1qs=new T1(0,_1qr),_1qt=new T2(1,_1qs,_1),_1qu=0,_1qv=new T1(2,_1qu),_1qw=new T3(3,_1q6,_1q6,_1qv),_1qx={_:1,a:_1q6,b:_1q6,c:_1qw,d:_1qq,e:_1qg,f:_137,g:_137},_1qy=new T1(2,_1qb),_1qz=new T2(6,_1qw,_1qy),_1qA=new T2(5,_1q6,_1q6),_1qB=new T2(1,_1qA,_1qz),_1qC=new T4(6,_1qB,_1qq,_1qx,_137),_1qD=new T3(3,_1q4,_1q4,_1qv),_1qE={_:1,a:_1q4,b:_1q4,c:_1qD,d:_1qq,e:_1qg,f:_137,g:_137},_1qF=new T2(6,_1qD,_1qy),_1qG=new T2(5,_1q4,_1q4),_1qH=new T2(1,_1qG,_1qF),_1qI=new T4(6,_1qH,_1qq,_1qE,_137),_1qJ=new T2(4,_1qI,_1qC),_1qK=new T3(3,_1q9,_1q9,_1qv),_1qL={_:1,a:_1q9,b:_1q9,c:_1qK,d:_1qq,e:_1qg,f:_137,g:_137},_1qM=new T2(6,_1qK,_1qy),_1qN=new T2(5,_1q9,_1q9),_1qO=new T2(1,_1qN,_1qM),_1qP=new T4(6,_1qO,_1qq,_1qL,_137),_1qQ=new T3(3,_1qb,_1qb,_1qv),_1qR={_:1,a:_1qb,b:_1qb,c:_1qQ,d:_1qq,e:_1qg,f:_137,g:_137},_1qS=new T2(6,_1qQ,_1qy),_1qT=new T2(5,_1qb,_1qb),_1qU=new T2(1,_1qT,_1qS),_1qV=new T4(6,_1qU,_1qq,_1qR,_137),_1qW=new T2(4,_1qV,_1qP),_1qX=new T2(4,_1qW,_1qJ),_1qY=new T1(0,_1qX),_1qZ=new T2(1,_1qY,_1qt),_1r0=new T(function(){return B(_1jn(0,_1hS,_1qZ));}),_1r1=function(_){var _1r2=B(_1pW(_)),_1r3=B(_1eC(_1jV,_1r0,_)),_1r4=eval(E(_18i)),_1r5=__app1(E(_1r4),toJSStr(E(_1jV)));return new F(function(){return _1pu(new T(function(){var _1r6=String(_1r5);return fromJSStr(_1r6);}),_);});},_1r7=1,_1r8=new T1(3,_1r7),_1r9=new T1(6,_1r7),_1ra=100,_1rb=new T1(2,_1ra),_1rc=new T1(2,_1rb),_1rd=10,_1re=new T1(6,_1rd),_1rf=200,_1rg=new T1(6,_1rf),_1rh=20,_1ri=new T1(2,_1rh),_1rj=new T2(2,_1r7,_137),_1rk=new T2(5,_1r7,_1r7),_1rl=2,_1rm=new T2(2,_1rl,_137),_1rn=new T2(4,_1rj,_1rm),_1ro=new T6(3,_1r7,_1rl,_1r7,_1ri,_1rf,_1rn),_1rp=new T4(6,_1rk,_1ra,_1rn,_1ro),_1rq={_:1,a:_1rl,b:_1rl,c:_1ri,d:_1rh,e:_1rf,f:_1rp,g:_1rj},_1rr=new T1(0,_1rq),_1rs=new T1(0,_137),_1rt=new T2(1,_1rs,_1),_1ru=new T2(1,_1rr,_1rt),_1rv=new T2(1,_1rg,_1ru),_1rw=new T2(1,_1re,_1rv),_1rx=new T2(1,_1rc,_1rw),_1ry=new T2(1,_1r9,_1rx),_1rz=new T2(1,_1r8,_1ry),_1rA=new T(function(){return B(_1jn(0,_1hV,_1rz));}),_1rB=function(_){var _1rC=B(_1pW(_)),_1rD=B(_1eC(_1jV,_1rA,_)),_1rE=eval(E(_18i)),_1rF=__app1(E(_1rE),toJSStr(E(_1jV)));return new F(function(){return _1pu(new T(function(){var _1rG=String(_1rF);return fromJSStr(_1rG);}),_);});},_1rH=1,_1rI=new T1(3,_1rH),_1rJ=new T1(6,_1rH),_1rK=450,_1rL=new T1(2,_1rK),_1rM=new T1(2,_1rL),_1rN=10,_1rO=new T1(6,_1rN),_1rP=100,_1rQ=new T1(6,_1rP),_1rR=90,_1rS=3,_1rT=0,_1rU=new T3(4,_1rS,_1rS,_1rT),_1rV=2,_1rW=new T3(4,_1rV,_1rV,_1rT),_1rX=new T2(1,_1rW,_1rU),_1rY=new T2(2,_1rW,_1rU),_1rZ=new T3(4,_1rH,_1rH,_1rT),_1s0=new T2(1,_1rZ,_1rY),_1s1=new T2(2,_1s0,_1rX),_1s2=new T3(4,_1rS,_1rS,_1rH),_1s3=new T3(4,_1rV,_1rV,_1rH),_1s4=new T2(1,_1s3,_1s2),_1s5=new T2(2,_1s3,_1s2),_1s6=new T3(4,_1rH,_1rH,_1rH),_1s7=new T2(1,_1s6,_1s5),_1s8=new T2(2,_1s7,_1s4),_1s9=new T2(2,_1s1,_1s8),_1sa=new T2(2,_1rH,_137),_1sb=new T1(0,_1rH),_1sc=new T6(3,_1rH,_1rH,_1rV,_1sb,_1rP,_1sa),_1sd=new T3(5,_1s8,_1sc,_1sa),_1se=new T4(6,_1s9,_1rR,_1sd,_1sa),_1sf=new T1(0,_1se),_1sg=new T2(1,_1sf,_1rt),_1sh=new T2(1,_1rQ,_1sg),_1si=new T2(1,_1rO,_1sh),_1sj=new T2(1,_1rM,_1si),_1sk=new T2(1,_1rJ,_1sj),_1sl=new T2(1,_1rI,_1sk),_1sm=new T(function(){return B(_1jn(0,_1hV,_1sl));}),_1sn=function(_){var _1so=B(_1pW(_)),_1sp=B(_1eC(_1jV,_1sm,_)),_1sq=eval(E(_18i)),_1sr=__app1(E(_1sq),toJSStr(E(_1jV)));return new F(function(){return _1pu(new T(function(){var _1ss=String(_1sr);return fromJSStr(_1ss);}),_);});},_1st=new T(function(){return B(unCStr("NotRedeemed "));}),_1su=function(_1sv,_1sw,_1sx){var _1sy=E(_1sw);if(!_1sy._){var _1sz=function(_1sA){return new F(function(){return _hA(11,E(_1sy.a),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1sy.b),_1sA));})));});};if(E(_1sv)<11){return new F(function(){return _hq(_1st,new T(function(){return B(_1sz(_1sx));},1));});}else{var _1sB=new T(function(){return B(_hq(_1st,new T(function(){return B(_1sz(new T2(1,_hy,_1sx)));},1)));});return new T2(1,_hz,_1sB);}}else{return new F(function(){return _hq(_18E,_1sx);});}},_1sC=0,_1sD=function(_1sE,_1sF,_1sG){var _1sH=new T(function(){var _1sI=function(_1sJ){var _1sK=E(_1sF),_1sL=new T(function(){return B(A3(_is,_hk,new T2(1,function(_1sM){return new F(function(){return _hA(0,E(_1sK.a),_1sM);});},new T2(1,function(_Av){return new F(function(){return _1su(_1sC,_1sK.b,_Av);});},_1)),new T2(1,_hy,_1sJ)));});return new T2(1,_hz,_1sL);};return B(A3(_is,_hk,new T2(1,function(_1sN){return new F(function(){return _hF(0,_1sE,_1sN);});},new T2(1,_1sI,_1)),new T2(1,_hy,_1sG)));});return new T2(0,_hz,_1sH);},_1sO=function(_1sP,_1sQ){var _1sR=E(_1sP),_1sS=B(_1sD(_1sR.a,_1sR.b,_1sQ));return new T2(1,_1sS.a,_1sS.b);},_1sT=function(_1sU,_1sV){return new F(function(){return _iR(_1sO,_1sU,_1sV);});},_1sW=new T(function(){return B(unCStr("ChoiceMade "));}),_1sX=new T(function(){return B(unCStr("DuplicateRedeem "));}),_1sY=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_1sZ=new T(function(){return B(unCStr("CommitRedeemed "));}),_1t0=new T(function(){return B(unCStr("SuccessfulCommit "));}),_1t1=new T(function(){return B(unCStr("FailedPay "));}),_1t2=new T(function(){return B(unCStr("ExpiredPay "));}),_1t3=new T(function(){return B(unCStr("SuccessfulPay "));}),_1t4=function(_1t5,_1t6,_1t7){var _1t8=E(_1t6);switch(_1t8._){case 0:var _1t9=function(_1ta){var _1tb=new T(function(){var _1tc=new T(function(){return B(_hA(11,E(_1t8.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t8.d),_1ta));}))));});return B(_hA(11,E(_1t8.b),new T2(1,_hK,_1tc)));});return new F(function(){return _ih(11,_1t8.a,new T2(1,_hK,_1tb));});};if(_1t5<11){return new F(function(){return _hq(_1t3,new T(function(){return B(_1t9(_1t7));},1));});}else{var _1td=new T(function(){return B(_hq(_1t3,new T(function(){return B(_1t9(new T2(1,_hy,_1t7)));},1)));});return new T2(1,_hz,_1td);}break;case 1:var _1te=function(_1tf){var _1tg=new T(function(){var _1th=new T(function(){return B(_hA(11,E(_1t8.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t8.d),_1tf));}))));});return B(_hA(11,E(_1t8.b),new T2(1,_hK,_1th)));});return new F(function(){return _ih(11,_1t8.a,new T2(1,_hK,_1tg));});};if(_1t5<11){return new F(function(){return _hq(_1t2,new T(function(){return B(_1te(_1t7));},1));});}else{var _1ti=new T(function(){return B(_hq(_1t2,new T(function(){return B(_1te(new T2(1,_hy,_1t7)));},1)));});return new T2(1,_hz,_1ti);}break;case 2:var _1tj=function(_1tk){var _1tl=new T(function(){var _1tm=new T(function(){return B(_hA(11,E(_1t8.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t8.d),_1tk));}))));});return B(_hA(11,E(_1t8.b),new T2(1,_hK,_1tm)));});return new F(function(){return _ih(11,_1t8.a,new T2(1,_hK,_1tl));});};if(_1t5<11){return new F(function(){return _hq(_1t1,new T(function(){return B(_1tj(_1t7));},1));});}else{var _1tn=new T(function(){return B(_hq(_1t1,new T(function(){return B(_1tj(new T2(1,_hy,_1t7)));},1)));});return new T2(1,_hz,_1tn);}break;case 3:var _1to=function(_1tp){var _1tq=new T(function(){var _1tr=new T(function(){return B(_hA(11,E(_1t8.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t8.c),_1tp));}))));});return B(_hF(11,_1t8.a,new T2(1,_hK,_1tr)));},1);return new F(function(){return _hq(_1t0,_1tq);});};if(_1t5<11){return new F(function(){return _1to(_1t7);});}else{return new T2(1,_hz,new T(function(){return B(_1to(new T2(1,_hy,_1t7)));}));}break;case 4:var _1ts=function(_1tt){var _1tu=new T(function(){var _1tv=new T(function(){return B(_hA(11,E(_1t8.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t8.c),_1tt));}))));});return B(_hF(11,_1t8.a,new T2(1,_hK,_1tv)));},1);return new F(function(){return _hq(_1sZ,_1tu);});};if(_1t5<11){return new F(function(){return _1ts(_1t7);});}else{return new T2(1,_hz,new T(function(){return B(_1ts(new T2(1,_hy,_1t7)));}));}break;case 5:var _1tw=function(_1tx){var _1ty=new T(function(){var _1tz=new T(function(){return B(_hA(11,E(_1t8.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t8.c),_1tx));}))));});return B(_hF(11,_1t8.a,new T2(1,_hK,_1tz)));},1);return new F(function(){return _hq(_1sY,_1ty);});};if(_1t5<11){return new F(function(){return _1tw(_1t7);});}else{return new T2(1,_hz,new T(function(){return B(_1tw(new T2(1,_hy,_1t7)));}));}break;case 6:var _1tA=function(_1tB){return new F(function(){return _hF(11,_1t8.a,new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t8.b),_1tB));})));});};if(_1t5<11){return new F(function(){return _hq(_1sX,new T(function(){return B(_1tA(_1t7));},1));});}else{var _1tC=new T(function(){return B(_hq(_1sX,new T(function(){return B(_1tA(new T2(1,_hy,_1t7)));},1)));});return new T2(1,_hz,_1tC);}break;default:var _1tD=function(_1tE){var _1tF=new T(function(){var _1tG=new T(function(){return B(_hA(11,E(_1t8.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t8.c),_1tE));}))));});return B(_j6(11,_1t8.a,new T2(1,_hK,_1tG)));},1);return new F(function(){return _hq(_1sW,_1tF);});};if(_1t5<11){return new F(function(){return _1tD(_1t7);});}else{return new T2(1,_hz,new T(function(){return B(_1tD(new T2(1,_hy,_1t7)));}));}}},_1tH=new T(function(){return B(unAppCStr("[]",_1));}),_1tI=new T2(1,_iP,_1),_1tJ=function(_1tK){var _1tL=E(_1tK);if(!_1tL._){return E(_1tI);}else{var _1tM=new T(function(){return B(_1t4(0,_1tL.a,new T(function(){return B(_1tJ(_1tL.b));})));});return new T2(1,_hj,_1tM);}},_1tN=function(_){var _1tO=E(_1eA),_1tP=toJSStr(_1tO),_1tQ=eval(E(_18i)),_1tR=_1tQ,_1tS=__app1(E(_1tR),_1tP),_1tT=E(_18k),_1tU=__app1(E(_1tR),toJSStr(_1tT)),_1tV=__app0(E(_18j)),_1tW=E(_18l),_1tX=eval(E(_18q)),_1tY=__app1(E(_1tX),toJSStr(_1tW)),_1tZ=new T(function(){var _1u0=B(_19I(B(_l5(_18p,new T(function(){var _1u1=String(_1tY);return fromJSStr(_1u1);})))));if(!_1u0._){return E(_18o);}else{if(!E(_1u0.b)._){return E(_1u0.a);}else{return E(_18n);}}}),_1u2=new T(function(){var _1u3=B(_19I(B(_l5(_1eg,new T(function(){var _1u4=String(_1tV);return fromJSStr(_1u4);})))));if(!_1u3._){return E(_19Q);}else{if(!E(_1u3.b)._){return E(_1u3.a);}else{return E(_19P);}}}),_1u5=new T(function(){var _1u6=B(_19I(B(_l5(_19F,new T(function(){var _1u7=String(_1tU);return fromJSStr(_1u7);})))));if(!_1u6._){return E(_18s);}else{if(!E(_1u6.b)._){var _1u8=E(_1u6.a);return new T2(0,new T(function(){return B(_EV(_1u8.a));}),new T(function(){return B(_5s(_1u8.b));}));}else{return E(_18r);}}}),_1u9=new T(function(){var _1ua=B(_19I(B(_l5(_DG,new T(function(){var _1ub=String(_1tS);return fromJSStr(_1ub);})))));if(!_1ua._){return E(_jT);}else{if(!E(_1ua.b)._){var _1uc=E(_1ua.a);return new T4(0,new T(function(){return B(_gR(_1uc.a));}),new T(function(){return B(_c2(_1uc.b));}),new T(function(){return B(_fb(_1uc.c));}),new T(function(){return B(_5s(_1uc.d));}));}else{return E(_jR);}}}),_1ud=B(_17B(_1u9,_1u5,_1u2,new T2(0,_19G,_1tZ))),_1ue=function(_,_1uf){var _1ug=function(_,_1uh){var _1ui=E(_1ud.a),_1uj=new T(function(){var _1uk=new T(function(){return B(_hc(_1,_1ui.b));}),_1ul=new T(function(){return B(_hc(_1,_1ui.a));});return B(A3(_is,_hk,new T2(1,function(_1um){return new F(function(){return _1sT(_1ul,_1um);});},new T2(1,function(_1un){return new F(function(){return _js(_1uk,_1un);});},_1)),_jv));}),_1uo=B(_1eC(_1tT,new T2(1,_hz,_1uj),_)),_1up=B(_1eC(_1tO,_1pN,_)),_1uq=B(_1pR(_1tW,B(_hA(0,E(_1tZ)+1|0,_1)),_)),_1ur=__app1(E(_1tR),toJSStr(E(_1jV))),_1us=B(_1pu(new T(function(){var _1ut=String(_1ur);return fromJSStr(_1ut);}),_)),_1uu=__app1(E(_1tR),_1tP),_1uv=new T(function(){var _1uw=B(_19I(B(_l5(_DG,new T(function(){var _1ux=String(_1uu);return fromJSStr(_1ux);})))));if(!_1uw._){return E(_jT);}else{if(!E(_1uw.b)._){var _1uy=E(_1uw.a);return new T4(0,new T(function(){return B(_gR(_1uy.a));}),new T(function(){return B(_c2(_1uy.b));}),new T(function(){return B(_fb(_1uy.c));}),new T(function(){return B(_5s(_1uy.d));}));}else{return E(_jR);}}});return new F(function(){return _1eh(_1uv,_);});},_1uz=E(_1ud.b);switch(_1uz._){case 0:var _1uA=B(_1eC(_1jV,_1jQ,_));return new F(function(){return _1ug(_,_1uA);});break;case 1:var _1uB=B(_1eC(_1jV,B(_1jn(0,_1hV,new T2(1,new T1(3,_1uz.a),new T2(1,new T1(6,_1uz.b),new T2(1,new T1(2,_1uz.c),new T2(1,new T1(6,_1uz.d),new T2(1,new T1(6,_1uz.e),new T2(1,new T1(0,_1uz.f),new T2(1,new T1(0,_1uz.g),_1))))))))),_));return new F(function(){return _1ug(_,_1uB);});break;case 2:var _1uC=B(_1eC(_1jV,B(_1jn(0,_1hU,new T2(1,new T1(3,_1uz.a),new T2(1,new T1(0,_1uz.b),_1)))),_));return new F(function(){return _1ug(_,_1uC);});break;case 3:var _1uD=B(_1eC(_1jV,B(_1jn(0,_1hT,new T2(1,new T1(5,_1uz.a),new T2(1,new T1(6,_1uz.b),new T2(1,new T1(6,_1uz.c),new T2(1,new T1(2,_1uz.d),new T2(1,new T1(6,_1uz.e),new T2(1,new T1(0,_1uz.f),_1)))))))),_));return new F(function(){return _1ug(_,_1uD);});break;case 4:var _1uE=B(_1eC(_1jV,B(_1jn(0,_1hS,new T2(1,new T1(0,_1uz.a),new T2(1,new T1(0,_1uz.b),_1)))),_));return new F(function(){return _1ug(_,_1uE);});break;case 5:var _1uF=B(_1eC(_1jV,B(_1jn(0,_1hR,new T2(1,new T1(1,_1uz.a),new T2(1,new T1(0,_1uz.b),new T2(1,new T1(0,_1uz.c),_1))))),_));return new F(function(){return _1ug(_,_1uF);});break;default:var _1uG=B(_1eC(_1jV,B(_1jn(0,_1hQ,new T2(1,new T1(1,_1uz.a),new T2(1,new T1(6,_1uz.b),new T2(1,new T1(0,_1uz.c),new T2(1,new T1(0,_1uz.d),_1)))))),_));return new F(function(){return _1ug(_,_1uG);});}},_1uH=E(_1ud.c);if(!_1uH._){var _1uI=B(_1eC(_1pM,_1tH,_));return new F(function(){return _1ue(_,_1uI);});}else{var _1uJ=new T(function(){return B(_1t4(0,_1uH.a,new T(function(){return B(_1tJ(_1uH.b));})));}),_1uK=B(_1eC(_1pM,new T2(1,_iQ,_1uJ),_));return new F(function(){return _1ue(_,_1uK);});}},_1uL=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uM=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uN=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uO=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uP=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uQ=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uR=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uS=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uT=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uU=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uV=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uW=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uX=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uY=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uZ=function(_){return new F(function(){return __jsNull();});},_1v0=function(_1v1){var _1v2=B(A1(_1v1,_));return E(_1v2);},_1v3=new T(function(){return B(_1v0(_1uZ));}),_1v4=new T(function(){return E(_1v3);}),_1v5=function(_){var _1v6=eval(E(_18i)),_1v7=__app1(E(_1v6),toJSStr(E(_1eA))),_1v8=new T(function(){var _1v9=B(_19I(B(_l5(_DG,new T(function(){var _1va=String(_1v7);return fromJSStr(_1va);})))));if(!_1v9._){return E(_jT);}else{if(!E(_1v9.b)._){var _1vb=E(_1v9.a);return new T4(0,new T(function(){return B(_gR(_1vb.a));}),new T(function(){return B(_c2(_1vb.b));}),new T(function(){return B(_fb(_1vb.c));}),new T(function(){return B(_5s(_1vb.d));}));}else{return E(_jR);}}});return new F(function(){return _1eh(_1v8,_);});},_1vc=function(_){var _1vd=eval(E(_18i)),_1ve=__app1(E(_1vd),toJSStr(E(_1jV))),_1vf=B(_1pu(new T(function(){var _1vg=String(_1ve);return fromJSStr(_1vg);}),_)),_1vh=__createJSFunc(0,function(_){var _1vi=B(_1pW(_));return _1v4;}),_1vj=__app2(E(_1uV),"clear_workspace",_1vh),_1vk=__createJSFunc(0,function(_){var _1vl=B(_1jW(_));return _1v4;}),_1vm=__app2(E(_1uU),"b2c",_1vk),_1vn=__createJSFunc(0,function(_){var _1vo=B(_1pI(_));return _1v4;}),_1vp=__app2(E(_1uT),"c2b",_1vn),_1vq=function(_1vr){var _1vs=new T(function(){var _1vt=Number(E(_1vr));return jsTrunc(_1vt);}),_1vu=function(_1vv){var _1vw=new T(function(){var _1vx=Number(E(_1vv));return jsTrunc(_1vx);}),_1vy=function(_1vz){var _1vA=new T(function(){var _1vB=Number(E(_1vz));return jsTrunc(_1vB);}),_1vC=function(_1vD,_){var _1vE=B(_1gc(_1vs,_1vw,_1vA,new T(function(){var _1vF=Number(E(_1vD));return jsTrunc(_1vF);}),_));return _1v4;};return E(_1vC);};return E(_1vy);};return E(_1vu);},_1vG=__createJSFunc(5,E(_1vq)),_1vH=__app2(E(_1uS),"commit",_1vG),_1vI=function(_1vJ){var _1vK=new T(function(){var _1vL=Number(E(_1vJ));return jsTrunc(_1vL);}),_1vM=function(_1vN){var _1vO=new T(function(){var _1vP=Number(E(_1vN));return jsTrunc(_1vP);}),_1vQ=function(_1vR,_){var _1vS=B(_1fU(_1vK,_1vO,new T(function(){var _1vT=Number(E(_1vR));return jsTrunc(_1vT);}),_));return _1v4;};return E(_1vQ);};return E(_1vM);},_1vU=__createJSFunc(4,E(_1vI)),_1vV=__app2(E(_1uR),"redeem",_1vU),_1vW=function(_1vX){var _1vY=new T(function(){var _1vZ=Number(E(_1vX));return jsTrunc(_1vZ);}),_1w0=function(_1w1){var _1w2=new T(function(){var _1w3=Number(E(_1w1));return jsTrunc(_1w3);}),_1w4=function(_1w5,_){var _1w6=B(_1eH(_1vY,_1w2,new T(function(){var _1w7=Number(E(_1w5));return jsTrunc(_1w7);}),_));return _1v4;};return E(_1w4);};return E(_1w0);},_1w8=__createJSFunc(4,E(_1vW)),_1w9=__app2(E(_1uQ),"claim",_1w8),_1wa=function(_1wb){var _1wc=new T(function(){var _1wd=Number(E(_1wb));return jsTrunc(_1wd);}),_1we=function(_1wf){var _1wg=new T(function(){var _1wh=Number(E(_1wf));return jsTrunc(_1wh);}),_1wi=function(_1wj,_){var _1wk=B(_1hp(_1wc,_1wg,new T(function(){var _1wl=Number(E(_1wj));return jsTrunc(_1wl);}),_));return _1v4;};return E(_1wi);};return E(_1we);},_1wm=__createJSFunc(4,E(_1wa)),_1wn=__app2(E(_1uP),"choose",_1wm),_1wo=__createJSFunc(0,function(_){var _1wp=B(_1tN(_));return _1v4;}),_1wq=__app2(E(_1uO),"execute",_1wo),_1wr=__createJSFunc(0,function(_){var _1ws=B(_1v5(_));return _1v4;}),_1wt=__app2(E(_1uN),"refreshActions",_1wr),_1wu=function(_1wv,_){var _1ww=B(_1hl(new T(function(){var _1wx=String(E(_1wv));return fromJSStr(_1wx);}),_));return _1v4;},_1wy=__createJSFunc(2,E(_1wu)),_1wz=__app2(E(_1uM),"addAction",_1wy),_1wA=function(_1wB){var _1wC=new T(function(){var _1wD=String(E(_1wB));return fromJSStr(_1wD);}),_1wE=function(_1wF,_){var _1wG=B(_1hK(_1wC,new T(function(){var _1wH=Number(E(_1wF));return jsTrunc(_1wH);}),_));return _1v4;};return E(_1wE);},_1wI=__createJSFunc(3,E(_1wA)),_1wJ=__app2(E(_1uL),"addActionWithNum",_1wI),_1wK=__createJSFunc(0,function(_){var _1wL=B(_1rB(_));return _1v4;}),_1wM=__app2(E(_1uY),"depositIncentive",_1wK),_1wN=__createJSFunc(0,function(_){var _1wO=B(_1r1(_));return _1v4;}),_1wP=__app2(E(_1uX),"crowdFunding",_1wN),_1wQ=__createJSFunc(0,function(_){var _1wR=B(_1sn(_));return _1v4;}),_1wS=__app2(E(_1uW),"escrow",_1wQ),_1wT=__app1(E(_1vd),toJSStr(E(_1eA))),_1wU=new T(function(){var _1wV=B(_19I(B(_l5(_DG,new T(function(){var _1wW=String(_1wT);return fromJSStr(_1wW);})))));if(!_1wV._){return E(_jT);}else{if(!E(_1wV.b)._){var _1wX=E(_1wV.a);return new T4(0,new T(function(){return B(_gR(_1wX.a));}),new T(function(){return B(_c2(_1wX.b));}),new T(function(){return B(_fb(_1wX.c));}),new T(function(){return B(_5s(_1wX.d));}));}else{return E(_jR);}}}),_1wY=B(_1eh(_1wU,_));return _h9;},_1wZ=function(_){return new F(function(){return _1vc(_);});};
var hasteMain = function() {B(A(_1wZ, [0]));};window.onload = hasteMain;