"use strict";
var __haste_prog_id = '0a26d6c6c24d56a6cfa219dabf081568c6a0e3239a6e8b25d32615da580f2ffe';
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

var _0=0,_1=new T(function(){return B(unCStr("codeArea"));}),_2=function(_){return _0;},_3="(function (t, s) {document.getElementById(t).value = s})",_4=function(_5,_6,_){var _7=eval(E(_3)),_8=__app2(E(_7),toJSStr(E(_5)),toJSStr(E(_6)));return new F(function(){return _2(_);});},_9=__Z,_a=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_b=new T(function(){return B(err(_a));}),_c=function(_d,_e){var _f=E(_d);return (_f._==0)?E(_e):new T2(1,_f.a,new T(function(){return B(_c(_f.b,_e));}));},_g=new T(function(){return B(unCStr("base"));}),_h=new T(function(){return B(unCStr("Control.Exception.Base"));}),_i=new T(function(){return B(unCStr("PatternMatchFail"));}),_j=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_g,_h,_i),_k=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_j,_9,_9),_l=function(_m){return E(_k);},_n=function(_o){return E(E(_o).a);},_p=function(_q,_r,_s){var _t=B(A1(_q,_)),_u=B(A1(_r,_)),_v=hs_eqWord64(_t.a,_u.a);if(!_v){return __Z;}else{var _w=hs_eqWord64(_t.b,_u.b);return (!_w)?__Z:new T1(1,_s);}},_x=function(_y){var _z=E(_y);return new F(function(){return _p(B(_n(_z.a)),_l,_z.b);});},_A=function(_B){return E(E(_B).a);},_C=function(_D){return new T2(0,_E,_D);},_F=function(_G,_H){return new F(function(){return _c(E(_G).a,_H);});},_I=44,_J=93,_K=91,_L=function(_M,_N,_O){var _P=E(_N);if(!_P._){return new F(function(){return unAppCStr("[]",_O);});}else{var _Q=new T(function(){var _R=new T(function(){var _S=function(_T){var _U=E(_T);if(!_U._){return E(new T2(1,_J,_O));}else{var _V=new T(function(){return B(A2(_M,_U.a,new T(function(){return B(_S(_U.b));})));});return new T2(1,_I,_V);}};return B(_S(_P.b));});return B(A2(_M,_P.a,_R));});return new T2(1,_K,_Q);}},_W=function(_X,_Y){return new F(function(){return _L(_F,_X,_Y);});},_Z=function(_10,_11,_12){return new F(function(){return _c(E(_11).a,_12);});},_13=new T3(0,_Z,_A,_W),_E=new T(function(){return new T5(0,_l,_13,_C,_x,_A);}),_14=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_15=function(_16){return E(E(_16).c);},_17=function(_18,_19){return new F(function(){return die(new T(function(){return B(A2(_15,_19,_18));}));});},_1a=function(_1b,_1c){return new F(function(){return _17(_1b,_1c);});},_1d=function(_1e,_1f){var _1g=E(_1f);if(!_1g._){return new T2(0,_9,_9);}else{var _1h=_1g.a;if(!B(A1(_1e,_1h))){return new T2(0,_9,_1g);}else{var _1i=new T(function(){var _1j=B(_1d(_1e,_1g.b));return new T2(0,_1j.a,_1j.b);});return new T2(0,new T2(1,_1h,new T(function(){return E(E(_1i).a);})),new T(function(){return E(E(_1i).b);}));}}},_1k=32,_1l=new T(function(){return B(unCStr("\n"));}),_1m=function(_1n){return (E(_1n)==124)?false:true;},_1o=function(_1p,_1q){var _1r=B(_1d(_1m,B(unCStr(_1p)))),_1s=_1r.a,_1t=function(_1u,_1v){var _1w=new T(function(){var _1x=new T(function(){return B(_c(_1q,new T(function(){return B(_c(_1v,_1l));},1)));});return B(unAppCStr(": ",_1x));},1);return new F(function(){return _c(_1u,_1w);});},_1y=E(_1r.b);if(!_1y._){return new F(function(){return _1t(_1s,_9);});}else{if(E(_1y.a)==124){return new F(function(){return _1t(_1s,new T2(1,_1k,_1y.b));});}else{return new F(function(){return _1t(_1s,_9);});}}},_1z=function(_1A){return new F(function(){return _1a(new T1(0,new T(function(){return B(_1o(_1A,_14));})),_E);});},_1B=new T(function(){return B(_1z("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_1C=function(_1D,_1E){while(1){var _1F=B((function(_1G,_1H){var _1I=E(_1G);switch(_1I._){case 0:var _1J=E(_1H);if(!_1J._){return __Z;}else{_1D=B(A1(_1I.a,_1J.a));_1E=_1J.b;return __continue;}break;case 1:var _1K=B(A1(_1I.a,_1H)),_1L=_1H;_1D=_1K;_1E=_1L;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_1I.a,_1H),new T(function(){return B(_1C(_1I.b,_1H));}));default:return E(_1I.a);}})(_1D,_1E));if(_1F!=__continue){return _1F;}}},_1M=function(_1N,_1O){var _1P=function(_1Q){var _1R=E(_1O);if(_1R._==3){return new T2(3,_1R.a,new T(function(){return B(_1M(_1N,_1R.b));}));}else{var _1S=E(_1N);if(_1S._==2){return E(_1R);}else{var _1T=E(_1R);if(_1T._==2){return E(_1S);}else{var _1U=function(_1V){var _1W=E(_1T);if(_1W._==4){var _1X=function(_1Y){return new T1(4,new T(function(){return B(_c(B(_1C(_1S,_1Y)),_1W.a));}));};return new T1(1,_1X);}else{var _1Z=E(_1S);if(_1Z._==1){var _20=_1Z.a,_21=E(_1W);if(!_21._){return new T1(1,function(_22){return new F(function(){return _1M(B(A1(_20,_22)),_21);});});}else{var _23=function(_24){return new F(function(){return _1M(B(A1(_20,_24)),new T(function(){return B(A1(_21.a,_24));}));});};return new T1(1,_23);}}else{var _25=E(_1W);if(!_25._){return E(_1B);}else{var _26=function(_27){return new F(function(){return _1M(_1Z,new T(function(){return B(A1(_25.a,_27));}));});};return new T1(1,_26);}}}},_28=E(_1S);switch(_28._){case 1:var _29=E(_1T);if(_29._==4){var _2a=function(_2b){return new T1(4,new T(function(){return B(_c(B(_1C(B(A1(_28.a,_2b)),_2b)),_29.a));}));};return new T1(1,_2a);}else{return new F(function(){return _1U(_);});}break;case 4:var _2c=_28.a,_2d=E(_1T);switch(_2d._){case 0:var _2e=function(_2f){var _2g=new T(function(){return B(_c(_2c,new T(function(){return B(_1C(_2d,_2f));},1)));});return new T1(4,_2g);};return new T1(1,_2e);case 1:var _2h=function(_2i){var _2j=new T(function(){return B(_c(_2c,new T(function(){return B(_1C(B(A1(_2d.a,_2i)),_2i));},1)));});return new T1(4,_2j);};return new T1(1,_2h);default:return new T1(4,new T(function(){return B(_c(_2c,_2d.a));}));}break;default:return new F(function(){return _1U(_);});}}}}},_2k=E(_1N);switch(_2k._){case 0:var _2l=E(_1O);if(!_2l._){var _2m=function(_2n){return new F(function(){return _1M(B(A1(_2k.a,_2n)),new T(function(){return B(A1(_2l.a,_2n));}));});};return new T1(0,_2m);}else{return new F(function(){return _1P(_);});}break;case 3:return new T2(3,_2k.a,new T(function(){return B(_1M(_2k.b,_1O));}));default:return new F(function(){return _1P(_);});}},_2o=11,_2p=new T(function(){return B(unCStr("IdentCC"));}),_2q=new T(function(){return B(unCStr("("));}),_2r=new T(function(){return B(unCStr(")"));}),_2s=function(_2t,_2u){while(1){var _2v=E(_2t);if(!_2v._){return (E(_2u)._==0)?true:false;}else{var _2w=E(_2u);if(!_2w._){return false;}else{if(E(_2v.a)!=E(_2w.a)){return false;}else{_2t=_2v.b;_2u=_2w.b;continue;}}}}},_2x=function(_2y,_2z){return E(_2y)!=E(_2z);},_2A=function(_2B,_2C){return E(_2B)==E(_2C);},_2D=new T2(0,_2A,_2x),_2E=function(_2F,_2G){while(1){var _2H=E(_2F);if(!_2H._){return (E(_2G)._==0)?true:false;}else{var _2I=E(_2G);if(!_2I._){return false;}else{if(E(_2H.a)!=E(_2I.a)){return false;}else{_2F=_2H.b;_2G=_2I.b;continue;}}}}},_2J=function(_2K,_2L){return (!B(_2E(_2K,_2L)))?true:false;},_2M=new T2(0,_2E,_2J),_2N=function(_2O,_2P){var _2Q=E(_2O);switch(_2Q._){case 0:return new T1(0,function(_2R){return new F(function(){return _2N(B(A1(_2Q.a,_2R)),_2P);});});case 1:return new T1(1,function(_2S){return new F(function(){return _2N(B(A1(_2Q.a,_2S)),_2P);});});case 2:return new T0(2);case 3:return new F(function(){return _1M(B(A1(_2P,_2Q.a)),new T(function(){return B(_2N(_2Q.b,_2P));}));});break;default:var _2T=function(_2U){var _2V=E(_2U);if(!_2V._){return __Z;}else{var _2W=E(_2V.a);return new F(function(){return _c(B(_1C(B(A1(_2P,_2W.a)),_2W.b)),new T(function(){return B(_2T(_2V.b));},1));});}},_2X=B(_2T(_2Q.a));return (_2X._==0)?new T0(2):new T1(4,_2X);}},_2Y=new T0(2),_2Z=function(_30){return new T2(3,_30,_2Y);},_31=function(_32,_33){var _34=E(_32);if(!_34){return new F(function(){return A1(_33,_0);});}else{var _35=new T(function(){return B(_31(_34-1|0,_33));});return new T1(0,function(_36){return E(_35);});}},_37=function(_38,_39,_3a){var _3b=new T(function(){return B(A1(_38,_2Z));}),_3c=function(_3d,_3e,_3f,_3g){while(1){var _3h=B((function(_3i,_3j,_3k,_3l){var _3m=E(_3i);switch(_3m._){case 0:var _3n=E(_3j);if(!_3n._){return new F(function(){return A1(_39,_3l);});}else{var _3o=_3k+1|0,_3p=_3l;_3d=B(A1(_3m.a,_3n.a));_3e=_3n.b;_3f=_3o;_3g=_3p;return __continue;}break;case 1:var _3q=B(A1(_3m.a,_3j)),_3r=_3j,_3o=_3k,_3p=_3l;_3d=_3q;_3e=_3r;_3f=_3o;_3g=_3p;return __continue;case 2:return new F(function(){return A1(_39,_3l);});break;case 3:var _3s=new T(function(){return B(_2N(_3m,_3l));});return new F(function(){return _31(_3k,function(_3t){return E(_3s);});});break;default:return new F(function(){return _2N(_3m,_3l);});}})(_3d,_3e,_3f,_3g));if(_3h!=__continue){return _3h;}}};return function(_3u){return new F(function(){return _3c(_3b,_3u,0,_3a);});};},_3v=function(_3w){return new F(function(){return A1(_3w,_9);});},_3x=function(_3y,_3z){var _3A=function(_3B){var _3C=E(_3B);if(!_3C._){return E(_3v);}else{var _3D=_3C.a;if(!B(A1(_3y,_3D))){return E(_3v);}else{var _3E=new T(function(){return B(_3A(_3C.b));}),_3F=function(_3G){var _3H=new T(function(){return B(A1(_3E,function(_3I){return new F(function(){return A1(_3G,new T2(1,_3D,_3I));});}));});return new T1(0,function(_3J){return E(_3H);});};return E(_3F);}}};return function(_3K){return new F(function(){return A2(_3A,_3K,_3z);});};},_3L=new T0(6),_3M=function(_3N){return E(_3N);},_3O=new T(function(){return B(unCStr("valDig: Bad base"));}),_3P=new T(function(){return B(err(_3O));}),_3Q=function(_3R,_3S){var _3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=new T(function(){return B(A1(_3V,_9));});return function(_3Y){return new F(function(){return A1(_3Y,_3X);});};}else{var _3Z=E(_3W.a),_40=function(_41){var _42=new T(function(){return B(_3T(_3W.b,function(_43){return new F(function(){return A1(_3V,new T2(1,_41,_43));});}));}),_44=function(_45){var _46=new T(function(){return B(A1(_42,_45));});return new T1(0,function(_47){return E(_46);});};return E(_44);};switch(E(_3R)){case 8:if(48>_3Z){var _48=new T(function(){return B(A1(_3V,_9));});return function(_49){return new F(function(){return A1(_49,_48);});};}else{if(_3Z>55){var _4a=new T(function(){return B(A1(_3V,_9));});return function(_4b){return new F(function(){return A1(_4b,_4a);});};}else{return new F(function(){return _40(_3Z-48|0);});}}break;case 10:if(48>_3Z){var _4c=new T(function(){return B(A1(_3V,_9));});return function(_4d){return new F(function(){return A1(_4d,_4c);});};}else{if(_3Z>57){var _4e=new T(function(){return B(A1(_3V,_9));});return function(_4f){return new F(function(){return A1(_4f,_4e);});};}else{return new F(function(){return _40(_3Z-48|0);});}}break;case 16:if(48>_3Z){if(97>_3Z){if(65>_3Z){var _4g=new T(function(){return B(A1(_3V,_9));});return function(_4h){return new F(function(){return A1(_4h,_4g);});};}else{if(_3Z>70){var _4i=new T(function(){return B(A1(_3V,_9));});return function(_4j){return new F(function(){return A1(_4j,_4i);});};}else{return new F(function(){return _40((_3Z-65|0)+10|0);});}}}else{if(_3Z>102){if(65>_3Z){var _4k=new T(function(){return B(A1(_3V,_9));});return function(_4l){return new F(function(){return A1(_4l,_4k);});};}else{if(_3Z>70){var _4m=new T(function(){return B(A1(_3V,_9));});return function(_4n){return new F(function(){return A1(_4n,_4m);});};}else{return new F(function(){return _40((_3Z-65|0)+10|0);});}}}else{return new F(function(){return _40((_3Z-97|0)+10|0);});}}}else{if(_3Z>57){if(97>_3Z){if(65>_3Z){var _4o=new T(function(){return B(A1(_3V,_9));});return function(_4p){return new F(function(){return A1(_4p,_4o);});};}else{if(_3Z>70){var _4q=new T(function(){return B(A1(_3V,_9));});return function(_4r){return new F(function(){return A1(_4r,_4q);});};}else{return new F(function(){return _40((_3Z-65|0)+10|0);});}}}else{if(_3Z>102){if(65>_3Z){var _4s=new T(function(){return B(A1(_3V,_9));});return function(_4t){return new F(function(){return A1(_4t,_4s);});};}else{if(_3Z>70){var _4u=new T(function(){return B(A1(_3V,_9));});return function(_4v){return new F(function(){return A1(_4v,_4u);});};}else{return new F(function(){return _40((_3Z-65|0)+10|0);});}}}else{return new F(function(){return _40((_3Z-97|0)+10|0);});}}}else{return new F(function(){return _40(_3Z-48|0);});}}break;default:return E(_3P);}}},_4w=function(_4x){var _4y=E(_4x);if(!_4y._){return new T0(2);}else{return new F(function(){return A1(_3S,_4y);});}};return function(_4z){return new F(function(){return A3(_3T,_4z,_3M,_4w);});};},_4A=16,_4B=8,_4C=function(_4D){var _4E=function(_4F){return new F(function(){return A1(_4D,new T1(5,new T2(0,_4B,_4F)));});},_4G=function(_4H){return new F(function(){return A1(_4D,new T1(5,new T2(0,_4A,_4H)));});},_4I=function(_4J){switch(E(_4J)){case 79:return new T1(1,B(_3Q(_4B,_4E)));case 88:return new T1(1,B(_3Q(_4A,_4G)));case 111:return new T1(1,B(_3Q(_4B,_4E)));case 120:return new T1(1,B(_3Q(_4A,_4G)));default:return new T0(2);}};return function(_4K){return (E(_4K)==48)?E(new T1(0,_4I)):new T0(2);};},_4L=function(_4M){return new T1(0,B(_4C(_4M)));},_4N=__Z,_4O=function(_4P){return new F(function(){return A1(_4P,_4N);});},_4Q=function(_4R){return new F(function(){return A1(_4R,_4N);});},_4S=10,_4T=new T1(0,1),_4U=new T1(0,2147483647),_4V=function(_4W,_4X){while(1){var _4Y=E(_4W);if(!_4Y._){var _4Z=_4Y.a,_50=E(_4X);if(!_50._){var _51=_50.a,_52=addC(_4Z,_51);if(!E(_52.b)){return new T1(0,_52.a);}else{_4W=new T1(1,I_fromInt(_4Z));_4X=new T1(1,I_fromInt(_51));continue;}}else{_4W=new T1(1,I_fromInt(_4Z));_4X=_50;continue;}}else{var _53=E(_4X);if(!_53._){_4W=_4Y;_4X=new T1(1,I_fromInt(_53.a));continue;}else{return new T1(1,I_add(_4Y.a,_53.a));}}}},_54=new T(function(){return B(_4V(_4U,_4T));}),_55=function(_56){var _57=E(_56);if(!_57._){var _58=E(_57.a);return (_58==( -2147483648))?E(_54):new T1(0, -_58);}else{return new T1(1,I_negate(_57.a));}},_59=new T1(0,10),_5a=function(_5b,_5c){while(1){var _5d=E(_5b);if(!_5d._){return E(_5c);}else{var _5e=_5c+1|0;_5b=_5d.b;_5c=_5e;continue;}}},_5f=function(_5g,_5h){var _5i=E(_5h);return (_5i._==0)?__Z:new T2(1,new T(function(){return B(A1(_5g,_5i.a));}),new T(function(){return B(_5f(_5g,_5i.b));}));},_5j=function(_5k){return new T1(0,_5k);},_5l=function(_5m){return new F(function(){return _5j(E(_5m));});},_5n=new T(function(){return B(unCStr("this should not happen"));}),_5o=new T(function(){return B(err(_5n));}),_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){var _5v=_5u.a;if(!(imul(_5t,_5v)|0)){return new T1(0,imul(_5t,_5v)|0);}else{_5q=new T1(1,I_fromInt(_5t));_5r=new T1(1,I_fromInt(_5v));continue;}}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5w=E(_5r);if(!_5w._){_5q=_5s;_5r=new T1(1,I_fromInt(_5w.a));continue;}else{return new T1(1,I_mul(_5s.a,_5w.a));}}}},_5x=function(_5y,_5z){var _5A=E(_5z);if(!_5A._){return __Z;}else{var _5B=E(_5A.b);return (_5B._==0)?E(_5o):new T2(1,B(_4V(B(_5p(_5A.a,_5y)),_5B.a)),new T(function(){return B(_5x(_5y,_5B.b));}));}},_5C=new T1(0,0),_5D=function(_5E,_5F,_5G){while(1){var _5H=B((function(_5I,_5J,_5K){var _5L=E(_5K);if(!_5L._){return E(_5C);}else{if(!E(_5L.b)._){return E(_5L.a);}else{var _5M=E(_5J);if(_5M<=40){var _5N=function(_5O,_5P){while(1){var _5Q=E(_5P);if(!_5Q._){return E(_5O);}else{var _5R=B(_4V(B(_5p(_5O,_5I)),_5Q.a));_5O=_5R;_5P=_5Q.b;continue;}}};return new F(function(){return _5N(_5C,_5L);});}else{var _5S=B(_5p(_5I,_5I));if(!(_5M%2)){var _5T=B(_5x(_5I,_5L));_5E=_5S;_5F=quot(_5M+1|0,2);_5G=_5T;return __continue;}else{var _5T=B(_5x(_5I,new T2(1,_5C,_5L)));_5E=_5S;_5F=quot(_5M+1|0,2);_5G=_5T;return __continue;}}}}})(_5E,_5F,_5G));if(_5H!=__continue){return _5H;}}},_5U=function(_5V,_5W){return new F(function(){return _5D(_5V,new T(function(){return B(_5a(_5W,0));},1),B(_5f(_5l,_5W)));});},_5X=function(_5Y){var _5Z=new T(function(){var _60=new T(function(){var _61=function(_62){return new F(function(){return A1(_5Y,new T1(1,new T(function(){return B(_5U(_59,_62));})));});};return new T1(1,B(_3Q(_4S,_61)));}),_63=function(_64){if(E(_64)==43){var _65=function(_66){return new F(function(){return A1(_5Y,new T1(1,new T(function(){return B(_5U(_59,_66));})));});};return new T1(1,B(_3Q(_4S,_65)));}else{return new T0(2);}},_67=function(_68){if(E(_68)==45){var _69=function(_6a){return new F(function(){return A1(_5Y,new T1(1,new T(function(){return B(_55(B(_5U(_59,_6a))));})));});};return new T1(1,B(_3Q(_4S,_69)));}else{return new T0(2);}};return B(_1M(B(_1M(new T1(0,_67),new T1(0,_63))),_60));});return new F(function(){return _1M(new T1(0,function(_6b){return (E(_6b)==101)?E(_5Z):new T0(2);}),new T1(0,function(_6c){return (E(_6c)==69)?E(_5Z):new T0(2);}));});},_6d=function(_6e){var _6f=function(_6g){return new F(function(){return A1(_6e,new T1(1,_6g));});};return function(_6h){return (E(_6h)==46)?new T1(1,B(_3Q(_4S,_6f))):new T0(2);};},_6i=function(_6j){return new T1(0,B(_6d(_6j)));},_6k=function(_6l){var _6m=function(_6n){var _6o=function(_6p){return new T1(1,B(_37(_5X,_4O,function(_6q){return new F(function(){return A1(_6l,new T1(5,new T3(1,_6n,_6p,_6q)));});})));};return new T1(1,B(_37(_6i,_4Q,_6o)));};return new F(function(){return _3Q(_4S,_6m);});},_6r=function(_6s){return new T1(1,B(_6k(_6s)));},_6t=function(_6u){return E(E(_6u).a);},_6v=function(_6w,_6x,_6y){while(1){var _6z=E(_6y);if(!_6z._){return false;}else{if(!B(A3(_6t,_6w,_6x,_6z.a))){_6y=_6z.b;continue;}else{return true;}}}},_6A=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_6B=function(_6C){return new F(function(){return _6v(_2D,_6C,_6A);});},_6D=false,_6E=true,_6F=function(_6G){var _6H=new T(function(){return B(A1(_6G,_4B));}),_6I=new T(function(){return B(A1(_6G,_4A));});return function(_6J){switch(E(_6J)){case 79:return E(_6H);case 88:return E(_6I);case 111:return E(_6H);case 120:return E(_6I);default:return new T0(2);}};},_6K=function(_6L){return new T1(0,B(_6F(_6L)));},_6M=function(_6N){return new F(function(){return A1(_6N,_4S);});},_6O=function(_6P,_6Q){var _6R=jsShowI(_6P);return new F(function(){return _c(fromJSStr(_6R),_6Q);});},_6S=41,_6T=40,_6U=function(_6V,_6W,_6X){if(_6W>=0){return new F(function(){return _6O(_6W,_6X);});}else{if(_6V<=6){return new F(function(){return _6O(_6W,_6X);});}else{return new T2(1,_6T,new T(function(){var _6Y=jsShowI(_6W);return B(_c(fromJSStr(_6Y),new T2(1,_6S,_6X)));}));}}},_6Z=function(_70){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_6U(9,_70,_9));}))));});},_71=function(_72){var _73=E(_72);if(!_73._){return E(_73.a);}else{return new F(function(){return I_toInt(_73.a);});}},_74=function(_75,_76){var _77=E(_75);if(!_77._){var _78=_77.a,_79=E(_76);return (_79._==0)?_78<=_79.a:I_compareInt(_79.a,_78)>=0;}else{var _7a=_77.a,_7b=E(_76);return (_7b._==0)?I_compareInt(_7a,_7b.a)<=0:I_compare(_7a,_7b.a)<=0;}},_7c=function(_7d){return new T0(2);},_7e=function(_7f){var _7g=E(_7f);if(!_7g._){return E(_7c);}else{var _7h=_7g.a,_7i=E(_7g.b);if(!_7i._){return E(_7h);}else{var _7j=new T(function(){return B(_7e(_7i));}),_7k=function(_7l){return new F(function(){return _1M(B(A1(_7h,_7l)),new T(function(){return B(A1(_7j,_7l));}));});};return E(_7k);}}},_7m=function(_7n,_7o){var _7p=function(_7q,_7r,_7s){var _7t=E(_7q);if(!_7t._){return new F(function(){return A1(_7s,_7n);});}else{var _7u=E(_7r);if(!_7u._){return new T0(2);}else{if(E(_7t.a)!=E(_7u.a)){return new T0(2);}else{var _7v=new T(function(){return B(_7p(_7t.b,_7u.b,_7s));});return new T1(0,function(_7w){return E(_7v);});}}}};return function(_7x){return new F(function(){return _7p(_7n,_7x,_7o);});};},_7y=new T(function(){return B(unCStr("SO"));}),_7z=14,_7A=function(_7B){var _7C=new T(function(){return B(A1(_7B,_7z));});return new T1(1,B(_7m(_7y,function(_7D){return E(_7C);})));},_7E=new T(function(){return B(unCStr("SOH"));}),_7F=1,_7G=function(_7H){var _7I=new T(function(){return B(A1(_7H,_7F));});return new T1(1,B(_7m(_7E,function(_7J){return E(_7I);})));},_7K=function(_7L){return new T1(1,B(_37(_7G,_7A,_7L)));},_7M=new T(function(){return B(unCStr("NUL"));}),_7N=0,_7O=function(_7P){var _7Q=new T(function(){return B(A1(_7P,_7N));});return new T1(1,B(_7m(_7M,function(_7R){return E(_7Q);})));},_7S=new T(function(){return B(unCStr("STX"));}),_7T=2,_7U=function(_7V){var _7W=new T(function(){return B(A1(_7V,_7T));});return new T1(1,B(_7m(_7S,function(_7X){return E(_7W);})));},_7Y=new T(function(){return B(unCStr("ETX"));}),_7Z=3,_80=function(_81){var _82=new T(function(){return B(A1(_81,_7Z));});return new T1(1,B(_7m(_7Y,function(_83){return E(_82);})));},_84=new T(function(){return B(unCStr("EOT"));}),_85=4,_86=function(_87){var _88=new T(function(){return B(A1(_87,_85));});return new T1(1,B(_7m(_84,function(_89){return E(_88);})));},_8a=new T(function(){return B(unCStr("ENQ"));}),_8b=5,_8c=function(_8d){var _8e=new T(function(){return B(A1(_8d,_8b));});return new T1(1,B(_7m(_8a,function(_8f){return E(_8e);})));},_8g=new T(function(){return B(unCStr("ACK"));}),_8h=6,_8i=function(_8j){var _8k=new T(function(){return B(A1(_8j,_8h));});return new T1(1,B(_7m(_8g,function(_8l){return E(_8k);})));},_8m=new T(function(){return B(unCStr("BEL"));}),_8n=7,_8o=function(_8p){var _8q=new T(function(){return B(A1(_8p,_8n));});return new T1(1,B(_7m(_8m,function(_8r){return E(_8q);})));},_8s=new T(function(){return B(unCStr("BS"));}),_8t=8,_8u=function(_8v){var _8w=new T(function(){return B(A1(_8v,_8t));});return new T1(1,B(_7m(_8s,function(_8x){return E(_8w);})));},_8y=new T(function(){return B(unCStr("HT"));}),_8z=9,_8A=function(_8B){var _8C=new T(function(){return B(A1(_8B,_8z));});return new T1(1,B(_7m(_8y,function(_8D){return E(_8C);})));},_8E=new T(function(){return B(unCStr("LF"));}),_8F=10,_8G=function(_8H){var _8I=new T(function(){return B(A1(_8H,_8F));});return new T1(1,B(_7m(_8E,function(_8J){return E(_8I);})));},_8K=new T(function(){return B(unCStr("VT"));}),_8L=11,_8M=function(_8N){var _8O=new T(function(){return B(A1(_8N,_8L));});return new T1(1,B(_7m(_8K,function(_8P){return E(_8O);})));},_8Q=new T(function(){return B(unCStr("FF"));}),_8R=12,_8S=function(_8T){var _8U=new T(function(){return B(A1(_8T,_8R));});return new T1(1,B(_7m(_8Q,function(_8V){return E(_8U);})));},_8W=new T(function(){return B(unCStr("CR"));}),_8X=13,_8Y=function(_8Z){var _90=new T(function(){return B(A1(_8Z,_8X));});return new T1(1,B(_7m(_8W,function(_91){return E(_90);})));},_92=new T(function(){return B(unCStr("SI"));}),_93=15,_94=function(_95){var _96=new T(function(){return B(A1(_95,_93));});return new T1(1,B(_7m(_92,function(_97){return E(_96);})));},_98=new T(function(){return B(unCStr("DLE"));}),_99=16,_9a=function(_9b){var _9c=new T(function(){return B(A1(_9b,_99));});return new T1(1,B(_7m(_98,function(_9d){return E(_9c);})));},_9e=new T(function(){return B(unCStr("DC1"));}),_9f=17,_9g=function(_9h){var _9i=new T(function(){return B(A1(_9h,_9f));});return new T1(1,B(_7m(_9e,function(_9j){return E(_9i);})));},_9k=new T(function(){return B(unCStr("DC2"));}),_9l=18,_9m=function(_9n){var _9o=new T(function(){return B(A1(_9n,_9l));});return new T1(1,B(_7m(_9k,function(_9p){return E(_9o);})));},_9q=new T(function(){return B(unCStr("DC3"));}),_9r=19,_9s=function(_9t){var _9u=new T(function(){return B(A1(_9t,_9r));});return new T1(1,B(_7m(_9q,function(_9v){return E(_9u);})));},_9w=new T(function(){return B(unCStr("DC4"));}),_9x=20,_9y=function(_9z){var _9A=new T(function(){return B(A1(_9z,_9x));});return new T1(1,B(_7m(_9w,function(_9B){return E(_9A);})));},_9C=new T(function(){return B(unCStr("NAK"));}),_9D=21,_9E=function(_9F){var _9G=new T(function(){return B(A1(_9F,_9D));});return new T1(1,B(_7m(_9C,function(_9H){return E(_9G);})));},_9I=new T(function(){return B(unCStr("SYN"));}),_9J=22,_9K=function(_9L){var _9M=new T(function(){return B(A1(_9L,_9J));});return new T1(1,B(_7m(_9I,function(_9N){return E(_9M);})));},_9O=new T(function(){return B(unCStr("ETB"));}),_9P=23,_9Q=function(_9R){var _9S=new T(function(){return B(A1(_9R,_9P));});return new T1(1,B(_7m(_9O,function(_9T){return E(_9S);})));},_9U=new T(function(){return B(unCStr("CAN"));}),_9V=24,_9W=function(_9X){var _9Y=new T(function(){return B(A1(_9X,_9V));});return new T1(1,B(_7m(_9U,function(_9Z){return E(_9Y);})));},_a0=new T(function(){return B(unCStr("EM"));}),_a1=25,_a2=function(_a3){var _a4=new T(function(){return B(A1(_a3,_a1));});return new T1(1,B(_7m(_a0,function(_a5){return E(_a4);})));},_a6=new T(function(){return B(unCStr("SUB"));}),_a7=26,_a8=function(_a9){var _aa=new T(function(){return B(A1(_a9,_a7));});return new T1(1,B(_7m(_a6,function(_ab){return E(_aa);})));},_ac=new T(function(){return B(unCStr("ESC"));}),_ad=27,_ae=function(_af){var _ag=new T(function(){return B(A1(_af,_ad));});return new T1(1,B(_7m(_ac,function(_ah){return E(_ag);})));},_ai=new T(function(){return B(unCStr("FS"));}),_aj=28,_ak=function(_al){var _am=new T(function(){return B(A1(_al,_aj));});return new T1(1,B(_7m(_ai,function(_an){return E(_am);})));},_ao=new T(function(){return B(unCStr("GS"));}),_ap=29,_aq=function(_ar){var _as=new T(function(){return B(A1(_ar,_ap));});return new T1(1,B(_7m(_ao,function(_at){return E(_as);})));},_au=new T(function(){return B(unCStr("RS"));}),_av=30,_aw=function(_ax){var _ay=new T(function(){return B(A1(_ax,_av));});return new T1(1,B(_7m(_au,function(_az){return E(_ay);})));},_aA=new T(function(){return B(unCStr("US"));}),_aB=31,_aC=function(_aD){var _aE=new T(function(){return B(A1(_aD,_aB));});return new T1(1,B(_7m(_aA,function(_aF){return E(_aE);})));},_aG=new T(function(){return B(unCStr("SP"));}),_aH=32,_aI=function(_aJ){var _aK=new T(function(){return B(A1(_aJ,_aH));});return new T1(1,B(_7m(_aG,function(_aL){return E(_aK);})));},_aM=new T(function(){return B(unCStr("DEL"));}),_aN=127,_aO=function(_aP){var _aQ=new T(function(){return B(A1(_aP,_aN));});return new T1(1,B(_7m(_aM,function(_aR){return E(_aQ);})));},_aS=new T2(1,_aO,_9),_aT=new T2(1,_aI,_aS),_aU=new T2(1,_aC,_aT),_aV=new T2(1,_aw,_aU),_aW=new T2(1,_aq,_aV),_aX=new T2(1,_ak,_aW),_aY=new T2(1,_ae,_aX),_aZ=new T2(1,_a8,_aY),_b0=new T2(1,_a2,_aZ),_b1=new T2(1,_9W,_b0),_b2=new T2(1,_9Q,_b1),_b3=new T2(1,_9K,_b2),_b4=new T2(1,_9E,_b3),_b5=new T2(1,_9y,_b4),_b6=new T2(1,_9s,_b5),_b7=new T2(1,_9m,_b6),_b8=new T2(1,_9g,_b7),_b9=new T2(1,_9a,_b8),_ba=new T2(1,_94,_b9),_bb=new T2(1,_8Y,_ba),_bc=new T2(1,_8S,_bb),_bd=new T2(1,_8M,_bc),_be=new T2(1,_8G,_bd),_bf=new T2(1,_8A,_be),_bg=new T2(1,_8u,_bf),_bh=new T2(1,_8o,_bg),_bi=new T2(1,_8i,_bh),_bj=new T2(1,_8c,_bi),_bk=new T2(1,_86,_bj),_bl=new T2(1,_80,_bk),_bm=new T2(1,_7U,_bl),_bn=new T2(1,_7O,_bm),_bo=new T2(1,_7K,_bn),_bp=new T(function(){return B(_7e(_bo));}),_bq=34,_br=new T1(0,1114111),_bs=92,_bt=39,_bu=function(_bv){var _bw=new T(function(){return B(A1(_bv,_8n));}),_bx=new T(function(){return B(A1(_bv,_8t));}),_by=new T(function(){return B(A1(_bv,_8z));}),_bz=new T(function(){return B(A1(_bv,_8F));}),_bA=new T(function(){return B(A1(_bv,_8L));}),_bB=new T(function(){return B(A1(_bv,_8R));}),_bC=new T(function(){return B(A1(_bv,_8X));}),_bD=new T(function(){return B(A1(_bv,_bs));}),_bE=new T(function(){return B(A1(_bv,_bt));}),_bF=new T(function(){return B(A1(_bv,_bq));}),_bG=new T(function(){var _bH=function(_bI){var _bJ=new T(function(){return B(_5j(E(_bI)));}),_bK=function(_bL){var _bM=B(_5U(_bJ,_bL));if(!B(_74(_bM,_br))){return new T0(2);}else{return new F(function(){return A1(_bv,new T(function(){var _bN=B(_71(_bM));if(_bN>>>0>1114111){return B(_6Z(_bN));}else{return _bN;}}));});}};return new T1(1,B(_3Q(_bI,_bK)));},_bO=new T(function(){var _bP=new T(function(){return B(A1(_bv,_aB));}),_bQ=new T(function(){return B(A1(_bv,_av));}),_bR=new T(function(){return B(A1(_bv,_ap));}),_bS=new T(function(){return B(A1(_bv,_aj));}),_bT=new T(function(){return B(A1(_bv,_ad));}),_bU=new T(function(){return B(A1(_bv,_a7));}),_bV=new T(function(){return B(A1(_bv,_a1));}),_bW=new T(function(){return B(A1(_bv,_9V));}),_bX=new T(function(){return B(A1(_bv,_9P));}),_bY=new T(function(){return B(A1(_bv,_9J));}),_bZ=new T(function(){return B(A1(_bv,_9D));}),_c0=new T(function(){return B(A1(_bv,_9x));}),_c1=new T(function(){return B(A1(_bv,_9r));}),_c2=new T(function(){return B(A1(_bv,_9l));}),_c3=new T(function(){return B(A1(_bv,_9f));}),_c4=new T(function(){return B(A1(_bv,_99));}),_c5=new T(function(){return B(A1(_bv,_93));}),_c6=new T(function(){return B(A1(_bv,_7z));}),_c7=new T(function(){return B(A1(_bv,_8h));}),_c8=new T(function(){return B(A1(_bv,_8b));}),_c9=new T(function(){return B(A1(_bv,_85));}),_ca=new T(function(){return B(A1(_bv,_7Z));}),_cb=new T(function(){return B(A1(_bv,_7T));}),_cc=new T(function(){return B(A1(_bv,_7F));}),_cd=new T(function(){return B(A1(_bv,_7N));}),_ce=function(_cf){switch(E(_cf)){case 64:return E(_cd);case 65:return E(_cc);case 66:return E(_cb);case 67:return E(_ca);case 68:return E(_c9);case 69:return E(_c8);case 70:return E(_c7);case 71:return E(_bw);case 72:return E(_bx);case 73:return E(_by);case 74:return E(_bz);case 75:return E(_bA);case 76:return E(_bB);case 77:return E(_bC);case 78:return E(_c6);case 79:return E(_c5);case 80:return E(_c4);case 81:return E(_c3);case 82:return E(_c2);case 83:return E(_c1);case 84:return E(_c0);case 85:return E(_bZ);case 86:return E(_bY);case 87:return E(_bX);case 88:return E(_bW);case 89:return E(_bV);case 90:return E(_bU);case 91:return E(_bT);case 92:return E(_bS);case 93:return E(_bR);case 94:return E(_bQ);case 95:return E(_bP);default:return new T0(2);}};return B(_1M(new T1(0,function(_cg){return (E(_cg)==94)?E(new T1(0,_ce)):new T0(2);}),new T(function(){return B(A1(_bp,_bv));})));});return B(_1M(new T1(1,B(_37(_6K,_6M,_bH))),_bO));});return new F(function(){return _1M(new T1(0,function(_ch){switch(E(_ch)){case 34:return E(_bF);case 39:return E(_bE);case 92:return E(_bD);case 97:return E(_bw);case 98:return E(_bx);case 102:return E(_bB);case 110:return E(_bz);case 114:return E(_bC);case 116:return E(_by);case 118:return E(_bA);default:return new T0(2);}}),_bG);});},_ci=function(_cj){return new F(function(){return A1(_cj,_0);});},_ck=function(_cl){var _cm=E(_cl);if(!_cm._){return E(_ci);}else{var _cn=E(_cm.a),_co=_cn>>>0,_cp=new T(function(){return B(_ck(_cm.b));});if(_co>887){var _cq=u_iswspace(_cn);if(!E(_cq)){return E(_ci);}else{var _cr=function(_cs){var _ct=new T(function(){return B(A1(_cp,_cs));});return new T1(0,function(_cu){return E(_ct);});};return E(_cr);}}else{var _cv=E(_co);if(_cv==32){var _cw=function(_cx){var _cy=new T(function(){return B(A1(_cp,_cx));});return new T1(0,function(_cz){return E(_cy);});};return E(_cw);}else{if(_cv-9>>>0>4){if(E(_cv)==160){var _cA=function(_cB){var _cC=new T(function(){return B(A1(_cp,_cB));});return new T1(0,function(_cD){return E(_cC);});};return E(_cA);}else{return E(_ci);}}else{var _cE=function(_cF){var _cG=new T(function(){return B(A1(_cp,_cF));});return new T1(0,function(_cH){return E(_cG);});};return E(_cE);}}}}},_cI=function(_cJ){var _cK=new T(function(){return B(_cI(_cJ));}),_cL=function(_cM){return (E(_cM)==92)?E(_cK):new T0(2);},_cN=function(_cO){return E(new T1(0,_cL));},_cP=new T1(1,function(_cQ){return new F(function(){return A2(_ck,_cQ,_cN);});}),_cR=new T(function(){return B(_bu(function(_cS){return new F(function(){return A1(_cJ,new T2(0,_cS,_6E));});}));}),_cT=function(_cU){var _cV=E(_cU);if(_cV==38){return E(_cK);}else{var _cW=_cV>>>0;if(_cW>887){var _cX=u_iswspace(_cV);return (E(_cX)==0)?new T0(2):E(_cP);}else{var _cY=E(_cW);return (_cY==32)?E(_cP):(_cY-9>>>0>4)?(E(_cY)==160)?E(_cP):new T0(2):E(_cP);}}};return new F(function(){return _1M(new T1(0,function(_cZ){return (E(_cZ)==92)?E(new T1(0,_cT)):new T0(2);}),new T1(0,function(_d0){var _d1=E(_d0);if(E(_d1)==92){return E(_cR);}else{return new F(function(){return A1(_cJ,new T2(0,_d1,_6D));});}}));});},_d2=function(_d3,_d4){var _d5=new T(function(){return B(A1(_d4,new T1(1,new T(function(){return B(A1(_d3,_9));}))));}),_d6=function(_d7){var _d8=E(_d7),_d9=E(_d8.a);if(E(_d9)==34){if(!E(_d8.b)){return E(_d5);}else{return new F(function(){return _d2(function(_da){return new F(function(){return A1(_d3,new T2(1,_d9,_da));});},_d4);});}}else{return new F(function(){return _d2(function(_db){return new F(function(){return A1(_d3,new T2(1,_d9,_db));});},_d4);});}};return new F(function(){return _cI(_d6);});},_dc=new T(function(){return B(unCStr("_\'"));}),_dd=function(_de){var _df=u_iswalnum(_de);if(!E(_df)){return new F(function(){return _6v(_2D,_de,_dc);});}else{return true;}},_dg=function(_dh){return new F(function(){return _dd(E(_dh));});},_di=new T(function(){return B(unCStr(",;()[]{}`"));}),_dj=new T(function(){return B(unCStr("=>"));}),_dk=new T2(1,_dj,_9),_dl=new T(function(){return B(unCStr("~"));}),_dm=new T2(1,_dl,_dk),_dn=new T(function(){return B(unCStr("@"));}),_do=new T2(1,_dn,_dm),_dp=new T(function(){return B(unCStr("->"));}),_dq=new T2(1,_dp,_do),_dr=new T(function(){return B(unCStr("<-"));}),_ds=new T2(1,_dr,_dq),_dt=new T(function(){return B(unCStr("|"));}),_du=new T2(1,_dt,_ds),_dv=new T(function(){return B(unCStr("\\"));}),_dw=new T2(1,_dv,_du),_dx=new T(function(){return B(unCStr("="));}),_dy=new T2(1,_dx,_dw),_dz=new T(function(){return B(unCStr("::"));}),_dA=new T2(1,_dz,_dy),_dB=new T(function(){return B(unCStr(".."));}),_dC=new T2(1,_dB,_dA),_dD=function(_dE){var _dF=new T(function(){return B(A1(_dE,_3L));}),_dG=new T(function(){var _dH=new T(function(){var _dI=function(_dJ){var _dK=new T(function(){return B(A1(_dE,new T1(0,_dJ)));});return new T1(0,function(_dL){return (E(_dL)==39)?E(_dK):new T0(2);});};return B(_bu(_dI));}),_dM=function(_dN){var _dO=E(_dN);switch(E(_dO)){case 39:return new T0(2);case 92:return E(_dH);default:var _dP=new T(function(){return B(A1(_dE,new T1(0,_dO)));});return new T1(0,function(_dQ){return (E(_dQ)==39)?E(_dP):new T0(2);});}},_dR=new T(function(){var _dS=new T(function(){return B(_d2(_3M,_dE));}),_dT=new T(function(){var _dU=new T(function(){var _dV=new T(function(){var _dW=function(_dX){var _dY=E(_dX),_dZ=u_iswalpha(_dY);return (E(_dZ)==0)?(E(_dY)==95)?new T1(1,B(_3x(_dg,function(_e0){return new F(function(){return A1(_dE,new T1(3,new T2(1,_dY,_e0)));});}))):new T0(2):new T1(1,B(_3x(_dg,function(_e1){return new F(function(){return A1(_dE,new T1(3,new T2(1,_dY,_e1)));});})));};return B(_1M(new T1(0,_dW),new T(function(){return new T1(1,B(_37(_4L,_6r,_dE)));})));}),_e2=function(_e3){return (!B(_6v(_2D,_e3,_6A)))?new T0(2):new T1(1,B(_3x(_6B,function(_e4){var _e5=new T2(1,_e3,_e4);if(!B(_6v(_2M,_e5,_dC))){return new F(function(){return A1(_dE,new T1(4,_e5));});}else{return new F(function(){return A1(_dE,new T1(2,_e5));});}})));};return B(_1M(new T1(0,_e2),_dV));});return B(_1M(new T1(0,function(_e6){if(!B(_6v(_2D,_e6,_di))){return new T0(2);}else{return new F(function(){return A1(_dE,new T1(2,new T2(1,_e6,_9)));});}}),_dU));});return B(_1M(new T1(0,function(_e7){return (E(_e7)==34)?E(_dS):new T0(2);}),_dT));});return B(_1M(new T1(0,function(_e8){return (E(_e8)==39)?E(new T1(0,_dM)):new T0(2);}),_dR));});return new F(function(){return _1M(new T1(1,function(_e9){return (E(_e9)._==0)?E(_dF):new T0(2);}),_dG);});},_ea=0,_eb=function(_ec,_ed){var _ee=new T(function(){var _ef=new T(function(){var _eg=function(_eh){var _ei=new T(function(){var _ej=new T(function(){return B(A1(_ed,_eh));});return B(_dD(function(_ek){var _el=E(_ek);return (_el._==2)?(!B(_2s(_el.a,_2r)))?new T0(2):E(_ej):new T0(2);}));}),_em=function(_en){return E(_ei);};return new T1(1,function(_eo){return new F(function(){return A2(_ck,_eo,_em);});});};return B(A2(_ec,_ea,_eg));});return B(_dD(function(_ep){var _eq=E(_ep);return (_eq._==2)?(!B(_2s(_eq.a,_2q)))?new T0(2):E(_ef):new T0(2);}));}),_er=function(_es){return E(_ee);};return function(_et){return new F(function(){return A2(_ck,_et,_er);});};},_eu=function(_ev,_ew){var _ex=function(_ey){var _ez=new T(function(){return B(A1(_ev,_ey));}),_eA=function(_eB){return new F(function(){return _1M(B(A1(_ez,_eB)),new T(function(){return new T1(1,B(_eb(_ex,_eB)));}));});};return E(_eA);},_eC=new T(function(){return B(A1(_ev,_ew));}),_eD=function(_eE){return new F(function(){return _1M(B(A1(_eC,_eE)),new T(function(){return new T1(1,B(_eb(_ex,_eE)));}));});};return E(_eD);},_eF=function(_eG,_eH){var _eI=function(_eJ,_eK){var _eL=function(_eM){return new F(function(){return A1(_eK,new T(function(){return  -E(_eM);}));});},_eN=new T(function(){return B(_dD(function(_eO){return new F(function(){return A3(_eG,_eO,_eJ,_eL);});}));}),_eP=function(_eQ){return E(_eN);},_eR=function(_eS){return new F(function(){return A2(_ck,_eS,_eP);});},_eT=new T(function(){return B(_dD(function(_eU){var _eV=E(_eU);if(_eV._==4){var _eW=E(_eV.a);if(!_eW._){return new F(function(){return A3(_eG,_eV,_eJ,_eK);});}else{if(E(_eW.a)==45){if(!E(_eW.b)._){return E(new T1(1,_eR));}else{return new F(function(){return A3(_eG,_eV,_eJ,_eK);});}}else{return new F(function(){return A3(_eG,_eV,_eJ,_eK);});}}}else{return new F(function(){return A3(_eG,_eV,_eJ,_eK);});}}));}),_eX=function(_eY){return E(_eT);};return new T1(1,function(_eZ){return new F(function(){return A2(_ck,_eZ,_eX);});});};return new F(function(){return _eu(_eI,_eH);});},_f0=function(_f1){var _f2=E(_f1);if(!_f2._){var _f3=_f2.b,_f4=new T(function(){return B(_5D(new T(function(){return B(_5j(E(_f2.a)));}),new T(function(){return B(_5a(_f3,0));},1),B(_5f(_5l,_f3))));});return new T1(1,_f4);}else{return (E(_f2.b)._==0)?(E(_f2.c)._==0)?new T1(1,new T(function(){return B(_5U(_59,_f2.a));})):__Z:__Z;}},_f5=function(_f6,_f7){return new T0(2);},_f8=function(_f9){var _fa=E(_f9);if(_fa._==5){var _fb=B(_f0(_fa.a));if(!_fb._){return E(_f5);}else{var _fc=new T(function(){return B(_71(_fb.a));});return function(_fd,_fe){return new F(function(){return A1(_fe,_fc);});};}}else{return E(_f5);}},_ff=function(_fg,_fh){if(_fg>10){return new T0(2);}else{var _fi=new T(function(){var _fj=new T(function(){return B(A3(_eF,_f8,_2o,function(_fk){return new F(function(){return A1(_fh,_fk);});}));});return B(_dD(function(_fl){var _fm=E(_fl);return (_fm._==3)?(!B(_2s(_fm.a,_2p)))?new T0(2):E(_fj):new T0(2);}));}),_fn=function(_fo){return E(_fi);};return new T1(1,function(_fp){return new F(function(){return A2(_ck,_fp,_fn);});});}},_fq=function(_fr,_fs){return new F(function(){return _ff(E(_fr),_fs);});},_ft=new T(function(){return B(unCStr("IdentPay"));}),_fu=function(_fv,_fw){if(_fv>10){return new T0(2);}else{var _fx=new T(function(){var _fy=new T(function(){return B(A3(_eF,_f8,_2o,function(_fz){return new F(function(){return A1(_fw,_fz);});}));});return B(_dD(function(_fA){var _fB=E(_fA);return (_fB._==3)?(!B(_2s(_fB.a,_ft)))?new T0(2):E(_fy):new T0(2);}));}),_fC=function(_fD){return E(_fx);};return new T1(1,function(_fE){return new F(function(){return A2(_ck,_fE,_fC);});});}},_fF=function(_fG,_fH){return new F(function(){return _fu(E(_fG),_fH);});},_fI=new T(function(){return B(unCStr("IdentChoice"));}),_fJ=function(_fK,_fL){if(_fK>10){return new T0(2);}else{var _fM=new T(function(){var _fN=new T(function(){return B(A3(_eF,_f8,_2o,function(_fO){return new F(function(){return A1(_fL,_fO);});}));});return B(_dD(function(_fP){var _fQ=E(_fP);return (_fQ._==3)?(!B(_2s(_fQ.a,_fI)))?new T0(2):E(_fN):new T0(2);}));}),_fR=function(_fS){return E(_fM);};return new T1(1,function(_fT){return new F(function(){return A2(_ck,_fT,_fR);});});}},_fU=function(_fV,_fW){return new F(function(){return _fJ(E(_fV),_fW);});},_fX=new T(function(){return B(unCStr("ConstMoney"));}),_fY=new T(function(){return B(unCStr("AvailableMoney"));}),_fZ=new T(function(){return B(unCStr("AddMoney"));}),_g0=function(_g1,_g2){var _g3=new T(function(){var _g4=new T(function(){if(_g1>10){return new T0(2);}else{var _g5=new T(function(){var _g6=new T(function(){return B(A3(_eF,_f8,_2o,function(_g7){return new F(function(){return A1(_g2,new T1(2,_g7));});}));});return B(_dD(function(_g8){var _g9=E(_g8);return (_g9._==3)?(!B(_2s(_g9.a,_fX)))?new T0(2):E(_g6):new T0(2);}));}),_ga=function(_gb){return E(_g5);};return new T1(1,function(_gc){return new F(function(){return A2(_ck,_gc,_ga);});});}});if(_g1>10){return B(_1M(_2Y,_g4));}else{var _gd=new T(function(){var _ge=new T(function(){var _gf=function(_gg){return new F(function(){return A3(_eu,_gh,_2o,function(_gi){return new F(function(){return A1(_g2,new T2(1,_gg,_gi));});});});};return B(A3(_eu,_gh,_2o,_gf));});return B(_dD(function(_gj){var _gk=E(_gj);return (_gk._==3)?(!B(_2s(_gk.a,_fZ)))?new T0(2):E(_ge):new T0(2);}));}),_gl=function(_gm){return E(_gd);};return B(_1M(new T1(1,function(_gn){return new F(function(){return A2(_ck,_gn,_gl);});}),_g4));}});if(_g1>10){return new F(function(){return _1M(_2Y,_g3);});}else{var _go=new T(function(){var _gp=new T(function(){return B(A3(_eu,_fq,_2o,function(_gq){return new F(function(){return A1(_g2,new T1(0,_gq));});}));});return B(_dD(function(_gr){var _gs=E(_gr);return (_gs._==3)?(!B(_2s(_gs.a,_fY)))?new T0(2):E(_gp):new T0(2);}));}),_gt=function(_gu){return E(_go);};return new F(function(){return _1M(new T1(1,function(_gv){return new F(function(){return A2(_ck,_gv,_gt);});}),_g3);});}},_gh=function(_gw,_gx){return new F(function(){return _g0(E(_gw),_gx);});},_gy=new T0(7),_gz=function(_gA,_gB){return new F(function(){return A1(_gB,_gy);});},_gC=new T(function(){return B(unCStr("TrueObs"));}),_gD=new T2(0,_gC,_gz),_gE=new T0(8),_gF=function(_gG,_gH){return new F(function(){return A1(_gH,_gE);});},_gI=new T(function(){return B(unCStr("FalseObs"));}),_gJ=new T2(0,_gI,_gF),_gK=new T2(1,_gJ,_9),_gL=new T2(1,_gD,_gK),_gM=function(_gN,_gO,_gP){var _gQ=E(_gN);if(!_gQ._){return new T0(2);}else{var _gR=E(_gQ.a),_gS=_gR.a,_gT=new T(function(){return B(A2(_gR.b,_gO,_gP));}),_gU=new T(function(){return B(_dD(function(_gV){var _gW=E(_gV);switch(_gW._){case 3:return (!B(_2s(_gS,_gW.a)))?new T0(2):E(_gT);case 4:return (!B(_2s(_gS,_gW.a)))?new T0(2):E(_gT);default:return new T0(2);}}));}),_gX=function(_gY){return E(_gU);};return new F(function(){return _1M(new T1(1,function(_gZ){return new F(function(){return A2(_ck,_gZ,_gX);});}),new T(function(){return B(_gM(_gQ.b,_gO,_gP));}));});}},_h0=new T(function(){return B(unCStr("ValueGE"));}),_h1=new T(function(){return B(unCStr("PersonChoseSomething"));}),_h2=new T(function(){return B(unCStr("PersonChoseThis"));}),_h3=new T(function(){return B(unCStr("BelowTimeout"));}),_h4=new T(function(){return B(unCStr("AndObs"));}),_h5=new T(function(){return B(unCStr("OrObs"));}),_h6=new T(function(){return B(unCStr("NotObs"));}),_h7=function(_h8,_h9){var _ha=new T(function(){var _hb=E(_h8),_hc=new T(function(){var _hd=new T(function(){var _he=new T(function(){var _hf=new T(function(){var _hg=new T(function(){var _hh=new T(function(){if(_hb>10){return new T0(2);}else{var _hi=new T(function(){var _hj=new T(function(){var _hk=function(_hl){return new F(function(){return A3(_eu,_gh,_2o,function(_hm){return new F(function(){return A1(_h9,new T2(6,_hl,_hm));});});});};return B(A3(_eu,_gh,_2o,_hk));});return B(_dD(function(_hn){var _ho=E(_hn);return (_ho._==3)?(!B(_2s(_ho.a,_h0)))?new T0(2):E(_hj):new T0(2);}));}),_hp=function(_hq){return E(_hi);};return new T1(1,function(_hr){return new F(function(){return A2(_ck,_hr,_hp);});});}});if(_hb>10){return B(_1M(_2Y,_hh));}else{var _hs=new T(function(){var _ht=new T(function(){var _hu=function(_hv){return new F(function(){return A3(_eF,_f8,_2o,function(_hw){return new F(function(){return A1(_h9,new T2(5,_hv,_hw));});});});};return B(A3(_eu,_fU,_2o,_hu));});return B(_dD(function(_hx){var _hy=E(_hx);return (_hy._==3)?(!B(_2s(_hy.a,_h1)))?new T0(2):E(_ht):new T0(2);}));}),_hz=function(_hA){return E(_hs);};return B(_1M(new T1(1,function(_hB){return new F(function(){return A2(_ck,_hB,_hz);});}),_hh));}});if(_hb>10){return B(_1M(_2Y,_hg));}else{var _hC=new T(function(){var _hD=new T(function(){var _hE=function(_hF){var _hG=function(_hH){return new F(function(){return A3(_eF,_f8,_2o,function(_hI){return new F(function(){return A1(_h9,new T3(4,_hF,_hH,_hI));});});});};return new F(function(){return A3(_eF,_f8,_2o,_hG);});};return B(A3(_eu,_fU,_2o,_hE));});return B(_dD(function(_hJ){var _hK=E(_hJ);return (_hK._==3)?(!B(_2s(_hK.a,_h2)))?new T0(2):E(_hD):new T0(2);}));}),_hL=function(_hM){return E(_hC);};return B(_1M(new T1(1,function(_hN){return new F(function(){return A2(_ck,_hN,_hL);});}),_hg));}});if(_hb>10){return B(_1M(_2Y,_hf));}else{var _hO=new T(function(){var _hP=new T(function(){return B(A3(_eu,_h7,_2o,function(_hQ){return new F(function(){return A1(_h9,new T1(3,_hQ));});}));});return B(_dD(function(_hR){var _hS=E(_hR);return (_hS._==3)?(!B(_2s(_hS.a,_h6)))?new T0(2):E(_hP):new T0(2);}));}),_hT=function(_hU){return E(_hO);};return B(_1M(new T1(1,function(_hV){return new F(function(){return A2(_ck,_hV,_hT);});}),_hf));}});if(_hb>10){return B(_1M(_2Y,_he));}else{var _hW=new T(function(){var _hX=new T(function(){var _hY=function(_hZ){return new F(function(){return A3(_eu,_h7,_2o,function(_i0){return new F(function(){return A1(_h9,new T2(2,_hZ,_i0));});});});};return B(A3(_eu,_h7,_2o,_hY));});return B(_dD(function(_i1){var _i2=E(_i1);return (_i2._==3)?(!B(_2s(_i2.a,_h5)))?new T0(2):E(_hX):new T0(2);}));}),_i3=function(_i4){return E(_hW);};return B(_1M(new T1(1,function(_i5){return new F(function(){return A2(_ck,_i5,_i3);});}),_he));}});if(_hb>10){return B(_1M(_2Y,_hd));}else{var _i6=new T(function(){var _i7=new T(function(){var _i8=function(_i9){return new F(function(){return A3(_eu,_h7,_2o,function(_ia){return new F(function(){return A1(_h9,new T2(1,_i9,_ia));});});});};return B(A3(_eu,_h7,_2o,_i8));});return B(_dD(function(_ib){var _ic=E(_ib);return (_ic._==3)?(!B(_2s(_ic.a,_h4)))?new T0(2):E(_i7):new T0(2);}));}),_id=function(_ie){return E(_i6);};return B(_1M(new T1(1,function(_if){return new F(function(){return A2(_ck,_if,_id);});}),_hd));}});if(_hb>10){return B(_1M(_2Y,_hc));}else{var _ig=new T(function(){var _ih=new T(function(){return B(A3(_eF,_f8,_2o,function(_ii){return new F(function(){return A1(_h9,new T1(0,_ii));});}));});return B(_dD(function(_ij){var _ik=E(_ij);return (_ik._==3)?(!B(_2s(_ik.a,_h3)))?new T0(2):E(_ih):new T0(2);}));}),_il=function(_im){return E(_ig);};return B(_1M(new T1(1,function(_in){return new F(function(){return A2(_ck,_in,_il);});}),_hc));}});return new F(function(){return _1M(B(_gM(_gL,_h8,_h9)),_ha);});},_io=__Z,_ip=new T(function(){return B(unCStr("Null"));}),_iq=new T(function(){return B(unCStr("CommitCash"));}),_ir=new T(function(){return B(unCStr("RedeemCC"));}),_is=new T(function(){return B(unCStr("Pay"));}),_it=new T(function(){return B(unCStr("Both"));}),_iu=new T(function(){return B(unCStr("Choice"));}),_iv=new T(function(){return B(unCStr("When"));}),_iw=function(_ix,_iy){var _iz=new T(function(){var _iA=new T(function(){return B(A1(_iy,_io));});return B(_dD(function(_iB){var _iC=E(_iB);return (_iC._==3)?(!B(_2s(_iC.a,_ip)))?new T0(2):E(_iA):new T0(2);}));}),_iD=function(_iE){return E(_iz);},_iF=new T(function(){var _iG=E(_ix),_iH=new T(function(){var _iI=new T(function(){var _iJ=new T(function(){var _iK=new T(function(){var _iL=new T(function(){if(_iG>10){return new T0(2);}else{var _iM=new T(function(){var _iN=new T(function(){var _iO=function(_iP){var _iQ=function(_iR){var _iS=function(_iT){return new F(function(){return A3(_eu,_iw,_2o,function(_iU){return new F(function(){return A1(_iy,new T4(6,_iP,_iR,_iT,_iU));});});});};return new F(function(){return A3(_eu,_iw,_2o,_iS);});};return new F(function(){return A3(_eF,_f8,_2o,_iQ);});};return B(A3(_eu,_h7,_2o,_iO));});return B(_dD(function(_iV){var _iW=E(_iV);return (_iW._==3)?(!B(_2s(_iW.a,_iv)))?new T0(2):E(_iN):new T0(2);}));}),_iX=function(_iY){return E(_iM);};return new T1(1,function(_iZ){return new F(function(){return A2(_ck,_iZ,_iX);});});}});if(_iG>10){return B(_1M(_2Y,_iL));}else{var _j0=new T(function(){var _j1=new T(function(){var _j2=function(_j3){var _j4=function(_j5){return new F(function(){return A3(_eu,_iw,_2o,function(_j6){return new F(function(){return A1(_iy,new T3(5,_j3,_j5,_j6));});});});};return new F(function(){return A3(_eu,_iw,_2o,_j4);});};return B(A3(_eu,_h7,_2o,_j2));});return B(_dD(function(_j7){var _j8=E(_j7);return (_j8._==3)?(!B(_2s(_j8.a,_iu)))?new T0(2):E(_j1):new T0(2);}));}),_j9=function(_ja){return E(_j0);};return B(_1M(new T1(1,function(_jb){return new F(function(){return A2(_ck,_jb,_j9);});}),_iL));}});if(_iG>10){return B(_1M(_2Y,_iK));}else{var _jc=new T(function(){var _jd=new T(function(){var _je=function(_jf){return new F(function(){return A3(_eu,_iw,_2o,function(_jg){return new F(function(){return A1(_iy,new T2(4,_jf,_jg));});});});};return B(A3(_eu,_iw,_2o,_je));});return B(_dD(function(_jh){var _ji=E(_jh);return (_ji._==3)?(!B(_2s(_ji.a,_it)))?new T0(2):E(_jd):new T0(2);}));}),_jj=function(_jk){return E(_jc);};return B(_1M(new T1(1,function(_jl){return new F(function(){return A2(_ck,_jl,_jj);});}),_iK));}});if(_iG>10){return B(_1M(_2Y,_iJ));}else{var _jm=new T(function(){var _jn=new T(function(){var _jo=function(_jp){var _jq=function(_jr){var _js=function(_jt){var _ju=function(_jv){var _jw=function(_jx){return new F(function(){return A3(_eu,_iw,_2o,function(_jy){return new F(function(){return A1(_iy,new T6(3,_jp,_jr,_jt,_jv,_jx,_jy));});});});};return new F(function(){return A3(_eF,_f8,_2o,_jw);});};return new F(function(){return A3(_eF,_f8,_2o,_ju);});};return new F(function(){return A3(_eF,_f8,_2o,_js);});};return new F(function(){return A3(_eF,_f8,_2o,_jq);});};return B(A3(_eu,_fF,_2o,_jo));});return B(_dD(function(_jz){var _jA=E(_jz);return (_jA._==3)?(!B(_2s(_jA.a,_is)))?new T0(2):E(_jn):new T0(2);}));}),_jB=function(_jC){return E(_jm);};return B(_1M(new T1(1,function(_jD){return new F(function(){return A2(_ck,_jD,_jB);});}),_iJ));}});if(_iG>10){return B(_1M(_2Y,_iI));}else{var _jE=new T(function(){var _jF=new T(function(){var _jG=function(_jH){return new F(function(){return A3(_eu,_iw,_2o,function(_jI){return new F(function(){return A1(_iy,new T2(2,_jH,_jI));});});});};return B(A3(_eu,_fq,_2o,_jG));});return B(_dD(function(_jJ){var _jK=E(_jJ);return (_jK._==3)?(!B(_2s(_jK.a,_ir)))?new T0(2):E(_jF):new T0(2);}));}),_jL=function(_jM){return E(_jE);};return B(_1M(new T1(1,function(_jN){return new F(function(){return A2(_ck,_jN,_jL);});}),_iI));}});if(_iG>10){return B(_1M(_2Y,_iH));}else{var _jO=new T(function(){var _jP=new T(function(){var _jQ=function(_jR){var _jS=function(_jT){var _jU=function(_jV){var _jW=function(_jX){var _jY=function(_jZ){var _k0=function(_k1){return new F(function(){return A3(_eu,_iw,_2o,function(_k2){return new F(function(){return A1(_iy,{_:1,a:_jR,b:_jT,c:_jV,d:_jX,e:_jZ,f:_k1,g:_k2});});});});};return new F(function(){return A3(_eu,_iw,_2o,_k0);});};return new F(function(){return A3(_eF,_f8,_2o,_jY);});};return new F(function(){return A3(_eF,_f8,_2o,_jW);});};return new F(function(){return A3(_eF,_f8,_2o,_jU);});};return new F(function(){return A3(_eF,_f8,_2o,_jS);});};return B(A3(_eu,_fq,_2o,_jQ));});return B(_dD(function(_k3){var _k4=E(_k3);return (_k4._==3)?(!B(_2s(_k4.a,_iq)))?new T0(2):E(_jP):new T0(2);}));}),_k5=function(_k6){return E(_jO);};return B(_1M(new T1(1,function(_k7){return new F(function(){return A2(_ck,_k7,_k5);});}),_iH));}});return new F(function(){return _1M(new T1(1,function(_k8){return new F(function(){return A2(_ck,_k8,_iD);});}),_iF);});},_k9=function(_ka){var _kb=function(_kc){return E(new T2(3,_ka,_2Y));};return new T1(1,function(_kd){return new F(function(){return A2(_ck,_kd,_kb);});});},_ke=new T(function(){return B(A3(_eu,_iw,_ea,_k9));}),_kf=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_kg=new T(function(){return B(err(_kf));}),_kh=new T(function(){return B(unCStr("When"));}),_ki=new T(function(){return B(unCStr("Choice"));}),_kj=new T(function(){return B(unCStr("Both"));}),_kk=new T(function(){return B(unCStr("Pay"));}),_kl=new T(function(){return B(unCStr("RedeemCC"));}),_km=new T(function(){return B(unCStr("CommitCash"));}),_kn=new T(function(){return B(unCStr("Null"));}),_ko=32,_kp=new T2(1,_ko,_9),_kq=function(_kr){var _ks=E(_kr);return (_ks==1)?E(_kp):new T2(1,_ko,new T(function(){return B(_kq(_ks-1|0));}));},_kt=new T(function(){return B(unCStr(": empty list"));}),_ku=new T(function(){return B(unCStr("Prelude."));}),_kv=function(_kw){return new F(function(){return err(B(_c(_ku,new T(function(){return B(_c(_kw,_kt));},1))));});},_kx=new T(function(){return B(unCStr("head"));}),_ky=new T(function(){return B(_kv(_kx));}),_kz=function(_kA,_kB){return (E(_kA)._==2)?false:(E(_kB)._==2)?false:true;},_kC=function(_kD){return new F(function(){return _6U(0,E(_kD),_9);});},_kE=new T(function(){return B(unCStr("IdentPay"));}),_kF=new T(function(){return B(unCStr("PersonChoseSomething"));}),_kG=new T(function(){return B(unCStr("PersonChoseThis"));}),_kH=new T(function(){return B(unCStr("NotObs"));}),_kI=new T(function(){return B(unCStr("OrObs"));}),_kJ=new T(function(){return B(unCStr("AndObs"));}),_kK=new T(function(){return B(unCStr("BelowTimeout"));}),_kL=new T(function(){return B(unCStr("IdentChoice"));}),_kM=new T(function(){return B(unCStr("IdentCC"));}),_kN=new T(function(){return B(unCStr("ConstMoney"));}),_kO=new T(function(){return B(unCStr("AddMoney"));}),_kP=new T(function(){return B(unCStr("AvailableMoney"));}),_kQ=new T(function(){return B(unCStr("FalseObs"));}),_kR=new T(function(){return B(unCStr("TrueObs"));}),_kS=new T(function(){return B(unCStr("ValueGE"));}),_kT=function(_kU){var _kV=E(_kU);switch(_kV._){case 0:var _kW=E(_kV.a);switch(_kW._){case 0:return new T2(0,_kn,_9);case 1:return new T2(0,_km,new T2(1,new T1(3,_kW.a),new T2(1,new T1(6,_kW.b),new T2(1,new T1(6,_kW.c),new T2(1,new T1(6,_kW.d),new T2(1,new T1(6,_kW.e),new T2(1,new T1(0,_kW.f),new T2(1,new T1(0,_kW.g),_9))))))));case 2:return new T2(0,_kl,new T2(1,new T1(3,_kW.a),new T2(1,new T1(0,_kW.b),_9)));case 3:return new T2(0,_kk,new T2(1,new T1(5,_kW.a),new T2(1,new T1(6,_kW.b),new T2(1,new T1(6,_kW.c),new T2(1,new T1(6,_kW.d),new T2(1,new T1(6,_kW.e),new T2(1,new T1(0,_kW.f),_9)))))));case 4:return new T2(0,_kj,new T2(1,new T1(0,_kW.a),new T2(1,new T1(0,_kW.b),_9)));case 5:return new T2(0,_ki,new T2(1,new T1(1,_kW.a),new T2(1,new T1(0,_kW.b),new T2(1,new T1(0,_kW.c),_9))));default:return new T2(0,_kh,new T2(1,new T1(1,_kW.a),new T2(1,new T1(6,_kW.b),new T2(1,new T1(0,_kW.c),new T2(1,new T1(0,_kW.d),_9)))));}break;case 1:var _kX=E(_kV.a);switch(_kX._){case 0:return new T2(0,_kK,new T2(1,new T1(6,_kX.a),_9));case 1:return new T2(0,_kJ,new T2(1,new T1(1,_kX.a),new T2(1,new T1(1,_kX.b),_9)));case 2:return new T2(0,_kI,new T2(1,new T1(1,_kX.a),new T2(1,new T1(1,_kX.b),_9)));case 3:return new T2(0,_kH,new T2(1,new T1(1,_kX.a),_9));case 4:return new T2(0,_kG,new T2(1,new T1(4,_kX.a),new T2(1,new T1(6,_kX.b),new T2(1,new T1(6,_kX.c),_9))));case 5:return new T2(0,_kF,new T2(1,new T1(4,_kX.a),new T2(1,new T1(6,_kX.b),_9)));case 6:return new T2(0,_kS,new T2(1,new T1(2,_kX.a),new T2(1,new T1(2,_kX.b),_9)));case 7:return new T2(0,_kR,_9);default:return new T2(0,_kQ,_9);}break;case 2:var _kY=E(_kV.a);switch(_kY._){case 0:return new T2(0,_kP,new T2(1,new T1(3,_kY.a),_9));case 1:return new T2(0,_kO,new T2(1,new T1(2,_kY.a),new T2(1,new T1(2,_kY.b),_9)));default:return new T2(0,_kN,new T2(1,new T1(6,_kY.a),_9));}break;case 3:return new T2(0,_kM,new T2(1,new T1(6,_kV.a),_9));case 4:return new T2(0,_kL,new T2(1,new T1(6,_kV.a),_9));case 5:return new T2(0,_kE,new T2(1,new T1(6,_kV.a),_9));default:return new T2(0,new T(function(){return B(_kC(_kV.a));}),_9);}},_kZ=function(_l0){var _l1=B(_kT(_l0)),_l2=_l1.a,_l3=E(_l1.b);if(!_l3._){return new T1(0,new T2(0,_l2,_9));}else{switch(E(_l0)._){case 0:return new T1(2,new T2(0,_l2,_l3));case 1:return new T1(2,new T2(0,_l2,_l3));case 2:return new T1(2,new T2(0,_l2,_l3));default:return new T1(1,new T2(0,_l2,_l3));}}},_l4=function(_l5,_l6){var _l7=E(_l6);if(!_l7._){return __Z;}else{var _l8=_l7.a,_l9=new T(function(){var _la=B(_1d(new T(function(){return B(A1(_l5,_l8));}),_l7.b));return new T2(0,_la.a,_la.b);});return new T2(1,new T2(1,_l8,new T(function(){return E(E(_l9).a);})),new T(function(){return B(_l4(_l5,E(_l9).b));}));}},_lb=new T(function(){return B(unCStr(" "));}),_lc=function(_ld,_le){var _lf=E(_le);return (_lf._==0)?__Z:new T2(1,_ld,new T2(1,_lf.a,new T(function(){return B(_lc(_ld,_lf.b));})));},_lg=new T(function(){return B(unCStr("\n"));}),_lh=function(_li){var _lj=E(_li);if(!_lj._){return __Z;}else{return new F(function(){return _c(_lj.a,new T(function(){return B(_lh(_lj.b));},1));});}},_lk=function(_ll,_lm){return new F(function(){return _c(_ll,new T(function(){return B(_lh(_lm));},1));});},_ln=function(_lo){var _lp=E(_lo);if(!_lp._){return __Z;}else{return new F(function(){return _c(_lp.a,new T(function(){return B(_ln(_lp.b));},1));});}},_lq=function(_lr,_ls){return new F(function(){return _c(_lr,new T(function(){return B(_ln(_ls));},1));});},_lt=function(_lu){var _lv=E(_lu);if(!_lv._){return __Z;}else{return new F(function(){return _c(_lv.a,new T(function(){return B(_lt(_lv.b));},1));});}},_lw=function(_lx,_ly){return new F(function(){return _c(_lx,new T(function(){return B(_lt(_ly));},1));});},_lz=new T(function(){return B(unCStr("tail"));}),_lA=new T(function(){return B(_kv(_lz));}),_lB=function(_lC,_lD,_lE){var _lF=E(_lE);if(!_lF._){return E(_lD);}else{var _lG=new T(function(){return (E(_lC)+B(_5a(_lD,0))|0)+1|0;}),_lH=new T(function(){return B(_l4(_kz,B(_5f(_kZ,_lF))));}),_lI=new T(function(){var _lJ=E(_lH);if(!_lJ._){return E(_lA);}else{var _lK=new T(function(){var _lL=E(_lG);if(0>=_lL){return __Z;}else{return B(_kq(_lL));}}),_lM=function(_lN){return new F(function(){return _lO(_lG,_lN);});},_lP=function(_lQ){var _lR=new T(function(){var _lS=B(_5f(_lM,_lQ));if(!_lS._){return __Z;}else{return B(_lk(_lS.a,new T(function(){return B(_lc(_lb,_lS.b));})));}},1);return new F(function(){return _c(_lK,_lR);});};return B(_lc(_lg,B(_5f(_lP,_lJ.b))));}}),_lT=new T(function(){var _lU=new T(function(){var _lV=E(_lH);if(!_lV._){return E(_ky);}else{return B(_lc(_lb,B(_5f(function(_lN){return new F(function(){return _lO(_lG,_lN);});},_lV.a))));}});return B(_lq(_lD,_lU));});return new F(function(){return _lw(_lT,_lI);});}},_lW=new T(function(){return B(unCStr(")"));}),_lO=function(_lX,_lY){var _lZ=E(_lY);switch(_lZ._){case 0:var _m0=E(_lZ.a);return new F(function(){return _m1(0,_m0.a,_m0.b);});break;case 1:return new F(function(){return unAppCStr("(",new T(function(){var _m2=E(_lZ.a);return B(_c(B(_m1(0,_m2.a,_m2.b)),_lW));}));});break;default:var _m3=new T(function(){var _m4=E(_lZ.a);return B(_c(B(_lB(new T(function(){return E(_lX)+1|0;},1),_m4.a,_m4.b)),_lW));});return new F(function(){return unAppCStr("(",_m3);});}},_m1=function(_m5,_m6,_m7){var _m8=E(_m7);if(!_m8._){return E(_m6);}else{var _m9=new T(function(){return (_m5+B(_5a(_m6,0))|0)+1|0;}),_ma=new T(function(){return B(_l4(_kz,B(_5f(_kZ,_m8))));}),_mb=new T(function(){var _mc=E(_ma);if(!_mc._){return E(_lA);}else{var _md=new T(function(){var _me=E(_m9);if(0>=_me){return __Z;}else{return B(_kq(_me));}}),_mf=function(_lN){return new F(function(){return _lO(_m9,_lN);});},_mg=function(_mh){var _mi=new T(function(){var _mj=B(_5f(_mf,_mh));if(!_mj._){return __Z;}else{return B(_lk(_mj.a,new T(function(){return B(_lc(_lb,_mj.b));})));}},1);return new F(function(){return _c(_md,_mi);});};return B(_lc(_lg,B(_5f(_mg,_mc.b))));}}),_mk=new T(function(){var _ml=new T(function(){var _mm=E(_ma);if(!_mm._){return E(_ky);}else{return B(_lc(_lb,B(_5f(function(_lN){return new F(function(){return _lO(_m9,_lN);});},_mm.a))));}});return B(_lq(_m6,_ml));});return new F(function(){return _lw(_mk,_mb);});}},_mn=new T(function(){return B(_m1(0,_kn,_9));}),_mo=function(_mp){while(1){var _mq=B((function(_mr){var _ms=E(_mr);if(!_ms._){return __Z;}else{var _mt=_ms.b,_mu=E(_ms.a);if(!E(_mu.b)._){return new T2(1,_mu.a,new T(function(){return B(_mo(_mt));}));}else{_mp=_mt;return __continue;}}})(_mp));if(_mq!=__continue){return _mq;}}},_mv=function(_mw,_){return new T(function(){var _mx=B(_mo(B(_1C(_ke,_mw))));if(!_mx._){return E(_b);}else{if(!E(_mx.b)._){var _my=E(_mx.a);switch(_my._){case 0:return E(_mn);break;case 1:return B(_m1(0,_km,new T2(1,new T1(3,_my.a),new T2(1,new T1(6,_my.b),new T2(1,new T1(6,_my.c),new T2(1,new T1(6,_my.d),new T2(1,new T1(6,_my.e),new T2(1,new T1(0,_my.f),new T2(1,new T1(0,_my.g),_9)))))))));break;case 2:return B(_m1(0,_kl,new T2(1,new T1(3,_my.a),new T2(1,new T1(0,_my.b),_9))));break;case 3:return B(_m1(0,_kk,new T2(1,new T1(5,_my.a),new T2(1,new T1(6,_my.b),new T2(1,new T1(6,_my.c),new T2(1,new T1(6,_my.d),new T2(1,new T1(6,_my.e),new T2(1,new T1(0,_my.f),_9))))))));break;case 4:return B(_m1(0,_kj,new T2(1,new T1(0,_my.a),new T2(1,new T1(0,_my.b),_9))));break;case 5:return B(_m1(0,_ki,new T2(1,new T1(1,_my.a),new T2(1,new T1(0,_my.b),new T2(1,new T1(0,_my.c),_9)))));break;default:return B(_m1(0,_kh,new T2(1,new T1(1,_my.a),new T2(1,new T1(6,_my.b),new T2(1,new T1(0,_my.c),new T2(1,new T1(0,_my.d),_9))))));}}else{return E(_kg);}}});},_mz=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_mA=function(_){var _mB=__app0(E(_mz)),_mC=B(_mv(new T(function(){var _mD=String(_mB);return fromJSStr(_mD);}),_));return new F(function(){return _4(_1,_mC,_);});},_mE="(function (t) {return document.getElementById(t).value})",_mF="(function (b) { return (b.inputList.length); })",_mG="(function (b, x) { return (b.inputList[x]); })",_mH=function(_mI,_mJ,_){var _mK=eval(E(_mG)),_mL=__app2(E(_mK),_mI,_mJ);return new T1(0,_mL);},_mM=function(_mN,_mO,_mP,_){var _mQ=E(_mP);if(!_mQ._){return _9;}else{var _mR=B(_mH(_mN,E(_mQ.a),_)),_mS=B(_mM(_mN,_,_mQ.b,_));return new T2(1,_mR,_mS);}},_mT=function(_mU,_mV){if(_mU<=_mV){var _mW=function(_mX){return new T2(1,_mX,new T(function(){if(_mX!=_mV){return B(_mW(_mX+1|0));}else{return __Z;}}));};return new F(function(){return _mW(_mU);});}else{return __Z;}},_mY=function(_mZ,_){var _n0=eval(E(_mF)),_n1=__app1(E(_n0),_mZ),_n2=Number(_n1),_n3=jsTrunc(_n2);return new F(function(){return _mM(_mZ,_,new T(function(){return B(_mT(0,_n3-1|0));}),_);});},_n4="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_n5="(function (x) { return x.name; })",_n6=new T(function(){return B(unCStr("\""));}),_n7=function(_n8){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_c(_n8,_n6));}))));});},_n9=function(_na,_nb,_){var _nc=E(_nb);if(!_nc._){return new F(function(){return _n7(_na);});}else{var _nd=E(_nc.a),_ne=E(_n5),_nf=eval(_ne),_ng=__app1(E(_nf),E(_nd.a)),_nh=String(_ng);if(!B(_2s(fromJSStr(_nh),_na))){var _ni=function(_nj,_nk,_){while(1){var _nl=E(_nk);if(!_nl._){return new F(function(){return _n7(_nj);});}else{var _nm=E(_nl.a),_nn=eval(_ne),_no=__app1(E(_nn),E(_nm.a)),_np=String(_no);if(!B(_2s(fromJSStr(_np),_nj))){_nk=_nl.b;continue;}else{return _nm;}}}};return new F(function(){return _ni(_na,_nc.b,_);});}else{return _nd;}}},_nq=function(_nr,_ns,_nt,_){var _nu=B(_mY(_ns,_)),_nv=B(_n9(_nr,_nu,_)),_nw=eval(E(_n4)),_nx=__app2(E(_nw),E(E(_nt).a),E(E(_nv).a));return new F(function(){return _2(_);});},_ny=function(_nz){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_c(_nz,_n6));}))));});},_nA=function(_nB,_nC,_){var _nD=E(_nC);if(!_nD._){return new F(function(){return _ny(_nB);});}else{var _nE=E(_nD.a),_nF=E(_n5),_nG=eval(_nF),_nH=__app1(E(_nG),E(_nE.a)),_nI=String(_nH);if(!B(_2s(fromJSStr(_nI),_nB))){var _nJ=function(_nK,_nL,_){while(1){var _nM=E(_nL);if(!_nM._){return new F(function(){return _ny(_nK);});}else{var _nN=E(_nM.a),_nO=eval(_nF),_nP=__app1(E(_nO),E(_nN.a)),_nQ=String(_nP);if(!B(_2s(fromJSStr(_nQ),_nK))){_nL=_nM.b;continue;}else{return _nN;}}}};return new F(function(){return _nJ(_nB,_nD.b,_);});}else{return _nE;}}},_nR="(function (b) { return (b.fieldRow.length); })",_nS="(function (b, x) { return (b.fieldRow[x]); })",_nT=function(_nU,_nV,_){var _nW=eval(E(_nS)),_nX=__app2(E(_nW),_nU,_nV);return new T1(0,_nX);},_nY=function(_nZ,_o0,_o1,_){var _o2=E(_o1);if(!_o2._){return _9;}else{var _o3=B(_nT(_nZ,E(_o2.a),_)),_o4=B(_nY(_nZ,_,_o2.b,_));return new T2(1,_o3,_o4);}},_o5=function(_o6,_){var _o7=eval(E(_nR)),_o8=__app1(E(_o7),_o6),_o9=Number(_o8),_oa=jsTrunc(_o9);return new F(function(){return _nY(_o6,_,new T(function(){return B(_mT(0,_oa-1|0));}),_);});},_ob=function(_oc,_){var _od=E(_oc);if(!_od._){return _9;}else{var _oe=B(_o5(E(E(_od.a).a),_)),_of=B(_ob(_od.b,_));return new T2(1,_oe,_of);}},_og=function(_oh){var _oi=E(_oh);if(!_oi._){return __Z;}else{return new F(function(){return _c(_oi.a,new T(function(){return B(_og(_oi.b));},1));});}},_oj=function(_ok,_ol,_){var _om=B(_mY(_ol,_)),_on=B(_ob(_om,_));return new F(function(){return _nA(_ok,B(_og(_on)),_);});},_oo="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_op=function(_oq,_or,_os,_){var _ot=B(_mY(_or,_)),_ou=B(_n9(_oq,_ot,_)),_ov=eval(E(_oo)),_ow=__app2(E(_ov),E(E(_os).a),E(E(_ou).a));return new F(function(){return _2(_);});},_ox=new T(function(){return B(unCStr("contract_commitcash"));}),_oy=new T(function(){return B(unCStr("contract_redeemcc"));}),_oz=new T(function(){return B(unCStr("contract_pay"));}),_oA=new T(function(){return B(unCStr("contract_both"));}),_oB=new T(function(){return B(unCStr("contract_choice"));}),_oC=new T(function(){return B(unCStr("contract_when"));}),_oD="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_oE=function(_oF,_){var _oG=eval(E(_oD)),_oH=__app1(E(_oG),toJSStr(E(_oF)));return new T1(0,_oH);},_oI=new T(function(){return B(unCStr("contract2"));}),_oJ=new T(function(){return B(unCStr("contract1"));}),_oK=new T(function(){return B(unCStr("ccommit_id"));}),_oL=new T(function(){return B(unCStr("end_expiration"));}),_oM=new T(function(){return B(unCStr("start_expiration"));}),_oN=new T(function(){return B(unCStr("person_id"));}),_oO=new T(function(){return B(unCStr("contract_null"));}),_oP=new T(function(){return B(unCStr("observation"));}),_oQ=new T(function(){return B(unCStr("timeout"));}),_oR=new T(function(){return B(unCStr("contract"));}),_oS=new T(function(){return B(unCStr("expiration"));}),_oT=new T(function(){return B(unCStr("ammount"));}),_oU=new T(function(){return B(unCStr("payee_id"));}),_oV=new T(function(){return B(unCStr("payer_id"));}),_oW=new T(function(){return B(unCStr("pay_id"));}),_oX=function(_oY,_oZ,_p0,_){var _p1=B(_mY(_oZ,_)),_p2=B(_n9(_oY,_p1,_)),_p3=eval(E(_oo)),_p4=__app2(E(_p3),E(E(_p0).a),E(E(_p2).a));return new F(function(){return _2(_);});},_p5=new T(function(){return B(unCStr("observation_personchosethis"));}),_p6=new T(function(){return B(unCStr("observation_personchosesomething"));}),_p7=new T(function(){return B(unCStr("observation_value_ge"));}),_p8=new T(function(){return B(unCStr("observation_trueobs"));}),_p9=new T(function(){return B(unCStr("observation_falseobs"));}),_pa=new T(function(){return B(unCStr("observation_belowtimeout"));}),_pb=new T(function(){return B(unCStr("observation_andobs"));}),_pc=new T(function(){return B(unCStr("observation_orobs"));}),_pd=new T(function(){return B(unCStr("observation_notobs"));}),_pe=new T(function(){return B(unCStr("value2"));}),_pf=new T(function(){return B(unCStr("value1"));}),_pg=new T(function(){return B(unCStr("person"));}),_ph=new T(function(){return B(unCStr("choice_id"));}),_pi=new T(function(){return B(unCStr("choice_value"));}),_pj=new T(function(){return B(unCStr("observation2"));}),_pk=new T(function(){return B(unCStr("observation1"));}),_pl=new T(function(){return B(unCStr("block_number"));}),_pm=new T(function(){return B(unCStr("value_available_money"));}),_pn=new T(function(){return B(unCStr("value_add_money"));}),_po=new T(function(){return B(unCStr("value_const_money"));}),_pp=new T(function(){return B(unCStr("money"));}),_pq=new T(function(){return B(unCStr("commit_id"));}),_pr="(function (b, s) { return (b.setText(s)); })",_ps=function(_pt,_){var _pu=E(_pt);switch(_pu._){case 0:var _pv=B(_oE(_pm,_)),_pw=E(_pv),_px=B(_oj(_pq,E(_pw.a),_)),_py=eval(E(_pr)),_pz=__app2(E(_py),E(E(_px).a),toJSStr(B(_6U(0,E(_pu.a),_9))));return _pw;case 1:var _pA=B(_ps(_pu.a,_)),_pB=B(_ps(_pu.b,_)),_pC=B(_oE(_pn,_)),_pD=E(_pC),_pE=E(_pD.a),_pF=B(_oX(_pf,_pE,_pA,_)),_pG=B(_oX(_pe,_pE,_pB,_));return _pD;default:var _pH=B(_oE(_po,_)),_pI=E(_pH),_pJ=B(_oj(_pp,E(_pI.a),_)),_pK=eval(E(_pr)),_pL=__app2(E(_pK),E(E(_pJ).a),toJSStr(B(_6U(0,E(_pu.a),_9))));return _pI;}},_pM=function(_pN,_){var _pO=E(_pN);switch(_pO._){case 0:var _pP=B(_oE(_pa,_)),_pQ=E(_pP),_pR=B(_oj(_pl,E(_pQ.a),_)),_pS=eval(E(_pr)),_pT=__app2(E(_pS),E(E(_pR).a),toJSStr(B(_6U(0,E(_pO.a),_9))));return _pQ;case 1:var _pU=B(_pM(_pO.a,_)),_pV=B(_pM(_pO.b,_)),_pW=B(_oE(_pb,_)),_pX=E(_pW),_pY=E(_pX.a),_pZ=B(_op(_pk,_pY,_pU,_)),_q0=B(_op(_pj,_pY,_pV,_));return _pX;case 2:var _q1=B(_pM(_pO.a,_)),_q2=B(_pM(_pO.b,_)),_q3=B(_oE(_pc,_)),_q4=E(_q3),_q5=E(_q4.a),_q6=B(_op(_pk,_q5,_q1,_)),_q7=B(_op(_pj,_q5,_q2,_));return _q4;case 3:var _q8=B(_pM(_pO.a,_)),_q9=B(_oE(_pd,_)),_qa=E(_q9),_qb=B(_op(_oP,E(_qa.a),_q8,_));return _qa;case 4:var _qc=B(_oE(_p5,_)),_qd=E(_qc),_qe=E(_qd.a),_qf=B(_oj(_ph,_qe,_)),_qg=eval(E(_pr)),_qh=__app2(E(_qg),E(E(_qf).a),toJSStr(B(_6U(0,E(_pO.a),_9)))),_qi=B(_oj(_pg,_qe,_)),_qj=__app2(E(_qg),E(E(_qi).a),toJSStr(B(_6U(0,E(_pO.b),_9)))),_qk=B(_oj(_pi,_qe,_)),_ql=__app2(E(_qg),E(E(_qk).a),toJSStr(B(_6U(0,E(_pO.c),_9))));return _qd;case 5:var _qm=B(_oE(_p6,_)),_qn=E(_qm),_qo=E(_qn.a),_qp=B(_oj(_ph,_qo,_)),_qq=eval(E(_pr)),_qr=__app2(E(_qq),E(E(_qp).a),toJSStr(B(_6U(0,E(_pO.a),_9)))),_qs=B(_oj(_pg,_qo,_)),_qt=__app2(E(_qq),E(E(_qs).a),toJSStr(B(_6U(0,E(_pO.b),_9))));return _qn;case 6:var _qu=B(_ps(_pO.a,_)),_qv=B(_ps(_pO.b,_)),_qw=B(_oE(_p7,_)),_qx=E(_qw),_qy=E(_qx.a),_qz=B(_oX(_pf,_qy,_qu,_)),_qA=B(_oX(_pe,_qy,_qv,_));return _qx;case 7:return new F(function(){return _oE(_p8,_);});break;default:return new F(function(){return _oE(_p9,_);});}},_qB=function(_qC,_){var _qD=E(_qC);switch(_qD._){case 0:return new F(function(){return _oE(_oO,_);});break;case 1:var _qE=B(_qB(_qD.f,_)),_qF=B(_qB(_qD.g,_)),_qG=B(_oE(_ox,_)),_qH=E(_qG),_qI=E(_qH.a),_qJ=B(_oj(_oK,_qI,_)),_qK=eval(E(_pr)),_qL=__app2(E(_qK),E(E(_qJ).a),toJSStr(B(_6U(0,E(_qD.a),_9)))),_qM=B(_oj(_oN,_qI,_)),_qN=__app2(E(_qK),E(E(_qM).a),toJSStr(B(_6U(0,E(_qD.b),_9)))),_qO=B(_oj(_oT,_qI,_)),_qP=__app2(E(_qK),E(E(_qO).a),toJSStr(B(_6U(0,E(_qD.c),_9)))),_qQ=B(_oj(_oM,_qI,_)),_qR=__app2(E(_qK),E(E(_qQ).a),toJSStr(B(_6U(0,E(_qD.d),_9)))),_qS=B(_oj(_oL,_qI,_)),_qT=__app2(E(_qK),E(E(_qS).a),toJSStr(B(_6U(0,E(_qD.e),_9)))),_qU=B(_nq(_oJ,_qI,_qE,_)),_qV=B(_nq(_oI,_qI,_qF,_));return _qH;case 2:var _qW=B(_qB(_qD.b,_)),_qX=B(_oE(_oy,_)),_qY=E(_qX),_qZ=E(_qY.a),_r0=B(_oj(_oK,_qZ,_)),_r1=eval(E(_pr)),_r2=__app2(E(_r1),E(E(_r0).a),toJSStr(B(_6U(0,E(_qD.a),_9)))),_r3=B(_nq(_oR,_qZ,_qW,_));return _qY;case 3:var _r4=B(_qB(_qD.f,_)),_r5=B(_oE(_oz,_)),_r6=E(_r5),_r7=E(_r6.a),_r8=B(_oj(_oW,_r7,_)),_r9=eval(E(_pr)),_ra=__app2(E(_r9),E(E(_r8).a),toJSStr(B(_6U(0,E(_qD.a),_9)))),_rb=B(_oj(_oV,_r7,_)),_rc=__app2(E(_r9),E(E(_rb).a),toJSStr(B(_6U(0,E(_qD.b),_9)))),_rd=B(_oj(_oU,_r7,_)),_re=__app2(E(_r9),E(E(_rd).a),toJSStr(B(_6U(0,E(_qD.c),_9)))),_rf=B(_oj(_oT,_r7,_)),_rg=__app2(E(_r9),E(E(_rf).a),toJSStr(B(_6U(0,E(_qD.d),_9)))),_rh=B(_oj(_oS,_r7,_)),_ri=__app2(E(_r9),E(E(_rh).a),toJSStr(B(_6U(0,E(_qD.e),_9)))),_rj=B(_nq(_oR,_r7,_r4,_));return _r6;case 4:var _rk=B(_qB(_qD.a,_)),_rl=B(_qB(_qD.b,_)),_rm=B(_oE(_oA,_)),_rn=E(_rm),_ro=E(_rn.a),_rp=B(_nq(_oJ,_ro,_rk,_)),_rq=B(_nq(_oI,_ro,_rl,_));return _rn;case 5:var _rr=B(_pM(_qD.a,_)),_rs=B(_qB(_qD.b,_)),_rt=B(_qB(_qD.c,_)),_ru=B(_oE(_oB,_)),_rv=E(_ru),_rw=E(_rv.a),_rx=B(_op(_oP,_rw,_rr,_)),_ry=B(_nq(_oJ,_rw,_rs,_)),_rz=B(_nq(_oI,_rw,_rt,_));return _rv;default:var _rA=B(_pM(_qD.a,_)),_rB=B(_qB(_qD.c,_)),_rC=B(_qB(_qD.d,_)),_rD=B(_oE(_oC,_)),_rE=E(_rD),_rF=E(_rE.a),_rG=B(_oj(_oQ,_rF,_)),_rH=eval(E(_pr)),_rI=__app2(E(_rH),E(E(_rG).a),toJSStr(B(_6U(0,E(_qD.b),_9)))),_rJ=B(_op(_oP,_rF,_rA,_)),_rK=B(_nq(_oJ,_rF,_rB,_)),_rL=B(_nq(_oI,_rF,_rC,_));return _rE;}},_rM=new T(function(){return B(unCStr("base_contract"));}),_rN=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_rO=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_rP=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_rQ=function(_rR,_){var _rS=__app0(E(_rP)),_rT=__app0(E(_rO)),_rU=B(_mo(B(_1C(_ke,_rR))));if(!_rU._){return E(_b);}else{if(!E(_rU.b)._){var _rV=B(_qB(_rU.a,_)),_rW=B(_nq(_rM,_rT,_rV,_)),_rX=__app0(E(_rN));return _0;}else{return E(_kg);}}},_rY=function(_){var _rZ=eval(E(_mE)),_s0=__app1(E(_rZ),toJSStr(E(_1)));return new F(function(){return _rQ(new T(function(){var _s1=String(_s0);return fromJSStr(_s1);}),_);});},_s2=new T0(1),_s3=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_s4=function(_s5){return new F(function(){return err(_s3);});},_s6=new T(function(){return B(_s4(_));}),_s7=function(_s8,_s9,_sa,_sb){var _sc=E(_sa);if(!_sc._){var _sd=_sc.a,_se=E(_sb);if(!_se._){var _sf=_se.a,_sg=_se.b,_sh=_se.c;if(_sf<=(imul(3,_sd)|0)){return new T5(0,(1+_sd|0)+_sf|0,E(_s8),_s9,E(_sc),E(_se));}else{var _si=E(_se.d);if(!_si._){var _sj=_si.a,_sk=_si.b,_sl=_si.c,_sm=_si.d,_sn=E(_se.e);if(!_sn._){var _so=_sn.a;if(_sj>=(imul(2,_so)|0)){var _sp=function(_sq){var _sr=E(_s8),_ss=E(_si.e);return (_ss._==0)?new T5(0,(1+_sd|0)+_sf|0,E(_sk),_sl,E(new T5(0,(1+_sd|0)+_sq|0,E(_sr),_s9,E(_sc),E(_sm))),E(new T5(0,(1+_so|0)+_ss.a|0,E(_sg),_sh,E(_ss),E(_sn)))):new T5(0,(1+_sd|0)+_sf|0,E(_sk),_sl,E(new T5(0,(1+_sd|0)+_sq|0,E(_sr),_s9,E(_sc),E(_sm))),E(new T5(0,1+_so|0,E(_sg),_sh,E(_s2),E(_sn))));},_st=E(_sm);if(!_st._){return new F(function(){return _sp(_st.a);});}else{return new F(function(){return _sp(0);});}}else{return new T5(0,(1+_sd|0)+_sf|0,E(_sg),_sh,E(new T5(0,(1+_sd|0)+_sj|0,E(_s8),_s9,E(_sc),E(_si))),E(_sn));}}else{return E(_s6);}}else{return E(_s6);}}}else{return new T5(0,1+_sd|0,E(_s8),_s9,E(_sc),E(_s2));}}else{var _su=E(_sb);if(!_su._){var _sv=_su.a,_sw=_su.b,_sx=_su.c,_sy=_su.e,_sz=E(_su.d);if(!_sz._){var _sA=_sz.a,_sB=_sz.b,_sC=_sz.c,_sD=_sz.d,_sE=E(_sy);if(!_sE._){var _sF=_sE.a;if(_sA>=(imul(2,_sF)|0)){var _sG=function(_sH){var _sI=E(_s8),_sJ=E(_sz.e);return (_sJ._==0)?new T5(0,1+_sv|0,E(_sB),_sC,E(new T5(0,1+_sH|0,E(_sI),_s9,E(_s2),E(_sD))),E(new T5(0,(1+_sF|0)+_sJ.a|0,E(_sw),_sx,E(_sJ),E(_sE)))):new T5(0,1+_sv|0,E(_sB),_sC,E(new T5(0,1+_sH|0,E(_sI),_s9,E(_s2),E(_sD))),E(new T5(0,1+_sF|0,E(_sw),_sx,E(_s2),E(_sE))));},_sK=E(_sD);if(!_sK._){return new F(function(){return _sG(_sK.a);});}else{return new F(function(){return _sG(0);});}}else{return new T5(0,1+_sv|0,E(_sw),_sx,E(new T5(0,1+_sA|0,E(_s8),_s9,E(_s2),E(_sz))),E(_sE));}}else{return new T5(0,3,E(_sB),_sC,E(new T5(0,1,E(_s8),_s9,E(_s2),E(_s2))),E(new T5(0,1,E(_sw),_sx,E(_s2),E(_s2))));}}else{var _sL=E(_sy);return (_sL._==0)?new T5(0,3,E(_sw),_sx,E(new T5(0,1,E(_s8),_s9,E(_s2),E(_s2))),E(_sL)):new T5(0,2,E(_s8),_s9,E(_s2),E(_su));}}else{return new T5(0,1,E(_s8),_s9,E(_s2),E(_s2));}}},_sM=function(_sN,_sO){return new T5(0,1,E(_sN),_sO,E(_s2),E(_s2));},_sP=function(_sQ,_sR,_sS){var _sT=E(_sS);if(!_sT._){return new F(function(){return _s7(_sT.b,_sT.c,_sT.d,B(_sP(_sQ,_sR,_sT.e)));});}else{return new F(function(){return _sM(_sQ,_sR);});}},_sU=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_sV=function(_sW){return new F(function(){return err(_sU);});},_sX=new T(function(){return B(_sV(_));}),_sY=function(_sZ,_t0,_t1,_t2){var _t3=E(_t2);if(!_t3._){var _t4=_t3.a,_t5=E(_t1);if(!_t5._){var _t6=_t5.a,_t7=_t5.b,_t8=_t5.c;if(_t6<=(imul(3,_t4)|0)){return new T5(0,(1+_t6|0)+_t4|0,E(_sZ),_t0,E(_t5),E(_t3));}else{var _t9=E(_t5.d);if(!_t9._){var _ta=_t9.a,_tb=E(_t5.e);if(!_tb._){var _tc=_tb.a,_td=_tb.b,_te=_tb.c,_tf=_tb.d;if(_tc>=(imul(2,_ta)|0)){var _tg=function(_th){var _ti=E(_tb.e);return (_ti._==0)?new T5(0,(1+_t6|0)+_t4|0,E(_td),_te,E(new T5(0,(1+_ta|0)+_th|0,E(_t7),_t8,E(_t9),E(_tf))),E(new T5(0,(1+_t4|0)+_ti.a|0,E(_sZ),_t0,E(_ti),E(_t3)))):new T5(0,(1+_t6|0)+_t4|0,E(_td),_te,E(new T5(0,(1+_ta|0)+_th|0,E(_t7),_t8,E(_t9),E(_tf))),E(new T5(0,1+_t4|0,E(_sZ),_t0,E(_s2),E(_t3))));},_tj=E(_tf);if(!_tj._){return new F(function(){return _tg(_tj.a);});}else{return new F(function(){return _tg(0);});}}else{return new T5(0,(1+_t6|0)+_t4|0,E(_t7),_t8,E(_t9),E(new T5(0,(1+_t4|0)+_tc|0,E(_sZ),_t0,E(_tb),E(_t3))));}}else{return E(_sX);}}else{return E(_sX);}}}else{return new T5(0,1+_t4|0,E(_sZ),_t0,E(_s2),E(_t3));}}else{var _tk=E(_t1);if(!_tk._){var _tl=_tk.a,_tm=_tk.b,_tn=_tk.c,_to=_tk.e,_tp=E(_tk.d);if(!_tp._){var _tq=_tp.a,_tr=E(_to);if(!_tr._){var _ts=_tr.a,_tt=_tr.b,_tu=_tr.c,_tv=_tr.d;if(_ts>=(imul(2,_tq)|0)){var _tw=function(_tx){var _ty=E(_tr.e);return (_ty._==0)?new T5(0,1+_tl|0,E(_tt),_tu,E(new T5(0,(1+_tq|0)+_tx|0,E(_tm),_tn,E(_tp),E(_tv))),E(new T5(0,1+_ty.a|0,E(_sZ),_t0,E(_ty),E(_s2)))):new T5(0,1+_tl|0,E(_tt),_tu,E(new T5(0,(1+_tq|0)+_tx|0,E(_tm),_tn,E(_tp),E(_tv))),E(new T5(0,1,E(_sZ),_t0,E(_s2),E(_s2))));},_tz=E(_tv);if(!_tz._){return new F(function(){return _tw(_tz.a);});}else{return new F(function(){return _tw(0);});}}else{return new T5(0,1+_tl|0,E(_tm),_tn,E(_tp),E(new T5(0,1+_ts|0,E(_sZ),_t0,E(_tr),E(_s2))));}}else{return new T5(0,3,E(_tm),_tn,E(_tp),E(new T5(0,1,E(_sZ),_t0,E(_s2),E(_s2))));}}else{var _tA=E(_to);return (_tA._==0)?new T5(0,3,E(_tA.b),_tA.c,E(new T5(0,1,E(_tm),_tn,E(_s2),E(_s2))),E(new T5(0,1,E(_sZ),_t0,E(_s2),E(_s2)))):new T5(0,2,E(_sZ),_t0,E(_tk),E(_s2));}}else{return new T5(0,1,E(_sZ),_t0,E(_s2),E(_s2));}}},_tB=function(_tC,_tD,_tE){var _tF=E(_tE);if(!_tF._){return new F(function(){return _sY(_tF.b,_tF.c,B(_tB(_tC,_tD,_tF.d)),_tF.e);});}else{return new F(function(){return _sM(_tC,_tD);});}},_tG=function(_tH,_tI,_tJ,_tK,_tL,_tM,_tN){return new F(function(){return _sY(_tK,_tL,B(_tB(_tH,_tI,_tM)),_tN);});},_tO=function(_tP,_tQ,_tR,_tS,_tT,_tU,_tV,_tW){var _tX=E(_tR);if(!_tX._){var _tY=_tX.a,_tZ=_tX.b,_u0=_tX.c,_u1=_tX.d,_u2=_tX.e;if((imul(3,_tY)|0)>=_tS){if((imul(3,_tS)|0)>=_tY){return new T5(0,(_tY+_tS|0)+1|0,E(_tP),_tQ,E(_tX),E(new T5(0,_tS,E(_tT),_tU,E(_tV),E(_tW))));}else{return new F(function(){return _s7(_tZ,_u0,_u1,B(_tO(_tP,_tQ,_u2,_tS,_tT,_tU,_tV,_tW)));});}}else{return new F(function(){return _sY(_tT,_tU,B(_u3(_tP,_tQ,_tY,_tZ,_u0,_u1,_u2,_tV)),_tW);});}}else{return new F(function(){return _tG(_tP,_tQ,_tS,_tT,_tU,_tV,_tW);});}},_u3=function(_u4,_u5,_u6,_u7,_u8,_u9,_ua,_ub){var _uc=E(_ub);if(!_uc._){var _ud=_uc.a,_ue=_uc.b,_uf=_uc.c,_ug=_uc.d,_uh=_uc.e;if((imul(3,_u6)|0)>=_ud){if((imul(3,_ud)|0)>=_u6){return new T5(0,(_u6+_ud|0)+1|0,E(_u4),_u5,E(new T5(0,_u6,E(_u7),_u8,E(_u9),E(_ua))),E(_uc));}else{return new F(function(){return _s7(_u7,_u8,_u9,B(_tO(_u4,_u5,_ua,_ud,_ue,_uf,_ug,_uh)));});}}else{return new F(function(){return _sY(_ue,_uf,B(_u3(_u4,_u5,_u6,_u7,_u8,_u9,_ua,_ug)),_uh);});}}else{return new F(function(){return _sP(_u4,_u5,new T5(0,_u6,E(_u7),_u8,E(_u9),E(_ua)));});}},_ui=function(_uj,_uk,_ul,_um){var _un=E(_ul);if(!_un._){var _uo=_un.a,_up=_un.b,_uq=_un.c,_ur=_un.d,_us=_un.e,_ut=E(_um);if(!_ut._){var _uu=_ut.a,_uv=_ut.b,_uw=_ut.c,_ux=_ut.d,_uy=_ut.e;if((imul(3,_uo)|0)>=_uu){if((imul(3,_uu)|0)>=_uo){return new T5(0,(_uo+_uu|0)+1|0,E(_uj),_uk,E(_un),E(_ut));}else{return new F(function(){return _s7(_up,_uq,_ur,B(_tO(_uj,_uk,_us,_uu,_uv,_uw,_ux,_uy)));});}}else{return new F(function(){return _sY(_uv,_uw,B(_u3(_uj,_uk,_uo,_up,_uq,_ur,_us,_ux)),_uy);});}}else{return new F(function(){return _sP(_uj,_uk,_un);});}}else{return new F(function(){return _tB(_uj,_uk,_um);});}},_uz=function(_uA,_uB,_uC,_uD,_uE){var _uF=E(_uA);if(_uF==1){var _uG=E(_uE);if(!_uG._){return new T3(0,new T5(0,1,E(new T2(0,_uB,_uC)),_uD,E(_s2),E(_s2)),_9,_9);}else{var _uH=E(E(_uG.a).a),_uI=E(_uB),_uJ=E(_uH.a);return (_uI>=_uJ)?(_uI!=_uJ)?new T3(0,new T5(0,1,E(new T2(0,_uI,_uC)),_uD,E(_s2),E(_s2)),_9,_uG):(_uC<E(_uH.b))?new T3(0,new T5(0,1,E(new T2(0,_uI,_uC)),_uD,E(_s2),E(_s2)),_uG,_9):new T3(0,new T5(0,1,E(new T2(0,_uI,_uC)),_uD,E(_s2),E(_s2)),_9,_uG):new T3(0,new T5(0,1,E(new T2(0,_uI,_uC)),_uD,E(_s2),E(_s2)),_uG,_9);}}else{var _uK=B(_uz(_uF>>1,_uB,_uC,_uD,_uE)),_uL=_uK.a,_uM=_uK.c,_uN=E(_uK.b);if(!_uN._){return new T3(0,_uL,_9,_uM);}else{var _uO=E(_uN.a),_uP=_uO.a,_uQ=_uO.b,_uR=E(_uN.b);if(!_uR._){return new T3(0,new T(function(){return B(_sP(_uP,_uQ,_uL));}),_9,_uM);}else{var _uS=_uR.b,_uT=E(_uR.a),_uU=_uT.b,_uV=E(_uP),_uW=E(_uT.a),_uX=_uW.b,_uY=E(_uV.a),_uZ=E(_uW.a);if(_uY>=_uZ){if(_uY!=_uZ){return new T3(0,_uL,_9,_uN);}else{var _v0=E(_uX);if(E(_uV.b)<_v0){var _v1=B(_uz(_uF>>1,_uZ,_v0,_uU,_uS));return new T3(0,new T(function(){return B(_ui(_uV,_uQ,_uL,_v1.a));}),_v1.b,_v1.c);}else{return new T3(0,_uL,_9,_uN);}}}else{var _v2=B(_v3(_uF>>1,_uZ,_uX,_uU,_uS));return new T3(0,new T(function(){return B(_ui(_uV,_uQ,_uL,_v2.a));}),_v2.b,_v2.c);}}}}},_v3=function(_v4,_v5,_v6,_v7,_v8){var _v9=E(_v4);if(_v9==1){var _va=E(_v8);if(!_va._){return new T3(0,new T5(0,1,E(new T2(0,_v5,_v6)),_v7,E(_s2),E(_s2)),_9,_9);}else{var _vb=E(E(_va.a).a),_vc=E(_v5),_vd=E(_vb.a);if(_vc>=_vd){if(_vc!=_vd){return new T3(0,new T5(0,1,E(new T2(0,_vc,_v6)),_v7,E(_s2),E(_s2)),_9,_va);}else{var _ve=E(_v6);return (_ve<E(_vb.b))?new T3(0,new T5(0,1,E(new T2(0,_vc,_ve)),_v7,E(_s2),E(_s2)),_va,_9):new T3(0,new T5(0,1,E(new T2(0,_vc,_ve)),_v7,E(_s2),E(_s2)),_9,_va);}}else{return new T3(0,new T5(0,1,E(new T2(0,_vc,_v6)),_v7,E(_s2),E(_s2)),_va,_9);}}}else{var _vf=B(_v3(_v9>>1,_v5,_v6,_v7,_v8)),_vg=_vf.a,_vh=_vf.c,_vi=E(_vf.b);if(!_vi._){return new T3(0,_vg,_9,_vh);}else{var _vj=E(_vi.a),_vk=_vj.a,_vl=_vj.b,_vm=E(_vi.b);if(!_vm._){return new T3(0,new T(function(){return B(_sP(_vk,_vl,_vg));}),_9,_vh);}else{var _vn=_vm.b,_vo=E(_vm.a),_vp=_vo.b,_vq=E(_vk),_vr=E(_vo.a),_vs=_vr.b,_vt=E(_vq.a),_vu=E(_vr.a);if(_vt>=_vu){if(_vt!=_vu){return new T3(0,_vg,_9,_vi);}else{var _vv=E(_vs);if(E(_vq.b)<_vv){var _vw=B(_uz(_v9>>1,_vu,_vv,_vp,_vn));return new T3(0,new T(function(){return B(_ui(_vq,_vl,_vg,_vw.a));}),_vw.b,_vw.c);}else{return new T3(0,_vg,_9,_vi);}}}else{var _vx=B(_v3(_v9>>1,_vu,_vs,_vp,_vn));return new T3(0,new T(function(){return B(_ui(_vq,_vl,_vg,_vx.a));}),_vx.b,_vx.c);}}}}},_vy=function(_vz,_vA,_vB,_vC,_vD){var _vE=E(_vD);if(!_vE._){var _vF=_vE.c,_vG=_vE.d,_vH=_vE.e,_vI=E(_vE.b),_vJ=E(_vI.a);if(_vz>=_vJ){if(_vz!=_vJ){return new F(function(){return _s7(_vI,_vF,_vG,B(_vy(_vz,_,_vB,_vC,_vH)));});}else{var _vK=E(_vI.b);if(_vB>=_vK){if(_vB!=_vK){return new F(function(){return _s7(_vI,_vF,_vG,B(_vy(_vz,_,_vB,_vC,_vH)));});}else{return new T5(0,_vE.a,E(new T2(0,_vz,_vB)),_vC,E(_vG),E(_vH));}}else{return new F(function(){return _sY(_vI,_vF,B(_vy(_vz,_,_vB,_vC,_vG)),_vH);});}}}else{return new F(function(){return _sY(_vI,_vF,B(_vy(_vz,_,_vB,_vC,_vG)),_vH);});}}else{return new T5(0,1,E(new T2(0,_vz,_vB)),_vC,E(_s2),E(_s2));}},_vL=function(_vM,_vN,_vO,_vP,_vQ){var _vR=E(_vQ);if(!_vR._){var _vS=_vR.c,_vT=_vR.d,_vU=_vR.e,_vV=E(_vR.b),_vW=E(_vV.a);if(_vM>=_vW){if(_vM!=_vW){return new F(function(){return _s7(_vV,_vS,_vT,B(_vL(_vM,_,_vO,_vP,_vU)));});}else{var _vX=E(_vO),_vY=E(_vV.b);if(_vX>=_vY){if(_vX!=_vY){return new F(function(){return _s7(_vV,_vS,_vT,B(_vy(_vM,_,_vX,_vP,_vU)));});}else{return new T5(0,_vR.a,E(new T2(0,_vM,_vX)),_vP,E(_vT),E(_vU));}}else{return new F(function(){return _sY(_vV,_vS,B(_vy(_vM,_,_vX,_vP,_vT)),_vU);});}}}else{return new F(function(){return _sY(_vV,_vS,B(_vL(_vM,_,_vO,_vP,_vT)),_vU);});}}else{return new T5(0,1,E(new T2(0,_vM,_vO)),_vP,E(_s2),E(_s2));}},_vZ=function(_w0,_w1,_w2,_w3){var _w4=E(_w3);if(!_w4._){var _w5=_w4.c,_w6=_w4.d,_w7=_w4.e,_w8=E(_w4.b),_w9=E(_w0),_wa=E(_w8.a);if(_w9>=_wa){if(_w9!=_wa){return new F(function(){return _s7(_w8,_w5,_w6,B(_vL(_w9,_,_w1,_w2,_w7)));});}else{var _wb=E(_w1),_wc=E(_w8.b);if(_wb>=_wc){if(_wb!=_wc){return new F(function(){return _s7(_w8,_w5,_w6,B(_vy(_w9,_,_wb,_w2,_w7)));});}else{return new T5(0,_w4.a,E(new T2(0,_w9,_wb)),_w2,E(_w6),E(_w7));}}else{return new F(function(){return _sY(_w8,_w5,B(_vy(_w9,_,_wb,_w2,_w6)),_w7);});}}}else{return new F(function(){return _sY(_w8,_w5,B(_vL(_w9,_,_w1,_w2,_w6)),_w7);});}}else{return new T5(0,1,E(new T2(0,_w0,_w1)),_w2,E(_s2),E(_s2));}},_wd=function(_we,_wf){while(1){var _wg=E(_wf);if(!_wg._){return E(_we);}else{var _wh=E(_wg.a),_wi=E(_wh.a),_wj=B(_vZ(_wi.a,_wi.b,_wh.b,_we));_we=_wj;_wf=_wg.b;continue;}}},_wk=function(_wl,_wm,_wn,_wo,_wp){return new F(function(){return _wd(B(_vZ(_wm,_wn,_wo,_wl)),_wp);});},_wq=function(_wr,_ws,_wt){var _wu=E(_ws),_wv=E(_wu.a);return new F(function(){return _wd(B(_vZ(_wv.a,_wv.b,_wu.b,_wr)),_wt);});},_ww=function(_wx,_wy,_wz){var _wA=E(_wz);if(!_wA._){return E(_wy);}else{var _wB=E(_wA.a),_wC=_wB.a,_wD=_wB.b,_wE=E(_wA.b);if(!_wE._){return new F(function(){return _sP(_wC,_wD,_wy);});}else{var _wF=E(_wE.a),_wG=E(_wC),_wH=_wG.b,_wI=E(_wF.a),_wJ=_wI.b,_wK=E(_wG.a),_wL=E(_wI.a),_wM=function(_wN){var _wO=B(_v3(_wx,_wL,_wJ,_wF.b,_wE.b)),_wP=_wO.a,_wQ=E(_wO.c);if(!_wQ._){return new F(function(){return _ww(_wx<<1,B(_ui(_wG,_wD,_wy,_wP)),_wO.b);});}else{return new F(function(){return _wq(B(_ui(_wG,_wD,_wy,_wP)),_wQ.a,_wQ.b);});}};if(_wK>=_wL){if(_wK!=_wL){return new F(function(){return _wk(_wy,_wK,_wH,_wD,_wE);});}else{var _wR=E(_wH);if(_wR<E(_wJ)){return new F(function(){return _wM(_);});}else{return new F(function(){return _wk(_wy,_wK,_wR,_wD,_wE);});}}}else{return new F(function(){return _wM(_);});}}}},_wS=function(_wT,_wU,_wV,_wW,_wX,_wY){var _wZ=E(_wY);if(!_wZ._){return new F(function(){return _sP(new T2(0,_wV,_wW),_wX,_wU);});}else{var _x0=E(_wZ.a),_x1=E(_x0.a),_x2=_x1.b,_x3=E(_wV),_x4=E(_x1.a),_x5=function(_x6){var _x7=B(_v3(_wT,_x4,_x2,_x0.b,_wZ.b)),_x8=_x7.a,_x9=E(_x7.c);if(!_x9._){return new F(function(){return _ww(_wT<<1,B(_ui(new T2(0,_x3,_wW),_wX,_wU,_x8)),_x7.b);});}else{return new F(function(){return _wq(B(_ui(new T2(0,_x3,_wW),_wX,_wU,_x8)),_x9.a,_x9.b);});}};if(_x3>=_x4){if(_x3!=_x4){return new F(function(){return _wk(_wU,_x3,_wW,_wX,_wZ);});}else{if(_wW<E(_x2)){return new F(function(){return _x5(_);});}else{return new F(function(){return _wk(_wU,_x3,_wW,_wX,_wZ);});}}}else{return new F(function(){return _x5(_);});}}},_xa=function(_xb,_xc,_xd,_xe,_xf,_xg){var _xh=E(_xg);if(!_xh._){return new F(function(){return _sP(new T2(0,_xd,_xe),_xf,_xc);});}else{var _xi=E(_xh.a),_xj=E(_xi.a),_xk=_xj.b,_xl=E(_xd),_xm=E(_xj.a),_xn=function(_xo){var _xp=B(_v3(_xb,_xm,_xk,_xi.b,_xh.b)),_xq=_xp.a,_xr=E(_xp.c);if(!_xr._){return new F(function(){return _ww(_xb<<1,B(_ui(new T2(0,_xl,_xe),_xf,_xc,_xq)),_xp.b);});}else{return new F(function(){return _wq(B(_ui(new T2(0,_xl,_xe),_xf,_xc,_xq)),_xr.a,_xr.b);});}};if(_xl>=_xm){if(_xl!=_xm){return new F(function(){return _wk(_xc,_xl,_xe,_xf,_xh);});}else{var _xs=E(_xe);if(_xs<E(_xk)){return new F(function(){return _xn(_);});}else{return new F(function(){return _wk(_xc,_xl,_xs,_xf,_xh);});}}}else{return new F(function(){return _xn(_);});}}},_xt=function(_xu){var _xv=E(_xu);if(!_xv._){return new T0(1);}else{var _xw=E(_xv.a),_xx=_xw.a,_xy=_xw.b,_xz=E(_xv.b);if(!_xz._){return new T5(0,1,E(_xx),_xy,E(_s2),E(_s2));}else{var _xA=_xz.b,_xB=E(_xz.a),_xC=_xB.b,_xD=E(_xx),_xE=E(_xB.a),_xF=_xE.b,_xG=E(_xD.a),_xH=E(_xE.a);if(_xG>=_xH){if(_xG!=_xH){return new F(function(){return _wk(new T5(0,1,E(_xD),_xy,E(_s2),E(_s2)),_xH,_xF,_xC,_xA);});}else{var _xI=E(_xF);if(E(_xD.b)<_xI){return new F(function(){return _wS(1,new T5(0,1,E(_xD),_xy,E(_s2),E(_s2)),_xH,_xI,_xC,_xA);});}else{return new F(function(){return _wk(new T5(0,1,E(_xD),_xy,E(_s2),E(_s2)),_xH,_xI,_xC,_xA);});}}}else{return new F(function(){return _xa(1,new T5(0,1,E(_xD),_xy,E(_s2),E(_s2)),_xH,_xF,_xC,_xA);});}}}},_xJ=function(_xK,_xL,_xM,_xN,_xO){var _xP=E(_xK);if(_xP==1){var _xQ=E(_xO);if(!_xQ._){return new T3(0,new T5(0,1,E(new T2(0,_xL,_xM)),_xN,E(_s2),E(_s2)),_9,_9);}else{var _xR=E(E(_xQ.a).a),_xS=E(_xL),_xT=E(_xR.a);return (_xS>=_xT)?(_xS!=_xT)?new T3(0,new T5(0,1,E(new T2(0,_xS,_xM)),_xN,E(_s2),E(_s2)),_9,_xQ):(_xM<E(_xR.b))?new T3(0,new T5(0,1,E(new T2(0,_xS,_xM)),_xN,E(_s2),E(_s2)),_xQ,_9):new T3(0,new T5(0,1,E(new T2(0,_xS,_xM)),_xN,E(_s2),E(_s2)),_9,_xQ):new T3(0,new T5(0,1,E(new T2(0,_xS,_xM)),_xN,E(_s2),E(_s2)),_xQ,_9);}}else{var _xU=B(_xJ(_xP>>1,_xL,_xM,_xN,_xO)),_xV=_xU.a,_xW=_xU.c,_xX=E(_xU.b);if(!_xX._){return new T3(0,_xV,_9,_xW);}else{var _xY=E(_xX.a),_xZ=_xY.a,_y0=_xY.b,_y1=E(_xX.b);if(!_y1._){return new T3(0,new T(function(){return B(_sP(_xZ,_y0,_xV));}),_9,_xW);}else{var _y2=_y1.b,_y3=E(_y1.a),_y4=_y3.b,_y5=E(_xZ),_y6=E(_y3.a),_y7=_y6.b,_y8=E(_y5.a),_y9=E(_y6.a);if(_y8>=_y9){if(_y8!=_y9){return new T3(0,_xV,_9,_xX);}else{var _ya=E(_y7);if(E(_y5.b)<_ya){var _yb=B(_xJ(_xP>>1,_y9,_ya,_y4,_y2));return new T3(0,new T(function(){return B(_ui(_y5,_y0,_xV,_yb.a));}),_yb.b,_yb.c);}else{return new T3(0,_xV,_9,_xX);}}}else{var _yc=B(_yd(_xP>>1,_y9,_y7,_y4,_y2));return new T3(0,new T(function(){return B(_ui(_y5,_y0,_xV,_yc.a));}),_yc.b,_yc.c);}}}}},_yd=function(_ye,_yf,_yg,_yh,_yi){var _yj=E(_ye);if(_yj==1){var _yk=E(_yi);if(!_yk._){return new T3(0,new T5(0,1,E(new T2(0,_yf,_yg)),_yh,E(_s2),E(_s2)),_9,_9);}else{var _yl=E(E(_yk.a).a),_ym=E(_yf),_yn=E(_yl.a);if(_ym>=_yn){if(_ym!=_yn){return new T3(0,new T5(0,1,E(new T2(0,_ym,_yg)),_yh,E(_s2),E(_s2)),_9,_yk);}else{var _yo=E(_yg);return (_yo<E(_yl.b))?new T3(0,new T5(0,1,E(new T2(0,_ym,_yo)),_yh,E(_s2),E(_s2)),_yk,_9):new T3(0,new T5(0,1,E(new T2(0,_ym,_yo)),_yh,E(_s2),E(_s2)),_9,_yk);}}else{return new T3(0,new T5(0,1,E(new T2(0,_ym,_yg)),_yh,E(_s2),E(_s2)),_yk,_9);}}}else{var _yp=B(_yd(_yj>>1,_yf,_yg,_yh,_yi)),_yq=_yp.a,_yr=_yp.c,_ys=E(_yp.b);if(!_ys._){return new T3(0,_yq,_9,_yr);}else{var _yt=E(_ys.a),_yu=_yt.a,_yv=_yt.b,_yw=E(_ys.b);if(!_yw._){return new T3(0,new T(function(){return B(_sP(_yu,_yv,_yq));}),_9,_yr);}else{var _yx=_yw.b,_yy=E(_yw.a),_yz=_yy.b,_yA=E(_yu),_yB=E(_yy.a),_yC=_yB.b,_yD=E(_yA.a),_yE=E(_yB.a);if(_yD>=_yE){if(_yD!=_yE){return new T3(0,_yq,_9,_ys);}else{var _yF=E(_yC);if(E(_yA.b)<_yF){var _yG=B(_xJ(_yj>>1,_yE,_yF,_yz,_yx));return new T3(0,new T(function(){return B(_ui(_yA,_yv,_yq,_yG.a));}),_yG.b,_yG.c);}else{return new T3(0,_yq,_9,_ys);}}}else{var _yH=B(_yd(_yj>>1,_yE,_yC,_yz,_yx));return new T3(0,new T(function(){return B(_ui(_yA,_yv,_yq,_yH.a));}),_yH.b,_yH.c);}}}}},_yI=function(_yJ,_yK,_yL,_yM,_yN){var _yO=E(_yN);if(!_yO._){var _yP=_yO.c,_yQ=_yO.d,_yR=_yO.e,_yS=E(_yO.b),_yT=E(_yS.a);if(_yJ>=_yT){if(_yJ!=_yT){return new F(function(){return _s7(_yS,_yP,_yQ,B(_yI(_yJ,_,_yL,_yM,_yR)));});}else{var _yU=E(_yS.b);if(_yL>=_yU){if(_yL!=_yU){return new F(function(){return _s7(_yS,_yP,_yQ,B(_yI(_yJ,_,_yL,_yM,_yR)));});}else{return new T5(0,_yO.a,E(new T2(0,_yJ,_yL)),_yM,E(_yQ),E(_yR));}}else{return new F(function(){return _sY(_yS,_yP,B(_yI(_yJ,_,_yL,_yM,_yQ)),_yR);});}}}else{return new F(function(){return _sY(_yS,_yP,B(_yI(_yJ,_,_yL,_yM,_yQ)),_yR);});}}else{return new T5(0,1,E(new T2(0,_yJ,_yL)),_yM,E(_s2),E(_s2));}},_yV=function(_yW,_yX,_yY,_yZ,_z0){var _z1=E(_z0);if(!_z1._){var _z2=_z1.c,_z3=_z1.d,_z4=_z1.e,_z5=E(_z1.b),_z6=E(_z5.a);if(_yW>=_z6){if(_yW!=_z6){return new F(function(){return _s7(_z5,_z2,_z3,B(_yV(_yW,_,_yY,_yZ,_z4)));});}else{var _z7=E(_yY),_z8=E(_z5.b);if(_z7>=_z8){if(_z7!=_z8){return new F(function(){return _s7(_z5,_z2,_z3,B(_yI(_yW,_,_z7,_yZ,_z4)));});}else{return new T5(0,_z1.a,E(new T2(0,_yW,_z7)),_yZ,E(_z3),E(_z4));}}else{return new F(function(){return _sY(_z5,_z2,B(_yI(_yW,_,_z7,_yZ,_z3)),_z4);});}}}else{return new F(function(){return _sY(_z5,_z2,B(_yV(_yW,_,_yY,_yZ,_z3)),_z4);});}}else{return new T5(0,1,E(new T2(0,_yW,_yY)),_yZ,E(_s2),E(_s2));}},_z9=function(_za,_zb,_zc,_zd){var _ze=E(_zd);if(!_ze._){var _zf=_ze.c,_zg=_ze.d,_zh=_ze.e,_zi=E(_ze.b),_zj=E(_za),_zk=E(_zi.a);if(_zj>=_zk){if(_zj!=_zk){return new F(function(){return _s7(_zi,_zf,_zg,B(_yV(_zj,_,_zb,_zc,_zh)));});}else{var _zl=E(_zb),_zm=E(_zi.b);if(_zl>=_zm){if(_zl!=_zm){return new F(function(){return _s7(_zi,_zf,_zg,B(_yI(_zj,_,_zl,_zc,_zh)));});}else{return new T5(0,_ze.a,E(new T2(0,_zj,_zl)),_zc,E(_zg),E(_zh));}}else{return new F(function(){return _sY(_zi,_zf,B(_yI(_zj,_,_zl,_zc,_zg)),_zh);});}}}else{return new F(function(){return _sY(_zi,_zf,B(_yV(_zj,_,_zb,_zc,_zg)),_zh);});}}else{return new T5(0,1,E(new T2(0,_za,_zb)),_zc,E(_s2),E(_s2));}},_zn=function(_zo,_zp){while(1){var _zq=E(_zp);if(!_zq._){return E(_zo);}else{var _zr=E(_zq.a),_zs=E(_zr.a),_zt=B(_z9(_zs.a,_zs.b,_zr.b,_zo));_zo=_zt;_zp=_zq.b;continue;}}},_zu=function(_zv,_zw,_zx,_zy,_zz){return new F(function(){return _zn(B(_z9(_zw,_zx,_zy,_zv)),_zz);});},_zA=function(_zB,_zC,_zD){var _zE=E(_zC),_zF=E(_zE.a);return new F(function(){return _zn(B(_z9(_zF.a,_zF.b,_zE.b,_zB)),_zD);});},_zG=function(_zH,_zI,_zJ){var _zK=E(_zJ);if(!_zK._){return E(_zI);}else{var _zL=E(_zK.a),_zM=_zL.a,_zN=_zL.b,_zO=E(_zK.b);if(!_zO._){return new F(function(){return _sP(_zM,_zN,_zI);});}else{var _zP=E(_zO.a),_zQ=E(_zM),_zR=_zQ.b,_zS=E(_zP.a),_zT=_zS.b,_zU=E(_zQ.a),_zV=E(_zS.a),_zW=function(_zX){var _zY=B(_yd(_zH,_zV,_zT,_zP.b,_zO.b)),_zZ=_zY.a,_A0=E(_zY.c);if(!_A0._){return new F(function(){return _zG(_zH<<1,B(_ui(_zQ,_zN,_zI,_zZ)),_zY.b);});}else{return new F(function(){return _zA(B(_ui(_zQ,_zN,_zI,_zZ)),_A0.a,_A0.b);});}};if(_zU>=_zV){if(_zU!=_zV){return new F(function(){return _zu(_zI,_zU,_zR,_zN,_zO);});}else{var _A1=E(_zR);if(_A1<E(_zT)){return new F(function(){return _zW(_);});}else{return new F(function(){return _zu(_zI,_zU,_A1,_zN,_zO);});}}}else{return new F(function(){return _zW(_);});}}}},_A2=function(_A3,_A4,_A5,_A6,_A7,_A8){var _A9=E(_A8);if(!_A9._){return new F(function(){return _sP(new T2(0,_A5,_A6),_A7,_A4);});}else{var _Aa=E(_A9.a),_Ab=E(_Aa.a),_Ac=_Ab.b,_Ad=E(_A5),_Ae=E(_Ab.a),_Af=function(_Ag){var _Ah=B(_yd(_A3,_Ae,_Ac,_Aa.b,_A9.b)),_Ai=_Ah.a,_Aj=E(_Ah.c);if(!_Aj._){return new F(function(){return _zG(_A3<<1,B(_ui(new T2(0,_Ad,_A6),_A7,_A4,_Ai)),_Ah.b);});}else{return new F(function(){return _zA(B(_ui(new T2(0,_Ad,_A6),_A7,_A4,_Ai)),_Aj.a,_Aj.b);});}};if(_Ad>=_Ae){if(_Ad!=_Ae){return new F(function(){return _zu(_A4,_Ad,_A6,_A7,_A9);});}else{var _Ak=E(_A6);if(_Ak<E(_Ac)){return new F(function(){return _Af(_);});}else{return new F(function(){return _zu(_A4,_Ad,_Ak,_A7,_A9);});}}}else{return new F(function(){return _Af(_);});}}},_Al=function(_Am,_An,_Ao,_Ap,_Aq,_Ar){var _As=E(_Ar);if(!_As._){return new F(function(){return _sP(new T2(0,_Ao,_Ap),_Aq,_An);});}else{var _At=E(_As.a),_Au=E(_At.a),_Av=_Au.b,_Aw=E(_Ao),_Ax=E(_Au.a),_Ay=function(_Az){var _AA=B(_yd(_Am,_Ax,_Av,_At.b,_As.b)),_AB=_AA.a,_AC=E(_AA.c);if(!_AC._){return new F(function(){return _zG(_Am<<1,B(_ui(new T2(0,_Aw,_Ap),_Aq,_An,_AB)),_AA.b);});}else{return new F(function(){return _zA(B(_ui(new T2(0,_Aw,_Ap),_Aq,_An,_AB)),_AC.a,_AC.b);});}};if(_Aw>=_Ax){if(_Aw!=_Ax){return new F(function(){return _zu(_An,_Aw,_Ap,_Aq,_As);});}else{if(_Ap<E(_Av)){return new F(function(){return _Ay(_);});}else{return new F(function(){return _zu(_An,_Aw,_Ap,_Aq,_As);});}}}else{return new F(function(){return _Ay(_);});}}},_AD=function(_AE){var _AF=E(_AE);if(!_AF._){return new T0(1);}else{var _AG=E(_AF.a),_AH=_AG.a,_AI=_AG.b,_AJ=E(_AF.b);if(!_AJ._){return new T5(0,1,E(_AH),_AI,E(_s2),E(_s2));}else{var _AK=_AJ.b,_AL=E(_AJ.a),_AM=_AL.b,_AN=E(_AH),_AO=E(_AL.a),_AP=_AO.b,_AQ=E(_AN.a),_AR=E(_AO.a);if(_AQ>=_AR){if(_AQ!=_AR){return new F(function(){return _zu(new T5(0,1,E(_AN),_AI,E(_s2),E(_s2)),_AR,_AP,_AM,_AK);});}else{var _AS=E(_AP);if(E(_AN.b)<_AS){return new F(function(){return _Al(1,new T5(0,1,E(_AN),_AI,E(_s2),E(_s2)),_AR,_AS,_AM,_AK);});}else{return new F(function(){return _zu(new T5(0,1,E(_AN),_AI,E(_s2),E(_s2)),_AR,_AS,_AM,_AK);});}}}else{return new F(function(){return _A2(1,new T5(0,1,E(_AN),_AI,E(_s2),E(_s2)),_AR,_AP,_AM,_AK);});}}}},_AT=new T0(1),_AU=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_AV=function(_AW){return new F(function(){return err(_AU);});},_AX=new T(function(){return B(_AV(_));}),_AY=function(_AZ,_B0,_B1){var _B2=E(_B1);if(!_B2._){var _B3=_B2.a,_B4=E(_B0);if(!_B4._){var _B5=_B4.a,_B6=_B4.b;if(_B5<=(imul(3,_B3)|0)){return new T4(0,(1+_B5|0)+_B3|0,E(_AZ),E(_B4),E(_B2));}else{var _B7=E(_B4.c);if(!_B7._){var _B8=_B7.a,_B9=E(_B4.d);if(!_B9._){var _Ba=_B9.a,_Bb=_B9.b,_Bc=_B9.c;if(_Ba>=(imul(2,_B8)|0)){var _Bd=function(_Be){var _Bf=E(_B9.d);return (_Bf._==0)?new T4(0,(1+_B5|0)+_B3|0,E(_Bb),E(new T4(0,(1+_B8|0)+_Be|0,E(_B6),E(_B7),E(_Bc))),E(new T4(0,(1+_B3|0)+_Bf.a|0,E(_AZ),E(_Bf),E(_B2)))):new T4(0,(1+_B5|0)+_B3|0,E(_Bb),E(new T4(0,(1+_B8|0)+_Be|0,E(_B6),E(_B7),E(_Bc))),E(new T4(0,1+_B3|0,E(_AZ),E(_AT),E(_B2))));},_Bg=E(_Bc);if(!_Bg._){return new F(function(){return _Bd(_Bg.a);});}else{return new F(function(){return _Bd(0);});}}else{return new T4(0,(1+_B5|0)+_B3|0,E(_B6),E(_B7),E(new T4(0,(1+_B3|0)+_Ba|0,E(_AZ),E(_B9),E(_B2))));}}else{return E(_AX);}}else{return E(_AX);}}}else{return new T4(0,1+_B3|0,E(_AZ),E(_AT),E(_B2));}}else{var _Bh=E(_B0);if(!_Bh._){var _Bi=_Bh.a,_Bj=_Bh.b,_Bk=_Bh.d,_Bl=E(_Bh.c);if(!_Bl._){var _Bm=_Bl.a,_Bn=E(_Bk);if(!_Bn._){var _Bo=_Bn.a,_Bp=_Bn.b,_Bq=_Bn.c;if(_Bo>=(imul(2,_Bm)|0)){var _Br=function(_Bs){var _Bt=E(_Bn.d);return (_Bt._==0)?new T4(0,1+_Bi|0,E(_Bp),E(new T4(0,(1+_Bm|0)+_Bs|0,E(_Bj),E(_Bl),E(_Bq))),E(new T4(0,1+_Bt.a|0,E(_AZ),E(_Bt),E(_AT)))):new T4(0,1+_Bi|0,E(_Bp),E(new T4(0,(1+_Bm|0)+_Bs|0,E(_Bj),E(_Bl),E(_Bq))),E(new T4(0,1,E(_AZ),E(_AT),E(_AT))));},_Bu=E(_Bq);if(!_Bu._){return new F(function(){return _Br(_Bu.a);});}else{return new F(function(){return _Br(0);});}}else{return new T4(0,1+_Bi|0,E(_Bj),E(_Bl),E(new T4(0,1+_Bo|0,E(_AZ),E(_Bn),E(_AT))));}}else{return new T4(0,3,E(_Bj),E(_Bl),E(new T4(0,1,E(_AZ),E(_AT),E(_AT))));}}else{var _Bv=E(_Bk);return (_Bv._==0)?new T4(0,3,E(_Bv.b),E(new T4(0,1,E(_Bj),E(_AT),E(_AT))),E(new T4(0,1,E(_AZ),E(_AT),E(_AT)))):new T4(0,2,E(_AZ),E(_Bh),E(_AT));}}else{return new T4(0,1,E(_AZ),E(_AT),E(_AT));}}},_Bw=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Bx=function(_By){return new F(function(){return err(_Bw);});},_Bz=new T(function(){return B(_Bx(_));}),_BA=function(_BB,_BC,_BD){var _BE=E(_BC);if(!_BE._){var _BF=_BE.a,_BG=E(_BD);if(!_BG._){var _BH=_BG.a,_BI=_BG.b;if(_BH<=(imul(3,_BF)|0)){return new T4(0,(1+_BF|0)+_BH|0,E(_BB),E(_BE),E(_BG));}else{var _BJ=E(_BG.c);if(!_BJ._){var _BK=_BJ.a,_BL=_BJ.b,_BM=_BJ.c,_BN=E(_BG.d);if(!_BN._){var _BO=_BN.a;if(_BK>=(imul(2,_BO)|0)){var _BP=function(_BQ){var _BR=E(_BB),_BS=E(_BJ.d);return (_BS._==0)?new T4(0,(1+_BF|0)+_BH|0,E(_BL),E(new T4(0,(1+_BF|0)+_BQ|0,E(_BR),E(_BE),E(_BM))),E(new T4(0,(1+_BO|0)+_BS.a|0,E(_BI),E(_BS),E(_BN)))):new T4(0,(1+_BF|0)+_BH|0,E(_BL),E(new T4(0,(1+_BF|0)+_BQ|0,E(_BR),E(_BE),E(_BM))),E(new T4(0,1+_BO|0,E(_BI),E(_AT),E(_BN))));},_BT=E(_BM);if(!_BT._){return new F(function(){return _BP(_BT.a);});}else{return new F(function(){return _BP(0);});}}else{return new T4(0,(1+_BF|0)+_BH|0,E(_BI),E(new T4(0,(1+_BF|0)+_BK|0,E(_BB),E(_BE),E(_BJ))),E(_BN));}}else{return E(_Bz);}}else{return E(_Bz);}}}else{return new T4(0,1+_BF|0,E(_BB),E(_BE),E(_AT));}}else{var _BU=E(_BD);if(!_BU._){var _BV=_BU.a,_BW=_BU.b,_BX=_BU.d,_BY=E(_BU.c);if(!_BY._){var _BZ=_BY.a,_C0=_BY.b,_C1=_BY.c,_C2=E(_BX);if(!_C2._){var _C3=_C2.a;if(_BZ>=(imul(2,_C3)|0)){var _C4=function(_C5){var _C6=E(_BB),_C7=E(_BY.d);return (_C7._==0)?new T4(0,1+_BV|0,E(_C0),E(new T4(0,1+_C5|0,E(_C6),E(_AT),E(_C1))),E(new T4(0,(1+_C3|0)+_C7.a|0,E(_BW),E(_C7),E(_C2)))):new T4(0,1+_BV|0,E(_C0),E(new T4(0,1+_C5|0,E(_C6),E(_AT),E(_C1))),E(new T4(0,1+_C3|0,E(_BW),E(_AT),E(_C2))));},_C8=E(_C1);if(!_C8._){return new F(function(){return _C4(_C8.a);});}else{return new F(function(){return _C4(0);});}}else{return new T4(0,1+_BV|0,E(_BW),E(new T4(0,1+_BZ|0,E(_BB),E(_AT),E(_BY))),E(_C2));}}else{return new T4(0,3,E(_C0),E(new T4(0,1,E(_BB),E(_AT),E(_AT))),E(new T4(0,1,E(_BW),E(_AT),E(_AT))));}}else{var _C9=E(_BX);return (_C9._==0)?new T4(0,3,E(_BW),E(new T4(0,1,E(_BB),E(_AT),E(_AT))),E(_C9)):new T4(0,2,E(_BB),E(_AT),E(_BU));}}else{return new T4(0,1,E(_BB),E(_AT),E(_AT));}}},_Ca=function(_Cb,_Cc,_Cd,_Ce,_Cf){var _Cg=E(_Cf);if(!_Cg._){var _Ch=_Cg.c,_Ci=_Cg.d,_Cj=E(_Cg.b),_Ck=E(_Cb),_Cl=E(_Cj.a);if(_Ck>=_Cl){if(_Ck!=_Cl){return new F(function(){return _BA(_Cj,_Ch,B(_Ca(_Ck,_Cc,_Cd,_Ce,_Ci)));});}else{var _Cm=E(_Cc),_Cn=E(_Cj.b);if(_Cm>=_Cn){if(_Cm!=_Cn){return new F(function(){return _BA(_Cj,_Ch,B(_Ca(_Ck,_Cm,_Cd,_Ce,_Ci)));});}else{var _Co=E(_Cd),_Cp=E(_Cj.c);if(_Co>=_Cp){if(_Co!=_Cp){return new F(function(){return _BA(_Cj,_Ch,B(_Ca(_Ck,_Cm,_Co,_Ce,_Ci)));});}else{var _Cq=E(_Ce),_Cr=E(_Cj.d);if(_Cq>=_Cr){if(_Cq!=_Cr){return new F(function(){return _BA(_Cj,_Ch,B(_Ca(_Ck,_Cm,_Co,_Cq,_Ci)));});}else{return new T4(0,_Cg.a,E(new T4(0,_Ck,_Cm,_Co,_Cq)),E(_Ch),E(_Ci));}}else{return new F(function(){return _AY(_Cj,B(_Ca(_Ck,_Cm,_Co,_Cq,_Ch)),_Ci);});}}}else{return new F(function(){return _AY(_Cj,B(_Ca(_Ck,_Cm,_Co,_Ce,_Ch)),_Ci);});}}}else{return new F(function(){return _AY(_Cj,B(_Ca(_Ck,_Cm,_Cd,_Ce,_Ch)),_Ci);});}}}else{return new F(function(){return _AY(_Cj,B(_Ca(_Ck,_Cc,_Cd,_Ce,_Ch)),_Ci);});}}else{return new T4(0,1,E(new T4(0,_Cb,_Cc,_Cd,_Ce)),E(_AT),E(_AT));}},_Cs=function(_Ct,_Cu){while(1){var _Cv=E(_Cu);if(!_Cv._){return E(_Ct);}else{var _Cw=E(_Cv.a),_Cx=B(_Ca(_Cw.a,_Cw.b,_Cw.c,_Cw.d,_Ct));_Ct=_Cx;_Cu=_Cv.b;continue;}}},_Cy=function(_Cz,_CA,_CB,_CC,_CD,_CE){return new F(function(){return _Cs(B(_Ca(_CA,_CB,_CC,_CD,_Cz)),_CE);});},_CF=function(_CG){return new T4(0,1,E(_CG),E(_AT),E(_AT));},_CH=function(_CI,_CJ){var _CK=E(_CJ);if(!_CK._){return new F(function(){return _BA(_CK.b,_CK.c,B(_CH(_CI,_CK.d)));});}else{return new F(function(){return _CF(_CI);});}},_CL=function(_CM,_CN){var _CO=E(_CN);if(!_CO._){return new F(function(){return _AY(_CO.b,B(_CL(_CM,_CO.c)),_CO.d);});}else{return new F(function(){return _CF(_CM);});}},_CP=function(_CQ,_CR,_CS,_CT,_CU){return new F(function(){return _BA(_CS,_CT,B(_CH(_CQ,_CU)));});},_CV=function(_CW,_CX,_CY,_CZ,_D0){return new F(function(){return _AY(_CY,B(_CL(_CW,_CZ)),_D0);});},_D1=function(_D2,_D3,_D4,_D5,_D6,_D7){var _D8=E(_D3);if(!_D8._){var _D9=_D8.a,_Da=_D8.b,_Db=_D8.c,_Dc=_D8.d;if((imul(3,_D9)|0)>=_D4){if((imul(3,_D4)|0)>=_D9){return new T4(0,(_D9+_D4|0)+1|0,E(_D2),E(_D8),E(new T4(0,_D4,E(_D5),E(_D6),E(_D7))));}else{return new F(function(){return _BA(_Da,_Db,B(_D1(_D2,_Dc,_D4,_D5,_D6,_D7)));});}}else{return new F(function(){return _AY(_D5,B(_Dd(_D2,_D9,_Da,_Db,_Dc,_D6)),_D7);});}}else{return new F(function(){return _CV(_D2,_D4,_D5,_D6,_D7);});}},_Dd=function(_De,_Df,_Dg,_Dh,_Di,_Dj){var _Dk=E(_Dj);if(!_Dk._){var _Dl=_Dk.a,_Dm=_Dk.b,_Dn=_Dk.c,_Do=_Dk.d;if((imul(3,_Df)|0)>=_Dl){if((imul(3,_Dl)|0)>=_Df){return new T4(0,(_Df+_Dl|0)+1|0,E(_De),E(new T4(0,_Df,E(_Dg),E(_Dh),E(_Di))),E(_Dk));}else{return new F(function(){return _BA(_Dg,_Dh,B(_D1(_De,_Di,_Dl,_Dm,_Dn,_Do)));});}}else{return new F(function(){return _AY(_Dm,B(_Dd(_De,_Df,_Dg,_Dh,_Di,_Dn)),_Do);});}}else{return new F(function(){return _CP(_De,_Df,_Dg,_Dh,_Di);});}},_Dp=function(_Dq,_Dr,_Ds){var _Dt=E(_Dr);if(!_Dt._){var _Du=_Dt.a,_Dv=_Dt.b,_Dw=_Dt.c,_Dx=_Dt.d,_Dy=E(_Ds);if(!_Dy._){var _Dz=_Dy.a,_DA=_Dy.b,_DB=_Dy.c,_DC=_Dy.d;if((imul(3,_Du)|0)>=_Dz){if((imul(3,_Dz)|0)>=_Du){return new T4(0,(_Du+_Dz|0)+1|0,E(_Dq),E(_Dt),E(_Dy));}else{return new F(function(){return _BA(_Dv,_Dw,B(_D1(_Dq,_Dx,_Dz,_DA,_DB,_DC)));});}}else{return new F(function(){return _AY(_DA,B(_Dd(_Dq,_Du,_Dv,_Dw,_Dx,_DB)),_DC);});}}else{return new F(function(){return _CP(_Dq,_Du,_Dv,_Dw,_Dx);});}}else{return new F(function(){return _CL(_Dq,_Ds);});}},_DD=function(_DE,_DF){var _DG=E(_DF);if(!_DG._){return new T3(0,_AT,_9,_9);}else{var _DH=_DG.a,_DI=E(_DE);if(_DI==1){var _DJ=E(_DG.b);if(!_DJ._){return new T3(0,new T(function(){return new T4(0,1,E(_DH),E(_AT),E(_AT));}),_9,_9);}else{var _DK=E(_DH),_DL=E(_DK.a),_DM=E(_DJ.a),_DN=E(_DM.a);if(_DL>=_DN){if(_DL!=_DN){return new T3(0,new T4(0,1,E(_DK),E(_AT),E(_AT)),_9,_DJ);}else{var _DO=E(_DK.b),_DP=E(_DM.b);if(_DO>=_DP){if(_DO!=_DP){return new T3(0,new T4(0,1,E(_DK),E(_AT),E(_AT)),_9,_DJ);}else{var _DQ=E(_DK.c),_DR=E(_DM.c);return (_DQ>=_DR)?(_DQ!=_DR)?new T3(0,new T4(0,1,E(_DK),E(_AT),E(_AT)),_9,_DJ):(E(_DK.d)<E(_DM.d))?new T3(0,new T4(0,1,E(_DK),E(_AT),E(_AT)),_DJ,_9):new T3(0,new T4(0,1,E(_DK),E(_AT),E(_AT)),_9,_DJ):new T3(0,new T4(0,1,E(_DK),E(_AT),E(_AT)),_DJ,_9);}}else{return new T3(0,new T4(0,1,E(_DK),E(_AT),E(_AT)),_DJ,_9);}}}else{return new T3(0,new T4(0,1,E(_DK),E(_AT),E(_AT)),_DJ,_9);}}}else{var _DS=B(_DD(_DI>>1,_DG)),_DT=_DS.a,_DU=_DS.c,_DV=E(_DS.b);if(!_DV._){return new T3(0,_DT,_9,_DU);}else{var _DW=_DV.a,_DX=E(_DV.b);if(!_DX._){return new T3(0,new T(function(){return B(_CH(_DW,_DT));}),_9,_DU);}else{var _DY=E(_DW),_DZ=E(_DY.a),_E0=E(_DX.a),_E1=E(_E0.a);if(_DZ>=_E1){if(_DZ!=_E1){return new T3(0,_DT,_9,_DV);}else{var _E2=E(_DY.b),_E3=E(_E0.b);if(_E2>=_E3){if(_E2!=_E3){return new T3(0,_DT,_9,_DV);}else{var _E4=E(_DY.c),_E5=E(_E0.c);if(_E4>=_E5){if(_E4!=_E5){return new T3(0,_DT,_9,_DV);}else{if(E(_DY.d)<E(_E0.d)){var _E6=B(_DD(_DI>>1,_DX));return new T3(0,new T(function(){return B(_Dp(_DY,_DT,_E6.a));}),_E6.b,_E6.c);}else{return new T3(0,_DT,_9,_DV);}}}else{var _E7=B(_DD(_DI>>1,_DX));return new T3(0,new T(function(){return B(_Dp(_DY,_DT,_E7.a));}),_E7.b,_E7.c);}}}else{var _E8=B(_DD(_DI>>1,_DX));return new T3(0,new T(function(){return B(_Dp(_DY,_DT,_E8.a));}),_E8.b,_E8.c);}}}else{var _E9=B(_DD(_DI>>1,_DX));return new T3(0,new T(function(){return B(_Dp(_DY,_DT,_E9.a));}),_E9.b,_E9.c);}}}}}},_Ea=function(_Eb,_Ec,_Ed){var _Ee=E(_Ed);if(!_Ee._){return E(_Ec);}else{var _Ef=_Ee.a,_Eg=E(_Ee.b);if(!_Eg._){return new F(function(){return _CH(_Ef,_Ec);});}else{var _Eh=E(_Ef),_Ei=_Eh.b,_Ej=_Eh.c,_Ek=_Eh.d,_El=E(_Eh.a),_Em=E(_Eg.a),_En=E(_Em.a),_Eo=function(_Ep){var _Eq=B(_DD(_Eb,_Eg)),_Er=_Eq.a,_Es=E(_Eq.c);if(!_Es._){return new F(function(){return _Ea(_Eb<<1,B(_Dp(_Eh,_Ec,_Er)),_Eq.b);});}else{return new F(function(){return _Cs(B(_Dp(_Eh,_Ec,_Er)),_Es);});}};if(_El>=_En){if(_El!=_En){return new F(function(){return _Cy(_Ec,_El,_Ei,_Ej,_Ek,_Eg);});}else{var _Et=E(_Ei),_Eu=E(_Em.b);if(_Et>=_Eu){if(_Et!=_Eu){return new F(function(){return _Cy(_Ec,_El,_Et,_Ej,_Ek,_Eg);});}else{var _Ev=E(_Ej),_Ew=E(_Em.c);if(_Ev>=_Ew){if(_Ev!=_Ew){return new F(function(){return _Cy(_Ec,_El,_Et,_Ev,_Ek,_Eg);});}else{var _Ex=E(_Ek);if(_Ex<E(_Em.d)){return new F(function(){return _Eo(_);});}else{return new F(function(){return _Cy(_Ec,_El,_Et,_Ev,_Ex,_Eg);});}}}else{return new F(function(){return _Eo(_);});}}}else{return new F(function(){return _Eo(_);});}}}else{return new F(function(){return _Eo(_);});}}}},_Ey=function(_Ez){var _EA=E(_Ez);if(!_EA._){return new T0(1);}else{var _EB=_EA.a,_EC=E(_EA.b);if(!_EC._){return new T4(0,1,E(_EB),E(_AT),E(_AT));}else{var _ED=_EC.b,_EE=E(_EB),_EF=E(_EE.a),_EG=E(_EC.a),_EH=_EG.b,_EI=_EG.c,_EJ=_EG.d,_EK=E(_EG.a);if(_EF>=_EK){if(_EF!=_EK){return new F(function(){return _Cy(new T4(0,1,E(_EE),E(_AT),E(_AT)),_EK,_EH,_EI,_EJ,_ED);});}else{var _EL=E(_EE.b),_EM=E(_EH);if(_EL>=_EM){if(_EL!=_EM){return new F(function(){return _Cy(new T4(0,1,E(_EE),E(_AT),E(_AT)),_EK,_EM,_EI,_EJ,_ED);});}else{var _EN=E(_EE.c),_EO=E(_EI);if(_EN>=_EO){if(_EN!=_EO){return new F(function(){return _Cy(new T4(0,1,E(_EE),E(_AT),E(_AT)),_EK,_EM,_EO,_EJ,_ED);});}else{var _EP=E(_EJ);if(E(_EE.d)<_EP){return new F(function(){return _Ea(1,new T4(0,1,E(_EE),E(_AT),E(_AT)),_EC);});}else{return new F(function(){return _Cy(new T4(0,1,E(_EE),E(_AT),E(_AT)),_EK,_EM,_EO,_EP,_ED);});}}}else{return new F(function(){return _Ea(1,new T4(0,1,E(_EE),E(_AT),E(_AT)),_EC);});}}}else{return new F(function(){return _Ea(1,new T4(0,1,E(_EE),E(_AT),E(_AT)),_EC);});}}}else{return new F(function(){return _Ea(1,new T4(0,1,E(_EE),E(_AT),E(_AT)),_EC);});}}}},_EQ=function(_ER,_ES,_ET,_EU,_EV){var _EW=E(_ER);if(_EW==1){var _EX=E(_EV);if(!_EX._){return new T3(0,new T4(0,1,E(new T3(0,_ES,_ET,_EU)),E(_AT),E(_AT)),_9,_9);}else{var _EY=E(_ES),_EZ=E(_EX.a),_F0=E(_EZ.a);if(_EY>=_F0){if(_EY!=_F0){return new T3(0,new T4(0,1,E(new T3(0,_EY,_ET,_EU)),E(_AT),E(_AT)),_9,_EX);}else{var _F1=E(_EZ.b);return (_ET>=_F1)?(_ET!=_F1)?new T3(0,new T4(0,1,E(new T3(0,_EY,_ET,_EU)),E(_AT),E(_AT)),_9,_EX):(_EU<E(_EZ.c))?new T3(0,new T4(0,1,E(new T3(0,_EY,_ET,_EU)),E(_AT),E(_AT)),_EX,_9):new T3(0,new T4(0,1,E(new T3(0,_EY,_ET,_EU)),E(_AT),E(_AT)),_9,_EX):new T3(0,new T4(0,1,E(new T3(0,_EY,_ET,_EU)),E(_AT),E(_AT)),_EX,_9);}}else{return new T3(0,new T4(0,1,E(new T3(0,_EY,_ET,_EU)),E(_AT),E(_AT)),_EX,_9);}}}else{var _F2=B(_EQ(_EW>>1,_ES,_ET,_EU,_EV)),_F3=_F2.a,_F4=_F2.c,_F5=E(_F2.b);if(!_F5._){return new T3(0,_F3,_9,_F4);}else{var _F6=_F5.a,_F7=E(_F5.b);if(!_F7._){return new T3(0,new T(function(){return B(_CH(_F6,_F3));}),_9,_F4);}else{var _F8=_F7.b,_F9=E(_F6),_Fa=E(_F9.a),_Fb=E(_F7.a),_Fc=_Fb.b,_Fd=_Fb.c,_Fe=E(_Fb.a);if(_Fa>=_Fe){if(_Fa!=_Fe){return new T3(0,_F3,_9,_F5);}else{var _Ff=E(_F9.b),_Fg=E(_Fc);if(_Ff>=_Fg){if(_Ff!=_Fg){return new T3(0,_F3,_9,_F5);}else{var _Fh=E(_Fd);if(E(_F9.c)<_Fh){var _Fi=B(_EQ(_EW>>1,_Fe,_Fg,_Fh,_F8));return new T3(0,new T(function(){return B(_Dp(_F9,_F3,_Fi.a));}),_Fi.b,_Fi.c);}else{return new T3(0,_F3,_9,_F5);}}}else{var _Fj=B(_Fk(_EW>>1,_Fe,_Fg,_Fd,_F8));return new T3(0,new T(function(){return B(_Dp(_F9,_F3,_Fj.a));}),_Fj.b,_Fj.c);}}}else{var _Fl=B(_Fm(_EW>>1,_Fe,_Fc,_Fd,_F8));return new T3(0,new T(function(){return B(_Dp(_F9,_F3,_Fl.a));}),_Fl.b,_Fl.c);}}}}},_Fk=function(_Fn,_Fo,_Fp,_Fq,_Fr){var _Fs=E(_Fn);if(_Fs==1){var _Ft=E(_Fr);if(!_Ft._){return new T3(0,new T4(0,1,E(new T3(0,_Fo,_Fp,_Fq)),E(_AT),E(_AT)),_9,_9);}else{var _Fu=E(_Fo),_Fv=E(_Ft.a),_Fw=E(_Fv.a);if(_Fu>=_Fw){if(_Fu!=_Fw){return new T3(0,new T4(0,1,E(new T3(0,_Fu,_Fp,_Fq)),E(_AT),E(_AT)),_9,_Ft);}else{var _Fx=E(_Fv.b);if(_Fp>=_Fx){if(_Fp!=_Fx){return new T3(0,new T4(0,1,E(new T3(0,_Fu,_Fp,_Fq)),E(_AT),E(_AT)),_9,_Ft);}else{var _Fy=E(_Fq);return (_Fy<E(_Fv.c))?new T3(0,new T4(0,1,E(new T3(0,_Fu,_Fp,_Fy)),E(_AT),E(_AT)),_Ft,_9):new T3(0,new T4(0,1,E(new T3(0,_Fu,_Fp,_Fy)),E(_AT),E(_AT)),_9,_Ft);}}else{return new T3(0,new T4(0,1,E(new T3(0,_Fu,_Fp,_Fq)),E(_AT),E(_AT)),_Ft,_9);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_Fu,_Fp,_Fq)),E(_AT),E(_AT)),_Ft,_9);}}}else{var _Fz=B(_Fk(_Fs>>1,_Fo,_Fp,_Fq,_Fr)),_FA=_Fz.a,_FB=_Fz.c,_FC=E(_Fz.b);if(!_FC._){return new T3(0,_FA,_9,_FB);}else{var _FD=_FC.a,_FE=E(_FC.b);if(!_FE._){return new T3(0,new T(function(){return B(_CH(_FD,_FA));}),_9,_FB);}else{var _FF=_FE.b,_FG=E(_FD),_FH=E(_FG.a),_FI=E(_FE.a),_FJ=_FI.b,_FK=_FI.c,_FL=E(_FI.a);if(_FH>=_FL){if(_FH!=_FL){return new T3(0,_FA,_9,_FC);}else{var _FM=E(_FG.b),_FN=E(_FJ);if(_FM>=_FN){if(_FM!=_FN){return new T3(0,_FA,_9,_FC);}else{var _FO=E(_FK);if(E(_FG.c)<_FO){var _FP=B(_EQ(_Fs>>1,_FL,_FN,_FO,_FF));return new T3(0,new T(function(){return B(_Dp(_FG,_FA,_FP.a));}),_FP.b,_FP.c);}else{return new T3(0,_FA,_9,_FC);}}}else{var _FQ=B(_Fk(_Fs>>1,_FL,_FN,_FK,_FF));return new T3(0,new T(function(){return B(_Dp(_FG,_FA,_FQ.a));}),_FQ.b,_FQ.c);}}}else{var _FR=B(_Fm(_Fs>>1,_FL,_FJ,_FK,_FF));return new T3(0,new T(function(){return B(_Dp(_FG,_FA,_FR.a));}),_FR.b,_FR.c);}}}}},_Fm=function(_FS,_FT,_FU,_FV,_FW){var _FX=E(_FS);if(_FX==1){var _FY=E(_FW);if(!_FY._){return new T3(0,new T4(0,1,E(new T3(0,_FT,_FU,_FV)),E(_AT),E(_AT)),_9,_9);}else{var _FZ=E(_FT),_G0=E(_FY.a),_G1=E(_G0.a);if(_FZ>=_G1){if(_FZ!=_G1){return new T3(0,new T4(0,1,E(new T3(0,_FZ,_FU,_FV)),E(_AT),E(_AT)),_9,_FY);}else{var _G2=E(_FU),_G3=E(_G0.b);if(_G2>=_G3){if(_G2!=_G3){return new T3(0,new T4(0,1,E(new T3(0,_FZ,_G2,_FV)),E(_AT),E(_AT)),_9,_FY);}else{var _G4=E(_FV);return (_G4<E(_G0.c))?new T3(0,new T4(0,1,E(new T3(0,_FZ,_G2,_G4)),E(_AT),E(_AT)),_FY,_9):new T3(0,new T4(0,1,E(new T3(0,_FZ,_G2,_G4)),E(_AT),E(_AT)),_9,_FY);}}else{return new T3(0,new T4(0,1,E(new T3(0,_FZ,_G2,_FV)),E(_AT),E(_AT)),_FY,_9);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_FZ,_FU,_FV)),E(_AT),E(_AT)),_FY,_9);}}}else{var _G5=B(_Fm(_FX>>1,_FT,_FU,_FV,_FW)),_G6=_G5.a,_G7=_G5.c,_G8=E(_G5.b);if(!_G8._){return new T3(0,_G6,_9,_G7);}else{var _G9=_G8.a,_Ga=E(_G8.b);if(!_Ga._){return new T3(0,new T(function(){return B(_CH(_G9,_G6));}),_9,_G7);}else{var _Gb=_Ga.b,_Gc=E(_G9),_Gd=E(_Gc.a),_Ge=E(_Ga.a),_Gf=_Ge.b,_Gg=_Ge.c,_Gh=E(_Ge.a);if(_Gd>=_Gh){if(_Gd!=_Gh){return new T3(0,_G6,_9,_G8);}else{var _Gi=E(_Gc.b),_Gj=E(_Gf);if(_Gi>=_Gj){if(_Gi!=_Gj){return new T3(0,_G6,_9,_G8);}else{var _Gk=E(_Gg);if(E(_Gc.c)<_Gk){var _Gl=B(_EQ(_FX>>1,_Gh,_Gj,_Gk,_Gb));return new T3(0,new T(function(){return B(_Dp(_Gc,_G6,_Gl.a));}),_Gl.b,_Gl.c);}else{return new T3(0,_G6,_9,_G8);}}}else{var _Gm=B(_Fk(_FX>>1,_Gh,_Gj,_Gg,_Gb));return new T3(0,new T(function(){return B(_Dp(_Gc,_G6,_Gm.a));}),_Gm.b,_Gm.c);}}}else{var _Gn=B(_Fm(_FX>>1,_Gh,_Gf,_Gg,_Gb));return new T3(0,new T(function(){return B(_Dp(_Gc,_G6,_Gn.a));}),_Gn.b,_Gn.c);}}}}},_Go=function(_Gp,_Gq,_Gr,_Gs,_Gt){var _Gu=E(_Gt);if(!_Gu._){var _Gv=_Gu.c,_Gw=_Gu.d,_Gx=E(_Gu.b),_Gy=E(_Gx.a);if(_Gp>=_Gy){if(_Gp!=_Gy){return new F(function(){return _BA(_Gx,_Gv,B(_Go(_Gp,_,_Gr,_Gs,_Gw)));});}else{var _Gz=E(_Gx.b);if(_Gr>=_Gz){if(_Gr!=_Gz){return new F(function(){return _BA(_Gx,_Gv,B(_Go(_Gp,_,_Gr,_Gs,_Gw)));});}else{var _GA=E(_Gx.c);if(_Gs>=_GA){if(_Gs!=_GA){return new F(function(){return _BA(_Gx,_Gv,B(_Go(_Gp,_,_Gr,_Gs,_Gw)));});}else{return new T4(0,_Gu.a,E(new T3(0,_Gp,_Gr,_Gs)),E(_Gv),E(_Gw));}}else{return new F(function(){return _AY(_Gx,B(_Go(_Gp,_,_Gr,_Gs,_Gv)),_Gw);});}}}else{return new F(function(){return _AY(_Gx,B(_Go(_Gp,_,_Gr,_Gs,_Gv)),_Gw);});}}}else{return new F(function(){return _AY(_Gx,B(_Go(_Gp,_,_Gr,_Gs,_Gv)),_Gw);});}}else{return new T4(0,1,E(new T3(0,_Gp,_Gr,_Gs)),E(_AT),E(_AT));}},_GB=function(_GC,_GD,_GE,_GF,_GG){var _GH=E(_GG);if(!_GH._){var _GI=_GH.c,_GJ=_GH.d,_GK=E(_GH.b),_GL=E(_GK.a);if(_GC>=_GL){if(_GC!=_GL){return new F(function(){return _BA(_GK,_GI,B(_GB(_GC,_,_GE,_GF,_GJ)));});}else{var _GM=E(_GK.b);if(_GE>=_GM){if(_GE!=_GM){return new F(function(){return _BA(_GK,_GI,B(_GB(_GC,_,_GE,_GF,_GJ)));});}else{var _GN=E(_GF),_GO=E(_GK.c);if(_GN>=_GO){if(_GN!=_GO){return new F(function(){return _BA(_GK,_GI,B(_Go(_GC,_,_GE,_GN,_GJ)));});}else{return new T4(0,_GH.a,E(new T3(0,_GC,_GE,_GN)),E(_GI),E(_GJ));}}else{return new F(function(){return _AY(_GK,B(_Go(_GC,_,_GE,_GN,_GI)),_GJ);});}}}else{return new F(function(){return _AY(_GK,B(_GB(_GC,_,_GE,_GF,_GI)),_GJ);});}}}else{return new F(function(){return _AY(_GK,B(_GB(_GC,_,_GE,_GF,_GI)),_GJ);});}}else{return new T4(0,1,E(new T3(0,_GC,_GE,_GF)),E(_AT),E(_AT));}},_GP=function(_GQ,_GR,_GS,_GT,_GU){var _GV=E(_GU);if(!_GV._){var _GW=_GV.c,_GX=_GV.d,_GY=E(_GV.b),_GZ=E(_GY.a);if(_GQ>=_GZ){if(_GQ!=_GZ){return new F(function(){return _BA(_GY,_GW,B(_GP(_GQ,_,_GS,_GT,_GX)));});}else{var _H0=E(_GS),_H1=E(_GY.b);if(_H0>=_H1){if(_H0!=_H1){return new F(function(){return _BA(_GY,_GW,B(_GB(_GQ,_,_H0,_GT,_GX)));});}else{var _H2=E(_GT),_H3=E(_GY.c);if(_H2>=_H3){if(_H2!=_H3){return new F(function(){return _BA(_GY,_GW,B(_Go(_GQ,_,_H0,_H2,_GX)));});}else{return new T4(0,_GV.a,E(new T3(0,_GQ,_H0,_H2)),E(_GW),E(_GX));}}else{return new F(function(){return _AY(_GY,B(_Go(_GQ,_,_H0,_H2,_GW)),_GX);});}}}else{return new F(function(){return _AY(_GY,B(_GB(_GQ,_,_H0,_GT,_GW)),_GX);});}}}else{return new F(function(){return _AY(_GY,B(_GP(_GQ,_,_GS,_GT,_GW)),_GX);});}}else{return new T4(0,1,E(new T3(0,_GQ,_GS,_GT)),E(_AT),E(_AT));}},_H4=function(_H5,_H6,_H7,_H8){var _H9=E(_H8);if(!_H9._){var _Ha=_H9.c,_Hb=_H9.d,_Hc=E(_H9.b),_Hd=E(_H5),_He=E(_Hc.a);if(_Hd>=_He){if(_Hd!=_He){return new F(function(){return _BA(_Hc,_Ha,B(_GP(_Hd,_,_H6,_H7,_Hb)));});}else{var _Hf=E(_H6),_Hg=E(_Hc.b);if(_Hf>=_Hg){if(_Hf!=_Hg){return new F(function(){return _BA(_Hc,_Ha,B(_GB(_Hd,_,_Hf,_H7,_Hb)));});}else{var _Hh=E(_H7),_Hi=E(_Hc.c);if(_Hh>=_Hi){if(_Hh!=_Hi){return new F(function(){return _BA(_Hc,_Ha,B(_Go(_Hd,_,_Hf,_Hh,_Hb)));});}else{return new T4(0,_H9.a,E(new T3(0,_Hd,_Hf,_Hh)),E(_Ha),E(_Hb));}}else{return new F(function(){return _AY(_Hc,B(_Go(_Hd,_,_Hf,_Hh,_Ha)),_Hb);});}}}else{return new F(function(){return _AY(_Hc,B(_GB(_Hd,_,_Hf,_H7,_Ha)),_Hb);});}}}else{return new F(function(){return _AY(_Hc,B(_GP(_Hd,_,_H6,_H7,_Ha)),_Hb);});}}else{return new T4(0,1,E(new T3(0,_H5,_H6,_H7)),E(_AT),E(_AT));}},_Hj=function(_Hk,_Hl){while(1){var _Hm=E(_Hl);if(!_Hm._){return E(_Hk);}else{var _Hn=E(_Hm.a),_Ho=B(_H4(_Hn.a,_Hn.b,_Hn.c,_Hk));_Hk=_Ho;_Hl=_Hm.b;continue;}}},_Hp=function(_Hq,_Hr,_Hs,_Ht,_Hu){return new F(function(){return _Hj(B(_H4(_Hr,_Hs,_Ht,_Hq)),_Hu);});},_Hv=function(_Hw,_Hx,_Hy){var _Hz=E(_Hx);return new F(function(){return _Hj(B(_H4(_Hz.a,_Hz.b,_Hz.c,_Hw)),_Hy);});},_HA=function(_HB,_HC,_HD){var _HE=E(_HD);if(!_HE._){return E(_HC);}else{var _HF=_HE.a,_HG=E(_HE.b);if(!_HG._){return new F(function(){return _CH(_HF,_HC);});}else{var _HH=E(_HF),_HI=_HH.b,_HJ=_HH.c,_HK=E(_HH.a),_HL=E(_HG.a),_HM=_HL.b,_HN=_HL.c,_HO=E(_HL.a),_HP=function(_HQ){var _HR=B(_Fm(_HB,_HO,_HM,_HN,_HG.b)),_HS=_HR.a,_HT=E(_HR.c);if(!_HT._){return new F(function(){return _HA(_HB<<1,B(_Dp(_HH,_HC,_HS)),_HR.b);});}else{return new F(function(){return _Hv(B(_Dp(_HH,_HC,_HS)),_HT.a,_HT.b);});}};if(_HK>=_HO){if(_HK!=_HO){return new F(function(){return _Hp(_HC,_HK,_HI,_HJ,_HG);});}else{var _HU=E(_HI),_HV=E(_HM);if(_HU>=_HV){if(_HU!=_HV){return new F(function(){return _Hp(_HC,_HK,_HU,_HJ,_HG);});}else{var _HW=E(_HJ);if(_HW<E(_HN)){return new F(function(){return _HP(_);});}else{return new F(function(){return _Hp(_HC,_HK,_HU,_HW,_HG);});}}}else{return new F(function(){return _HP(_);});}}}else{return new F(function(){return _HP(_);});}}}},_HX=function(_HY,_HZ,_I0,_I1,_I2,_I3){var _I4=E(_I3);if(!_I4._){return new F(function(){return _CH(new T3(0,_I0,_I1,_I2),_HZ);});}else{var _I5=E(_I0),_I6=E(_I4.a),_I7=_I6.b,_I8=_I6.c,_I9=E(_I6.a),_Ia=function(_Ib){var _Ic=B(_Fm(_HY,_I9,_I7,_I8,_I4.b)),_Id=_Ic.a,_Ie=E(_Ic.c);if(!_Ie._){return new F(function(){return _HA(_HY<<1,B(_Dp(new T3(0,_I5,_I1,_I2),_HZ,_Id)),_Ic.b);});}else{return new F(function(){return _Hv(B(_Dp(new T3(0,_I5,_I1,_I2),_HZ,_Id)),_Ie.a,_Ie.b);});}};if(_I5>=_I9){if(_I5!=_I9){return new F(function(){return _Hp(_HZ,_I5,_I1,_I2,_I4);});}else{var _If=E(_I7);if(_I1>=_If){if(_I1!=_If){return new F(function(){return _Hp(_HZ,_I5,_I1,_I2,_I4);});}else{var _Ig=E(_I2);if(_Ig<E(_I8)){return new F(function(){return _Ia(_);});}else{return new F(function(){return _Hp(_HZ,_I5,_I1,_Ig,_I4);});}}}else{return new F(function(){return _Ia(_);});}}}else{return new F(function(){return _Ia(_);});}}},_Ih=function(_Ii,_Ij,_Ik,_Il,_Im,_In){var _Io=E(_In);if(!_Io._){return new F(function(){return _CH(new T3(0,_Ik,_Il,_Im),_Ij);});}else{var _Ip=E(_Ik),_Iq=E(_Io.a),_Ir=_Iq.b,_Is=_Iq.c,_It=E(_Iq.a),_Iu=function(_Iv){var _Iw=B(_Fm(_Ii,_It,_Ir,_Is,_Io.b)),_Ix=_Iw.a,_Iy=E(_Iw.c);if(!_Iy._){return new F(function(){return _HA(_Ii<<1,B(_Dp(new T3(0,_Ip,_Il,_Im),_Ij,_Ix)),_Iw.b);});}else{return new F(function(){return _Hv(B(_Dp(new T3(0,_Ip,_Il,_Im),_Ij,_Ix)),_Iy.a,_Iy.b);});}};if(_Ip>=_It){if(_Ip!=_It){return new F(function(){return _Hp(_Ij,_Ip,_Il,_Im,_Io);});}else{var _Iz=E(_Ir);if(_Il>=_Iz){if(_Il!=_Iz){return new F(function(){return _Hp(_Ij,_Ip,_Il,_Im,_Io);});}else{if(_Im<E(_Is)){return new F(function(){return _Iu(_);});}else{return new F(function(){return _Hp(_Ij,_Ip,_Il,_Im,_Io);});}}}else{return new F(function(){return _Iu(_);});}}}else{return new F(function(){return _Iu(_);});}}},_IA=function(_IB,_IC,_ID,_IE,_IF,_IG){var _IH=E(_IG);if(!_IH._){return new F(function(){return _CH(new T3(0,_ID,_IE,_IF),_IC);});}else{var _II=E(_ID),_IJ=E(_IH.a),_IK=_IJ.b,_IL=_IJ.c,_IM=E(_IJ.a),_IN=function(_IO){var _IP=B(_Fm(_IB,_IM,_IK,_IL,_IH.b)),_IQ=_IP.a,_IR=E(_IP.c);if(!_IR._){return new F(function(){return _HA(_IB<<1,B(_Dp(new T3(0,_II,_IE,_IF),_IC,_IQ)),_IP.b);});}else{return new F(function(){return _Hv(B(_Dp(new T3(0,_II,_IE,_IF),_IC,_IQ)),_IR.a,_IR.b);});}};if(_II>=_IM){if(_II!=_IM){return new F(function(){return _Hp(_IC,_II,_IE,_IF,_IH);});}else{var _IS=E(_IE),_IT=E(_IK);if(_IS>=_IT){if(_IS!=_IT){return new F(function(){return _Hp(_IC,_II,_IS,_IF,_IH);});}else{var _IU=E(_IF);if(_IU<E(_IL)){return new F(function(){return _IN(_);});}else{return new F(function(){return _Hp(_IC,_II,_IS,_IU,_IH);});}}}else{return new F(function(){return _IN(_);});}}}else{return new F(function(){return _IN(_);});}}},_IV=function(_IW){var _IX=E(_IW);if(!_IX._){return new T0(1);}else{var _IY=_IX.a,_IZ=E(_IX.b);if(!_IZ._){return new T4(0,1,E(_IY),E(_AT),E(_AT));}else{var _J0=_IZ.b,_J1=E(_IY),_J2=E(_J1.a),_J3=E(_IZ.a),_J4=_J3.b,_J5=_J3.c,_J6=E(_J3.a);if(_J2>=_J6){if(_J2!=_J6){return new F(function(){return _Hp(new T4(0,1,E(_J1),E(_AT),E(_AT)),_J6,_J4,_J5,_J0);});}else{var _J7=E(_J1.b),_J8=E(_J4);if(_J7>=_J8){if(_J7!=_J8){return new F(function(){return _Hp(new T4(0,1,E(_J1),E(_AT),E(_AT)),_J6,_J8,_J5,_J0);});}else{var _J9=E(_J5);if(E(_J1.c)<_J9){return new F(function(){return _Ih(1,new T4(0,1,E(_J1),E(_AT),E(_AT)),_J6,_J8,_J9,_J0);});}else{return new F(function(){return _Hp(new T4(0,1,E(_J1),E(_AT),E(_AT)),_J6,_J8,_J9,_J0);});}}}else{return new F(function(){return _HX(1,new T4(0,1,E(_J1),E(_AT),E(_AT)),_J6,_J8,_J5,_J0);});}}}else{return new F(function(){return _IA(1,new T4(0,1,E(_J1),E(_AT),E(_AT)),_J6,_J4,_J5,_J0);});}}}},_Ja=function(_Jb,_Jc){while(1){var _Jd=B((function(_Je,_Jf){var _Jg=E(_Jf);if(!_Jg._){_Jb=new T2(1,new T2(0,_Jg.b,_Jg.c),new T(function(){return B(_Ja(_Je,_Jg.e));}));_Jc=_Jg.d;return __continue;}else{return E(_Je);}})(_Jb,_Jc));if(_Jd!=__continue){return _Jd;}}},_Jh=function(_Ji,_Jj,_Jk){return new F(function(){return A1(_Ji,new T2(1,_I,new T(function(){return B(A1(_Jj,_Jk));})));});},_Jl=new T(function(){return B(unCStr("CC "));}),_Jm=new T(function(){return B(unCStr("IdentCC "));}),_Jn=function(_Jo,_Jp,_Jq){if(_Jo<11){return new F(function(){return _c(_Jm,new T(function(){return B(_6U(11,E(_Jp),_Jq));},1));});}else{var _Jr=new T(function(){return B(_c(_Jm,new T(function(){return B(_6U(11,E(_Jp),new T2(1,_6S,_Jq)));},1)));});return new T2(1,_6T,_Jr);}},_Js=32,_Jt=function(_Ju,_Jv,_Jw,_Jx,_Jy,_Jz){var _JA=function(_JB){var _JC=new T(function(){var _JD=new T(function(){return B(_6U(11,E(_Jx),new T2(1,_Js,new T(function(){return B(_6U(11,E(_Jy),_JB));}))));});return B(_6U(11,E(_Jw),new T2(1,_Js,_JD)));});return new F(function(){return _Jn(11,_Jv,new T2(1,_Js,_JC));});};if(_Ju<11){return new F(function(){return _c(_Jl,new T(function(){return B(_JA(_Jz));},1));});}else{var _JE=new T(function(){return B(_c(_Jl,new T(function(){return B(_JA(new T2(1,_6S,_Jz)));},1)));});return new T2(1,_6T,_JE);}},_JF=function(_JG,_JH){var _JI=E(_JG);return new F(function(){return _Jt(0,_JI.a,_JI.b,_JI.c,_JI.d,_JH);});},_JJ=new T(function(){return B(unCStr("RC "));}),_JK=function(_JL,_JM,_JN,_JO,_JP){var _JQ=function(_JR){var _JS=new T(function(){var _JT=new T(function(){return B(_6U(11,E(_JN),new T2(1,_Js,new T(function(){return B(_6U(11,E(_JO),_JR));}))));});return B(_Jn(11,_JM,new T2(1,_Js,_JT)));},1);return new F(function(){return _c(_JJ,_JS);});};if(_JL<11){return new F(function(){return _JQ(_JP);});}else{return new T2(1,_6T,new T(function(){return B(_JQ(new T2(1,_6S,_JP)));}));}},_JU=function(_JV,_JW){var _JX=E(_JV);return new F(function(){return _JK(0,_JX.a,_JX.b,_JX.c,_JW);});},_JY=new T(function(){return B(unCStr("IdentPay "));}),_JZ=function(_K0,_K1,_K2){if(_K0<11){return new F(function(){return _c(_JY,new T(function(){return B(_6U(11,E(_K1),_K2));},1));});}else{var _K3=new T(function(){return B(_c(_JY,new T(function(){return B(_6U(11,E(_K1),new T2(1,_6S,_K2)));},1)));});return new T2(1,_6T,_K3);}},_K4=new T(function(){return B(unCStr("foldr1"));}),_K5=new T(function(){return B(_kv(_K4));}),_K6=function(_K7,_K8){var _K9=E(_K8);if(!_K9._){return E(_K5);}else{var _Ka=_K9.a,_Kb=E(_K9.b);if(!_Kb._){return E(_Ka);}else{return new F(function(){return A2(_K7,_Ka,new T(function(){return B(_K6(_K7,_Kb));}));});}}},_Kc=function(_Kd,_Ke,_Kf){var _Kg=new T(function(){var _Kh=function(_Ki){var _Kj=E(_Kd),_Kk=new T(function(){return B(A3(_K6,_Jh,new T2(1,function(_Kl){return new F(function(){return _JZ(0,_Kj.a,_Kl);});},new T2(1,function(_Km){return new F(function(){return _6U(0,E(_Kj.b),_Km);});},_9)),new T2(1,_6S,_Ki)));});return new T2(1,_6T,_Kk);};return B(A3(_K6,_Jh,new T2(1,_Kh,new T2(1,function(_Kn){return new F(function(){return _6U(0,E(_Ke),_Kn);});},_9)),new T2(1,_6S,_Kf)));});return new T2(0,_6T,_Kg);},_Ko=function(_Kp,_Kq){var _Kr=E(_Kp),_Ks=B(_Kc(_Kr.a,_Kr.b,_Kq));return new T2(1,_Ks.a,_Ks.b);},_Kt=function(_Ku,_Kv){return new F(function(){return _L(_Ko,_Ku,_Kv);});},_Kw=new T(function(){return B(unCStr("IdentChoice "));}),_Kx=function(_Ky,_Kz,_KA){if(_Ky<11){return new F(function(){return _c(_Kw,new T(function(){return B(_6U(11,E(_Kz),_KA));},1));});}else{var _KB=new T(function(){return B(_c(_Kw,new T(function(){return B(_6U(11,E(_Kz),new T2(1,_6S,_KA)));},1)));});return new T2(1,_6T,_KB);}},_KC=function(_KD,_KE,_KF){var _KG=new T(function(){var _KH=function(_KI){var _KJ=E(_KD),_KK=new T(function(){return B(A3(_K6,_Jh,new T2(1,function(_KL){return new F(function(){return _Kx(0,_KJ.a,_KL);});},new T2(1,function(_KM){return new F(function(){return _6U(0,E(_KJ.b),_KM);});},_9)),new T2(1,_6S,_KI)));});return new T2(1,_6T,_KK);};return B(A3(_K6,_Jh,new T2(1,_KH,new T2(1,function(_KN){return new F(function(){return _6U(0,E(_KE),_KN);});},_9)),new T2(1,_6S,_KF)));});return new T2(0,_6T,_KG);},_KO=function(_KP,_KQ){var _KR=E(_KP),_KS=B(_KC(_KR.a,_KR.b,_KQ));return new T2(1,_KS.a,_KS.b);},_KT=function(_KU,_KV){return new F(function(){return _L(_KO,_KU,_KV);});},_KW=new T2(1,_6S,_9),_KX=function(_KY,_KZ){while(1){var _L0=B((function(_L1,_L2){var _L3=E(_L2);if(!_L3._){_KY=new T2(1,_L3.b,new T(function(){return B(_KX(_L1,_L3.d));}));_KZ=_L3.c;return __continue;}else{return E(_L1);}})(_KY,_KZ));if(_L0!=__continue){return _L0;}}},_L4=function(_L5,_L6,_L7,_L8){var _L9=new T(function(){var _La=new T(function(){return B(_Ja(_9,_L8));}),_Lb=new T(function(){return B(_Ja(_9,_L7));}),_Lc=new T(function(){return B(_KX(_9,_L6));}),_Ld=new T(function(){return B(_KX(_9,_L5));});return B(A3(_K6,_Jh,new T2(1,function(_Le){return new F(function(){return _L(_JF,_Ld,_Le);});},new T2(1,function(_Lf){return new F(function(){return _L(_JU,_Lc,_Lf);});},new T2(1,function(_Lg){return new F(function(){return _Kt(_Lb,_Lg);});},new T2(1,function(_Lh){return new F(function(){return _KT(_La,_Lh);});},_9)))),_KW));});return new T2(0,_6T,_L9);},_Li=new T(function(){return B(err(_kf));}),_Lj=new T(function(){return B(err(_a));}),_Lk=function(_Ll){return new F(function(){return _eF(_f8,_Ll);});},_Lm=new T(function(){return B(unCStr("["));}),_Ln=function(_Lo,_Lp){var _Lq=function(_Lr,_Ls){var _Lt=new T(function(){return B(A1(_Ls,_9));}),_Lu=new T(function(){var _Lv=function(_Lw){return new F(function(){return _Lq(_6E,function(_Lx){return new F(function(){return A1(_Ls,new T2(1,_Lw,_Lx));});});});};return B(A2(_Lo,_ea,_Lv));}),_Ly=new T(function(){return B(_dD(function(_Lz){var _LA=E(_Lz);if(_LA._==2){var _LB=E(_LA.a);if(!_LB._){return new T0(2);}else{var _LC=_LB.b;switch(E(_LB.a)){case 44:return (E(_LC)._==0)?(!E(_Lr))?new T0(2):E(_Lu):new T0(2);case 93:return (E(_LC)._==0)?E(_Lt):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_LD=function(_LE){return E(_Ly);};return new T1(1,function(_LF){return new F(function(){return A2(_ck,_LF,_LD);});});},_LG=function(_LH,_LI){return new F(function(){return _LJ(_LI);});},_LJ=function(_LK){var _LL=new T(function(){var _LM=new T(function(){var _LN=new T(function(){var _LO=function(_LP){return new F(function(){return _Lq(_6E,function(_LQ){return new F(function(){return A1(_LK,new T2(1,_LP,_LQ));});});});};return B(A2(_Lo,_ea,_LO));});return B(_1M(B(_Lq(_6D,_LK)),_LN));});return B(_dD(function(_LR){var _LS=E(_LR);return (_LS._==2)?(!B(_2s(_LS.a,_Lm)))?new T0(2):E(_LM):new T0(2);}));}),_LT=function(_LU){return E(_LL);};return new F(function(){return _1M(new T1(1,function(_LV){return new F(function(){return A2(_ck,_LV,_LT);});}),new T(function(){return new T1(1,B(_eb(_LG,_LK)));}));});};return new F(function(){return _LJ(_Lp);});},_LW=function(_LX,_LY){return new F(function(){return _Ln(_Lk,_LY);});},_LZ=new T(function(){return B(_Ln(_Lk,_2Z));}),_M0=function(_Ll){return new F(function(){return _1C(_LZ,_Ll);});},_M1=function(_M2){var _M3=new T(function(){return B(A3(_eF,_f8,_M2,_2Z));});return function(_M4){return new F(function(){return _1C(_M3,_M4);});};},_M5=new T4(0,_M1,_M0,_Lk,_LW),_M6=function(_M7){return new F(function(){return _eu(_fU,_M7);});},_M8=function(_M9,_Ma){return new F(function(){return _Ln(_M6,_Ma);});},_Mb=new T(function(){return B(_Ln(_M6,_2Z));}),_Mc=function(_M7){return new F(function(){return _1C(_Mb,_M7);});},_Md=function(_Me){var _Mf=new T(function(){return B(A3(_eu,_fU,_Me,_2Z));});return function(_M4){return new F(function(){return _1C(_Mf,_M4);});};},_Mg=new T4(0,_Md,_Mc,_M6,_M8),_Mh=new T(function(){return B(unCStr(","));}),_Mi=function(_Mj){return E(E(_Mj).c);},_Mk=function(_Ml,_Mm,_Mn){var _Mo=new T(function(){return B(_Mi(_Mm));}),_Mp=new T(function(){return B(A2(_Mi,_Ml,_Mn));}),_Mq=function(_Mr){var _Ms=function(_Mt){var _Mu=new T(function(){var _Mv=new T(function(){return B(A2(_Mo,_Mn,function(_Mw){return new F(function(){return A1(_Mr,new T2(0,_Mt,_Mw));});}));});return B(_dD(function(_Mx){var _My=E(_Mx);return (_My._==2)?(!B(_2s(_My.a,_Mh)))?new T0(2):E(_Mv):new T0(2);}));}),_Mz=function(_MA){return E(_Mu);};return new T1(1,function(_MB){return new F(function(){return A2(_ck,_MB,_Mz);});});};return new F(function(){return A1(_Mp,_Ms);});};return E(_Mq);},_MC=function(_MD,_ME,_MF){var _MG=function(_Ll){return new F(function(){return _Mk(_MD,_ME,_Ll);});},_MH=function(_MI,_MJ){return new F(function(){return _MK(_MJ);});},_MK=function(_ML){return new F(function(){return _1M(new T1(1,B(_eb(_MG,_ML))),new T(function(){return new T1(1,B(_eb(_MH,_ML)));}));});};return new F(function(){return _MK(_MF);});},_MM=function(_MN,_MO){return new F(function(){return _MC(_Mg,_M5,_MO);});},_MP=new T(function(){return B(_Ln(_MM,_2Z));}),_MQ=function(_M7){return new F(function(){return _1C(_MP,_M7);});},_MR=new T(function(){return B(_MC(_Mg,_M5,_2Z));}),_MS=function(_M7){return new F(function(){return _1C(_MR,_M7);});},_MT=function(_MU,_M7){return new F(function(){return _MS(_M7);});},_MV=function(_MW,_MX){return new F(function(){return _Ln(_MM,_MX);});},_MY=new T4(0,_MT,_MQ,_MM,_MV),_MZ=function(_N0,_N1){return new F(function(){return _MC(_MY,_M5,_N1);});},_N2=function(_N3,_N4){return new F(function(){return _Ln(_MZ,_N4);});},_N5=new T(function(){return B(_Ln(_N2,_2Z));}),_N6=function(_N7){return new F(function(){return _1C(_N5,_N7);});},_N8=function(_N9){return new F(function(){return _Ln(_N2,_N9);});},_Na=function(_Nb,_Nc){return new F(function(){return _N8(_Nc);});},_Nd=new T(function(){return B(_Ln(_MZ,_2Z));}),_Ne=function(_N7){return new F(function(){return _1C(_Nd,_N7);});},_Nf=function(_Ng,_N7){return new F(function(){return _Ne(_N7);});},_Nh=new T4(0,_Nf,_N6,_N2,_Na),_Ni=function(_M7){return new F(function(){return _eu(_fF,_M7);});},_Nj=function(_Nk,_Nl){return new F(function(){return _Ln(_Ni,_Nl);});},_Nm=new T(function(){return B(_Ln(_Ni,_2Z));}),_Nn=function(_M7){return new F(function(){return _1C(_Nm,_M7);});},_No=function(_Np){var _Nq=new T(function(){return B(A3(_eu,_fF,_Np,_2Z));});return function(_M4){return new F(function(){return _1C(_Nq,_M4);});};},_Nr=new T4(0,_No,_Nn,_Ni,_Nj),_Ns=function(_Nt,_Nu){return new F(function(){return _MC(_Nr,_M5,_Nu);});},_Nv=new T(function(){return B(_Ln(_Ns,_2Z));}),_Nw=function(_M7){return new F(function(){return _1C(_Nv,_M7);});},_Nx=new T(function(){return B(_MC(_Nr,_M5,_2Z));}),_Ny=function(_M7){return new F(function(){return _1C(_Nx,_M7);});},_Nz=function(_NA,_M7){return new F(function(){return _Ny(_M7);});},_NB=function(_NC,_ND){return new F(function(){return _Ln(_Ns,_ND);});},_NE=new T4(0,_Nz,_Nw,_Ns,_NB),_NF=function(_NG,_NH){return new F(function(){return _MC(_NE,_M5,_NH);});},_NI=function(_NJ,_NK){return new F(function(){return _Ln(_NF,_NK);});},_NL=new T(function(){return B(_Ln(_NI,_2Z));}),_NM=function(_N7){return new F(function(){return _1C(_NL,_N7);});},_NN=function(_NO){return new F(function(){return _Ln(_NI,_NO);});},_NP=function(_NQ,_NR){return new F(function(){return _NN(_NR);});},_NS=new T(function(){return B(_Ln(_NF,_2Z));}),_NT=function(_N7){return new F(function(){return _1C(_NS,_N7);});},_NU=function(_NV,_N7){return new F(function(){return _NT(_N7);});},_NW=new T4(0,_NU,_NM,_NI,_NP),_NX=new T(function(){return B(unCStr("RC"));}),_NY=function(_NZ,_O0){if(_NZ>10){return new T0(2);}else{var _O1=new T(function(){var _O2=new T(function(){var _O3=function(_O4){var _O5=function(_O6){return new F(function(){return A3(_eF,_f8,_2o,function(_O7){return new F(function(){return A1(_O0,new T3(0,_O4,_O6,_O7));});});});};return new F(function(){return A3(_eF,_f8,_2o,_O5);});};return B(A3(_eu,_fq,_2o,_O3));});return B(_dD(function(_O8){var _O9=E(_O8);return (_O9._==3)?(!B(_2s(_O9.a,_NX)))?new T0(2):E(_O2):new T0(2);}));}),_Oa=function(_Ob){return E(_O1);};return new T1(1,function(_Oc){return new F(function(){return A2(_ck,_Oc,_Oa);});});}},_Od=function(_Oe,_Of){return new F(function(){return _NY(E(_Oe),_Of);});},_Og=function(_M7){return new F(function(){return _eu(_Od,_M7);});},_Oh=function(_Oi,_Oj){return new F(function(){return _Ln(_Og,_Oj);});},_Ok=new T(function(){return B(_Ln(_Oh,_2Z));}),_Ol=function(_N7){return new F(function(){return _1C(_Ok,_N7);});},_Om=new T(function(){return B(_Ln(_Og,_2Z));}),_On=function(_N7){return new F(function(){return _1C(_Om,_N7);});},_Oo=function(_Op,_N7){return new F(function(){return _On(_N7);});},_Oq=function(_Or,_Os){return new F(function(){return _Ln(_Oh,_Os);});},_Ot=new T4(0,_Oo,_Ol,_Oh,_Oq),_Ou=new T(function(){return B(unCStr("CC"));}),_Ov=function(_Ow,_Ox){if(_Ow>10){return new T0(2);}else{var _Oy=new T(function(){var _Oz=new T(function(){var _OA=function(_OB){var _OC=function(_OD){var _OE=function(_OF){return new F(function(){return A3(_eF,_f8,_2o,function(_OG){return new F(function(){return A1(_Ox,new T4(0,_OB,_OD,_OF,_OG));});});});};return new F(function(){return A3(_eF,_f8,_2o,_OE);});};return new F(function(){return A3(_eF,_f8,_2o,_OC);});};return B(A3(_eu,_fq,_2o,_OA));});return B(_dD(function(_OH){var _OI=E(_OH);return (_OI._==3)?(!B(_2s(_OI.a,_Ou)))?new T0(2):E(_Oz):new T0(2);}));}),_OJ=function(_OK){return E(_Oy);};return new T1(1,function(_OL){return new F(function(){return A2(_ck,_OL,_OJ);});});}},_OM=function(_ON,_OO){return new F(function(){return _Ov(E(_ON),_OO);});},_OP=function(_M7){return new F(function(){return _eu(_OM,_M7);});},_OQ=function(_OR,_OS){return new F(function(){return _Ln(_OP,_OS);});},_OT=new T(function(){return B(_Ln(_OQ,_2Z));}),_OU=function(_N7){return new F(function(){return _1C(_OT,_N7);});},_OV=new T(function(){return B(_Ln(_OP,_2Z));}),_OW=function(_N7){return new F(function(){return _1C(_OV,_N7);});},_OX=function(_OY,_N7){return new F(function(){return _OW(_N7);});},_OZ=function(_P0,_P1){return new F(function(){return _Ln(_OQ,_P1);});},_P2=new T4(0,_OX,_OU,_OQ,_OZ),_P3=function(_P4,_P5,_P6,_P7,_P8){var _P9=new T(function(){return B(_Mk(_P4,_P5,_P8));}),_Pa=new T(function(){return B(_Mi(_P7));}),_Pb=function(_Pc){var _Pd=function(_Pe){var _Pf=E(_Pe),_Pg=new T(function(){var _Ph=new T(function(){var _Pi=function(_Pj){var _Pk=new T(function(){var _Pl=new T(function(){return B(A2(_Pa,_P8,function(_Pm){return new F(function(){return A1(_Pc,new T4(0,_Pf.a,_Pf.b,_Pj,_Pm));});}));});return B(_dD(function(_Pn){var _Po=E(_Pn);return (_Po._==2)?(!B(_2s(_Po.a,_Mh)))?new T0(2):E(_Pl):new T0(2);}));}),_Pp=function(_Pq){return E(_Pk);};return new T1(1,function(_Pr){return new F(function(){return A2(_ck,_Pr,_Pp);});});};return B(A3(_Mi,_P6,_P8,_Pi));});return B(_dD(function(_Ps){var _Pt=E(_Ps);return (_Pt._==2)?(!B(_2s(_Pt.a,_Mh)))?new T0(2):E(_Ph):new T0(2);}));}),_Pu=function(_Pv){return E(_Pg);};return new T1(1,function(_Pw){return new F(function(){return A2(_ck,_Pw,_Pu);});});};return new F(function(){return A1(_P9,_Pd);});};return E(_Pb);},_Px=function(_Py,_Pz,_PA,_PB,_PC){var _PD=function(_Ll){return new F(function(){return _P3(_Py,_Pz,_PA,_PB,_Ll);});},_PE=function(_PF,_PG){return new F(function(){return _PH(_PG);});},_PH=function(_PI){return new F(function(){return _1M(new T1(1,B(_eb(_PD,_PI))),new T(function(){return new T1(1,B(_eb(_PE,_PI)));}));});};return new F(function(){return _PH(_PC);});},_PJ=new T(function(){return B(_Px(_P2,_Ot,_NW,_Nh,_k9));}),_PK=new T(function(){return B(unCStr("contractInput"));}),_PL=function(_PM,_PN,_PO,_){var _PP=E(_PK),_PQ=eval(E(_mE)),_PR=__app1(E(_PQ),toJSStr(_PP)),_PS=B(_mo(B(_1C(_PJ,new T(function(){var _PT=String(_PR);return fromJSStr(_PT);})))));if(!_PS._){return E(_Lj);}else{if(!E(_PS.b)._){var _PU=E(_PS.a),_PV=B(_L4(new T(function(){return B(_Ey(_PU.a));},1),new T(function(){return B(_IV(_PU.b));},1),new T(function(){return B(_AD(_PU.c));},1),new T(function(){return B(_vZ(_PO,_PM,_PN,B(_xt(_PU.d))));},1)));return new F(function(){return _4(_PP,new T2(1,_PV.a,_PV.b),_);});}else{return E(_Li);}}},_PW=function(_PX,_PY,_PZ,_){var _Q0=E(_PK),_Q1=eval(E(_mE)),_Q2=__app1(E(_Q1),toJSStr(_Q0)),_Q3=B(_mo(B(_1C(_PJ,new T(function(){var _Q4=String(_Q2);return fromJSStr(_Q4);})))));if(!_Q3._){return E(_Lj);}else{if(!E(_Q3.b)._){var _Q5=E(_Q3.a),_Q6=B(_L4(new T(function(){return B(_Ey(_Q5.a));},1),new T(function(){return B(_IV(_Q5.b));},1),new T(function(){return B(_z9(_PZ,_PX,_PY,B(_AD(_Q5.c))));},1),new T(function(){return B(_xt(_Q5.d));},1)));return new F(function(){return _4(_Q0,new T2(1,_Q6.a,_Q6.b),_);});}else{return E(_Li);}}},_Q7=new T(function(){return B(unCStr("contractOutput"));}),_Q8=new T(function(){return B(unCStr("([], [], [], [])"));}),_Q9=new T(function(){return B(unCStr("([], [])"));}),_Qa=new T(function(){return B(unCStr("contractState"));}),_Qb=new T(function(){return B(_6U(0,0,_9));}),_Qc=new T(function(){return B(unCStr("currBlock"));}),_Qd=function(_){var _Qe=__app0(E(_rP)),_Qf=B(_4(_1,_9,_)),_Qg=B(_4(_Qc,_Qb,_)),_Qh=B(_4(_Qa,_Q9,_)),_Qi=B(_4(_PK,_Q8,_));return new F(function(){return _4(_Q7,_9,_);});},_Qj=function(_Qk,_Ql,_Qm,_Qn,_){var _Qo=E(_PK),_Qp=eval(E(_mE)),_Qq=__app1(E(_Qp),toJSStr(_Qo)),_Qr=B(_mo(B(_1C(_PJ,new T(function(){var _Qs=String(_Qq);return fromJSStr(_Qs);})))));if(!_Qr._){return E(_Lj);}else{if(!E(_Qr.b)._){var _Qt=E(_Qr.a),_Qu=B(_L4(new T(function(){return B(_Ca(_Qm,_Qk,_Ql,_Qn,B(_Ey(_Qt.a))));},1),new T(function(){return B(_IV(_Qt.b));},1),new T(function(){return B(_AD(_Qt.c));},1),new T(function(){return B(_xt(_Qt.d));},1)));return new F(function(){return _4(_Qo,new T2(1,_Qu.a,_Qu.b),_);});}else{return E(_Li);}}},_Qv=new T(function(){return B(unCStr("ConstMoney "));}),_Qw=new T(function(){return B(unCStr("AddMoney "));}),_Qx=new T(function(){return B(unCStr("AvailableMoney "));}),_Qy=function(_Qz,_QA,_QB){var _QC=E(_QA);switch(_QC._){case 0:var _QD=_QC.a;if(_Qz<11){return new F(function(){return _c(_Qx,new T(function(){return B(_Jn(11,_QD,_QB));},1));});}else{var _QE=new T(function(){return B(_c(_Qx,new T(function(){return B(_Jn(11,_QD,new T2(1,_6S,_QB)));},1)));});return new T2(1,_6T,_QE);}break;case 1:var _QF=function(_QG){var _QH=new T(function(){return B(_Qy(11,_QC.a,new T2(1,_Js,new T(function(){return B(_Qy(11,_QC.b,_QG));}))));},1);return new F(function(){return _c(_Qw,_QH);});};if(_Qz<11){return new F(function(){return _QF(_QB);});}else{return new T2(1,_6T,new T(function(){return B(_QF(new T2(1,_6S,_QB)));}));}break;default:var _QI=_QC.a;if(_Qz<11){return new F(function(){return _c(_Qv,new T(function(){return B(_6U(11,E(_QI),_QB));},1));});}else{var _QJ=new T(function(){return B(_c(_Qv,new T(function(){return B(_6U(11,E(_QI),new T2(1,_6S,_QB)));},1)));});return new T2(1,_6T,_QJ);}}},_QK=new T(function(){return B(unCStr("ValueGE "));}),_QL=new T(function(){return B(unCStr("PersonChoseSomething "));}),_QM=new T(function(){return B(unCStr("PersonChoseThis "));}),_QN=new T(function(){return B(unCStr("NotObs "));}),_QO=new T(function(){return B(unCStr("OrObs "));}),_QP=new T(function(){return B(unCStr("AndObs "));}),_QQ=new T(function(){return B(unCStr("BelowTimeout "));}),_QR=function(_QS,_QT,_QU){var _QV=E(_QT);switch(_QV._){case 0:var _QW=_QV.a;if(_QS<11){return new F(function(){return _c(_QQ,new T(function(){return B(_6U(11,E(_QW),_QU));},1));});}else{var _QX=new T(function(){return B(_c(_QQ,new T(function(){return B(_6U(11,E(_QW),new T2(1,_6S,_QU)));},1)));});return new T2(1,_6T,_QX);}break;case 1:var _QY=function(_QZ){var _R0=new T(function(){return B(_QR(11,_QV.a,new T2(1,_Js,new T(function(){return B(_QR(11,_QV.b,_QZ));}))));},1);return new F(function(){return _c(_QP,_R0);});};if(_QS<11){return new F(function(){return _QY(_QU);});}else{return new T2(1,_6T,new T(function(){return B(_QY(new T2(1,_6S,_QU)));}));}break;case 2:var _R1=function(_R2){var _R3=new T(function(){return B(_QR(11,_QV.a,new T2(1,_Js,new T(function(){return B(_QR(11,_QV.b,_R2));}))));},1);return new F(function(){return _c(_QO,_R3);});};if(_QS<11){return new F(function(){return _R1(_QU);});}else{return new T2(1,_6T,new T(function(){return B(_R1(new T2(1,_6S,_QU)));}));}break;case 3:var _R4=_QV.a;if(_QS<11){return new F(function(){return _c(_QN,new T(function(){return B(_QR(11,_R4,_QU));},1));});}else{var _R5=new T(function(){return B(_c(_QN,new T(function(){return B(_QR(11,_R4,new T2(1,_6S,_QU)));},1)));});return new T2(1,_6T,_R5);}break;case 4:var _R6=function(_R7){var _R8=new T(function(){var _R9=new T(function(){return B(_6U(11,E(_QV.b),new T2(1,_Js,new T(function(){return B(_6U(11,E(_QV.c),_R7));}))));});return B(_Kx(11,_QV.a,new T2(1,_Js,_R9)));},1);return new F(function(){return _c(_QM,_R8);});};if(_QS<11){return new F(function(){return _R6(_QU);});}else{return new T2(1,_6T,new T(function(){return B(_R6(new T2(1,_6S,_QU)));}));}break;case 5:var _Ra=function(_Rb){return new F(function(){return _Kx(11,_QV.a,new T2(1,_Js,new T(function(){return B(_6U(11,E(_QV.b),_Rb));})));});};if(_QS<11){return new F(function(){return _c(_QL,new T(function(){return B(_Ra(_QU));},1));});}else{var _Rc=new T(function(){return B(_c(_QL,new T(function(){return B(_Ra(new T2(1,_6S,_QU)));},1)));});return new T2(1,_6T,_Rc);}break;case 6:var _Rd=function(_Re){return new F(function(){return _Qy(11,_QV.a,new T2(1,_Js,new T(function(){return B(_Qy(11,_QV.b,_Re));})));});};if(_QS<11){return new F(function(){return _c(_QK,new T(function(){return B(_Rd(_QU));},1));});}else{var _Rf=new T(function(){return B(_c(_QK,new T(function(){return B(_Rd(new T2(1,_6S,_QU)));},1)));});return new T2(1,_6T,_Rf);}break;case 7:return new F(function(){return _c(_gC,_QU);});break;default:return new F(function(){return _c(_gI,_QU);});}},_Rg=new T(function(){return B(unCStr("When "));}),_Rh=new T(function(){return B(unCStr("Choice "));}),_Ri=new T(function(){return B(unCStr("Both "));}),_Rj=new T(function(){return B(unCStr("Pay "));}),_Rk=new T(function(){return B(unCStr("RedeemCC "));}),_Rl=new T(function(){return B(unCStr("CommitCash "));}),_Rm=function(_Rn,_Ro,_Rp){var _Rq=E(_Ro);switch(_Rq._){case 0:return new F(function(){return _c(_ip,_Rp);});break;case 1:var _Rr=function(_Rs){var _Rt=new T(function(){var _Ru=new T(function(){var _Rv=new T(function(){var _Rw=new T(function(){var _Rx=new T(function(){return B(_Rm(_2o,_Rq.f,new T2(1,_Js,new T(function(){return B(_Rm(_2o,_Rq.g,_Rs));}))));});return B(_6U(11,E(_Rq.e),new T2(1,_Js,_Rx)));});return B(_6U(11,E(_Rq.d),new T2(1,_Js,_Rw)));});return B(_6U(11,E(_Rq.c),new T2(1,_Js,_Rv)));});return B(_6U(11,E(_Rq.b),new T2(1,_Js,_Ru)));});return new F(function(){return _Jn(11,_Rq.a,new T2(1,_Js,_Rt));});};if(E(_Rn)<11){return new F(function(){return _c(_Rl,new T(function(){return B(_Rr(_Rp));},1));});}else{var _Ry=new T(function(){return B(_c(_Rl,new T(function(){return B(_Rr(new T2(1,_6S,_Rp)));},1)));});return new T2(1,_6T,_Ry);}break;case 2:var _Rz=function(_RA){var _RB=new T(function(){return B(_Jn(11,_Rq.a,new T2(1,_Js,new T(function(){return B(_Rm(_2o,_Rq.b,_RA));}))));},1);return new F(function(){return _c(_Rk,_RB);});};if(E(_Rn)<11){return new F(function(){return _Rz(_Rp);});}else{return new T2(1,_6T,new T(function(){return B(_Rz(new T2(1,_6S,_Rp)));}));}break;case 3:var _RC=function(_RD){var _RE=new T(function(){var _RF=new T(function(){var _RG=new T(function(){var _RH=new T(function(){var _RI=new T(function(){return B(_6U(11,E(_Rq.e),new T2(1,_Js,new T(function(){return B(_Rm(_2o,_Rq.f,_RD));}))));});return B(_6U(11,E(_Rq.d),new T2(1,_Js,_RI)));});return B(_6U(11,E(_Rq.c),new T2(1,_Js,_RH)));});return B(_6U(11,E(_Rq.b),new T2(1,_Js,_RG)));});return B(_JZ(11,_Rq.a,new T2(1,_Js,_RF)));},1);return new F(function(){return _c(_Rj,_RE);});};if(E(_Rn)<11){return new F(function(){return _RC(_Rp);});}else{return new T2(1,_6T,new T(function(){return B(_RC(new T2(1,_6S,_Rp)));}));}break;case 4:var _RJ=function(_RK){var _RL=new T(function(){return B(_Rm(_2o,_Rq.a,new T2(1,_Js,new T(function(){return B(_Rm(_2o,_Rq.b,_RK));}))));},1);return new F(function(){return _c(_Ri,_RL);});};if(E(_Rn)<11){return new F(function(){return _RJ(_Rp);});}else{return new T2(1,_6T,new T(function(){return B(_RJ(new T2(1,_6S,_Rp)));}));}break;case 5:var _RM=function(_RN){var _RO=new T(function(){return B(_Rm(_2o,_Rq.b,new T2(1,_Js,new T(function(){return B(_Rm(_2o,_Rq.c,_RN));}))));});return new F(function(){return _QR(11,_Rq.a,new T2(1,_Js,_RO));});};if(E(_Rn)<11){return new F(function(){return _c(_Rh,new T(function(){return B(_RM(_Rp));},1));});}else{var _RP=new T(function(){return B(_c(_Rh,new T(function(){return B(_RM(new T2(1,_6S,_Rp)));},1)));});return new T2(1,_6T,_RP);}break;default:var _RQ=function(_RR){var _RS=new T(function(){var _RT=new T(function(){var _RU=new T(function(){return B(_Rm(_2o,_Rq.c,new T2(1,_Js,new T(function(){return B(_Rm(_2o,_Rq.d,_RR));}))));});return B(_6U(11,E(_Rq.b),new T2(1,_Js,_RU)));});return B(_QR(11,_Rq.a,new T2(1,_Js,_RT)));},1);return new F(function(){return _c(_Rg,_RS);});};if(E(_Rn)<11){return new F(function(){return _RQ(_Rp);});}else{return new T2(1,_6T,new T(function(){return B(_RQ(new T2(1,_6S,_Rp)));}));}}},_RV=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_RW=new T(function(){return B(unCStr("NotRedeemed "));}),_RX=function(_RY,_RZ,_S0){var _S1=E(_RZ);if(!_S1._){var _S2=function(_S3){return new F(function(){return _6U(11,E(_S1.a),new T2(1,_Js,new T(function(){return B(_6U(11,E(_S1.b),_S3));})));});};if(E(_RY)<11){return new F(function(){return _c(_RW,new T(function(){return B(_S2(_S0));},1));});}else{var _S4=new T(function(){return B(_c(_RW,new T(function(){return B(_S2(new T2(1,_6S,_S0)));},1)));});return new T2(1,_6T,_S4);}}else{return new F(function(){return _c(_RV,_S0);});}},_S5=0,_S6=function(_S7,_S8,_S9){var _Sa=new T(function(){var _Sb=function(_Sc){var _Sd=E(_S8),_Se=new T(function(){return B(A3(_K6,_Jh,new T2(1,function(_Sf){return new F(function(){return _6U(0,E(_Sd.a),_Sf);});},new T2(1,function(_N7){return new F(function(){return _RX(_S5,_Sd.b,_N7);});},_9)),new T2(1,_6S,_Sc)));});return new T2(1,_6T,_Se);};return B(A3(_K6,_Jh,new T2(1,function(_Sg){return new F(function(){return _Jn(0,_S7,_Sg);});},new T2(1,_Sb,_9)),new T2(1,_6S,_S9)));});return new T2(0,_6T,_Sa);},_Sh=function(_Si,_Sj){var _Sk=E(_Si),_Sl=B(_S6(_Sk.a,_Sk.b,_Sj));return new T2(1,_Sl.a,_Sl.b);},_Sm=function(_Sn,_So){return new F(function(){return _L(_Sh,_Sn,_So);});},_Sp=function(_Sq,_Sr,_Ss,_St){var _Su=E(_Sq);if(_Su==1){var _Sv=E(_St);if(!_Sv._){return new T3(0,new T(function(){var _Sw=E(_Sr);return new T5(0,1,E(_Sw),_Ss,E(_s2),E(_s2));}),_9,_9);}else{var _Sx=E(_Sr);return (_Sx<E(E(_Sv.a).a))?new T3(0,new T5(0,1,E(_Sx),_Ss,E(_s2),E(_s2)),_Sv,_9):new T3(0,new T5(0,1,E(_Sx),_Ss,E(_s2),E(_s2)),_9,_Sv);}}else{var _Sy=B(_Sp(_Su>>1,_Sr,_Ss,_St)),_Sz=_Sy.a,_SA=_Sy.c,_SB=E(_Sy.b);if(!_SB._){return new T3(0,_Sz,_9,_SA);}else{var _SC=E(_SB.a),_SD=_SC.a,_SE=_SC.b,_SF=E(_SB.b);if(!_SF._){return new T3(0,new T(function(){return B(_sP(_SD,_SE,_Sz));}),_9,_SA);}else{var _SG=E(_SF.a),_SH=E(_SD),_SI=E(_SG.a);if(_SH<_SI){var _SJ=B(_Sp(_Su>>1,_SI,_SG.b,_SF.b));return new T3(0,new T(function(){return B(_ui(_SH,_SE,_Sz,_SJ.a));}),_SJ.b,_SJ.c);}else{return new T3(0,_Sz,_9,_SB);}}}}},_SK=function(_SL,_SM,_SN){var _SO=E(_SN);if(!_SO._){var _SP=_SO.c,_SQ=_SO.d,_SR=_SO.e,_SS=E(_SO.b);if(_SL>=_SS){if(_SL!=_SS){return new F(function(){return _s7(_SS,_SP,_SQ,B(_SK(_SL,_SM,_SR)));});}else{return new T5(0,_SO.a,E(_SL),_SM,E(_SQ),E(_SR));}}else{return new F(function(){return _sY(_SS,_SP,B(_SK(_SL,_SM,_SQ)),_SR);});}}else{return new T5(0,1,E(_SL),_SM,E(_s2),E(_s2));}},_ST=function(_SU,_SV){while(1){var _SW=E(_SV);if(!_SW._){return E(_SU);}else{var _SX=E(_SW.a),_SY=B(_SK(E(_SX.a),_SX.b,_SU));_SU=_SY;_SV=_SW.b;continue;}}},_SZ=function(_T0,_T1,_T2,_T3){return new F(function(){return _ST(B(_SK(E(_T1),_T2,_T0)),_T3);});},_T4=function(_T5,_T6,_T7){var _T8=E(_T6);return new F(function(){return _ST(B(_SK(E(_T8.a),_T8.b,_T5)),_T7);});},_T9=function(_Ta,_Tb,_Tc){while(1){var _Td=E(_Tc);if(!_Td._){return E(_Tb);}else{var _Te=E(_Td.a),_Tf=_Te.a,_Tg=_Te.b,_Th=E(_Td.b);if(!_Th._){return new F(function(){return _sP(_Tf,_Tg,_Tb);});}else{var _Ti=E(_Th.a),_Tj=E(_Tf),_Tk=E(_Ti.a);if(_Tj<_Tk){var _Tl=B(_Sp(_Ta,_Tk,_Ti.b,_Th.b)),_Tm=_Tl.a,_Tn=E(_Tl.c);if(!_Tn._){var _To=_Ta<<1,_Tp=B(_ui(_Tj,_Tg,_Tb,_Tm));_Ta=_To;_Tb=_Tp;_Tc=_Tl.b;continue;}else{return new F(function(){return _T4(B(_ui(_Tj,_Tg,_Tb,_Tm)),_Tn.a,_Tn.b);});}}else{return new F(function(){return _SZ(_Tb,_Tj,_Tg,_Th);});}}}}},_Tq=function(_Tr,_Ts,_Tt,_Tu,_Tv){var _Tw=E(_Tv);if(!_Tw._){return new F(function(){return _sP(_Tt,_Tu,_Ts);});}else{var _Tx=E(_Tw.a),_Ty=E(_Tt),_Tz=E(_Tx.a);if(_Ty<_Tz){var _TA=B(_Sp(_Tr,_Tz,_Tx.b,_Tw.b)),_TB=_TA.a,_TC=E(_TA.c);if(!_TC._){return new F(function(){return _T9(_Tr<<1,B(_ui(_Ty,_Tu,_Ts,_TB)),_TA.b);});}else{return new F(function(){return _T4(B(_ui(_Ty,_Tu,_Ts,_TB)),_TC.a,_TC.b);});}}else{return new F(function(){return _SZ(_Ts,_Ty,_Tu,_Tw);});}}},_TD=function(_TE){var _TF=E(_TE);if(!_TF._){return new T0(1);}else{var _TG=E(_TF.a),_TH=_TG.a,_TI=_TG.b,_TJ=E(_TF.b);if(!_TJ._){var _TK=E(_TH);return new T5(0,1,E(_TK),_TI,E(_s2),E(_s2));}else{var _TL=_TJ.b,_TM=E(_TJ.a),_TN=_TM.b,_TO=E(_TH),_TP=E(_TM.a);if(_TO<_TP){return new F(function(){return _Tq(1,new T5(0,1,E(_TO),_TI,E(_s2),E(_s2)),_TP,_TN,_TL);});}else{return new F(function(){return _SZ(new T5(0,1,E(_TO),_TI,E(_s2),E(_s2)),_TP,_TN,_TL);});}}}},_TQ=new T(function(){return B(unCStr("ChoiceMade "));}),_TR=new T(function(){return B(unCStr("DuplicateRedeem "));}),_TS=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_TT=new T(function(){return B(unCStr("CommitRedeemed "));}),_TU=new T(function(){return B(unCStr("SuccessfulCommit "));}),_TV=new T(function(){return B(unCStr("FailedPay "));}),_TW=new T(function(){return B(unCStr("ExpiredPay "));}),_TX=new T(function(){return B(unCStr("SuccessfulPay "));}),_TY=function(_TZ,_U0,_U1){var _U2=E(_U0);switch(_U2._){case 0:var _U3=function(_U4){var _U5=new T(function(){var _U6=new T(function(){return B(_6U(11,E(_U2.c),new T2(1,_Js,new T(function(){return B(_6U(11,E(_U2.d),_U4));}))));});return B(_6U(11,E(_U2.b),new T2(1,_Js,_U6)));});return new F(function(){return _JZ(11,_U2.a,new T2(1,_Js,_U5));});};if(_TZ<11){return new F(function(){return _c(_TX,new T(function(){return B(_U3(_U1));},1));});}else{var _U7=new T(function(){return B(_c(_TX,new T(function(){return B(_U3(new T2(1,_6S,_U1)));},1)));});return new T2(1,_6T,_U7);}break;case 1:var _U8=function(_U9){var _Ua=new T(function(){var _Ub=new T(function(){return B(_6U(11,E(_U2.c),new T2(1,_Js,new T(function(){return B(_6U(11,E(_U2.d),_U9));}))));});return B(_6U(11,E(_U2.b),new T2(1,_Js,_Ub)));});return new F(function(){return _JZ(11,_U2.a,new T2(1,_Js,_Ua));});};if(_TZ<11){return new F(function(){return _c(_TW,new T(function(){return B(_U8(_U1));},1));});}else{var _Uc=new T(function(){return B(_c(_TW,new T(function(){return B(_U8(new T2(1,_6S,_U1)));},1)));});return new T2(1,_6T,_Uc);}break;case 2:var _Ud=function(_Ue){var _Uf=new T(function(){var _Ug=new T(function(){return B(_6U(11,E(_U2.c),new T2(1,_Js,new T(function(){return B(_6U(11,E(_U2.d),_Ue));}))));});return B(_6U(11,E(_U2.b),new T2(1,_Js,_Ug)));});return new F(function(){return _JZ(11,_U2.a,new T2(1,_Js,_Uf));});};if(_TZ<11){return new F(function(){return _c(_TV,new T(function(){return B(_Ud(_U1));},1));});}else{var _Uh=new T(function(){return B(_c(_TV,new T(function(){return B(_Ud(new T2(1,_6S,_U1)));},1)));});return new T2(1,_6T,_Uh);}break;case 3:var _Ui=function(_Uj){var _Uk=new T(function(){var _Ul=new T(function(){return B(_6U(11,E(_U2.b),new T2(1,_Js,new T(function(){return B(_6U(11,E(_U2.c),_Uj));}))));});return B(_Jn(11,_U2.a,new T2(1,_Js,_Ul)));},1);return new F(function(){return _c(_TU,_Uk);});};if(_TZ<11){return new F(function(){return _Ui(_U1);});}else{return new T2(1,_6T,new T(function(){return B(_Ui(new T2(1,_6S,_U1)));}));}break;case 4:var _Um=function(_Un){var _Uo=new T(function(){var _Up=new T(function(){return B(_6U(11,E(_U2.b),new T2(1,_Js,new T(function(){return B(_6U(11,E(_U2.c),_Un));}))));});return B(_Jn(11,_U2.a,new T2(1,_Js,_Up)));},1);return new F(function(){return _c(_TT,_Uo);});};if(_TZ<11){return new F(function(){return _Um(_U1);});}else{return new T2(1,_6T,new T(function(){return B(_Um(new T2(1,_6S,_U1)));}));}break;case 5:var _Uq=function(_Ur){var _Us=new T(function(){var _Ut=new T(function(){return B(_6U(11,E(_U2.b),new T2(1,_Js,new T(function(){return B(_6U(11,E(_U2.c),_Ur));}))));});return B(_Jn(11,_U2.a,new T2(1,_Js,_Ut)));},1);return new F(function(){return _c(_TS,_Us);});};if(_TZ<11){return new F(function(){return _Uq(_U1);});}else{return new T2(1,_6T,new T(function(){return B(_Uq(new T2(1,_6S,_U1)));}));}break;case 6:var _Uu=function(_Uv){return new F(function(){return _Jn(11,_U2.a,new T2(1,_Js,new T(function(){return B(_6U(11,E(_U2.b),_Uv));})));});};if(_TZ<11){return new F(function(){return _c(_TR,new T(function(){return B(_Uu(_U1));},1));});}else{var _Uw=new T(function(){return B(_c(_TR,new T(function(){return B(_Uu(new T2(1,_6S,_U1)));},1)));});return new T2(1,_6T,_Uw);}break;default:var _Ux=function(_Uy){var _Uz=new T(function(){var _UA=new T(function(){return B(_6U(11,E(_U2.b),new T2(1,_Js,new T(function(){return B(_6U(11,E(_U2.c),_Uy));}))));});return B(_Kx(11,_U2.a,new T2(1,_Js,_UA)));},1);return new F(function(){return _c(_TQ,_Uz);});};if(_TZ<11){return new F(function(){return _Ux(_U1);});}else{return new T2(1,_6T,new T(function(){return B(_Ux(new T2(1,_6S,_U1)));}));}}},_UB=function(_UC,_UD){return E(_UC)==E(_UD);},_UE=function(_UF,_UG){var _UH=E(_UF);switch(_UH._){case 0:var _UI=E(_UG);if(!_UI._){if(E(_UH.a)!=E(_UI.a)){return false;}else{if(E(_UH.b)!=E(_UI.b)){return false;}else{if(E(_UH.c)!=E(_UI.c)){return false;}else{return new F(function(){return _UB(_UH.d,_UI.d);});}}}}else{return false;}break;case 1:var _UJ=E(_UG);if(_UJ._==1){if(E(_UH.a)!=E(_UJ.a)){return false;}else{if(E(_UH.b)!=E(_UJ.b)){return false;}else{if(E(_UH.c)!=E(_UJ.c)){return false;}else{return new F(function(){return _UB(_UH.d,_UJ.d);});}}}}else{return false;}break;case 2:var _UK=E(_UG);if(_UK._==2){if(E(_UH.a)!=E(_UK.a)){return false;}else{if(E(_UH.b)!=E(_UK.b)){return false;}else{if(E(_UH.c)!=E(_UK.c)){return false;}else{return new F(function(){return _UB(_UH.d,_UK.d);});}}}}else{return false;}break;case 3:var _UL=E(_UG);if(_UL._==3){if(E(_UH.a)!=E(_UL.a)){return false;}else{if(E(_UH.b)!=E(_UL.b)){return false;}else{return new F(function(){return _UB(_UH.c,_UL.c);});}}}else{return false;}break;case 4:var _UM=E(_UG);if(_UM._==4){if(E(_UH.a)!=E(_UM.a)){return false;}else{if(E(_UH.b)!=E(_UM.b)){return false;}else{return new F(function(){return _UB(_UH.c,_UM.c);});}}}else{return false;}break;case 5:var _UN=E(_UG);if(_UN._==5){if(E(_UH.a)!=E(_UN.a)){return false;}else{if(E(_UH.b)!=E(_UN.b)){return false;}else{return new F(function(){return _UB(_UH.c,_UN.c);});}}}else{return false;}break;case 6:var _UO=E(_UG);if(_UO._==6){if(E(_UH.a)!=E(_UO.a)){return false;}else{return new F(function(){return _UB(_UH.b,_UO.b);});}}else{return false;}break;default:var _UP=E(_UG);if(_UP._==7){if(E(_UH.a)!=E(_UP.a)){return false;}else{if(E(_UH.b)!=E(_UP.b)){return false;}else{return new F(function(){return _UB(_UH.c,_UP.c);});}}}else{return false;}}},_UQ=function(_UR,_US){return (!B(_UE(_UR,_US)))?true:false;},_UT=new T2(0,_UE,_UQ),_UU=function(_UV,_UW){while(1){var _UX=E(_UV);switch(_UX._){case 0:var _UY=E(_UW);if(!_UY._){return new F(function(){return _UB(_UX.a,_UY.a);});}else{return false;}break;case 1:var _UZ=E(_UW);if(_UZ._==1){if(!B(_UU(_UX.a,_UZ.a))){return false;}else{_UV=_UX.b;_UW=_UZ.b;continue;}}else{return false;}break;default:var _V0=E(_UW);if(_V0._==2){return new F(function(){return _UB(_UX.a,_V0.a);});}else{return false;}}}},_V1=function(_V2,_V3){while(1){var _V4=E(_V2);switch(_V4._){case 0:var _V5=E(_V3);if(!_V5._){return new F(function(){return _UB(_V4.a,_V5.a);});}else{return false;}break;case 1:var _V6=E(_V3);if(_V6._==1){if(!B(_V1(_V4.a,_V6.a))){return false;}else{_V2=_V4.b;_V3=_V6.b;continue;}}else{return false;}break;case 2:var _V7=E(_V3);if(_V7._==2){if(!B(_V1(_V4.a,_V7.a))){return false;}else{_V2=_V4.b;_V3=_V7.b;continue;}}else{return false;}break;case 3:var _V8=E(_V3);if(_V8._==3){_V2=_V4.a;_V3=_V8.a;continue;}else{return false;}break;case 4:var _V9=E(_V3);if(_V9._==4){if(E(_V4.a)!=E(_V9.a)){return false;}else{if(E(_V4.b)!=E(_V9.b)){return false;}else{return new F(function(){return _UB(_V4.c,_V9.c);});}}}else{return false;}break;case 5:var _Va=E(_V3);if(_Va._==5){if(E(_V4.a)!=E(_Va.a)){return false;}else{return new F(function(){return _UB(_V4.b,_Va.b);});}}else{return false;}break;case 6:var _Vb=E(_V3);if(_Vb._==6){if(!B(_UU(_V4.a,_Vb.a))){return false;}else{return new F(function(){return _UU(_V4.b,_Vb.b);});}}else{return false;}break;case 7:return (E(_V3)._==7)?true:false;default:return (E(_V3)._==8)?true:false;}}},_Vc=function(_Vd,_Ve){while(1){var _Vf=E(_Vd);switch(_Vf._){case 0:return (E(_Ve)._==0)?true:false;case 1:var _Vg=E(_Ve);if(_Vg._==1){if(E(_Vf.a)!=E(_Vg.a)){return false;}else{if(E(_Vf.b)!=E(_Vg.b)){return false;}else{if(E(_Vf.c)!=E(_Vg.c)){return false;}else{if(E(_Vf.d)!=E(_Vg.d)){return false;}else{if(E(_Vf.e)!=E(_Vg.e)){return false;}else{if(!B(_Vc(_Vf.f,_Vg.f))){return false;}else{_Vd=_Vf.g;_Ve=_Vg.g;continue;}}}}}}}else{return false;}break;case 2:var _Vh=E(_Ve);if(_Vh._==2){if(E(_Vf.a)!=E(_Vh.a)){return false;}else{_Vd=_Vf.b;_Ve=_Vh.b;continue;}}else{return false;}break;case 3:var _Vi=E(_Ve);if(_Vi._==3){if(E(_Vf.a)!=E(_Vi.a)){return false;}else{if(E(_Vf.b)!=E(_Vi.b)){return false;}else{if(E(_Vf.c)!=E(_Vi.c)){return false;}else{if(E(_Vf.d)!=E(_Vi.d)){return false;}else{if(E(_Vf.e)!=E(_Vi.e)){return false;}else{_Vd=_Vf.f;_Ve=_Vi.f;continue;}}}}}}else{return false;}break;case 4:var _Vj=E(_Ve);if(_Vj._==4){if(!B(_Vc(_Vf.a,_Vj.a))){return false;}else{_Vd=_Vf.b;_Ve=_Vj.b;continue;}}else{return false;}break;case 5:var _Vk=E(_Ve);if(_Vk._==5){if(!B(_V1(_Vf.a,_Vk.a))){return false;}else{if(!B(_Vc(_Vf.b,_Vk.b))){return false;}else{_Vd=_Vf.c;_Ve=_Vk.c;continue;}}}else{return false;}break;default:var _Vl=E(_Ve);if(_Vl._==6){if(!B(_V1(_Vf.a,_Vl.a))){return false;}else{if(E(_Vf.b)!=E(_Vl.b)){return false;}else{if(!B(_Vc(_Vf.c,_Vl.c))){return false;}else{_Vd=_Vf.d;_Ve=_Vl.d;continue;}}}}else{return false;}}}},_Vm=function(_Vn,_Vo,_Vp,_Vq){if(_Vn!=_Vp){return false;}else{return new F(function(){return _UB(_Vo,_Vq);});}},_Vr=function(_Vs,_Vt){var _Vu=E(_Vs),_Vv=E(_Vt);return new F(function(){return _Vm(E(_Vu.a),_Vu.b,E(_Vv.a),_Vv.b);});},_Vw=function(_Vx,_Vy,_Vz,_VA){return (_Vx!=_Vz)?true:(E(_Vy)!=E(_VA))?true:false;},_VB=function(_VC,_VD){var _VE=E(_VC),_VF=E(_VD);return new F(function(){return _Vw(E(_VE.a),_VE.b,E(_VF.a),_VF.b);});},_VG=new T2(0,_Vr,_VB),_VH=function(_VI,_VJ){return E(_VI)!=E(_VJ);},_VK=new T2(0,_UB,_VH),_VL=function(_VM,_VN,_VO,_VP,_VQ,_VR){return (!B(A3(_6t,_VM,_VO,_VQ)))?true:(!B(A3(_6t,_VN,_VP,_VR)))?true:false;},_VS=function(_VT,_VU,_VV,_VW){var _VX=E(_VV),_VY=E(_VW);return new F(function(){return _VL(_VT,_VU,_VX.a,_VX.b,_VY.a,_VY.b);});},_VZ=function(_W0,_W1,_W2,_W3,_W4,_W5){if(!B(A3(_6t,_W0,_W2,_W4))){return false;}else{return new F(function(){return A3(_6t,_W1,_W3,_W5);});}},_W6=function(_W7,_W8,_W9,_Wa){var _Wb=E(_W9),_Wc=E(_Wa);return new F(function(){return _VZ(_W7,_W8,_Wb.a,_Wb.b,_Wc.a,_Wc.b);});},_Wd=function(_We,_Wf){return new T2(0,function(_Wg,_Wh){return new F(function(){return _W6(_We,_Wf,_Wg,_Wh);});},function(_Wg,_Wh){return new F(function(){return _VS(_We,_Wf,_Wg,_Wh);});});},_Wi=function(_Wj,_Wk,_Wl){while(1){var _Wm=E(_Wk);if(!_Wm._){return (E(_Wl)._==0)?true:false;}else{var _Wn=E(_Wl);if(!_Wn._){return false;}else{if(!B(A3(_6t,_Wj,_Wm.a,_Wn.a))){return false;}else{_Wk=_Wm.b;_Wl=_Wn.b;continue;}}}}},_Wo=function(_Wp,_Wq){var _Wr=new T(function(){return B(_Wd(_Wp,_Wq));}),_Ws=function(_Wt,_Wu){var _Wv=function(_Ww){var _Wx=function(_Wy){if(_Ww!=_Wy){return false;}else{return new F(function(){return _Wi(_Wr,B(_Ja(_9,_Wt)),B(_Ja(_9,_Wu)));});}},_Wz=E(_Wu);if(!_Wz._){return new F(function(){return _Wx(_Wz.a);});}else{return new F(function(){return _Wx(0);});}},_WA=E(_Wt);if(!_WA._){return new F(function(){return _Wv(_WA.a);});}else{return new F(function(){return _Wv(0);});}};return E(_Ws);},_WB=new T(function(){return B(_Wo(_VG,_VK));}),_WC=new T2(0,_UB,_VH),_WD=function(_WE,_WF){var _WG=E(_WE);if(!_WG._){var _WH=E(_WF);if(!_WH._){if(E(_WG.a)!=E(_WH.a)){return false;}else{return new F(function(){return _UB(_WG.b,_WH.b);});}}else{return false;}}else{return (E(_WF)._==0)?false:true;}},_WI=function(_WJ,_WK,_WL,_WM){if(_WJ!=_WL){return false;}else{return new F(function(){return _WD(_WK,_WM);});}},_WN=function(_WO,_WP){var _WQ=E(_WO),_WR=E(_WP);return new F(function(){return _WI(E(_WQ.a),_WQ.b,E(_WR.a),_WR.b);});},_WS=function(_WT,_WU,_WV,_WW){if(_WT!=_WV){return true;}else{var _WX=E(_WU);if(!_WX._){var _WY=E(_WW);return (_WY._==0)?(E(_WX.a)!=E(_WY.a))?true:(E(_WX.b)!=E(_WY.b))?true:false:true;}else{return (E(_WW)._==0)?true:false;}}},_WZ=function(_X0,_X1){var _X2=E(_X0),_X3=E(_X1);return new F(function(){return _WS(E(_X2.a),_X2.b,E(_X3.a),_X3.b);});},_X4=new T2(0,_WN,_WZ),_X5=new T(function(){return B(_Wo(_WC,_X4));}),_X6=function(_X7,_X8){var _X9=E(_X7),_Xa=E(_X8);return (_X9>_Xa)?E(_X9):E(_Xa);},_Xb=function(_Xc,_Xd){var _Xe=E(_Xc),_Xf=E(_Xd);return (_Xe>_Xf)?E(_Xf):E(_Xe);},_Xg=function(_Xh,_Xi){return (_Xh>=_Xi)?(_Xh!=_Xi)?2:1:0;},_Xj=function(_Xk,_Xl){return new F(function(){return _Xg(E(_Xk),E(_Xl));});},_Xm=function(_Xn,_Xo){return E(_Xn)>=E(_Xo);},_Xp=function(_Xq,_Xr){return E(_Xq)>E(_Xr);},_Xs=function(_Xt,_Xu){return E(_Xt)<=E(_Xu);},_Xv=function(_Xw,_Xx){return E(_Xw)<E(_Xx);},_Xy={_:0,a:_WC,b:_Xj,c:_Xv,d:_Xs,e:_Xp,f:_Xm,g:_X6,h:_Xb},_Xz=function(_XA,_XB,_XC,_XD,_XE){while(1){var _XF=E(_XE);if(!_XF._){var _XG=_XF.c,_XH=_XF.d,_XI=E(_XF.b),_XJ=E(_XI.a);if(_XA>=_XJ){if(_XA!=_XJ){_XB=_;_XE=_XH;continue;}else{var _XK=E(_XI.b);if(_XC>=_XK){if(_XC!=_XK){_XB=_;_XE=_XH;continue;}else{var _XL=E(_XI.c);if(_XD>=_XL){if(_XD!=_XL){_XB=_;_XE=_XH;continue;}else{return true;}}else{_XB=_;_XE=_XG;continue;}}}else{_XB=_;_XE=_XG;continue;}}}else{_XB=_;_XE=_XG;continue;}}else{return false;}}},_XM=function(_XN,_XO,_XP,_XQ,_XR){while(1){var _XS=E(_XR);if(!_XS._){var _XT=_XS.c,_XU=_XS.d,_XV=E(_XS.b),_XW=E(_XV.a);if(_XN>=_XW){if(_XN!=_XW){_XO=_;_XR=_XU;continue;}else{var _XX=E(_XV.b);if(_XP>=_XX){if(_XP!=_XX){_XO=_;_XR=_XU;continue;}else{var _XY=E(_XQ),_XZ=E(_XV.c);if(_XY>=_XZ){if(_XY!=_XZ){return new F(function(){return _Xz(_XN,_,_XP,_XY,_XU);});}else{return true;}}else{return new F(function(){return _Xz(_XN,_,_XP,_XY,_XT);});}}}else{_XO=_;_XR=_XT;continue;}}}else{_XO=_;_XR=_XT;continue;}}else{return false;}}},_Y0=function(_Y1,_Y2,_Y3,_Y4,_Y5){while(1){var _Y6=E(_Y5);if(!_Y6._){var _Y7=_Y6.c,_Y8=_Y6.d,_Y9=E(_Y6.b),_Ya=E(_Y9.a);if(_Y1>=_Ya){if(_Y1!=_Ya){_Y2=_;_Y5=_Y8;continue;}else{var _Yb=E(_Y3),_Yc=E(_Y9.b);if(_Yb>=_Yc){if(_Yb!=_Yc){return new F(function(){return _XM(_Y1,_,_Yb,_Y4,_Y8);});}else{var _Yd=E(_Y4),_Ye=E(_Y9.c);if(_Yd>=_Ye){if(_Yd!=_Ye){return new F(function(){return _Xz(_Y1,_,_Yb,_Yd,_Y8);});}else{return true;}}else{return new F(function(){return _Xz(_Y1,_,_Yb,_Yd,_Y7);});}}}else{return new F(function(){return _XM(_Y1,_,_Yb,_Y4,_Y7);});}}}else{_Y2=_;_Y5=_Y7;continue;}}else{return false;}}},_Yf=function(_Yg,_Yh,_Yi,_Yj){var _Yk=E(_Yj);if(!_Yk._){var _Yl=_Yk.c,_Ym=_Yk.d,_Yn=E(_Yk.b),_Yo=E(_Yg),_Yp=E(_Yn.a);if(_Yo>=_Yp){if(_Yo!=_Yp){return new F(function(){return _Y0(_Yo,_,_Yh,_Yi,_Ym);});}else{var _Yq=E(_Yh),_Yr=E(_Yn.b);if(_Yq>=_Yr){if(_Yq!=_Yr){return new F(function(){return _XM(_Yo,_,_Yq,_Yi,_Ym);});}else{var _Ys=E(_Yi),_Yt=E(_Yn.c);if(_Ys>=_Yt){if(_Ys!=_Yt){return new F(function(){return _Xz(_Yo,_,_Yq,_Ys,_Ym);});}else{return true;}}else{return new F(function(){return _Xz(_Yo,_,_Yq,_Ys,_Yl);});}}}else{return new F(function(){return _XM(_Yo,_,_Yq,_Yi,_Yl);});}}}else{return new F(function(){return _Y0(_Yo,_,_Yh,_Yi,_Yl);});}}else{return false;}},_Yu=function(_Yv,_Yw,_Yx,_Yy,_Yz){var _YA=E(_Yz);if(!_YA._){if(E(_YA.b)>E(_Yw)){return false;}else{return new F(function(){return _Yf(_Yx,_Yy,_YA.a,E(_Yv).b);});}}else{return false;}},_YB=function(_YC,_YD,_YE,_YF,_YG){var _YH=E(_YG);if(!_YH._){var _YI=new T(function(){var _YJ=B(_YB(_YH.a,_YH.b,_YH.c,_YH.d,_YH.e));return new T2(0,_YJ.a,_YJ.b);});return new T2(0,new T(function(){return E(E(_YI).a);}),new T(function(){return B(_sY(_YD,_YE,_YF,E(_YI).b));}));}else{return new T2(0,new T2(0,_YD,_YE),_YF);}},_YK=function(_YL,_YM,_YN,_YO,_YP){var _YQ=E(_YO);if(!_YQ._){var _YR=new T(function(){var _YS=B(_YK(_YQ.a,_YQ.b,_YQ.c,_YQ.d,_YQ.e));return new T2(0,_YS.a,_YS.b);});return new T2(0,new T(function(){return E(E(_YR).a);}),new T(function(){return B(_s7(_YM,_YN,E(_YR).b,_YP));}));}else{return new T2(0,new T2(0,_YM,_YN),_YP);}},_YT=function(_YU,_YV){var _YW=E(_YU);if(!_YW._){var _YX=_YW.a,_YY=E(_YV);if(!_YY._){var _YZ=_YY.a;if(_YX<=_YZ){var _Z0=B(_YK(_YZ,_YY.b,_YY.c,_YY.d,_YY.e)),_Z1=E(_Z0.a);return new F(function(){return _sY(_Z1.a,_Z1.b,_YW,_Z0.b);});}else{var _Z2=B(_YB(_YX,_YW.b,_YW.c,_YW.d,_YW.e)),_Z3=E(_Z2.a);return new F(function(){return _s7(_Z3.a,_Z3.b,_Z2.b,_YY);});}}else{return E(_YW);}}else{return E(_YV);}},_Z4=function(_Z5,_Z6,_Z7,_Z8,_Z9,_Za){var _Zb=E(_Z5);if(!_Zb._){var _Zc=_Zb.a,_Zd=_Zb.b,_Ze=_Zb.c,_Zf=_Zb.d,_Zg=_Zb.e;if((imul(3,_Zc)|0)>=_Z6){if((imul(3,_Z6)|0)>=_Zc){return new F(function(){return _YT(_Zb,new T5(0,_Z6,E(_Z7),_Z8,E(_Z9),E(_Za)));});}else{return new F(function(){return _s7(_Zd,_Ze,_Zf,B(_Z4(_Zg,_Z6,_Z7,_Z8,_Z9,_Za)));});}}else{return new F(function(){return _sY(_Z7,_Z8,B(_Zh(_Zc,_Zd,_Ze,_Zf,_Zg,_Z9)),_Za);});}}else{return new T5(0,_Z6,E(_Z7),_Z8,E(_Z9),E(_Za));}},_Zh=function(_Zi,_Zj,_Zk,_Zl,_Zm,_Zn){var _Zo=E(_Zn);if(!_Zo._){var _Zp=_Zo.a,_Zq=_Zo.b,_Zr=_Zo.c,_Zs=_Zo.d,_Zt=_Zo.e;if((imul(3,_Zi)|0)>=_Zp){if((imul(3,_Zp)|0)>=_Zi){return new F(function(){return _YT(new T5(0,_Zi,E(_Zj),_Zk,E(_Zl),E(_Zm)),_Zo);});}else{return new F(function(){return _s7(_Zj,_Zk,_Zl,B(_Z4(_Zm,_Zp,_Zq,_Zr,_Zs,_Zt)));});}}else{return new F(function(){return _sY(_Zq,_Zr,B(_Zh(_Zi,_Zj,_Zk,_Zl,_Zm,_Zs)),_Zt);});}}else{return new T5(0,_Zi,E(_Zj),_Zk,E(_Zl),E(_Zm));}},_Zu=function(_Zv,_Zw){var _Zx=E(_Zv);if(!_Zx._){var _Zy=_Zx.a,_Zz=_Zx.b,_ZA=_Zx.c,_ZB=_Zx.d,_ZC=_Zx.e,_ZD=E(_Zw);if(!_ZD._){var _ZE=_ZD.a,_ZF=_ZD.b,_ZG=_ZD.c,_ZH=_ZD.d,_ZI=_ZD.e;if((imul(3,_Zy)|0)>=_ZE){if((imul(3,_ZE)|0)>=_Zy){return new F(function(){return _YT(_Zx,_ZD);});}else{return new F(function(){return _s7(_Zz,_ZA,_ZB,B(_Z4(_ZC,_ZE,_ZF,_ZG,_ZH,_ZI)));});}}else{return new F(function(){return _sY(_ZF,_ZG,B(_Zh(_Zy,_Zz,_ZA,_ZB,_ZC,_ZH)),_ZI);});}}else{return E(_Zx);}}else{return E(_Zw);}},_ZJ=function(_ZK,_ZL){var _ZM=E(_ZL);if(!_ZM._){var _ZN=_ZM.b,_ZO=_ZM.c,_ZP=B(_ZJ(_ZK,_ZM.d)),_ZQ=_ZP.a,_ZR=_ZP.b,_ZS=B(_ZJ(_ZK,_ZM.e)),_ZT=_ZS.a,_ZU=_ZS.b;return (!B(A2(_ZK,_ZN,_ZO)))?new T2(0,B(_Zu(_ZQ,_ZT)),B(_ui(_ZN,_ZO,_ZR,_ZU))):new T2(0,B(_ui(_ZN,_ZO,_ZQ,_ZT)),B(_Zu(_ZR,_ZU)));}else{return new T2(0,_s2,_s2);}},_ZV=__Z,_ZW=function(_ZX,_ZY){while(1){var _ZZ=B((function(_100,_101){var _102=E(_101);if(!_102._){var _103=_102.e,_104=new T(function(){var _105=E(_102.c),_106=E(_105.b);if(!_106._){return new T2(1,new T3(5,_102.b,_105.a,_106.a),new T(function(){return B(_ZW(_100,_103));}));}else{return B(_ZW(_100,_103));}},1);_ZX=_104;_ZY=_102.d;return __continue;}else{return E(_100);}})(_ZX,_ZY));if(_ZZ!=__continue){return _ZZ;}}},_107=function(_108,_109){var _10a=E(_109);return (_10a._==0)?new T5(0,_10a.a,E(_10a.b),new T(function(){return B(A1(_108,_10a.c));}),E(B(_107(_108,_10a.d))),E(B(_107(_108,_10a.e)))):new T0(1);},_10b=new T0(1),_10c=function(_10d){var _10e=E(_10d),_10f=E(_10e.b);return new T2(0,_10e.a,_10b);},_10g=function(_10h){return E(E(_10h).b);},_10i=function(_10j,_10k,_10l){var _10m=E(_10k);if(!_10m._){return E(_10l);}else{var _10n=function(_10o,_10p){while(1){var _10q=E(_10p);if(!_10q._){var _10r=_10q.b,_10s=_10q.e;switch(B(A3(_10g,_10j,_10o,_10r))){case 0:return new F(function(){return _ui(_10r,_10q.c,B(_10n(_10o,_10q.d)),_10s);});break;case 1:return E(_10s);default:_10p=_10s;continue;}}else{return new T0(1);}}};return new F(function(){return _10n(_10m.a,_10l);});}},_10t=function(_10u,_10v,_10w){var _10x=E(_10v);if(!_10x._){return E(_10w);}else{var _10y=function(_10z,_10A){while(1){var _10B=E(_10A);if(!_10B._){var _10C=_10B.b,_10D=_10B.d;switch(B(A3(_10g,_10u,_10C,_10z))){case 0:return new F(function(){return _ui(_10C,_10B.c,_10D,B(_10y(_10z,_10B.e)));});break;case 1:return E(_10D);default:_10A=_10D;continue;}}else{return new T0(1);}}};return new F(function(){return _10y(_10x.a,_10w);});}},_10E=function(_10F,_10G,_10H,_10I){var _10J=E(_10G),_10K=E(_10I);if(!_10K._){var _10L=_10K.b,_10M=_10K.c,_10N=_10K.d,_10O=_10K.e;switch(B(A3(_10g,_10F,_10J,_10L))){case 0:return new F(function(){return _sY(_10L,_10M,B(_10E(_10F,_10J,_10H,_10N)),_10O);});break;case 1:return E(_10K);default:return new F(function(){return _s7(_10L,_10M,_10N,B(_10E(_10F,_10J,_10H,_10O)));});}}else{return new T5(0,1,E(_10J),_10H,E(_s2),E(_s2));}},_10P=function(_10Q,_10R,_10S,_10T){return new F(function(){return _10E(_10Q,_10R,_10S,_10T);});},_10U=function(_10V){return E(E(_10V).d);},_10W=function(_10X){return E(E(_10X).f);},_10Y=function(_10Z,_110,_111,_112){var _113=E(_110);if(!_113._){var _114=E(_111);if(!_114._){return E(_112);}else{var _115=function(_116,_117){while(1){var _118=E(_117);if(!_118._){if(!B(A3(_10W,_10Z,_118.b,_116))){return E(_118);}else{_117=_118.d;continue;}}else{return new T0(1);}}};return new F(function(){return _115(_114.a,_112);});}}else{var _119=_113.a,_11a=E(_111);if(!_11a._){var _11b=function(_11c,_11d){while(1){var _11e=E(_11d);if(!_11e._){if(!B(A3(_10U,_10Z,_11e.b,_11c))){return E(_11e);}else{_11d=_11e.e;continue;}}else{return new T0(1);}}};return new F(function(){return _11b(_119,_112);});}else{var _11f=function(_11g,_11h,_11i){while(1){var _11j=E(_11i);if(!_11j._){var _11k=_11j.b;if(!B(A3(_10U,_10Z,_11k,_11g))){if(!B(A3(_10W,_10Z,_11k,_11h))){return E(_11j);}else{_11i=_11j.d;continue;}}else{_11i=_11j.e;continue;}}else{return new T0(1);}}};return new F(function(){return _11f(_119,_11a.a,_112);});}}},_11l=function(_11m,_11n,_11o,_11p,_11q){var _11r=E(_11q);if(!_11r._){var _11s=_11r.b,_11t=_11r.c,_11u=_11r.d,_11v=_11r.e,_11w=E(_11p);if(!_11w._){var _11x=_11w.b,_11y=function(_11z){var _11A=new T1(1,E(_11x));return new F(function(){return _ui(_11x,_11w.c,B(_11l(_11m,_11n,_11A,_11w.d,B(_10Y(_11m,_11n,_11A,_11r)))),B(_11l(_11m,_11A,_11o,_11w.e,B(_10Y(_11m,_11A,_11o,_11r)))));});};if(!E(_11u)._){return new F(function(){return _11y(_);});}else{if(!E(_11v)._){return new F(function(){return _11y(_);});}else{return new F(function(){return _10P(_11m,_11s,_11t,_11w);});}}}else{return new F(function(){return _ui(_11s,_11t,B(_10i(_11m,_11n,_11u)),B(_10t(_11m,_11o,_11v)));});}}else{return E(_11p);}},_11B=function(_11C,_11D,_11E,_11F,_11G,_11H,_11I,_11J,_11K,_11L,_11M,_11N,_11O){var _11P=function(_11Q){var _11R=new T1(1,E(_11G));return new F(function(){return _ui(_11G,_11H,B(_11l(_11C,_11D,_11R,_11I,B(_10Y(_11C,_11D,_11R,new T5(0,_11K,E(_11L),_11M,E(_11N),E(_11O)))))),B(_11l(_11C,_11R,_11E,_11J,B(_10Y(_11C,_11R,_11E,new T5(0,_11K,E(_11L),_11M,E(_11N),E(_11O)))))));});};if(!E(_11N)._){return new F(function(){return _11P(_);});}else{if(!E(_11O)._){return new F(function(){return _11P(_);});}else{return new F(function(){return _10P(_11C,_11L,_11M,new T5(0,_11F,E(_11G),_11H,E(_11I),E(_11J)));});}}},_11S=function(_11T,_11U,_11V){var _11W=new T(function(){var _11X=new T(function(){return E(E(_11V).b);}),_11Y=B(_ZJ(function(_11Z,_120){var _121=E(_120);return new F(function(){return _Yu(_11T,_11X,_11Z,_121.a,_121.b);});},_11U));return new T2(0,_11Y.a,_11Y.b);}),_122=new T(function(){return E(E(_11W).a);});return new T2(0,new T(function(){var _123=B(_107(_10c,_122));if(!_123._){var _124=E(E(_11W).b);if(!_124._){return B(_11B(_Xy,_ZV,_ZV,_123.a,_123.b,_123.c,_123.d,_123.e,_124.a,_124.b,_124.c,_124.d,_124.e));}else{return E(_123);}}else{return E(E(_11W).b);}}),new T(function(){return B(_ZW(_9,_122));}));},_125=function(_126,_127,_128,_129){while(1){var _12a=E(_129);if(!_12a._){var _12b=_12a.d,_12c=_12a.e,_12d=E(_12a.b),_12e=E(_12d.a);if(_126>=_12e){if(_126!=_12e){_127=_;_129=_12c;continue;}else{var _12f=E(_12d.b);if(_128>=_12f){if(_128!=_12f){_127=_;_129=_12c;continue;}else{return true;}}else{_127=_;_129=_12b;continue;}}}else{_127=_;_129=_12b;continue;}}else{return false;}}},_12g=function(_12h,_12i,_12j,_12k){while(1){var _12l=E(_12k);if(!_12l._){var _12m=_12l.d,_12n=_12l.e,_12o=E(_12l.b),_12p=E(_12o.a);if(_12h>=_12p){if(_12h!=_12p){_12i=_;_12k=_12n;continue;}else{var _12q=E(_12j),_12r=E(_12o.b);if(_12q>=_12r){if(_12q!=_12r){return new F(function(){return _125(_12h,_,_12q,_12n);});}else{return true;}}else{return new F(function(){return _125(_12h,_,_12q,_12m);});}}}else{_12i=_;_12k=_12m;continue;}}else{return false;}}},_12s=function(_12t,_12u,_12v,_12w,_12x){var _12y=E(_12x);if(!_12y._){var _12z=_12y.c,_12A=_12y.d,_12B=_12y.e,_12C=E(_12y.b),_12D=E(_12C.a);if(_12t>=_12D){if(_12t!=_12D){return new F(function(){return _s7(_12C,_12z,_12A,B(_12s(_12t,_,_12v,_12w,_12B)));});}else{var _12E=E(_12C.b);if(_12v>=_12E){if(_12v!=_12E){return new F(function(){return _s7(_12C,_12z,_12A,B(_12s(_12t,_,_12v,_12w,_12B)));});}else{return new T5(0,_12y.a,E(new T2(0,_12t,_12v)),_12w,E(_12A),E(_12B));}}else{return new F(function(){return _sY(_12C,_12z,B(_12s(_12t,_,_12v,_12w,_12A)),_12B);});}}}else{return new F(function(){return _sY(_12C,_12z,B(_12s(_12t,_,_12v,_12w,_12A)),_12B);});}}else{return new T5(0,1,E(new T2(0,_12t,_12v)),_12w,E(_s2),E(_s2));}},_12F=function(_12G,_12H,_12I,_12J,_12K){var _12L=E(_12K);if(!_12L._){var _12M=_12L.c,_12N=_12L.d,_12O=_12L.e,_12P=E(_12L.b),_12Q=E(_12P.a);if(_12G>=_12Q){if(_12G!=_12Q){return new F(function(){return _s7(_12P,_12M,_12N,B(_12F(_12G,_,_12I,_12J,_12O)));});}else{var _12R=E(_12I),_12S=E(_12P.b);if(_12R>=_12S){if(_12R!=_12S){return new F(function(){return _s7(_12P,_12M,_12N,B(_12s(_12G,_,_12R,_12J,_12O)));});}else{return new T5(0,_12L.a,E(new T2(0,_12G,_12R)),_12J,E(_12N),E(_12O));}}else{return new F(function(){return _sY(_12P,_12M,B(_12s(_12G,_,_12R,_12J,_12N)),_12O);});}}}else{return new F(function(){return _sY(_12P,_12M,B(_12F(_12G,_,_12I,_12J,_12N)),_12O);});}}else{return new T5(0,1,E(new T2(0,_12G,_12I)),_12J,E(_s2),E(_s2));}},_12T=function(_12U,_12V,_12W,_12X){var _12Y=E(_12X);if(!_12Y._){var _12Z=_12Y.c,_130=_12Y.d,_131=_12Y.e,_132=E(_12Y.b),_133=E(_12U),_134=E(_132.a);if(_133>=_134){if(_133!=_134){return new F(function(){return _s7(_132,_12Z,_130,B(_12F(_133,_,_12V,_12W,_131)));});}else{var _135=E(_12V),_136=E(_132.b);if(_135>=_136){if(_135!=_136){return new F(function(){return _s7(_132,_12Z,_130,B(_12s(_133,_,_135,_12W,_131)));});}else{return new T5(0,_12Y.a,E(new T2(0,_133,_135)),_12W,E(_130),E(_131));}}else{return new F(function(){return _sY(_132,_12Z,B(_12s(_133,_,_135,_12W,_130)),_131);});}}}else{return new F(function(){return _sY(_132,_12Z,B(_12F(_133,_,_12V,_12W,_130)),_131);});}}else{return new T5(0,1,E(new T2(0,_12U,_12V)),_12W,E(_s2),E(_s2));}},_137=function(_138,_139,_13a){while(1){var _13b=B((function(_13c,_13d,_13e){var _13f=E(_13e);if(!_13f._){var _13g=_13f.c,_13h=_13f.e,_13i=E(_13f.b),_13j=_13i.a,_13k=_13i.b,_13l=B(_137(_13c,_13d,_13f.d)),_13m=_13l.a,_13n=_13l.b,_13o=function(_13p){return new F(function(){return _137(new T(function(){return B(_12T(_13j,_13k,_13g,_13m));}),new T2(1,new T3(7,_13j,_13k,_13g),_13n),_13h);});},_13q=E(_13m);if(!_13q._){var _13r=_13q.d,_13s=_13q.e,_13t=E(_13q.b),_13u=E(_13j),_13v=E(_13t.a);if(_13u>=_13v){if(_13u!=_13v){if(!B(_12g(_13u,_,_13k,_13s))){return new F(function(){return _13o(_);});}else{_138=_13q;_139=_13n;_13a=_13h;return __continue;}}else{var _13w=E(_13k),_13x=E(_13t.b);if(_13w>=_13x){if(_13w!=_13x){if(!B(_125(_13u,_,_13w,_13s))){return new F(function(){return _13o(_);});}else{_138=_13q;_139=_13n;_13a=_13h;return __continue;}}else{_138=_13q;_139=_13n;_13a=_13h;return __continue;}}else{if(!B(_125(_13u,_,_13w,_13r))){return new F(function(){return _13o(_);});}else{_138=_13q;_139=_13n;_13a=_13h;return __continue;}}}}else{if(!B(_12g(_13u,_,_13k,_13r))){return new F(function(){return _13o(_);});}else{_138=_13q;_139=_13n;_13a=_13h;return __continue;}}}else{return new F(function(){return _13o(_);});}}else{return new T2(0,_13c,_13d);}})(_138,_139,_13a));if(_13b!=__continue){return _13b;}}},_13y=function(_13z,_13A,_13B,_13C){while(1){var _13D=E(_13C);if(!_13D._){var _13E=_13D.d,_13F=_13D.e,_13G=E(_13D.b),_13H=E(_13G.a);if(_13z>=_13H){if(_13z!=_13H){_13A=_;_13C=_13F;continue;}else{var _13I=E(_13G.b);if(_13B>=_13I){if(_13B!=_13I){_13A=_;_13C=_13F;continue;}else{return new T1(1,_13D.c);}}else{_13A=_;_13C=_13E;continue;}}}else{_13A=_;_13C=_13E;continue;}}else{return __Z;}}},_13J=function(_13K,_13L,_13M,_13N){while(1){var _13O=E(_13N);if(!_13O._){var _13P=_13O.d,_13Q=_13O.e,_13R=E(_13O.b),_13S=E(_13R.a);if(_13K>=_13S){if(_13K!=_13S){_13L=_;_13N=_13Q;continue;}else{var _13T=E(_13M),_13U=E(_13R.b);if(_13T>=_13U){if(_13T!=_13U){return new F(function(){return _13y(_13K,_,_13T,_13Q);});}else{return new T1(1,_13O.c);}}else{return new F(function(){return _13y(_13K,_,_13T,_13P);});}}}else{_13L=_;_13N=_13P;continue;}}else{return __Z;}}},_13V=function(_13W,_13X,_13Y,_13Z,_140){while(1){var _141=E(_140);if(!_141._){var _142=_141.c,_143=_141.d,_144=E(_141.b),_145=E(_13W),_146=E(_144.a);if(_145>=_146){if(_145!=_146){_13W=_145;_140=_143;continue;}else{var _147=E(_13X),_148=E(_144.b);if(_147>=_148){if(_147!=_148){_13W=_145;_13X=_147;_140=_143;continue;}else{var _149=E(_13Y),_14a=E(_144.c);if(_149>=_14a){if(_149!=_14a){_13W=_145;_13X=_147;_13Y=_149;_140=_143;continue;}else{var _14b=E(_144.d);if(_13Z>=_14b){if(_13Z!=_14b){_13W=_145;_13X=_147;_13Y=_149;_140=_143;continue;}else{return true;}}else{_13W=_145;_13X=_147;_13Y=_149;_140=_142;continue;}}}else{_13W=_145;_13X=_147;_13Y=_149;_140=_142;continue;}}}else{_13W=_145;_13X=_147;_140=_142;continue;}}}else{_13W=_145;_140=_142;continue;}}else{return false;}}},_14c=function(_14d,_14e){return E(_14d)+E(_14e)|0;},_14f=0,_14g=function(_14h,_14i,_14j){var _14k=function(_14l,_14m){while(1){var _14n=B((function(_14o,_14p){var _14q=E(_14p);if(!_14q._){var _14r=new T(function(){return B(_14k(_14o,_14q.e));}),_14s=function(_14t){var _14u=E(_14q.c),_14v=E(_14u.b);if(!_14v._){if(E(_14u.a)!=E(_14i)){return new F(function(){return A1(_14r,_14t);});}else{if(E(_14v.b)>E(_14j)){return new F(function(){return A1(_14r,new T(function(){return B(_14c(_14t,_14v.a));}));});}else{return new F(function(){return A1(_14r,_14t);});}}}else{return new F(function(){return A1(_14r,_14t);});}};_14l=_14s;_14m=_14q.d;return __continue;}else{return E(_14o);}})(_14l,_14m));if(_14n!=__continue){return _14n;}}};return new F(function(){return A3(_14k,_3M,_14h,_14f);});},_14w=function(_14x,_14y){while(1){var _14z=E(_14y);if(!_14z._){var _14A=E(_14z.b);if(_14x>=_14A){if(_14x!=_14A){_14y=_14z.e;continue;}else{return new T1(1,_14z.c);}}else{_14y=_14z.d;continue;}}else{return __Z;}}},_14B=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_14C=new T(function(){return B(err(_14B));}),_14D=function(_14E,_14F){var _14G=E(_14F);if(!_14G._){return E(_14C);}else{var _14H=_14G.b,_14I=E(_14G.a),_14J=_14I.a,_14K=E(_14I.b),_14L=_14K.a,_14M=E(_14K.b);if(!_14M._){var _14N=_14M.b,_14O=E(_14M.a);return (_14E>_14O)?(_14O>=_14E)?E(_14H):new T2(1,new T2(0,_14J,new T2(0,_14L,new T2(0,_14f,_14N))),new T(function(){return B(_14D(_14E-_14O|0,_14H));})):new T2(1,new T2(0,_14J,new T2(0,_14L,new T2(0,_14O-_14E|0,_14N))),_9);}else{return E(_14H);}}},_14P=function(_14Q,_14R){var _14S=E(_14R);if(!_14S._){return E(_14C);}else{var _14T=_14S.b,_14U=E(_14S.a),_14V=_14U.a,_14W=E(_14U.b),_14X=_14W.a,_14Y=E(_14W.b);if(!_14Y._){var _14Z=_14Y.b,_150=E(_14Q),_151=E(_14Y.a);return (_150>_151)?(_151>=_150)?E(_14T):new T2(1,new T2(0,_14V,new T2(0,_14X,new T2(0,_14f,_14Z))),new T(function(){return B(_14D(_150-_151|0,_14T));})):new T2(1,new T2(0,_14V,new T2(0,_14X,new T2(0,_151-_150|0,_14Z))),_9);}else{return E(_14T);}}},_152=function(_153,_154){var _155=E(_154);if(!_155._){var _156=_155.b,_157=_155.c,_158=_155.d,_159=_155.e;if(!B(A2(_153,_156,_157))){return new F(function(){return _Zu(B(_152(_153,_158)),B(_152(_153,_159)));});}else{return new F(function(){return _ui(_156,_157,B(_152(_153,_158)),B(_152(_153,_159)));});}}else{return new T0(1);}},_15a=function(_15b,_15c){var _15d=E(_15b);if(!_15d._){var _15e=E(_15c);if(!_15e._){return new F(function(){return _Xj(_15d.b,_15e.b);});}else{return 0;}}else{return (E(_15c)._==0)?2:1;}},_15f=function(_15g,_15h){return new F(function(){return _15a(E(E(_15g).b).b,E(E(_15h).b).b);});},_15i=new T2(1,_9,_9),_15j=function(_15k,_15l){var _15m=function(_15n,_15o){var _15p=E(_15n);if(!_15p._){return E(_15o);}else{var _15q=_15p.a,_15r=E(_15o);if(!_15r._){return E(_15p);}else{var _15s=_15r.a;return (B(A2(_15k,_15q,_15s))==2)?new T2(1,_15s,new T(function(){return B(_15m(_15p,_15r.b));})):new T2(1,_15q,new T(function(){return B(_15m(_15p.b,_15r));}));}}},_15t=function(_15u){var _15v=E(_15u);if(!_15v._){return __Z;}else{var _15w=E(_15v.b);return (_15w._==0)?E(_15v):new T2(1,new T(function(){return B(_15m(_15v.a,_15w.a));}),new T(function(){return B(_15t(_15w.b));}));}},_15x=new T(function(){return B(_15y(B(_15t(_9))));}),_15y=function(_15z){while(1){var _15A=E(_15z);if(!_15A._){return E(_15x);}else{if(!E(_15A.b)._){return E(_15A.a);}else{_15z=B(_15t(_15A));continue;}}}},_15B=new T(function(){return B(_15C(_9));}),_15D=function(_15E,_15F,_15G){while(1){var _15H=B((function(_15I,_15J,_15K){var _15L=E(_15K);if(!_15L._){return new T2(1,new T2(1,_15I,_15J),_15B);}else{var _15M=_15L.a;if(B(A2(_15k,_15I,_15M))==2){var _15N=new T2(1,_15I,_15J);_15E=_15M;_15F=_15N;_15G=_15L.b;return __continue;}else{return new T2(1,new T2(1,_15I,_15J),new T(function(){return B(_15C(_15L));}));}}})(_15E,_15F,_15G));if(_15H!=__continue){return _15H;}}},_15O=function(_15P,_15Q,_15R){while(1){var _15S=B((function(_15T,_15U,_15V){var _15W=E(_15V);if(!_15W._){return new T2(1,new T(function(){return B(A1(_15U,new T2(1,_15T,_9)));}),_15B);}else{var _15X=_15W.a,_15Y=_15W.b;switch(B(A2(_15k,_15T,_15X))){case 0:_15P=_15X;_15Q=function(_15Z){return new F(function(){return A1(_15U,new T2(1,_15T,_15Z));});};_15R=_15Y;return __continue;case 1:_15P=_15X;_15Q=function(_160){return new F(function(){return A1(_15U,new T2(1,_15T,_160));});};_15R=_15Y;return __continue;default:return new T2(1,new T(function(){return B(A1(_15U,new T2(1,_15T,_9)));}),new T(function(){return B(_15C(_15W));}));}}})(_15P,_15Q,_15R));if(_15S!=__continue){return _15S;}}},_15C=function(_161){var _162=E(_161);if(!_162._){return E(_15i);}else{var _163=_162.a,_164=E(_162.b);if(!_164._){return new T2(1,_162,_9);}else{var _165=_164.a,_166=_164.b;if(B(A2(_15k,_163,_165))==2){return new F(function(){return _15D(_165,new T2(1,_163,_9),_166);});}else{return new F(function(){return _15O(_165,function(_167){return new T2(1,_163,_167);},_166);});}}}};return new F(function(){return _15y(B(_15C(_15l)));});},_168=function(_169,_16a,_16b){var _16c=B(_TD(B(_14P(_16a,B(_15j(_15f,B(_Ja(_9,B(_152(function(_16d,_16e){return new F(function(){return A1(_169,_16e);});},_16b))))))))));if(!_16c._){var _16f=E(_16b);if(!_16f._){return new F(function(){return _11B(_Xy,_ZV,_ZV,_16c.a,_16c.b,_16c.c,_16c.d,_16c.e,_16f.a,_16f.b,_16f.c,_16f.d,_16f.e);});}else{return E(_16c);}}else{return E(_16b);}},_16g=function(_16h,_16i,_16j,_16k){while(1){var _16l=E(_16k);if(!_16l._){var _16m=_16l.d,_16n=_16l.e,_16o=E(_16l.b),_16p=E(_16o.a);if(_16h>=_16p){if(_16h!=_16p){_16i=_;_16k=_16n;continue;}else{var _16q=E(_16o.b);if(_16j>=_16q){if(_16j!=_16q){_16i=_;_16k=_16n;continue;}else{return new T1(1,_16l.c);}}else{_16i=_;_16k=_16m;continue;}}}else{_16i=_;_16k=_16m;continue;}}else{return __Z;}}},_16r=function(_16s,_16t,_16u,_16v){while(1){var _16w=E(_16v);if(!_16w._){var _16x=_16w.d,_16y=_16w.e,_16z=E(_16w.b),_16A=E(_16z.a);if(_16s>=_16A){if(_16s!=_16A){_16t=_;_16v=_16y;continue;}else{var _16B=E(_16u),_16C=E(_16z.b);if(_16B>=_16C){if(_16B!=_16C){return new F(function(){return _16g(_16s,_,_16B,_16y);});}else{return new T1(1,_16w.c);}}else{return new F(function(){return _16g(_16s,_,_16B,_16x);});}}}else{_16t=_;_16v=_16x;continue;}}else{return __Z;}}},_16D=function(_16E,_16F){var _16G=E(_16F);switch(_16G._){case 0:var _16H=B(_14w(E(_16G.a),_16E));if(!_16H._){return E(_14f);}else{var _16I=E(E(_16H.a).b);return (_16I._==0)?E(_16I.a):E(_14f);}break;case 1:return B(_16D(_16E,_16G.a))+B(_16D(_16E,_16G.b))|0;default:return E(_16G.a);}},_16J=function(_16K,_16L,_16M){var _16N=E(_16M);if(!_16N._){var _16O=_16N.d,_16P=_16N.e,_16Q=E(_16N.b),_16R=E(_16K),_16S=E(_16Q.a);if(_16R>=_16S){if(_16R!=_16S){return new F(function(){return _12g(_16R,_,_16L,_16P);});}else{var _16T=E(_16L),_16U=E(_16Q.b);if(_16T>=_16U){if(_16T!=_16U){return new F(function(){return _125(_16R,_,_16T,_16P);});}else{return true;}}else{return new F(function(){return _125(_16R,_,_16T,_16O);});}}}else{return new F(function(){return _12g(_16R,_,_16L,_16O);});}}else{return false;}},_16V=function(_16W,_16X,_16Y){while(1){var _16Z=E(_16X);switch(_16Z._){case 0:return (E(_16Z.a)>E(E(_16Y).b))?true:false;case 1:if(!B(_16V(_16W,_16Z.a,_16Y))){return false;}else{_16X=_16Z.b;continue;}break;case 2:if(!B(_16V(_16W,_16Z.a,_16Y))){_16X=_16Z.b;continue;}else{return true;}break;case 3:return (!B(_16V(_16W,_16Z.a,_16Y)))?true:false;case 4:var _170=_16Z.b,_171=_16Z.c,_172=E(E(_16W).b);if(!_172._){var _173=_172.d,_174=_172.e,_175=E(_172.b),_176=E(_16Z.a),_177=E(_175.a);if(_176>=_177){if(_176!=_177){var _178=B(_16r(_176,_,_170,_174));if(!_178._){return false;}else{return new F(function(){return _UB(_178.a,_171);});}}else{var _179=E(_170),_17a=E(_175.b);if(_179>=_17a){if(_179!=_17a){var _17b=B(_16g(_176,_,_179,_174));if(!_17b._){return false;}else{return new F(function(){return _UB(_17b.a,_171);});}}else{return new F(function(){return _UB(_172.c,_171);});}}else{var _17c=B(_16g(_176,_,_179,_173));if(!_17c._){return false;}else{return new F(function(){return _UB(_17c.a,_171);});}}}}else{var _17d=B(_16r(_176,_,_170,_173));if(!_17d._){return false;}else{return new F(function(){return _UB(_17d.a,_171);});}}}else{return false;}break;case 5:return new F(function(){return _16J(_16Z.a,_16Z.b,E(_16W).b);});break;case 6:var _17e=E(_16W).a;return B(_16D(_17e,_16Z.a))>=B(_16D(_17e,_16Z.b));case 7:return true;default:return false;}}},_17f=function(_17g,_17h,_17i,_17j){var _17k=E(_17i);switch(_17k._){case 0:return new T3(0,_17h,_io,_9);case 1:var _17l=_17k.a,_17m=_17k.b,_17n=_17k.c,_17o=_17k.g,_17p=E(_17k.e),_17q=E(E(_17j).b),_17r=_17p<=_17q,_17s=new T(function(){return E(_17k.d)<=_17q;}),_17t=new T(function(){return B(_SK(E(_17l),new T2(0,_17m,new T(function(){if(!E(_17r)){if(!E(_17s)){return new T2(0,_17n,_17p);}else{return new T0(1);}}else{return new T0(1);}})),E(_17h).a));});return (!E(_17r))?(!E(_17s))?(!B(_13V(_17l,_17m,_17n,_17p,E(_17g).a)))?new T3(0,_17h,_17k,_9):new T3(0,new T(function(){return new T2(0,_17t,E(_17h).b);}),_17k.f,new T2(1,new T3(3,_17l,_17m,_17n),_9)):new T3(0,new T(function(){return new T2(0,_17t,E(_17h).b);}),_17o,_9):new T3(0,new T(function(){return new T2(0,_17t,E(_17h).b);}),_17o,_9);case 2:var _17u=_17k.b,_17v=E(_17h),_17w=_17v.a,_17x=E(_17k.a),_17y=B(_14w(_17x,_17w));if(!_17y._){return new T3(0,_17v,_17k,_9);}else{var _17z=E(_17y.a),_17A=_17z.a,_17B=E(_17z.b);if(!_17B._){var _17C=_17B.a;return (!B(_Y0(_17x,_,_17A,_17C,E(_17g).b)))?new T3(0,_17v,_17k,_9):new T3(0,new T2(0,new T(function(){return B(_SK(_17x,new T2(0,_17A,_10b),_17w));}),_17v.b),_17u,new T2(1,new T3(4,_17x,_17A,_17C),_9));}else{return new T3(0,_17v,_17u,new T2(1,new T2(6,_17x,_17A),_9));}}break;case 3:var _17D=_17k.a,_17E=_17k.b,_17F=_17k.c,_17G=_17k.d,_17H=_17k.f,_17I=E(E(_17j).b);if(E(_17k.e)>_17I){var _17J=function(_17K){var _17L=E(_17G);if(E(_17K)!=_17L){return new T3(0,_17h,_17k,_9);}else{var _17M=E(_17h),_17N=_17M.a;if(B(_14g(_17N,_17E,_17I))<_17L){return new T3(0,_17M,_17H,new T2(1,new T4(2,_17D,_17E,_17F,_17L),_9));}else{var _17O=new T(function(){return B(_168(function(_17P){var _17Q=E(_17P),_17R=E(_17Q.b);return (_17R._==0)?(E(_17Q.a)!=E(_17E))?false:(E(_17R.b)>_17I)?true:false:false;},_17L,_17N));});return new T3(0,new T2(0,_17O,_17M.b),_17H,new T2(1,new T4(0,_17D,_17E,_17F,_17L),_9));}}},_17S=E(E(_17g).c);if(!_17S._){var _17T=_17S.d,_17U=_17S.e,_17V=E(_17S.b),_17W=E(_17D),_17X=E(_17V.a);if(_17W>=_17X){if(_17W!=_17X){var _17Y=B(_13J(_17W,_,_17F,_17U));if(!_17Y._){return new T3(0,_17h,_17k,_9);}else{return new F(function(){return _17J(_17Y.a);});}}else{var _17Z=E(_17F),_180=E(_17V.b);if(_17Z>=_180){if(_17Z!=_180){var _181=B(_13y(_17W,_,_17Z,_17U));if(!_181._){return new T3(0,_17h,_17k,_9);}else{return new F(function(){return _17J(_181.a);});}}else{return new F(function(){return _17J(_17S.c);});}}else{var _182=B(_13y(_17W,_,_17Z,_17T));if(!_182._){return new T3(0,_17h,_17k,_9);}else{return new F(function(){return _17J(_182.a);});}}}}else{var _183=B(_13J(_17W,_,_17F,_17T));if(!_183._){return new T3(0,_17h,_17k,_9);}else{return new F(function(){return _17J(_183.a);});}}}else{return new T3(0,_17h,_17k,_9);}}else{return new T3(0,_17h,_17H,new T2(1,new T4(1,_17D,_17E,_17F,_17G),_9));}break;case 4:var _184=new T(function(){var _185=B(_17f(_17g,_17h,_17k.a,_17j));return new T3(0,_185.a,_185.b,_185.c);}),_186=new T(function(){var _187=B(_17f(_17g,new T(function(){return E(E(_184).a);}),_17k.b,_17j));return new T3(0,_187.a,_187.b,_187.c);}),_188=new T(function(){return B(_c(E(_184).c,new T(function(){return E(E(_186).c);},1)));}),_189=new T(function(){var _18a=E(_184).b,_18b=E(_186).b,_18c=function(_18d){var _18e=E(_18b);switch(_18e._){case 0:return E(_18a);case 1:return new T2(4,_18a,_18e);case 2:return new T2(4,_18a,_18e);case 3:return new T2(4,_18a,_18e);case 4:return new T2(4,_18a,_18e);case 5:return new T2(4,_18a,_18e);default:return new T2(4,_18a,_18e);}};switch(E(_18a)._){case 0:return E(_18b);break;case 1:return B(_18c(_));break;case 2:return B(_18c(_));break;case 3:return B(_18c(_));break;case 4:return B(_18c(_));break;case 5:return B(_18c(_));break;default:return B(_18c(_));}});return new T3(0,new T(function(){return E(E(_186).a);}),_189,_188);case 5:return (!B(_16V(_17h,_17k.a,_17j)))?new T3(0,_17h,_17k.c,_9):new T3(0,_17h,_17k.b,_9);default:var _18f=E(_17j);return (E(_17k.b)>E(_18f.b))?(!B(_16V(_17h,_17k.a,_18f)))?new T3(0,_17h,_17k,_9):new T3(0,_17h,_17k.c,_9):new T3(0,_17h,_17k.d,_9);}},_18g=function(_18h,_18i,_18j,_18k){var _18l=new T(function(){var _18m=B(_11S(_18h,new T(function(){return E(E(_18i).a);},1),_18k));return new T2(0,_18m.a,_18m.b);}),_18n=new T(function(){var _18o=B(_137(new T(function(){return E(E(_18i).b);}),_9,E(_18h).d));return new T2(0,_18o.a,_18o.b);}),_18p=new T(function(){var _18q=new T(function(){var _18r=E(_18i);return new T2(0,new T(function(){return E(E(_18l).a);}),new T(function(){return E(E(_18n).a);}));}),_18s=B(_17f(_18h,_18q,_18j,_18k));return new T3(0,_18s.a,_18s.b,_18s.c);}),_18t=new T(function(){var _18u=new T(function(){return B(_c(E(_18l).b,new T(function(){return E(E(_18p).c);},1)));},1);return B(_c(E(_18n).b,_18u));});return new T3(0,new T(function(){return E(E(_18p).a);}),new T(function(){return E(E(_18p).b);}),_18t);},_18v=function(_18w,_18x,_18y,_18z,_18A,_18B){var _18C=new T2(0,_18x,_18y),_18D=B(_18g(_18w,_18C,_18z,_18A)),_18E=_18D.b,_18F=_18D.c,_18G=E(_18D.a),_18H=_18G.a,_18I=_18G.b,_18J=function(_18K){return new F(function(){return _18v(_18w,_18H,_18I,_18E,_18A,new T(function(){return B(_c(_18F,_18B));}));});};if(!B(A2(_X5,_18H,_18x))){return new F(function(){return _18J(_);});}else{if(!B(A2(_WB,_18I,_18y))){return new F(function(){return _18J(_);});}else{if(!B(_Vc(_18E,_18z))){return new F(function(){return _18J(_);});}else{if(!B(_Wi(_UT,_18F,_9))){return new F(function(){return _18J(_);});}else{return new T3(0,_18C,_18z,_18B);}}}}},_18L=new T(function(){return B(err(_kf));}),_18M=new T(function(){return B(err(_a));}),_18N=new T(function(){return B(A3(_eF,_f8,_ea,_k9));}),_18O=new T(function(){return B(err(_kf));}),_18P=new T(function(){return B(err(_a));}),_18Q=function(_M7){return new F(function(){return _eu(_fq,_M7);});},_18R=function(_18S,_18T){return new F(function(){return _Ln(_18Q,_18T);});},_18U=new T(function(){return B(_Ln(_18Q,_2Z));}),_18V=function(_M7){return new F(function(){return _1C(_18U,_M7);});},_18W=function(_18X){var _18Y=new T(function(){return B(A3(_eu,_fq,_18X,_2Z));});return function(_M4){return new F(function(){return _1C(_18Y,_M4);});};},_18Z=new T4(0,_18W,_18V,_18Q,_18R),_190=new T(function(){return B(unCStr("NotRedeemed"));}),_191=function(_192,_193){var _194=new T(function(){var _195=new T(function(){return B(A1(_193,_10b));});return B(_dD(function(_196){var _197=E(_196);return (_197._==3)?(!B(_2s(_197.a,_RV)))?new T0(2):E(_195):new T0(2);}));}),_198=function(_199){return E(_194);},_19a=new T(function(){if(E(_192)>10){return new T0(2);}else{var _19b=new T(function(){var _19c=new T(function(){var _19d=function(_19e){return new F(function(){return A3(_eF,_f8,_2o,function(_19f){return new F(function(){return A1(_193,new T2(0,_19e,_19f));});});});};return B(A3(_eF,_f8,_2o,_19d));});return B(_dD(function(_19g){var _19h=E(_19g);return (_19h._==3)?(!B(_2s(_19h.a,_190)))?new T0(2):E(_19c):new T0(2);}));}),_19i=function(_19j){return E(_19b);};return new T1(1,function(_19k){return new F(function(){return A2(_ck,_19k,_19i);});});}});return new F(function(){return _1M(new T1(1,function(_19l){return new F(function(){return A2(_ck,_19l,_198);});}),_19a);});},_19m=function(_M7){return new F(function(){return _eu(_191,_M7);});},_19n=function(_19o,_19p){return new F(function(){return _Ln(_19m,_19p);});},_19q=new T(function(){return B(_Ln(_19m,_2Z));}),_19r=function(_M7){return new F(function(){return _1C(_19q,_M7);});},_19s=function(_19t){var _19u=new T(function(){return B(A3(_eu,_191,_19t,_2Z));});return function(_M4){return new F(function(){return _1C(_19u,_M4);});};},_19v=new T4(0,_19s,_19r,_19m,_19n),_19w=function(_19x,_19y){return new F(function(){return _MC(_M5,_19v,_19y);});},_19z=new T(function(){return B(_Ln(_19w,_2Z));}),_19A=function(_M7){return new F(function(){return _1C(_19z,_M7);});},_19B=new T(function(){return B(_MC(_M5,_19v,_2Z));}),_19C=function(_M7){return new F(function(){return _1C(_19B,_M7);});},_19D=function(_19E,_M7){return new F(function(){return _19C(_M7);});},_19F=function(_19G,_19H){return new F(function(){return _Ln(_19w,_19H);});},_19I=new T4(0,_19D,_19A,_19w,_19F),_19J=function(_19K,_19L){return new F(function(){return _MC(_18Z,_19I,_19L);});},_19M=function(_19N,_19O){return new F(function(){return _Ln(_19J,_19O);});},_19P=new T(function(){return B(_Ln(_19M,_2Z));}),_19Q=function(_N7){return new F(function(){return _1C(_19P,_N7);});},_19R=function(_19S){return new F(function(){return _Ln(_19M,_19S);});},_19T=function(_19U,_19V){return new F(function(){return _19R(_19V);});},_19W=new T(function(){return B(_Ln(_19J,_2Z));}),_19X=function(_N7){return new F(function(){return _1C(_19W,_N7);});},_19Y=function(_19Z,_N7){return new F(function(){return _19X(_N7);});},_1a0=new T4(0,_19Y,_19Q,_19M,_19T),_1a1=new T(function(){return B(_MC(_1a0,_Nh,_k9));}),_1a2=new T(function(){return B(unAppCStr("[]",_9));}),_1a3=42,_1a4=new T2(1,_J,_9),_1a5=function(_1a6){var _1a7=E(_1a6);if(!_1a7._){return E(_1a4);}else{var _1a8=new T(function(){return B(_TY(0,_1a7.a,new T(function(){return B(_1a5(_1a7.b));})));});return new T2(1,_I,_1a8);}},_1a9=function(_){var _1aa=E(_PK),_1ab=eval(E(_mE)),_1ac=_1ab,_1ad=__app1(E(_1ac),toJSStr(_1aa)),_1ae=E(_Qa),_1af=__app1(E(_1ac),toJSStr(_1ae)),_1ag=__app0(E(_mz)),_1ah=E(_Qc),_1ai=__app1(E(_1ac),toJSStr(_1ah)),_1aj=new T(function(){var _1ak=B(_mo(B(_1C(_18N,new T(function(){var _1al=String(_1ai);return fromJSStr(_1al);})))));if(!_1ak._){return E(_18M);}else{if(!E(_1ak.b)._){return E(_1ak.a);}else{return E(_18L);}}}),_1am=B(_mo(B(_1C(_1a1,new T(function(){var _1an=String(_1af);return fromJSStr(_1an);})))));if(!_1am._){return E(_18P);}else{if(!E(_1am.b)._){var _1ao=E(_1am.a),_1ap=new T(function(){var _1aq=B(_mo(B(_1C(_ke,new T(function(){var _1ar=String(_1ag);return fromJSStr(_1ar);})))));if(!_1aq._){return E(_b);}else{if(!E(_1aq.b)._){return E(_1aq.a);}else{return E(_kg);}}}),_1as=new T(function(){var _1at=B(_mo(B(_1C(_PJ,new T(function(){var _1au=String(_1ad);return fromJSStr(_1au);})))));if(!_1at._){return E(_Lj);}else{if(!E(_1at.b)._){var _1av=E(_1at.a);return new T4(0,new T(function(){return B(_Ey(_1av.a));}),new T(function(){return B(_IV(_1av.b));}),new T(function(){return B(_AD(_1av.c));}),new T(function(){return B(_xt(_1av.d));}));}else{return E(_Li);}}}),_1aw=B(_18v(_1as,new T(function(){return B(_TD(_1ao.a));}),new T(function(){return B(_xt(_1ao.b));}),_1ap,new T2(0,_1a3,_1aj),_9)),_1ax=function(_,_1ay){var _1az=B(_4(_1,B(_Rm(_S5,_1aw.b,_9)),_)),_1aA=E(_1aw.a),_1aB=new T(function(){var _1aC=new T(function(){return B(_Ja(_9,_1aA.b));}),_1aD=new T(function(){return B(_Ja(_9,_1aA.a));});return B(A3(_K6,_Jh,new T2(1,function(_1aE){return new F(function(){return _Sm(_1aD,_1aE);});},new T2(1,function(_1aF){return new F(function(){return _KT(_1aC,_1aF);});},_9)),_KW));}),_1aG=B(_4(_1ae,new T2(1,_6T,_1aB),_)),_1aH=B(_4(_1aa,_Q8,_)),_1aI=B(_4(_1ah,B(_6U(0,E(_1aj)+1|0,_9)),_)),_1aJ=__app1(E(_1ac),toJSStr(E(_1)));return new F(function(){return _rQ(new T(function(){var _1aK=String(_1aJ);return fromJSStr(_1aK);}),_);});},_1aL=E(_1aw.c);if(!_1aL._){var _1aM=B(_4(_Q7,_1a2,_));return new F(function(){return _1ax(_,_1aM);});}else{var _1aN=new T(function(){return B(_TY(0,_1aL.a,new T(function(){return B(_1a5(_1aL.b));})));}),_1aO=B(_4(_Q7,new T2(1,_K,_1aN),_));return new F(function(){return _1ax(_,_1aO);});}}else{return E(_18O);}}},_1aP=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1aQ=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1aR=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1aS=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1aT=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1aU=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1aV=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1aW=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1aX=function(_){return new F(function(){return __jsNull();});},_1aY=function(_1aZ){var _1b0=B(A1(_1aZ,_));return E(_1b0);},_1b1=new T(function(){return B(_1aY(_1aX));}),_1b2=new T(function(){return E(_1b1);}),_1b3=function(_1b4,_1b5,_1b6,_){var _1b7=E(_PK),_1b8=eval(E(_mE)),_1b9=__app1(E(_1b8),toJSStr(_1b7)),_1ba=B(_mo(B(_1C(_PJ,new T(function(){var _1bb=String(_1b9);return fromJSStr(_1bb);})))));if(!_1ba._){return E(_Lj);}else{if(!E(_1ba.b)._){var _1bc=E(_1ba.a),_1bd=B(_L4(new T(function(){return B(_Ey(_1bc.a));},1),new T(function(){return B(_H4(_1b6,_1b4,_1b5,B(_IV(_1bc.b))));},1),new T(function(){return B(_AD(_1bc.c));},1),new T(function(){return B(_xt(_1bc.d));},1)));return new F(function(){return _4(_1b7,new T2(1,_1bd.a,_1bd.b),_);});}else{return E(_Li);}}},_1be=function(_){var _1bf=eval(E(_mE)),_1bg=__app1(E(_1bf),toJSStr(E(_1))),_1bh=B(_rQ(new T(function(){var _1bi=String(_1bg);return fromJSStr(_1bi);}),_)),_1bj=__createJSFunc(0,function(_){var _1bk=B(_Qd(_));return _1b2;}),_1bl=__app2(E(_1aR),"clear_workspace",_1bj),_1bm=__createJSFunc(0,function(_){var _1bn=B(_mA(_));return _1b2;}),_1bo=__app2(E(_1aQ),"b2c",_1bm),_1bp=__createJSFunc(0,function(_){var _1bq=B(_rY(_));return _1b2;}),_1br=__app2(E(_1aP),"c2b",_1bp),_1bs=function(_1bt){var _1bu=new T(function(){var _1bv=Number(E(_1bt));return jsTrunc(_1bv);}),_1bw=function(_1bx){var _1by=new T(function(){var _1bz=Number(E(_1bx));return jsTrunc(_1bz);}),_1bA=function(_1bB){var _1bC=new T(function(){var _1bD=Number(E(_1bB));return jsTrunc(_1bD);}),_1bE=function(_1bF,_){var _1bG=B(_Qj(_1bu,_1by,_1bC,new T(function(){var _1bH=Number(E(_1bF));return jsTrunc(_1bH);}),_));return _1b2;};return E(_1bE);};return E(_1bA);};return E(_1bw);},_1bI=__createJSFunc(5,E(_1bs)),_1bJ=__app2(E(_1aW),"commit",_1bI),_1bK=function(_1bL){var _1bM=new T(function(){var _1bN=Number(E(_1bL));return jsTrunc(_1bN);}),_1bO=function(_1bP){var _1bQ=new T(function(){var _1bR=Number(E(_1bP));return jsTrunc(_1bR);}),_1bS=function(_1bT,_){var _1bU=B(_1b3(_1bM,_1bQ,new T(function(){var _1bV=Number(E(_1bT));return jsTrunc(_1bV);}),_));return _1b2;};return E(_1bS);};return E(_1bO);},_1bW=__createJSFunc(4,E(_1bK)),_1bX=__app2(E(_1aV),"redeem",_1bW),_1bY=function(_1bZ){var _1c0=new T(function(){var _1c1=Number(E(_1bZ));return jsTrunc(_1c1);}),_1c2=function(_1c3){var _1c4=new T(function(){var _1c5=Number(E(_1c3));return jsTrunc(_1c5);}),_1c6=function(_1c7,_){var _1c8=B(_PW(_1c0,_1c4,new T(function(){var _1c9=Number(E(_1c7));return jsTrunc(_1c9);}),_));return _1b2;};return E(_1c6);};return E(_1c2);},_1ca=__createJSFunc(4,E(_1bY)),_1cb=__app2(E(_1aU),"claim",_1ca),_1cc=function(_1cd){var _1ce=new T(function(){var _1cf=Number(E(_1cd));return jsTrunc(_1cf);}),_1cg=function(_1ch){var _1ci=new T(function(){var _1cj=Number(E(_1ch));return jsTrunc(_1cj);}),_1ck=function(_1cl,_){var _1cm=B(_PL(_1ce,_1ci,new T(function(){var _1cn=Number(E(_1cl));return jsTrunc(_1cn);}),_));return _1b2;};return E(_1ck);};return E(_1cg);},_1co=__createJSFunc(4,E(_1cc)),_1cp=__app2(E(_1aT),"choose",_1co),_1cq=__createJSFunc(0,function(_){var _1cr=B(_1a9(_));return _1b2;}),_1cs=__app2(E(_1aS),"execute",_1cq);return _0;},_1ct=function(_){return new F(function(){return _1be(_);});};
var hasteMain = function() {B(A(_1ct, [0]));};window.onload = hasteMain;