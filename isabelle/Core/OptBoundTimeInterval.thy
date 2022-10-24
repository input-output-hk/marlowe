theory OptBoundTimeInterval
  imports Semantics 
begin

text \<open>The \<^emph>\<open>OptBoundTimeInterval\<close> is a \<^emph>\<open>TimeInterval\<close> with optional lower and higer bounds.
If bounded, the interval endpoints are closed. There are four possible options

\<^item> Totally unbound: (-\<infinity>, \<infinity>)
\<^item> Left bound [low, \<infinity>)
\<^item> Right bound (-\<infinity>, high]
\<^item> Bound [low, high].
\<close>
datatype OptBoundTimeInterval = OptBoundTimeInterval "POSIXTime option \<times> POSIXTime option"


text
\<open>
The \<^emph>\<open>combineIntervals\<close> function will merge two optionally bounded intervals into one.
For both the low and high endpoint, prefer bounded to unbounded.
When both intervals are totally bounded, we get the intersection
combineIntervals (-\<infinity>, \<infinity>) (-\<infinity>, \<infinity>) =  (-\<infinity>, \<infinity>)
combineIntervals (-\<infinity>, \<infinity>) [l, h] = [l, h]
combineIntervals [l, h] (-\<infinity>, \<infinity>) = [l, h]
combineIntervals [l1, h1] [l2, h2] = [max l1 l2, min h1 h2]


Q: should this be called intersect?
Q: Is this Semigroup (*) and monoid with 1 == (-\<infinity>, \<infinity>)?
\<close>
function combineIntervals :: "OptBoundTimeInterval \<Rightarrow> OptBoundTimeInterval \<Rightarrow> OptBoundTimeInterval"
and maxLow
and minHigh
where
 "maxLow None y = y"
| "maxLow x None = x"
| "maxLow (Some x) (Some y) = (Some (max x y))"

| "minHigh None y = y"
| "minHigh x None = x"
| "minHigh (Some x) (Some y) = (Some (min x y))"

| "combineIntervals (OptBoundTimeInterval (low1, high1)) (OptBoundTimeInterval (low2, high2))
    = OptBoundTimeInterval
        (maxLow low1 low2, minHigh high1 high2)"

  by (metis Option.option.exhaust Product_Type.old.prod.exhaust Semantics.OptBoundTimeInterval.exhaust Sum_Type.old.sum.exhaust) auto
termination  by lexicographic_order


fun gtIfNone :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"gtIfNone None _ = True" |
"gtIfNone (Some x) y = (x > y)"

fun geIfNone :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"geIfNone None _ = True" |
"geIfNone (Some x) y = (x \<ge> y)"

fun subIfSome :: "int option \<Rightarrow> int \<Rightarrow> int option" where
"subIfSome None _ = None" |
"subIfSome (Some x) y = Some (x - y)"

text
\<open>
The type of the function calculateTimeInterval is Maybe Integer -> POSIXTime -> Contract -> (Maybe POSIXTime, Maybe POSIXTime)
 where the Integer would be the number of inputs to consider (where Nothing means an arbitrary number),
the first POSIXTime would be a point in the interval (typically the current time),
the Contract would be the current remaining contract, and the tuple of POSIXTime resulting would be
the maximum interval for the given parameters, where Nothing would signal the interval is unbounded in that side.
\<close>
fun calculateTimeInterval :: "int option \<Rightarrow> POSIXTime \<Rightarrow> Contract \<Rightarrow> OptBoundTimeInterval"
where
"calculateTimeInterval _ _ Close = OptBoundTimeInterval (None, None)" |
"calculateTimeInterval n t (Pay _ _ _ _ c) = calculateTimeInterval n t c" |
"calculateTimeInterval n t (If _ ct cf) = combineIntervals (calculateTimeInterval n t ct)
                                                           (calculateTimeInterval n t cf)" |
"calculateTimeInterval n t (When Nil timeout tcont) =
  (if t < timeout
   then OptBoundTimeInterval (None, (Some (timeout - 1)))
   else combineIntervals (OptBoundTimeInterval (Some timeout, None)) (calculateTimeInterval n t tcont))" |
"calculateTimeInterval n t (When (Cons (Case _ cont ) tail) timeout tcont) =
  (if gtIfNone n 0
   then combineIntervals (calculateTimeInterval (subIfSome n 1) t cont)
                         (calculateTimeInterval n t (When tail timeout tcont))
   else calculateTimeInterval n t (When tail timeout tcont))" |
"calculateTimeInterval n t (Let _ _ c) = calculateTimeInterval n t c" |
"calculateTimeInterval n t (Assert _ c) = calculateTimeInterval n t c"



end