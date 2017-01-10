module Queues

(* Queue implementation Okasaki's style: 2 lists,
   the front list which represents the front of the queue where to retrieve elements,
   the back list, kept reversed, which represents the back of the queue.
   As suggested by Okasaki I impose the invariant on the size of the 2 lists :
   the front size must not be smaller than the back one.
   http://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf
*)

(* As implemented in fstar/example/data_structures/Vector.fst *)
type sList 'a : nat -> Type =
  | Nil  : sList 'a 0
  | Cons : hd:'a -> #n:nat ->  sList 'a n -> sList 'a (n+1)

(* Im trying to provide examples all over the file to double-check im doing right *)

let okSl1 = Cons 2 Nil
let okSl2 = Nil 
let okSl3 = Cons 1 okSl1

(* A function to retrieve the carried size of the list *)

val size : #a:Type -> #n:nat -> sList a n -> Tot nat
let size #a #n _ = n 

let okSize   = assert (size okSl1 = 1) //accepted
//let badSize  = assert (size okSl3 = 3) should be 2 so not accepted (OK)
let okSize2 = assert (size okSl3 = 2) //accepted


(* We now need a couple of functions to retrieve the elements of the list. *)

(* n must be pos cause we dont allow the call of on empty lists *)

val hd : #a:Type -> #n:pos -> sl:sList a n -> Tot a
let hd #a #n sl = match sl with
  | Cons h _ -> h

//let el1 = hd Nil not accepted (OK)
let el2 = hd okSl1 //accepted

val tl : #a:Type -> #n:pos -> sList a n -> Tot (sList a (n-1))
let tl #a #n sl = match sl with
  | Cons _ rest -> rest

// let badTl = tl Nil not accepted (OK)
let okTl  = tl okSl1 //accepted

(* reverse and append needed for the remove and insert operations on the queue *)

val append : #a:Type -> #n1:nat -> #n2:nat -> 
             sList a n1 -> sList a n2 ->
             Tot(sList a (n1+n2))
let rec append #a #n1 #n2 sl1 sl2 = match sl1 with
  | Nil         -> sl2
  | Cons h rest -> Cons h (append rest sl2)

val reverse : #a:Type -> #n:nat -> sList a n -> 
              Tot(sList a n)
let rec reverse #a #n sl = match sl with
  | Nil         -> Nil 
  | Cons h rest -> append (reverse rest) (Cons h Nil)

let okReverse = assert (reverse okSl3 = Cons 2 (Cons 1 Nil)) //accepted
//let badReverse = assert (reverse okSl1 = Nil) not accepted (OK)

(* Let's now give a queue type made up of 2 sized Lists imposing that the size of the
first list (the front of the queue) is never smaller than the second one (the back) *)

(* Important Note!!! The type given  after this comment  doesn't accept the binding
let emptyQ = Q Nil Nil 
but verifies the makeQ function.
If I change this to:
type queue 'a =
  | Q : #n1:nat -> #n2:nat{n2 <= n1} -> front:sList 'a n1 -> back:sList 'a n2 -> queue 'a
that is I just moved the refinment from the back list to #n2, it does accept the emptyQ
declaration but it wont verify the makeQ function (written later)
*)
type queue 'a =
  | Q : #n1:nat -> #n2:nat -> front:sList 'a n1 -> back:sList 'a n2{n2 <= n1} -> queue 'a

//let emptyQ = Q Nil Nil not accepted but it should
let okQ = Q okSl1 Nil //accepted
// let badQ = Q Nil okSl1 not accepted the first list is shorter (OK)

(* In order to transfer the element from the back to the front we give a rotate function.
Mind that this function is only called when the front list is one element smaller than the
back so as the re-balance them. The refinment {n2 > n1 ==> n2 = n1 + 1} is needed for the 
makeQ function and it's explained in the next comment. What i actually need though is proving
that rotate is actually called only when size back = size front + 1, but with this refinment
the makeQ function wouldn't work.

****************************Question: How can I do that???? **********************)

val rotate : #a:Type -> #n1:nat -> #n2:nat ->
             f:sList a n1 -> b:sList a n2{n2 > n1 ==> n2 = n1 + 1} -> Tot (sList a (n1 + n2))
let rotate #a #n1 #n2 f b = append f (reverse b)

(* Let's now implement a queue constructor in charge of preserving the invariant.
The makeQ function is called after every operation on the queue.
Note that by using n2:nat{n2 > n1 ==> n2 = n1 + 1} what I would like to say is : 
IF the back list is bigger the front than it can only have 1 element more than it.
Otherwise ,that is if n1 happens to be bigger or equal to n2,  then n1 and n2 can have any nat value.
****************** Question: Is that true? How can I impose that otherwise? **************)

val qSize : queue 'a -> Tot nat
let qSize (Q f b) = size f + size b 

let okqSize = assert (qSize okQ = 1) // accepted
// let badqSize = assert (qSize okQ = 2) not accepted (OK)

val makeQ : #a:Type -> #n1:nat -> #n2:nat{n2 > n1 ==> n2 = n1 + 1} ->
            f:sList a n1 -> b:sList a n2 -> Tot (q:queue a{qSize q = n1 + n2})
let makeQ #a #n1 #n2 f b =
  if n1 < n2  then Q (rotate f b) Nil
  else Q f b

(* recall that : okSl1 = [2] ; okSl3 = [1;2] ; okSl2 = [] *)
let okMakeQ1 = assert (Q (Cons 2(Cons 2(Cons 1 Nil))) Nil = makeQ okSl1 okSl3) 
let okMakeQ2 = assert (Q (Cons 1(Cons 2 Nil)) (Cons 2 Nil) = makeQ okSl3 okSl1) 
// let okMakeQ3 = assert (Q Nil Nil = makeQ okSl2 okSl2) //not accepted but it should 

(* Ok now the 2 main operations on the queue : insert and remove. 
To insert an element we just Cons it to be back list *)

val insert : #a:Type -> el:a -> q1:queue a -> Tot (q2:queue a{qSize q2 = qSize q1 + 1})
let insert #a el q = match q with
  | Q f b -> makeQ f (Cons el b)

(* If the queues is not empty than the front list must at least have one element because of the invariant *)

val notEmpty : queue 'a -> Tot bool
let notEmpty (Q f _) = size f > 0

(* To remove an element we just 'unCons' it from the front list *)

(* This function cannot be verified as it is, because hd and tl have a subtype error :
they expect a pos sList but they got a nat sList. For this reason I imposed q1 not to be empty
which means size f > 0 that is f has pos size. Despite this, the check does not work.
I understand that, maybe, a Lemma is needed to prove that.
Something like :
if the queue is not empty than the call of hd and tl on the front list is safe.
*************************** Question : How can i do that?? ********************************

val remove : #a:Type -> q1:queue a{notEmpty q1} -> Tot (el:a * q2:queue a{qSize q2 = qSize q1 - 1})
let remove #a q = match q with
  | Q f b -> hd f, makeQ (tl f) b
  
*)  
