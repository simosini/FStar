module BinarySearchTree

(* first we need to add a type tree. I decided to use int BST to start with to keep it as simple as possible. For the moment the simpler the better *)

type tree =
  | Leaf : tree
  | Node : v:int -> tree -> tree -> tree

(* I now add the basic function on a Bst using refinement types.
The functions are:
- val search
- val insert
- val count
plus some helper function used to verify their correctness *)

(* this function will be replaced by search but it's needed by the foreach function
in order to work otherwise the smt solver wont verify it and it gives also 
the chance to verify the search function itself *)

val contains : x:int -> tree -> Tot bool
let rec contains x t =
  match t with
  | Leaf -> false
  | Node v l r -> v = x || contains x l || contains x r

(* this one checks that a predicate is true for all nodes. 
Basically the results (res) is true iff for all nodes contained in the tree
the predicate is true*)

val foreach : f:(int -> Tot bool) -> t:tree -> 
                Tot (res:bool{res <==> (forall x. contains x t ==> f x)})
let rec foreach f t =
  match t with
  | Leaf -> true
  | Node v l r -> f v && foreach f l && foreach f r

(* Two simple functions to increase readability *)

val smaller : int -> int -> Tot bool
let smaller v1 v2 = v1 < v2

val bigger : int -> int -> Tot bool
let bigger v1 v2 = v1 > v2

(* this one checks the basic property of a BST : every node in the left subtree contains smaller values
and every right subtree contains bigger ones 
e.g 
           4                                          4
          / \                                        / \
         2   6  this is a correct BST               3   2  this is not
        / \
       1   3                *)

val is_bst : t:tree -> Tot bool
let rec is_bst t = 
  match t with
  | Leaf -> true
  | Node v l r -> foreach (bigger v) l && foreach (smaller v) r && is_bst l && is_bst r

(* this function yields true iff the tree is a proper BST and the contains fun is true *)

val search : x:int -> t:tree{is_bst t} -> Tot (res:bool{res <==> contains x t})
let rec search x t = 
  match t with 
  | Leaf -> false
  | Node v l r -> if      (smaller x v) then search x l
                  else if (bigger x v)  then search x r
                  else                  true

(* the insert function must yield a valid BST and every elements of the old 
tree must be contained in the new one *)

val insert : x:int -> t:tree{is_bst t} -> 
    Tot (t1:tree{is_bst t1 /\ (forall y. contains y t1 <==> contains y t \/ y=x)})
let rec insert x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node v l r -> if      (smaller x v) then Node v (insert x l) r
                  else if (bigger x v)  then Node v l (insert x r)
                  else                  t

(* just a counting function that yields the number of nodes of the BST *)

val count : t:tree{is_bst t} -> Tot nat
let rec count t =
  match t with
  | Leaf -> 0
  | Node v l r -> 1 + count l + count r


