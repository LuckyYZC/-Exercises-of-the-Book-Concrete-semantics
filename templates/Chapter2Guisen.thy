theory Chapter2Guisen
imports Main
begin

text\<open>
\section*{Chapter 2}

\exercise
Use the \textbf{value} command to evaluate the following expressions:
\<close>

value  "1 + (2::nat)"
value  "1 + (2::int)"
value  "1 - (2::nat)"
value  "1 - (2::int)"
value  "[a,b] @ [c,d]"

text\<open>
\endexercise


\exercise
Recall the definition of our own addition function on @{typ nat}:
\<close>

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

text\<open>
Prove that @{const add} is associative and commutative.
You will need additional lemmas.
\<close>

lemma add_assoc: "add (add m n) p = add m (add n p)"
(* your definition/proof here *)
apply(induction m)
apply(auto)

(*<*)
done
(*>*)


lemma add_comm [simp]: "add m n = add n m"
(* your definition/proof here *)
apply(induction m)
apply(auto)

(*<*)
oops
(*>*)

lemma add_zero [simp]: "add n 0 = n"
apply(induction n)
apply(auto)
done
(*<*)
(*>*)

lemma add_suc [simp]: "add n (Suc m) = Suc (add n m)"
apply(induction n)
apply(auto)
(*<*)
done
(*>*)

lemma add_comm [simp]: "add m n = add n m"
(* your definition/proof here *)
apply(induction m)
apply(auto)

text\<open> Define a recursive function \<close>
(*<*)
done
(*>*)
fun double :: "nat \<Rightarrow> nat" where
(* your definition/proof here *)
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

text\<open> test \<close>
value  "double 2"
text\<open> and prove that \<close>

lemma double_add: "double m = add m m"
(* your definition/proof here *)
apply(induction m)
apply(auto)
done
text\<open>
\endexercise


\exercise
Define a function that counts the number of occurrences of
an element in a list:
\<close>

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count Nil x = 0" |
"count (Cons x xs) z = (if x=z then Suc(count xs z) else count xs z)"


(* your definition/proof here *)
text \<open>
Test your definition of @{term count} on some examples.
Prove the following inequality:
\<close>

theorem "count xs x \<le> length xs"
(* your definition/proof here *)
apply(induction xs)
apply(auto)
done
text\<open>
\endexercise


\exercise
Define a function @{text snoc} that appends an element to the end of a list.
Do not use the existing append operator @{text "@"} for lists.
\<close>

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
(* your definition/proof here *)
"snoc Nil z = Cons z Nil"|
"snoc (Cons x xs) z = Cons x (snoc xs z)"
text \<open>
Convince yourself on some test cases that your definition
of @{term snoc} behaves as expected.
With the help of @{text snoc} define a recursive function @{text reverse}
that reverses a list. Do not use the predefined function @{const rev}.
\<close>

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil"|
"reverse (Cons x xs) =snoc (reverse xs) x"
(* your definition/proof here *)

text \<open>
Prove the following theorem. You will need an additional lemma.
\<close>
theorem "reverse (reverse xs) = xs"
(* your definition/proof here *)
apply(induction xs)
apply(auto)
(*<*)oops(*>*)
lemma reverse_snoc[simp]: "reverse (snoc xs x)=Cons x (reverse xs)"
apply(induction xs)
apply(auto)
(*<*)done(*>*)
theorem "reverse (reverse xs) = xs"
(* your definition/proof here *)
apply(induction xs)
apply(auto)
(*<*)oops(*>*)
text\<open>
\endexercise


\exercise
The aim of this exercise is to prove the summation formula
\[ \sum_{i=0}^{n}i = \frac{n(n+1)}{2} \]
Define a recursive function @{text "sum_upto n = 0 + ... + n"}:
\<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0"|
"sum_upto (Suc n) = (Suc n)+ (sum_upto n)"
(* your definition/proof here *)

text \<open>
Now prove the summation formula by induction on @{text "n"}.
First, write a clear but informal proof by hand following the examples
in the main text. Then prove the same property in Isabelle:
\<close>

lemma "sum_upto n = n * (n+1) div 2"
(* your definition/proof here *)
apply(induction n)
apply(auto)
(*<*)done(*>*)
text\<open>
\endexercise


\exercise
Starting from the type @{text "'a tree"} defined in the text, define
a function that collects all values in a tree in a list, in any order,
without removing duplicates.
\<close>
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = Nil"|
"contents (Node l a r) = (contents l) @ (Cons a (contents r))"
(* your definition/proof here *)

text\<open>
Then define a function that sums up all values in a tree of natural numbers
\<close>

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0"|
"sum_tree (Node l a r) = (sum_tree l) + a + (sum_tree r)"
(* your definition/proof here *)

text\<open> and prove \<close>

lemma "sum_tree t = sum_list(contents t)"
(* your definition/proof here *)
apply(induction t)
apply(auto)
(*<*)done(*>*)
text\<open>
\endexercise

\exercise
Define a new type @{text "'a tree2"} of binary trees where values are also
stored in the leaves of the tree.  Also reformulate the
@{text mirror} function accordingly. Define two functions \<close>

datatype 'a tree2 = Tip 'a | Node  "'a tree2"  'a  "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Tip a) = Tip a" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
(* your definition/proof here *)
"pre_order (Tip x) = Cons x Nil"|
"pre_order (Node l a r) =(Cons a Nil) @ (pre_order l) @  (pre_order r)"


fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
(* your definition/proof here *)
"post_order (Tip x) = Cons x Nil"|
"post_order (Node l a r) = (post_order l) @ (post_order r) @ (Cons a Nil)"
text\<open>
that traverse a tree and collect all stored values in the respective order in
a list. Prove \<close>

lemma "pre_order (mirror t) = rev (post_order t)"
(* your definition/proof here *)
apply(induction t)
apply(auto)
(*<*)done(*>*)
text\<open>
\endexercise

\exercise
Define a recursive function
\<close>

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
(* your definition/proof here *)
"intersperse z Nil = Cons z Nil"|
"intersperse z (Cons x xs) = Cons z (Cons x (intersperse z xs))"

text\<open>
such that @{text "intersperse a [x\<^sub>1, ..., x\<^sub>n] = [x\<^sub>1, a, x\<^sub>2, a, ..., a, x\<^sub>n]"}.
Prove
\<close>

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
(* your definition/proof here *)
apply(induction xs)
apply(auto)
(*<*)done(*>*)
text\<open>
\endexercise


\exercise
Write a tail-recursive variant of the @{text add} function on @{typ nat}:
\<close>

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n"|
"itadd (Suc m) n = itadd m (Suc n)"
(* your definition/proof here *)

text\<open>
Tail-recursive means that in the recursive case, @{const itadd} needs to call
itself directly: \mbox{@{term"itadd (Suc m) n"}} @{text"= itadd \<dots>"}.
Prove
\<close>

lemma "itadd m n = add m n"
(* your definition/proof here *)
apply(induction m arbitrary:n)
apply(auto)
(*<*)done(*>*)
text\<open>
\endexercise


\exercise\label{exe:tree0}
Define a datatype @{text tree0} of binary tree skeletons which do not store
any information, neither in the inner nodes nor in the leaves.
Define a function that counts the number of all nodes (inner nodes and leaves)
in such a tree:
\<close>

(*<*)
datatype tree0 = Tip | Node tree0 tree0
(*>*)

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1"|
"nodes (Node l r) = (nodes l) + (nodes r)+1"
(* your definition/proof here *)

text \<open>
Consider the following recursive function:
\<close>

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

text \<open>
Experiment how @{text explode} influences the size of a binary tree
and find an equation expressing the size of a tree after exploding it
(\noquotes{@{term [source] "nodes (explode n t)"}}) as a function
of @{term "nodes t"} and @{text n}. Prove your equation.
You may use the usual arithmetic operations including the exponentiation
operator ``@{text"^"}''. For example, \noquotes{@{prop [source] "2 ^ 2 = 4"}}.

Hint: simplifying with the list of theorems @{thm[source] algebra_simps}
takes care of common algebraic properties of the arithmetic operators.
\endexercise
\<close>

text\<open>test\<close>
value  "nodes (explode 2 Tip )"

lemma num_ex: "nodes (explode n t ) = ((nodes t) * (2^n))+(2^(n)-1)"

apply(induction n arbitrary:t)
apply(auto simp add:algebra_simps)
(*<*)done(*>*)
text\<open>

\exercise
Define arithmetic expressions in one variable over integers (type @{typ int})
as a data type:
\<close>

datatype exp = Var | Const int | Add exp exp | Mult exp exp

text\<open>
Define a function @{text eval} that evaluates an expression at some value:
\<close>

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x"|
"eval (Const y) x = y"|
"eval (Add z w) x = (eval z x) + (eval w x)"|
"eval (Mult u v) x = (eval u x) * (eval v x)"
(* your definition/proof here *)

text\<open>
For example, @{prop"eval (Add (Mult (Const 2) Var) (Const 3)) i = 2*i+3"}.

A polynomial can be represented as a list of coefficients, starting with
the constant. For example, @{term "[4, 2, -1, 3::int]"} represents the
polynomial $4 + 2x - x^2 + 3x^3$.
Define a function @{text evalp} that evaluates a polynomial at a given value:
\<close>

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp Nil z = 0"|
"evalp (Cons x xs) z = x + (evalp xs z)*z"
(* your definition/proof here *)

text\<open>
Define a function @{text coeffs} that transforms an expression into a polynomial.
This will require auxiliary functions.
\<close>
text\<open>test\<close>
value "eval (Add (Mult (Const 2) Var) (Const 3)) i"

fun addp :: "int list \<Rightarrow>int list \<Rightarrow>int list " where
"addp Nil xs = xs"|
"addp xs Nil = xs"|
"addp (Cons x xs) (Cons z zw)= Cons (x + z) (addp xs zw)"

fun multpre ::  "int list \<Rightarrow>int \<Rightarrow>int list " where
"multpre Nil z = Nil"|
"multpre  (Cons x xs) z= Cons (x*z) (multpre xs z) "
fun multp :: "int list \<Rightarrow>int list \<Rightarrow>int list " where  
"multp zw Nil = Nil"|
"multp  zw (Cons x xs) = (if zw=Nil then Nil else (addp(multpre zw x) (Cons 0 (multp zw xs))))"

fun coeffs :: "exp \<Rightarrow> int list" where
(* your definition/proof here *)
"coeffs Var = Cons 0 (Cons 1 Nil)"|
"coeffs (Const y) = Cons y Nil"|
"coeffs (Add z w) = (addp (coeffs z) (coeffs w))"|
"coeffs (Mult u v) = (multp (coeffs u) (coeffs v))"
text\<open>
Prove that @{text coeffs} preserves the value of the expression:
\<close>

value "coeffs (Add (Mult (Const 2) Var) (Const 3))"

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
(* your definition/proof here *)
  apply(induction e)
apply(auto simp add:algebra_simps split:exp.split)
(*<*)oops(*>*)
lemma addp[simp]: "evalp (addp z w) x =(evalp z x) + (evalp w x)"
apply(induction w  rule:addp.induct)
    apply(auto simp add:algebra_simps)
(*<*)done(*>*)
lemma multpre[simp]: "evalp (multpre z a) x = a * evalp z x"
apply(induction z a rule:multpre.induct)
apply(auto simp add:algebra_simps)
(*<*)done(*>*)
lemma multp[simp]: "evalp (multp z w) x =(evalp z x) * (evalp w x)"
apply(induction w arbitrary:x z)
apply(auto simp add:algebra_simps)
(*<*)done(*>*)
theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
(* your definition/proof here *)
  apply(induction e)
apply(auto simp add:algebra_simps split:exp.split)
(*<*)done(*>*)
text\<open>
Hint: consider the hint in Exercise~\ref{exe:tree0}.
\endexercise
\<close>

end

