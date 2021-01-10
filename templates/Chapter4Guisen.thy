theory Chapter4Guisen

imports "HOL-IMP.ASM"

begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

text\<open>
\section*{Chapter 4}

\exercise
Start from the data type of binary trees defined earlier:
\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text\<open>
An @{typ "int tree"} is ordered if for every @{term "Node l i r"} in the tree,
@{text l} and @{text r} are ordered
and all values in @{text l} are @{text "< i"}
and all values in @{text r} are @{text "> i"}.
Define a function that returns the elements in a tree and one
that tests if a tree is ordered:
\<close>

fun set :: "'a tree \<Rightarrow> 'a set"  where
(* your definition/proof here *)
"set Tip = {}"|
"set (Node l i r) = (set l) \<union> {i} \<union> (set r)"

text\<open>test\<close>
value "set ((Node Tip (2::int)) Tip)"

fun ord :: "int tree \<Rightarrow> bool"  where
(* your definition/proof here *)
"ord Tip = True"|
"ord (Node l i r) = ((\<forall>x\<in>(set l).i>x)\<and>(\<forall>y\<in>(set r).(y>i))\<and>(ord l)\<and>(ord r) )"

text\<open>test\<close>
value "ord (Node Tip ((- 1)::int) (Node Tip (- 1) Tip))"


text\<open> Hint: use quantifiers.

"ord (Node l i r) = ((\<forall>x\<in>(set l).i>x)\<and>(\<forall>y\<in>(set r).(y>i))\<and>(ord l)\<and>(ord r) )"

"ord (Node l i r) = ( ( \<forall>x\<in>(set l).( \<forall>y\<in>(set r).(y>i\<and>i>x) ) ) \<and> (ord l) \<and> (ord r) )" why?

Define a function @{text ins} that inserts an element into an ordered @{typ "int tree"}
while maintaining the order of the tree. If the element is already in the tree, the
same tree should be returned.
\<close>

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree"  where
(* your definition/proof here *)
"ins a Tip =  Node Tip a Tip "|
"ins a (Node l i r) = (if a<i then (Node (ins a l) i r) else if a=i then (Node l i r) else (Node l i (ins a r)))"

text\<open>test\<close>
value "ins (-3) (Node Tip ((- 1)::int) (Node Tip (- 1) Tip))"
value "ord (ins (-3) (Node Tip ((- 1)::int) (Node Tip (- 1) Tip))) "


text\<open> Prove correctness of @{const ins}: \<close>

lemma set_ins: "set(ins x t) = {x} \<union> set t"
(* your definition/proof here *)
apply(induction t arbitrary:x)
apply(auto)
(*<*)done(*>*)
theorem ord_ins: "ord t \<Longrightarrow> ord(ins i t)"
(* your definition/proof here *)
apply(induction t rule:ord.induct)
apply(auto simp add:set_ins)
(*<*)done(*>*)
text\<open>
\endexercise

\exercise
Formalize the following definition of palindromes
\begin{itemize}
\item The empty list and a singleton list are palindromes.
\item If @{text xs} is a palindrome, so is @{term "a # xs @ [a]"}.
\end{itemize}
as an inductive predicate
\<close>

inductive palindrome :: "'a list \<Rightarrow> bool" where
(* your definition/proof here *)
palindrome0: "palindrome (Nil)"|
palindrome1: "palindrome ([a])"|
palindromeSS: "(palindrome xs) \<Longrightarrow> (palindrome (a # xs @ [a]))"
text \<open> and prove \<close>

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
(* your definition/proof here *)
apply(induction rule:palindrome.induct)
apply(auto)
(*<*)done(*>*)
text\<open>
\endexercise

\exercise
We could also have defined @{const star} as follows:
\<close>

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

text\<open>
The single @{text r} step is performer after rather than before the @{text star'}
steps. Prove
\<close>

lemma star_trans [simp]: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
(*<*)
defer
apply(rename_tac u x y)
defer
(*>*)
apply(assumption)
apply(metis step)
done
lemma star'_tran: "star' r x y \<Longrightarrow>star' r y z \<Longrightarrow> star' r x z"
apply(induction rule: star'.induct)
(*<*)
defer
apply(rename_tac u x y)
defer
(*>*)
apply(assumption)
(*<*)oops(*>*)
lemma star_01 [simp]: "r x y \<Longrightarrow>star r x y"
  by (simp add: star.refl star.step)

lemma star_02: "star' r x y \<Longrightarrow> star r x y"
(* your definition/proof here *)
apply(induction rule: star'.induct)
apply (simp add: star.refl)
apply(auto)
done

lemma star'_01 [simp]: "r x y \<Longrightarrow>star' r x y"
sledgehammer
by (meson refl' step')

lemma star'_trans [simp]: "r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"
sledgehammer
  by (meson star'_01 step')

lemma star_trans_02 [simp]: "star r x y \<Longrightarrow>  r y z \<Longrightarrow> star r x z"
sledgehammer
  by simp


lemma star'_trans' [simp]: "star' r y z \<Longrightarrow>star' r x y \<Longrightarrow> star' r x z"
apply(induction rule: star'.induct)
sledgehammer
apply simp
sledgehammer
by (simp add: step')



lemma "star r x y \<Longrightarrow> star' r x y"
(* your definition/proof here *)
apply(induction rule: star.induct)
   apply (simp add: star'.refl')
sledgehammer
  by (meson refl' star'_trans' step')
text\<open>
You may need lemmas. Note that rule induction fails
if the assumption about the inductive predicate
is not the first assumption.
\endexercise

\exercise\label{exe:iter}
Analogous to @{const star}, give an inductive definition of the @{text n}-fold iteration
of a relation @{text r}: @{term "iter r n x y"} should hold if there are @{text x\<^sub>0}, \dots, @{text x\<^sub>n}
such that @{prop"x = x\<^sub>0"}, @{prop"x\<^sub>n = y"} and @{text"r x\<^bsub>i\<^esub> x\<^bsub>i+1\<^esub>"} for
all @{prop"i < n"}:
\<close>

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
(* your definition/proof here *)
it_refl:  "iter r 0 x x" |
it_step:  "iter r n x y \<Longrightarrow>r y z \<Longrightarrow> iter r (n+1) x z"
text\<open>
Correct and prove the following claim:
\<close>
lemma iter_trans [simp]: "iter r n y z \<Longrightarrow>iter r 1 x y \<Longrightarrow> iter r (n+1) x z"
  apply(induction rule: iter.induct)

   apply simp

  by (meson it_step)
lemma iter_01 [simp]: "r x y \<Longrightarrow>iter r 1 x y"

  using it_refl it_step by fastforce


lemma "star r x y \<Longrightarrow>(\<exists>n. iter r n x y)"
(* your definition/proof here *)
  apply(induction rule: star.induct)

   apply (meson it_refl)

  by (meson iter_01 iter_trans)
 
text\<open>
\endexercise

\exercise\label{exe:cfg}
A context-free grammar can be seen as an inductive definition where each
nonterminal $A$ is an inductively defined predicate on lists of terminal
symbols: $A(w)$ mans that $w$ is in the language generated by $A$.
For example, the production $S \to aSb$ can be viewed as the implication
@{prop"S w \<Longrightarrow> S (a # w @ [b])"} where @{text a} and @{text b} are terminal symbols,
i.e., elements of some alphabet. The alphabet can be defined as a datatype:
\<close>

datatype alpha = a | b

text\<open>
If you think of @{const a} and @{const b} as ``@{text "("}'' and  ``@{text ")"}'',
the following two grammars both generate strings of balanced parentheses
(where $\varepsilon$ is the empty word):
\[
\begin{array}{r@ {\quad}c@ {\quad}l}
S &\to& \varepsilon \quad\mid\quad aSb \quad\mid\quad SS \\
T &\to& \varepsilon \quad\mid\quad TaTb
\end{array}
\]
Define them as inductive predicates and prove their equivalence:
\<close>

inductive S :: "alpha list \<Rightarrow> bool" where
(* your definition/proof here *)
S_base:  "S Nil" |
S_step1:  "S x \<Longrightarrow>S (a#x@[b])" |
S_step2:  "S x \<Longrightarrow>S y \<Longrightarrow>S (x@y)"
inductive T :: "alpha list \<Rightarrow> bool" where
(* your definition/proof here *)
T_base:  "T Nil" |
T_step:  "T x\<Longrightarrow>T y \<Longrightarrow>T(x@[a]@y@[b])"

lemma T_01 [simp]: "T y\<Longrightarrow>T x \<Longrightarrow>T(x@y)"
  apply(induction rule: T.induct)

   apply simp

  by (metis T.simps append_assoc)

lemma TS: "T w \<Longrightarrow> S w"
(* your definition/proof here *)
 apply(induction rule: T.induct)
   apply (simp add: S_base)
  by (simp add: S_step1 S_step2)

lemma ST: "S w \<Longrightarrow> T w"
(* your definition/proof here *)
  apply(induction rule: S.induct)

   apply (simp add: T_base)

  using T_base T_step apply force

  by auto
corollary SeqT: "S w \<longleftrightarrow> T w"
(* your definition/proof here *)

  using ST TS by blast
text\<open>
\endexercise
\<close>
(* your definition/proof here *)
text\<open>
\exercise
In Chapter 3 we defined a recursive evaluation function
@{text "aval ::"} @{typ "aexp \<Rightarrow> state \<Rightarrow> val"}.
Define an inductive evaluation predicate and prove that it agrees with
the recursive function:
\<close>

inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
(* your definition/proof here *)
ar_base0:  "aval_rel (N n) s n" |
ar_base1:  "aval_rel (V x) s (s x)" |
ar_step:  "aval_rel k s z \<Longrightarrow>aval_rel v s w \<Longrightarrow>aval_rel (Plus k v) s (z+w)"
lemma aval_rel_aval: "aval_rel k s v \<Longrightarrow> aval k s = v"
(* your definition/proof here *)
  apply(induction rule: aval_rel.induct)
    apply simp
  apply simp
  by simp

lemma aval_01 [simp]: "aval (Plus k1 k2) s = v \<Longrightarrow>(aval k1 s)=z \<Longrightarrow>(aval k2 s) = v-z"
  by simp
lemma aval_02 [simp]: "aval_rel k1 s z \<Longrightarrow>aval_rel k2 s (v-z) \<Longrightarrow> aval_rel (Plus k1 k2) s  v"
  using ar_step by fastforce

  
lemma aval_aval_rel: "aval k s = v \<Longrightarrow> aval_rel k s v"
(* your definition/proof here *)
  apply(induction k)
   apply (simp add: ar_base0)
  using Chapter4Guisen.aval_rel.simps aval.simps(2) apply blast
  by simp

corollary "aval_rel k s v \<longleftrightarrow> aval k s = v"
(* your definition/proof here *)
  using aval_aval_rel aval_rel_aval by blast
text\<open>
\endexercise

\exercise
Consider the stack machine from Chapter~3
and recall the concept of \concept{stack underflow}
from Exercise~\ref{exe:stack-underflow}.
Define an inductive predicate
\<close>

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
(* your definition/proof here *)

ok_base0:  "ok 0 [] 0" |
ok_base01:  "ok n [] n \<Longrightarrow> ok (Suc n) [] (Suc n)"|
ok_step00:  "ok (Suc n) sk m \<Longrightarrow>ok n ((LOAD x)#sk) m"|
ok_step01:  "ok n sk m \<Longrightarrow>ok n ((LOAD x)#sk) (Suc m)"|
ok_step10:  "ok (Suc n) sk m \<Longrightarrow>ok n ((LOADI v)#sk) m"|
ok_step11:  "ok n sk m \<Longrightarrow>ok n ((LOADI v)#sk)(Suc m)"|
ok_step2:  "ok (Suc n) sk m \<Longrightarrow>ok (Suc (Suc n)) ((ADD)#sk) m"
text\<open>
such that @{text "ok n is n'"} means that with any initial stack of length
@{text n} the instructions @{text "is"} can be executed
without stack underflow and that the final stack has length @{text n'}.

Using the introduction rules for @{const ok},
prove the following special cases: \<close>

lemma ok_0[simp]:"ok 0 [LOAD x] (Suc 0)"
(* your definition/proof here *)
  
  by (simp add: ok_base0 ok_step01)

lemma ok_1[simp]:"ok (Suc 0) [LOAD y] (Suc (Suc 0))"

    by (simp add: ok_base0 ok_base01 ok_step01)
lemma ok_2[simp]:"ok (Suc(Suc 0)) [ADD,LOAD y] (Suc (Suc 0))"
  by (simp add: ok_step2)
lemma ok_3[simp]:"ok (Suc(Suc(Suc 0))) [ADD,ADD,LOAD y] (Suc (Suc 0))"
  by (simp add: ok_step2)


lemma "ok (Suc (Suc 0)) [LOAD x, ADD, ADD, LOAD y] (Suc (Suc 0))"
(* your definition/proof here *)
  by (simp add: ok_step00)
text \<open> Prove that @{text ok} correctly computes the final stack size: \<close>

lemma ok_4:"ok n [] n'\<Longrightarrow>(n=n')"
    using ok.cases by fastforce
lemma ok_5:" \<lbrakk>\<And>stk. \<lbrakk>ok n ts n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec ts s stk) = n'; ok n (z # ts) n';
        length stk = n\<rbrakk>
       \<Longrightarrow> length (exec (z # ts) s stk) = n'"
  apply(induction stk arbitrary:ts z n')
  
  oops
lemma "\<lbrakk>ok n ts n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec ts s stk) = n'"
(* your definition/proof here *)
  apply(induction ts arbitrary:stk)
   apply (simp add: ok_4)

text \<open>
Lemma @{thm [source] length_Suc_conv} may come in handy.

Prove that instruction sequences generated by @{text comp}
cannot cause stack underflow: \ @{text "ok n (comp a) ?"} \ for
some suitable value of @{text "?"}.
\endexercise
\<close>


end

