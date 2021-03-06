(* your definition/proof here *)
section "Stack Machine and Compilation"

theory Short_Theory 
  imports "HOL-IMP.BExp"
begin

subsection "Stack Machine"

text_raw\<open>\snip{ASMinstrdef}{0}{1}{%\<close>
datatype instr = LOADI val | LOAD vname | ADD
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{ASMstackdef}{1}{2}{%\<close>
type_synonym stack = "val list"
text_raw\<open>}%endsnip\<close>

text\<open>\noindent Abbreviations are transparent: they are unfolded after
parsing and folded back again before printing. Internally, they do not
exist.\<close>

text_raw\<open>\snip{ASMexeconedef}{0}{1}{%\<close>
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> (stack option) \<Rightarrow> stack option" where
"exec1  ADD _ None  =  None"|
"exec1  ADD _ (Some [])  =  None"|
"exec1  ADD _ (Some (j # []))  =  None"|
"exec1  ADD _ (Some (j # i # stk))  = Some ((i + j) # stk)"|
"exec1 (LOADI n) _ (None) = Some (n # [])" |
"exec1 (LOADI n) _ (Some stk) =Some  (n # stk)" |
"exec1 (LOAD x) s (None)  =Some  (s(x) # [])" |
"exec1 (LOAD x) s (Some stk)  =Some  (s(x) # stk)" 

text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{ASMexecdef}{1}{2}{%\<close>
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> (stack option) \<Rightarrow> (stack option)" where
"exec  [] _ None  =  None"|
"exec [] _ (Some stk) = Some stk" |
"exec (i#is) s (None) = exec is s (exec1 i s None)"|
"exec (i#is) s (Some stk) = exec is s (exec1 i s (Some stk))"
text_raw\<open>}%endsnip\<close>

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> (Some [50])"


lemma exec[simp] :"(\<And>a is1 stk.(exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk))) \<Longrightarrow> exec (is1 @ is2) s (exec1 a s stk) = exec is2 s (exec is1 s (exec1 a s stk))"
 sledgehammer
  by simp
lemma exec_append[simp]:
  "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)"
  apply(induction is1 arbitrary: stk)
   apply (auto split:instr.split)
  sledgehammer
   apply (metis exec.simps(1) exec.simps(2) option.collapse)
  sledgehammer
  by (metis exec.simps(3) exec.simps(4) not_Some_eq)
subsection "Compilation"

text_raw\<open>\snip{ASMcompdef}{0}{2}{%\<close>
fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"
text_raw\<open>}%endsnip\<close>

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

fun trans :: "int \<Rightarrow> (stack option) \<Rightarrow> (stack option) " where
"trans a None  = Some (a # [])"|
"trans a (Some stk) =  Some (a # stk)" 

lemma st01[simp]:"exec [LOADI x] s stk = Short_Theory.trans x stk"
  apply(induction stk arbitrary: x)
   apply simp
  by simp
lemma st02[simp]:"exec (Short_Theory.comp (V x)) s stk = Short_Theory.trans (aval (V x) s) stk"
  apply(induction stk arbitrary: x)
  apply simp
  by simp

lemma st03[simp]:"exec [ADD] s (Short_Theory.trans (aval a2 s) (Short_Theory.trans (aval a1 s) stk)) =
           Short_Theory.trans (aval a1 s + aval a2 s) stk"
  apply(induction stk arbitrary: a1 a2)
  sledgehammer
   apply simp
  sledgehammer
  by simp
  


theorem exec_comp: "exec (comp a) s stk =(trans (aval a s)  stk)"
apply(induction a arbitrary: stk)
  sledgehammer
  apply simp
   sledgehammer
   using st02 apply auto[1]
   apply(auto split:option.split)
   done
end

