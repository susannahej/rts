(* File: JVMSemantics.thy *)
(* Author: Susannah Mansky, UIUC 2017 *)
(* Using Jinja JVM to instantiate the general Semantics locale *)

theory JVMSemantics
imports "../Common/Semantics" "../../JinjaDCI/JVM/JVMExec"
begin

(** Instantiating Semantics with Jinja JVM **)

fun JVMsmall :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state set" where
"JVMsmall P \<sigma> = { \<sigma>'. exec (P, \<sigma>) = Some \<sigma>' }"

lemma JVMsmall_prealloc_pres:
assumes pre: "preallocated (fst(snd \<sigma>))"
  and "\<sigma>' \<in> JVMsmall P \<sigma>"
shows "preallocated (fst(snd \<sigma>'))"
using exec_prealloc_pres[OF pre] assms by(cases \<sigma>, cases \<sigma>', auto)

lemma JVMsmall_det: "JVMsmall P \<sigma> = {} \<or> (\<exists>\<sigma>'. JVMsmall P \<sigma> = {\<sigma>'})"
by auto

definition JVMendset :: "jvm_state set" where
"JVMendset \<equiv> { (xp,h,frs,sh). frs = [] \<or> (\<exists>x. xp = Some x) }"

lemma JVMendset_final: "\<sigma> \<in> JVMendset \<Longrightarrow> \<forall>P. JVMsmall P \<sigma> = {}"
 by(auto simp: JVMendset_def)

lemma start_state_nend:
 "start_state P \<notin> JVMendset"
 by(simp add: start_state_def JVMendset_def)

interpretation JVMSemantics: Semantics JVMsmall JVMendset
 by unfold_locales (auto dest: JVMendset_final)

end