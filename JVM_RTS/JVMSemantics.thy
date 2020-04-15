(* File: JVMSemantics.thy *)
(* Author: Susannah Mansky, UIUC 2017 *)
(* Proof that Jinja JVM is an instance of the general Semantics locale *)

theory JVMSemantics
imports "../Common/Semantics" "../../JinjaDCI/JVM/JVMExec" "../JinjaSuppl/ClassesAbove"
begin

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

(*******************************************)
(*** JVM-specific classes_above theory ***)

fun classes_above_frames :: "'m prog \<Rightarrow> frame list \<Rightarrow> cname set" where
"classes_above_frames P ((stk,loc,C,M,pc,ics)#frs) = classes_above P C \<union> classes_above_frames P frs" |
"classes_above_frames P [] = {}"

lemma classes_above_start_state:
assumes above_xcpts: "classes_above_xcpts P \<inter> classes_changed P P' = {}"
shows "start_state P = start_state P'"
using assms classes_above_start_heap by(simp add: start_state_def)

lemma classes_above_matches_ex_entry:
 "classes_above P C \<inter> classes_changed P P' = {}
  \<Longrightarrow> matches_ex_entry P C pc xcp = matches_ex_entry P' C pc xcp"
using classes_above_subcls classes_above_subcls2
 by(auto simp: matches_ex_entry_def)

lemma classes_above_match_ex_table:
assumes "classes_above P C \<inter> classes_changed P P' = {}"
shows "match_ex_table P C pc es = match_ex_table P' C pc es"
using classes_above_matches_ex_entry[OF assms] proof(induct es) qed(auto)

lemma classes_above_find_handler:
assumes "classes_above P (cname_of h a) \<inter> classes_changed P P' = {}"
shows "classes_above_frames P frs \<inter> classes_changed P P' = {}
  \<Longrightarrow> find_handler P a h frs sh = find_handler P' a h frs sh"
proof(induct frs)
  case (Cons fr' frs')
  obtain stk loc C M pc ics where fr': "fr' = (stk,loc,C,M,pc,ics)" by(cases fr')
  with Cons have
       intC: "classes_above P C \<inter> classes_changed P P' = {}"
   and int: "classes_above_frames P frs' \<inter> classes_changed P P' = {}"  by auto
  show ?case using Cons fr' int classes_above_method[OF intC]
    classes_above_match_ex_table[OF assms(1)] by(auto split: bool.splits)
qed(simp)

lemma find_handler_classes_above_frames:
 "find_handler P a h frs sh = (xp',h',frs',sh')
 \<Longrightarrow> classes_above_frames P frs' \<subseteq> classes_above_frames P frs"
proof(induct frs)
  case (Cons f1 frs1)
  then obtain stk loc C M pc ics where f1: "f1 = (stk,loc,C,M,pc,ics)" by(cases f1)
  show ?case
  proof(cases "match_ex_table P (cname_of h a) pc (ex_table_of P C M)")
    case None then show ?thesis using f1 None Cons
     by(auto split: bool.splits list.splits init_call_status.splits)
  next
    case (Some a) then show ?thesis using f1 Some Cons by auto
  qed
qed(simp)

lemma find_handler_pieces:
 "find_handler P a h frs sh = (xp',h',frs',sh')
 \<Longrightarrow> h = h' \<and> sh = sh' \<and> classes_above_frames P frs' \<subseteq> classes_above_frames P frs"
using find_handler_classes_above_frames by(auto dest: find_handler_heap find_handler_sheap)

(*********)
(** JVM next-step lemmas for instrs that call the initialization procedure **)

(* HERE: MOVE? *)
fun curr_instr :: "jvm_prog \<Rightarrow> frame \<Rightarrow> instr" where
"curr_instr P (stk,loc,C,M,pc,ics) = instrs_of P C M ! pc"

lemma JVM_New_next_step:
assumes step: "\<sigma>' \<in> JVMsmall P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = New C"
 and nDone: "\<not>(\<exists>sfs i. sheap \<sigma> C = Some(sfs,i) \<and> i = Done)"
 and ics: "ics_of(hd(frames_of \<sigma>)) = No_ics"
shows "ics_of (hd(frames_of \<sigma>')) = Calling C [] \<and> sheap \<sigma> = sheap \<sigma>' \<and> \<sigma>' \<notin> JVMendset"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
  then obtain f1 frs1 where frs: "frs=f1#frs1" using nend by(cases frs, simp_all add: JVMendset_def)
  then obtain stk loc C' M' pc ics where f1:"f1=(stk,loc,C',M',pc,ics)" by(cases f1)
  have xp: "xp = None" using \<sigma> nend by(simp add: JVMendset_def)
  obtain xp' h' frs' sh' where \<sigma>': "\<sigma>'=(xp',h',frs',sh')" by(cases \<sigma>')
  have "ics_of (hd frs') = Calling C [] \<and> sh = sh' \<and> frs' \<noteq> [] \<and> xp' = None"
  proof(cases "sh C")
    case None then show ?thesis using \<sigma>' xp f1 frs \<sigma> assms by auto
  next
    case (Some a)
    then obtain sfs i where a: "a=(sfs,i)" by(cases a)
    then have nDone': "i \<noteq> Done" using nDone Some f1 frs \<sigma> by simp
    show ?thesis using a Some \<sigma>' xp f1 frs \<sigma> assms by(auto split: init_state.splits)
  qed
  then show ?thesis using ics \<sigma> \<sigma>' by(cases frs', auto simp: JVMendset_def)
qed

lemma JVM_Getstatic_next_step:
assumes step: "\<sigma>' \<in> JVMsmall P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = Getstatic C F D"
 and fC: "P \<turnstile> C has F,Static:t in D"
 and nDone: "\<not>(\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done)"
 and ics: "ics_of(hd(frames_of \<sigma>)) = No_ics"
shows "ics_of (hd(frames_of \<sigma>')) = Calling D [] \<and> sheap \<sigma> = sheap \<sigma>' \<and> \<sigma>' \<notin> JVMendset"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
  then obtain f1 frs1 where frs: "frs=f1#frs1" using nend by(cases frs, simp_all add: JVMendset_def)
  then obtain stk loc C' M' pc ics where f1:"f1=(stk,loc,C',M',pc,ics)" by(cases f1)
  have xp: "xp = None" using \<sigma> nend by(simp add: JVMendset_def)
  obtain xp' h' frs' sh' where \<sigma>': "\<sigma>'=(xp',h',frs',sh')" by(cases \<sigma>')
  have ex': "\<exists>t b. P \<turnstile> C has F,b:t in D" using fC by auto
  have field: "\<exists>t. field P D F = (D,Static,t)"
    using fC field_def2 has_field_idemp has_field_sees by blast
  have nCalled': "\<forall>Cs. ics \<noteq> Called Cs" using ics f1 frs \<sigma> by simp
  have "ics_of (hd frs') = Calling D [] \<and> sh = sh' \<and> frs' \<noteq> [] \<and> xp' = None"
  proof(cases "sh D")
    case None then show ?thesis using field ex' \<sigma>' xp f1 frs \<sigma> assms by auto
  next
    case (Some a)
    then obtain sfs i where a: "a=(sfs,i)" by(cases a)
    show ?thesis using field ex' a Some \<sigma>' xp f1 frs \<sigma> assms by(auto split: init_state.splits)
  qed
  then show ?thesis using ics \<sigma> \<sigma>' by(auto simp: JVMendset_def)
qed

lemma JVM_Putstatic_next_step:
assumes step: "\<sigma>' \<in> JVMsmall P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = Putstatic C F D"
 and fC: "P \<turnstile> C has F,Static:t in D"
 and nDone: "\<not>(\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done)"
 and ics: "ics_of(hd(frames_of \<sigma>)) = No_ics"
shows "ics_of (hd(frames_of \<sigma>')) = Calling D [] \<and> sheap \<sigma> = sheap \<sigma>' \<and> \<sigma>' \<notin> JVMendset"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
  then obtain f1 frs1 where frs: "frs=f1#frs1" using nend by(cases frs, simp_all add: JVMendset_def)
  then obtain stk loc C' M' pc ics where f1:"f1=(stk,loc,C',M',pc,ics)" by(cases f1)
  have xp: "xp = None" using \<sigma> nend by(simp add: JVMendset_def)
  obtain xp' h' frs' sh' where \<sigma>': "\<sigma>'=(xp',h',frs',sh')" by(cases \<sigma>')
  have ex': "\<exists>t b. P \<turnstile> C has F,b:t in D" using fC by auto
  have field: "field P D F = (D,Static,t)"
    using fC field_def2 has_field_idemp has_field_sees by blast
  have ics': "ics_of (hd frs') = Calling D [] \<and> sh = sh' \<and> frs' \<noteq> [] \<and> xp' = None"
  proof(cases "sh D")
    case None then show ?thesis using field ex' \<sigma>' xp f1 frs \<sigma> assms by auto
  next
    case (Some a)
    then obtain sfs i where a: "a=(sfs,i)" by(cases a)
    show ?thesis using field ex' a Some \<sigma>' xp f1 frs \<sigma> assms by(auto split: init_state.splits)
  qed
  then show ?thesis using ics \<sigma> \<sigma>' by(auto simp: JVMendset_def)
qed

lemma JVM_Invokestatic_next_step:
assumes step: "\<sigma>' \<in> JVMsmall P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = Invokestatic C M n"
 and mC: "P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D"
 and nDone: "\<not>(\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done)"
 and ics: "ics_of(hd(frames_of \<sigma>)) = No_ics"
shows "ics_of (hd(frames_of \<sigma>')) = Calling D [] \<and> sheap \<sigma> = sheap \<sigma>' \<and> \<sigma>' \<notin> JVMendset"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
  then obtain f1 frs1 where frs: "frs=f1#frs1" using nend by(cases frs, simp_all add: JVMendset_def)
  then obtain stk loc C' M' pc ics where f1:"f1=(stk,loc,C',M',pc,ics)" by(cases f1)
  have xp: "xp = None" using \<sigma> nend by(simp add: JVMendset_def)
  obtain xp' h' frs' sh' where \<sigma>': "\<sigma>'=(xp',h',frs',sh')" by(cases \<sigma>')
  have ex': "\<exists>Ts T m D b. P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D" using mC by fastforce
  have method: "\<exists>m. method P C M = (D,Static,m)" using mC by(cases m, auto)
  have ics': "ics_of (hd frs') = Calling D [] \<and> sh = sh' \<and> frs' \<noteq> [] \<and> xp' = None"
  proof(cases "sh D")
    case None then show ?thesis using method ex' \<sigma>' xp f1 frs \<sigma> assms by auto
  next
    case (Some a)
    then obtain sfs i where a: "a=(sfs,i)" by(cases a)
    then have nDone': "i \<noteq> Done" using nDone Some f1 frs \<sigma> by simp
    show ?thesis using method ex' a Some \<sigma>' xp f1 frs \<sigma> assms by(auto split: init_state.splits)
  qed
  then show ?thesis using ics \<sigma> \<sigma>' by(auto simp: JVMendset_def)
qed

end