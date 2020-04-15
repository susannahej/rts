(* File: JVMCollectionSemantics.thy *)
(* Author: Susannah Mansky, UIUC 2017 *)
(* Collection functions for Jinja JVM as instances of the CollectionSemantics locale *)

theory JVMCollectionSemantics
imports "../Common/CollectionSemantics" JVMSemantics
begin

abbreviation JVMcombine :: "cname set \<Rightarrow> cname set \<Rightarrow> cname set" where
"JVMcombine C C' \<equiv> C \<union> C'"

abbreviation JVMcollect_id :: "cname set" where
"JVMcollect_id \<equiv> {}"

(********************Naive RTS algorithm********************)

fun JVMinstr_ncollect ::
 "[jvm_prog, instr, heap, val list] \<Rightarrow> cname set" where
"JVMinstr_ncollect P (New C) h stk = classes_above P C" |
"JVMinstr_ncollect P (Getfield F C) h stk =
  (if (hd stk) = Null then {}
   else classes_above P (cname_of h (the_Addr (hd stk))))" |
"JVMinstr_ncollect P (Getstatic C F D) h stk = classes_above P C" |
"JVMinstr_ncollect P (Putfield F C) h stk =
  (if (hd (tl stk)) = Null then {}
   else classes_above P (cname_of h (the_Addr (hd (tl stk)))))" |
"JVMinstr_ncollect P (Putstatic C F D) h stk = classes_above P C" |
"JVMinstr_ncollect P (Checkcast C) h stk =
  (if (hd stk) = Null then {}
   else classes_above P (cname_of h (the_Addr (hd stk))))" |
"JVMinstr_ncollect P (Invoke M n) h stk =
  (if (stk ! n) = Null then {}
   else classes_above P (cname_of h (the_Addr (stk ! n))))" |
"JVMinstr_ncollect P (Invokestatic C M n) h stk = classes_above P C" |
"JVMinstr_ncollect P Throw h stk =
  (if (hd stk) = Null then {}
   else classes_above P (cname_of h (the_Addr (hd stk))))" |
"JVMinstr_ncollect P _ h stk = {}"

fun JVMstep_ncollect ::
 "[jvm_prog, heap, val list, cname, mname, pc, init_call_status] \<Rightarrow> cname set" where
"JVMstep_ncollect P h stk C M pc (Calling C' Cs) = classes_above P C'" |
"JVMstep_ncollect P h stk C M pc (Called (C'#Cs))
 = classes_above P C' \<union> classes_above P (fst(method P C' clinit))" |
"JVMstep_ncollect P h stk C M pc (Throwing Cs a) = classes_above P (cname_of h a)" |
"JVMstep_ncollect P h stk C M pc ics = JVMinstr_ncollect P (instrs_of P C M ! pc) h stk"

fun JVMexec_ncollect :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> cname set" where
"JVMexec_ncollect P (None, h, (stk,loc,C,M,pc,ics)#frs, sh) =
   (JVMstep_ncollect P h stk C M pc ics
       \<union> classes_above P C \<union> classes_above_frames P frs \<union> classes_above_xcpts P
   )"
| "JVMexec_ncollect P _ = {}"

(****)

fun JVMNaiveCollect :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> cname set" where
"JVMNaiveCollect P \<sigma> \<sigma>' = JVMexec_ncollect P \<sigma>"

interpretation JVMNaiveCollectionSemantics:
  CollectionSemantics JVMsmall JVMendset JVMNaiveCollect JVMcombine JVMcollect_id
 by unfold_locales auto

(********************Smarter RTS algorithm********************)

fun JVMinstr_scollect ::
 "[jvm_prog, instr] \<Rightarrow> cname set" where
"JVMinstr_scollect P (Getstatic C F D)
 = (if \<not>(\<exists>t. P \<turnstile> C has F,Static:t in D) then classes_above P C
    else classes_between P C D - {D})" |
"JVMinstr_scollect P (Putstatic C F D)
 = (if \<not>(\<exists>t. P \<turnstile> C has F,Static:t in D) then classes_above P C
    else classes_between P C D - {D})" |
"JVMinstr_scollect P (Invokestatic C M n)
 = (if \<not>(\<exists>Ts T m D. P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D) then classes_above P C
    else classes_between P C (fst(method P C M)) - {fst(method P C M)})" |
"JVMinstr_scollect P _ = {}"

fun JVMstep_scollect ::
 "[jvm_prog, instr, init_call_status] \<Rightarrow> cname set" where
"JVMstep_scollect P i (Calling C' Cs) = {C'}" |
"JVMstep_scollect P i (Called (C'#Cs)) = {}" |
"JVMstep_scollect P i (Throwing Cs a) = {}" |
"JVMstep_scollect P i ics = JVMinstr_scollect P i"

fun JVMexec_scollect :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> cname set" where
"JVMexec_scollect P (None, h, (stk,loc,C,M,pc,ics)#frs, sh) =
   JVMstep_scollect P (instrs_of P C M ! pc) ics"
| "JVMexec_scollect P _ = {}"

(****)

fun JVMSmartCollect :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> cname set" where
"JVMSmartCollect P \<sigma> \<sigma>' = JVMexec_scollect P \<sigma>"

interpretation JVMSmartCollectionSemantics:
  CollectionSemantics JVMsmall JVMendset JVMSmartCollect JVMcombine JVMcollect_id
 by unfold_locales

(***********************************************)

lemma JVMnaive_csmallD:
"(\<sigma>', cset) \<in> JVMNaiveCollectionSemantics.csmall P \<sigma>
 \<Longrightarrow> JVMexec_ncollect P \<sigma> = cset \<and> \<sigma>' \<in> JVMsmall P \<sigma>"
 by(simp add: JVMNaiveCollectionSemantics.csmall_def)

lemma JVMsmart_csmallD:
"(\<sigma>', cset) \<in> JVMSmartCollectionSemantics.csmall P \<sigma>
 \<Longrightarrow> JVMexec_scollect P \<sigma> = cset \<and> \<sigma>' \<in> JVMsmall P \<sigma>"
 by(simp add: JVMSmartCollectionSemantics.csmall_def)


lemma jvm_naive_to_smart_csmall_nstep_last_eq:
 "\<lbrakk> (\<sigma>',cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.cbig P \<sigma>;
    (\<sigma>',cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.csmall_nstep P \<sigma> n;
    (\<sigma>',cset\<^sub>s) \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma> n' \<rbrakk>
  \<Longrightarrow> n = n'"
proof(induct n arbitrary: n' \<sigma> \<sigma>' cset\<^sub>n cset\<^sub>s)
  case 0
  have "\<sigma>' = \<sigma>" using "0.prems"(2) JVMNaiveCollectionSemantics.csmall_nstep_base by blast
  then have endset: "\<sigma> \<in> JVMendset" using "0.prems"(1) JVMNaiveCollectionSemantics.cbigD by blast
  show ?case
  proof(cases n')
    case Suc then show ?thesis using "0.prems"(3) JVMSmartCollectionSemantics.csmall_nstep_Suc_nend
      endset by blast
  qed(simp)
next
  case (Suc n1)
  then have endset: "\<sigma>' \<in> JVMendset" using Suc.prems(1) JVMNaiveCollectionSemantics.cbigD by blast
  have nend: "\<sigma> \<notin> JVMendset"
   using JVMNaiveCollectionSemantics.csmall_nstep_Suc_nend[OF Suc.prems(2)] by simp
  then have neq: "\<sigma>' \<noteq> \<sigma>" using endset by auto
  obtain \<sigma>1 cset cset1 where \<sigma>1: "(\<sigma>1,cset1) \<in> JVMNaiveCollectionSemantics.csmall P \<sigma>"
     "cset\<^sub>n = cset1 \<union> cset" "(\<sigma>',cset) \<in> JVMNaiveCollectionSemantics.csmall_nstep P \<sigma>1 n1"
    using JVMNaiveCollectionSemantics.csmall_nstep_SucD[OF Suc.prems(2)] by clarsimp
  then have cbig: "(\<sigma>',cset) \<in> JVMNaiveCollectionSemantics.cbig P \<sigma>1"
    using endset by(auto simp: JVMNaiveCollectionSemantics.cbig_def)
  show ?case
  proof(cases n')
    case 0 then show ?thesis
      using neq Suc.prems(3) JVMSmartCollectionSemantics.csmall_nstep_base by blast
  next
    case Suc': (Suc n1')
    then obtain \<sigma>1' cset2 cset1' where \<sigma>1': "(\<sigma>1',cset1') \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
      "cset\<^sub>s = cset1' \<union> cset2" "(\<sigma>',cset2) \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma>1' n1'"
      using JVMSmartCollectionSemantics.csmall_nstep_SucD[where \<sigma>=\<sigma> and \<sigma>'=\<sigma>' and coll'=cset\<^sub>s
               and n=n1'] Suc.prems(3) by blast
    then have "\<sigma>1=\<sigma>1'" using \<sigma>1 JVMNaiveCollectionSemantics.csmall_def
      JVMSmartCollectionSemantics.csmall_def by auto
    then show ?thesis using Suc.hyps(1)[OF cbig \<sigma>1(3)] \<sigma>1'(3) Suc' by blast
  qed
qed

end