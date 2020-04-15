(* File: CollectionBasedRTS.thy *)
(* Author: Susannah Mansky, UIUC 2017 *)
(* General model for Regression Test Selection based on Collection Semantics *)

theory CollectionBasedRTS
imports RTS_safe CollectionSemantics
begin

(********************* Non-Deterministic version *************************)

locale CollectionBasedRTS_base = RTS_safe + CollectionSemantics

locale CollectionBasedRTS = CollectionBasedRTS_base where
  small = "small :: 'prog \<Rightarrow> 'state \<Rightarrow> 'state set" and
  collect = "collect :: 'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> 'coll" and
  out = "out :: 'prog \<Rightarrow> 'test \<Rightarrow> ('state \<times> 'coll) set"
 for small collect out
+
 fixes
  make_test_prog :: "'prog \<Rightarrow> 'test \<Rightarrow> 'prog" and
  collect_start :: "'prog \<Rightarrow> 'coll"
 assumes
  out_cbig:
   "\<exists>i. out P t = {(\<sigma>',coll'). \<exists>coll. (\<sigma>',coll) \<in> cbig (make_test_prog P t) i
                                                  \<and> coll' = combine coll (collect_start P) }"

context CollectionBasedRTS begin

end (* CollectionBasedRTS *)

end
