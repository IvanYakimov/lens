theory ListHelper
imports Main List
begin

(*
lemma "P x \<Longrightarrow> takeWhile P (x # xs) = x # (takeWhile P xs)"
 by (induct xs) auto

lemma takeWhile_incremental: "P x \<Longrightarrow> length (takeWhile P (x # xs)) = length (takeWhile P xs) + 1"
 by (induct xs) auto
*)

(*
lemma "\<lbrakk>\<And>x. x : set xs \<Longrightarrow> P x; \<not> P x\<rbrakk> \<Longrightarrow> takeWhile P xs = xs" 
 by auto

lemma "\<lbrakk>\<And>x. x : set xs \<Longrightarrow> P x; \<not> P x\<rbrakk> \<Longrightarrow> takeWhile P (xs @ [x]) = xs"
 by simp
*)
 
end