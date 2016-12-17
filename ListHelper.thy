theory ListHelper
imports Main List
begin

(*
primrec takeUpto :: "('a => bool) => 'a list => 'a list" where
"takeUpto P [] = []" |
"takeUpto P (x # xs) = (if P x then x # takeUpto P xs else x # [])"

value "takeUpto (\<lambda>x. x \<noteq> 0) [1,2,3,4,5,8,0,5,6,5,4,435::int]"

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