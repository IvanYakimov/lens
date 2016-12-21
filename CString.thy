theory CString
imports Main String
begin

(* Author: Ivan Yakimov, e-mail: ivan.yakimov.research@yandex.ru *)

(* --------------------------------------- Definitions ------------------------------------- *)

definition terminator :: "char" where 
"terminator = Char Nibble0 Nibble0"

definition endl :: "char" where
"endl = Char Nibble0 NibbleA"

definition isCString :: "string \<Rightarrow> bool" where 
"isCString xs = (terminator \<in> set xs)"

definition isCLine :: "string \<Rightarrow> bool" where
"isCLine xs = (terminator \<in> set xs \<or> endl \<in> set xs)"

definition takeCString :: "char list \<Rightarrow> char list" where
"takeCString xs = (if isCString xs then takeWhile (\<lambda>x. x \<noteq> terminator) xs else [])"

definition takeBuff :: "string \<Rightarrow> string" where
"takeBuff xs = (if isCString xs then takeCString xs else xs)"

definition takeFullCString :: "string \<Rightarrow> string" where
"takeFullCString xs = (if isCString xs then takeCString xs @ [terminator] else [])"

definition takeCLine :: "string \<Rightarrow> string" where
"takeCLine xs = (if isCLine xs then takeWhile (\<lambda>x. x \<noteq> terminator \<and> x \<noteq> endl) xs else [])"
 
(* -------------------------------- Simplification Rules --------------------------- *)

lemma cstring_simps[simp]:
"terminator = Char Nibble0 Nibble0"
"endl = Char Nibble0 NibbleA"
"isCString xs = (terminator \<in> set xs)" 
"isCLine xs = (terminator \<in> set xs \<or> endl \<in> set xs)" 
"takeCString xs = (if isCString xs then takeWhile (\<lambda>x. x \<noteq> terminator) xs else [])"
"takeFullCString xs = (if isCString xs then takeCString xs @ [terminator] else [])"
"takeCLine xs = (if isCLine xs then takeWhile (\<lambda>x. x \<noteq> terminator \<and> x \<noteq> endl) xs else [])"
"takeBuff xs = (if isCString xs then takeCString xs else xs)"
by (simp_all add: terminator_def endl_def isCString_def isCLine_def takeCString_def takeCLine_def takeBuff_def takeFullCString_def)

(* -------------------------- isCString ------------------------ *)
lemma isCString_nil[simp]:
"isCString [] = False" 
 by simp
 
lemma isCString_bad[simp]:
"\<forall>x \<in> set xs. x \<noteq> terminator \<equiv> \<not> isCString xs"
 by (induct xs) auto
 
lemma isCString_well[simp]: 
"\<exists>x \<in> set xs. x = terminator \<equiv> isCString xs"
 by (induct xs) auto
 
lemma isCString_term[simp]:
"\<lbrakk>isCString xs; x \<notin> set xs\<rbrakk> \<Longrightarrow> x \<noteq> terminator"
 by (induct xs) auto

lemma isCString_inc[simp]:
"\<lbrakk>isCString xs; x \<noteq> terminator\<rbrakk> \<Longrightarrow> isCString (x#xs)"
 by (induct xs) auto

lemma isCString_app1[simp]:
"isCString xs \<or> isCString ys \<Longrightarrow> isCString (xs @ ys)"
 by auto
 
lemma isCString_app2[simp]:
"isCString (xs @ ys) = isCString (ys @ xs)" 
 by auto
 
lemma isCString_find[simp]:
"\<not> isCString xs \<equiv> List.find (\<lambda>x. x = terminator) xs = None"
 by (induct xs) auto

(* ------------------------------------ takeCString ---------------------------------- *)
lemma takeCString_nil[simp]:
"takeCString [] = []" 
 by simp

lemma takeCString_bad[simp]:
"\<not>(isCString xs) \<Longrightarrow> takeCString xs = []" 
 by simp

lemma takeString_app1[simp]:
"isCString xs \<Longrightarrow> takeCString (xs @ ys) = takeCString xs" 
 by (induct xs) auto
 
lemma takeCString_inc[simp]:
"\<lbrakk>isCString xs; x \<noteq> terminator\<rbrakk> \<Longrightarrow> takeCString (x # xs) = x # (takeCString xs)" 
 by (induct xs) auto

lemma takeCString_app2[simp]:
"\<lbrakk>\<not> isCString xs; isCString ys\<rbrakk> \<Longrightarrow> takeCString (xs @ ys) = xs @ (takeCString ys)" 
 by (induct xs) auto

(* ------------------------ takeFullCString ---------------------------- *)
lemma takeFullCString_1[simp]:
"isCString xs \<Longrightarrow> takeFullCString xs = (takeCString xs) @ [terminator]" 
 by auto

lemma takeFullCString_2[simp]:
"\<not> isCString xs \<Longrightarrow> takeFullCString xs = takeCString xs" 
 by auto

(* -------------------------- takeBuff ---------------------------- *)
lemma takeBuff_2[simp]: 
"isCString xs \<Longrightarrow> takeBuff xs = takeCString xs" 
 by auto

lemma takeBuff_1[simp]: 
"\<not> isCString xs \<Longrightarrow> takeBuff xs = xs" 
 by auto
 
(* --------------- support ----------------- *)
definition str_hello :: "string" where
"str_hello = [CHR ''H'', CHR ''e'', CHR ''l'', CHR ''l'', CHR ''o'', CHR ''!'', terminator]"

definition str_el :: "string" where
"str_el = [CHR ''e'', CHR ''l'', terminator]"

definition bad_str :: "string" where
"bad_str = [CHR ''b'', CHR ''a'', CHR ''d'']"

definition empty_str :: "string" where
"empty_str = [terminator]"

(* ------------------------------------------ EXPERIMENTAL -------------------------------------------- *)
experiment begin

theorem my5[simp]:" List.find (\<lambda>a. a = terminator) xs = None \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> terminator)"
 apply (induct xs)
 apply auto
oops
 
theorem my4:"List.find (\<lambda>x. x = terminator) xs = None \<Longrightarrow> \<not> isCString xs"
 apply (induct xs) 
 apply auto
oops

thm notI
thm ccontr

theorem "\<not> (\<forall>xs. \<not> isCString xs)"
proof (rule ccontr)
 assume P: "\<not> \<not> (\<forall>xs. \<not> isCString xs)"
 from P have 0: "\<forall>xs. \<not> isCString xs" by simp
 fix a
 from 0 have 1:"\<not> isCString a" by simp
 from 1 show "False" 
oops

theorem "\<not> isCString xs \<equiv> \<forall>xs. \<not> isCString xs"
nitpick
oops

theorem
"\<not> isCString xs \<Longrightarrow> False"
apply (induct xs)
apply simp_all
quickcheck
oops

theorem
"\<exists>xs. isCString xs"
proof (rule ccontr)
 assume 0:"\<not> (\<exists>xs. isCString xs)"
 from 0 have 1: "\<forall>xs. \<not> isCString xs" by blast
 from 1 have 2: "\<not> isCString xs" by simp
 from 2 have 3: "False"
 nitpick
 
oops

thm ccontr

theorem
"\<not> (\<exists>xs. isCString xs)"
proof (rule ccontr)
 assume 28:"\<not> \<not> (\<exists>xs. isCString xs)"
 from 28 have 0: "\<exists>xs. isCString xs" by blast
 nitpick
 
oops

end

end