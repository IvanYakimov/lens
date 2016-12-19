theory CString
imports Main String
begin

(* Author: Ivan Yakimov, e-mail: ivan.yakimov.research@yandex.ru *)

type_synonym string = "char list"

definition terminator :: "char" where 
"terminator = Char Nibble0 Nibble0"
lemma terminator_simp[simp]:"terminator = Char Nibble0 Nibble0" by (simp add: terminator_def)

definition endl :: "char" where
"endl = Char Nibble0 NibbleA"
lemma endl_simp[simp]:"endl = Char Nibble0 NibbleA" by (simp add: endl_def)

definition isCString :: "string \<Rightarrow> bool" where 
"isCString xs = (terminator \<in> set xs)"
lemma isCString_simp[simp]:"isCString xs = (terminator \<in> set xs)" by (simp add: isCString_def)

definition isCLine :: "string \<Rightarrow> bool" where
"isCLine xs = (terminator \<in> set xs \<or> endl \<in> set xs)"
lemma isCLine_simp[simp]:"isCLine xs = (terminator \<in> set xs \<or> endl \<in> set xs)" by (simp add: isCLine_def)

definition takeCString :: "char list \<Rightarrow> char list" where
"takeCString xs = (if isCString xs then takeWhile (\<lambda>x. x \<noteq> terminator) xs else [])"
lemma takeCString_simp[simp]: 
"takeCString xs = (if isCString xs then takeWhile (\<lambda>x. x \<noteq> terminator) xs else [])"  by (simp add: takeCString_def)

definition takeFullCString :: "string \<Rightarrow> string" where
"takeFullCString xs = (if isCString xs then takeCString xs @ [terminator] else [])"
lemma takeFullCString_simp[simp]: "takeFullCString xs = (if isCString xs then takeCString xs @ [terminator] else [])" by (simp add: takeFullCString_def)

definition takeCLine :: "string \<Rightarrow> string" where
"takeCLine xs = (if isCLine xs then takeWhile (\<lambda>x. x \<noteq> terminator \<and> x \<noteq> endl) xs else [])"
lemma takeCLine_simp[simp]:"takeCLine xs = (if isCLine xs then takeWhile (\<lambda>x. x \<noteq> terminator \<and> x \<noteq> endl) xs else [])" by (simp add: takeCLine_def)

lemma isCString_nil[simp]:
"isCString [] = False" 
 by simp
 
lemma isCString_bad[simp]:
"\<forall>x \<in> set xs. x \<noteq> terminator \<equiv> \<not> isCString xs"
 by (induct xs) auto
 
lemma isCString_well[simp]: 
"\<exists>x \<in> set xs. x = terminator \<equiv> isCString xs"
 by (induct xs) auto
 
(* < - - TODO: structured proof: = instead of \<Longrightarrow> *)

lemma isCString_find[simp]:"\<not> isCString xs \<Longrightarrow> List.find (\<lambda>x. x = terminator) xs = None"
 by (induct xs) auto
 
lemma find_term[simp]:"(\<forall> x \<in> set xs. x \<noteq> terminator) \<Longrightarrow> (List.find (\<lambda>a. a = terminator) xs = None)"
 by (induct xs) auto

lemma my5[simp]:" List.find (\<lambda>a. a = terminator) xs = None \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> terminator)"
 apply (induct xs)
 apply auto
oops
 
lemma my4:"List.find (\<lambda>x. x = terminator) xs = None \<Longrightarrow> \<not> isCString xs"
 apply (induct xs) 
 apply auto
oops
(* - - > *)

lemma takeCString_nil[simp]:"takeCString [] = []" by simp
lemma takeCString_bad[simp]:"\<not>(isCString xs) \<Longrightarrow> takeCString xs = []" by simp
lemma takeCString_well[simp]:"isCString xs \<Longrightarrow> \<exists>ys. takeCString xs = ys" by simp
lemma takeCString_inc[simp]:"\<lbrakk>isCString xs; x \<noteq> terminator\<rbrakk> \<Longrightarrow> x # (takeCString xs) = takeCString (x # xs)" 
 by (induct xs) auto 

lemma takeFullCString_eq[simp]:"isCString xs \<Longrightarrow> takeFullCString xs = (takeCString xs) @ [terminator]" by auto
lemma takeFullCString_nil[simp]:"takeFullCString [] = []"  by simp
lemma takeFullCString_bad[simp]:"\<not>(isCString xs) \<Longrightarrow> takeFullCString xs = []" by simp
lemma takeFullCString_well[simp]:"isCString xs \<Longrightarrow> \<exists>ys. takeFullCString xs = ys" by simp
lemma takeFullCString_inc[simp]:"\<lbrakk>isCString xs; x \<noteq> terminator\<rbrakk> \<Longrightarrow> x # (takeFullCString xs) = takeFullCString (x # xs)"
 by (induct xs) auto
 
lemma takeFullCString_app1[simp]:
 "isCString xs \<Longrightarrow> takeFullCString xs = takeFullCString (xs @ ys)"
 by (induct xs) auto

(* support *)
definition str_hello :: "string" where
"str_hello = [CHR ''H'', CHR ''e'', CHR ''l'', CHR ''l'', CHR ''o'', CHR ''!'', terminator]"

definition str_el :: "string" where
"str_el = [CHR ''e'', CHR ''l'', terminator]"

definition bad_str :: "string" where
"bad_str = [CHR ''b'', CHR ''a'', CHR ''d'']"

definition empty_str :: "string" where
"empty_str = [terminator]"

value "str_hello"

end