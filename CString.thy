theory CString
imports Main String
begin

(* Author: Ivan Yakimov, e-mail: ivan.yakimov.research@yandex.ru *)

type_synonym string = "char list"

definition terminator :: "char" where 
"terminator = Char Nibble0 Nibble0"
lemma terminator_simp[simp]:"terminator = Char Nibble0 Nibble0" by (simp add: terminator_def)

definition isCString :: "string \<Rightarrow> bool" where 
"isCString xs = (terminator \<in> set xs)"
lemma isCString_simp[simp]:"isCString xs = (terminator \<in> set xs)" by (simp add: isCString_def)

definition takeCString :: "char list \<Rightarrow> char list" where
"takeCString xs = (if isCString xs then takeWhile (\<lambda>x. x \<noteq> terminator) xs else [])"
lemma takeCString_simp[simp]: 
"takeCString xs = (if isCString xs then takeWhile (\<lambda>x. x \<noteq> terminator) xs else [])"  by (simp add: takeCString_def)

definition takeFullCString :: "string \<Rightarrow> string" where
"takeFullCString xs = (if isCString xs then takeCString xs @ [terminator] else [])"
lemma takeFullCString_simp[simp]: "takeFullCString xs = (if isCString xs then takeCString xs @ [terminator] else [])" by (simp add: takeFullCString_def)

lemma "isCString [] = False" by simp

(* < - - TODO: structured proof: = instead of \<Longrightarrow> *)
lemma my2[simp]:"(\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> terminator) \<Longrightarrow> (\<not> isCString xs)"
 by (induct xs) auto
lemma my10[simp]:"\<not> isCString xs \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> terminator)"
 by (induct xs) auto

lemma my1[simp]:"\<not> isCString xs \<Longrightarrow> List.find (\<lambda>x. x = terminator) xs = None"
 by (induct xs) auto
 
lemma my3[simp]:"(\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> terminator) \<Longrightarrow> (List.find (\<lambda>a. a = terminator) xs = None)"
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