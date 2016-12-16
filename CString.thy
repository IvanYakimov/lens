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
"takeCString xs = (takeWhile (\<lambda>x. x \<noteq> terminator) xs)"

lemma takeCString_simp[simp]: "takeCString xs = (takeWhile (\<lambda>x. x \<noteq> terminator) xs)" by (simp add: takeCString_def)

(* TODO: = instead of \<Longrightarrow> *)
lemma "\<not> isCString xs \<Longrightarrow> List.find (\<lambda>x. x = terminator) xs = None"
 by (induct xs) auto

(* TODO: better to modify the takeCString function to return [] in such cases *)
lemma "\<not>(isCString xs) \<Longrightarrow> takeCString xs = xs" by auto 

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