theory Strlen
imports Main String List "$PWD/CString" "$PWD/ListHelper"
begin

(* Author: Ivan Yakimov, Siberian Federal University, e-mail: ivan.yakimov.research@yandex.ru *)

definition strlen :: "char list \<Rightarrow> int option" where
"strlen xs = 
 (if \<not> (isCString xs) 
  then None
  else Some (int (length (takeCString xs))))"
  
definition strnlen :: "char list \<Rightarrow> int \<Rightarrow> int option" where
"strnlen xs n= 
 (if n \<noteq> int (length xs) 
  then None
  else strlen xs)"

lemma "n \<noteq> int (length xs) \<Longrightarrow> strnlen xs n = None"
 by (simp add: strnlen_def)
 
lemma "n = int (length xs) \<Longrightarrow> strnlen xs n = strlen xs"
 by (simp add: strnlen_def)

lemma strlen_none[simp]: "\<not>(isCString xs) \<Longrightarrow> strlen xs = None"
 by (simp add: isCString_def strlen_def)

lemma strlen_some[simp]: "isCString xs \<Longrightarrow> \<exists>x. strlen xs = Some x"
 by (simp add: isCString_def strlen_def)
 
lemma strlen_nonzero[simp]: "isCString xs \<Longrightarrow> the (strlen (xs)) \<ge> 0"
 apply (unfold terminator_def strlen_def takeCString_def isCString_def)
 by (induct xs) auto
 
lemma strlen_gt[simp]: "\<lbrakk>isCString xs; x \<noteq> terminator\<rbrakk> \<Longrightarrow> the (strlen (x # xs)) > the (strlen (xs))"
 apply (unfold terminator_def strlen_def takeCString_def isCString_def)
 by (induct xs) auto

lemma strlen_inc[simp]: "\<lbrakk>isCString xs; x \<noteq> terminator\<rbrakk> \<Longrightarrow> the (strlen (x # xs)) = the (strlen (xs)) + 1"
 apply (unfold terminator_def strlen_def takeCString_def isCString_def)
 by (induct xs) auto

(* Testing: *)
definition str_hi :: "char list" where "str_hi = [CHR ''H'', CHR ''i'', CHR ''!'', terminator]"

lemma "strlen [] = None" 
 by (simp add: strlen_def isCString_def)
lemma "strlen [CHR ''H'', CHR ''i'', CHR ''!''] = None"
 by (simp add: strlen_def isCString_def terminator_def)
lemma "strlen [CHR ''H'', CHR ''i'', CHR ''!'', terminator] = Some 3"
 by (simp add: strlen_def isCString_def terminator_def takeCString_def)
  
end