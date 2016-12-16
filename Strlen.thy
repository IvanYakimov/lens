theory Strlen
imports Main String List "$PWD/CString" "$PWD/ListHelper"
begin

(* Author: Ivan Yakimov, e-mail: ivan.yakimov.research@yandex.ru *)

definition strlen :: "char list \<Rightarrow> int option" where
"strlen xs = 
 (if \<not> (isCString xs) 
  then None
  else Some (int (length (takeCString xs))))"
  
lemma strlen_simp[simp]:"strlen xs = 
 (if \<not> (isCString xs) 
  then None
  else Some (int (length (takeCString xs))))" by (simp add: strlen_def)

definition strnlen :: "char list \<Rightarrow> int \<Rightarrow> int option" where
"strnlen xs n= 
 (if n \<noteq> int (length xs) 
  then None
  else strlen xs)"
  
lemma strnlen_simp[simp]:"strnlen xs n= 
 (if n \<noteq> int (length xs) 
  then None
  else strlen xs)" by (simp add: strnlen_def)

(* strlen properties *)
(* The result is only defined for null-terminated strings. *)
lemma strlen_none[simp]: "\<not>(isCString xs) \<Longrightarrow> strlen xs = None" 
 by simp

(* For each null-terminated string result is defined and it is indeed some integer number. *)
lemma strlen_some[simp]: "isCString xs \<Longrightarrow> \<exists>(n::int). strlen xs = Some n" 
 by simp

(* For each null-terminated string result is greater than zero *)
lemma strlen_nonzero[simp]: "isCString xs \<Longrightarrow> the (strlen (xs)) \<ge> 0"
 by (induct xs) auto

(* Let xs be a null-terminated string and let x be some not-null symbol.
The 'strlen' of string x#xs is greater than strlen' of the original xs string. *)
lemma strlen_gt[simp]: "\<lbrakk>isCString xs; x \<noteq> terminator\<rbrakk> \<Longrightarrow> the (strlen (x # xs)) > the (strlen (xs))"
 by (induct xs) auto

(* Let xs be a null-terminated string and let x be some not-null symbol.
The 'strlen' of string x#xs is equal to 'strlen' of string xs increased by one. *)
lemma strlen_inc[simp]: "\<lbrakk>isCString xs; x \<noteq> terminator\<rbrakk> \<Longrightarrow> the (strlen (x # xs)) = the (strlen (xs)) + 1"
 by (induct xs) auto

(* strnlen properties *)
lemma "n \<noteq> int (length xs) \<Longrightarrow> strnlen xs n = None"
 by simp
 
lemma "n = int (length xs) \<Longrightarrow> strnlen xs n = strlen xs"
 by simp

(* Testing: *)
definition str_hi :: "char list" where "str_hi = [CHR ''H'', CHR ''i'', CHR ''!'', terminator]"

lemma "strlen [] = None" 
 by simp
lemma "strlen [CHR ''H'', CHR ''i'', CHR ''!''] = None"
 by simp
lemma "strlen [CHR ''H'', CHR ''i'', CHR ''!'', terminator] = Some 3"
 by simp
  
end