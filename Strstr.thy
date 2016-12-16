theory Strstr
imports Main "$PWD/Strlen" "$PWD/CString" List
begin

(* Author: Ivan Yakimov, ivan.yakimov.research@yandex.ru *)

value "take (length [1,2]) [1::int,2,3,4]" 
 
(* helper for strstr *)
fun listList :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"listList [] _ = []" |
"listList _ [] = []" |
"listList (x#xs) ys = 
 (if (take (length ys) (x#xs) = ys)
  then x#xs
  else listList xs ys)"
  
lemma listList_Nil[simp]: "listList xs [] = []"
 by (induct xs) auto

lemma listList_Inc[simp]:"\<lbrakk>listList xs (y#ys) = (y#ys) @ ws; x \<noteq> y\<rbrakk> \<Longrightarrow> listList (x#xs) (y#ys) = (y#ys) @ ws"
 by (induct xs) auto
 
definition strstr :: "string \<Rightarrow> string \<Rightarrow> string option" where
"strstr xs ys = 
 (if (isCString xs \<and> isCString ys) \<and> (the (strlen ys) < the (strlen xs)) 
  then Some (listList xs (takeCString ys)) 
  else None)"
  
lemma strstr_simp[simp]:"strstr xs ys = 
 (if (isCString xs \<and> isCString ys) \<and> (the (strlen ys) < the (strlen xs)) 
  then Some (listList xs (takeCString ys)) 
  else None)" by (simp add: strstr_def)
  
definition strnstr :: "string \<Rightarrow> string \<Rightarrow> int \<Rightarrow> string option" where
"strnstr xs ys n = (if \<not> isCString ys then None else (if the (strlen ys) \<le> n then strstr xs ys else None))"

lemma strnstr_simp[simp]: 
"strnstr xs ys n = (if \<not> isCString ys then None else (if the (strlen ys) \<le> n then strstr xs ys else None))"
 by (simp add: strnstr_def)

lemma strstr_nil[simp]: "strstr [] [] = None" 
 by auto
lemma strstr_notCString[simp]: "\<not> (isCString xs \<and> isCString ys) \<Longrightarrow> strstr xs ys = None" 
 by auto
lemma strstr_overflow[simp]: "\<not> (the (strlen ys) < the (strlen xs)) \<Longrightarrow> strstr xs ys = None" 
 by auto
lemma strstr_listList[simp]:"\<lbrakk>isCString xs; isCString ys; the (strlen (ys)) < the (strlen xs)\<rbrakk> \<Longrightarrow> the (strstr xs ys) = listList xs (takeCString ys)"
 by auto

lemma "\<lbrakk>isCString xs; 
 isCString (y#ys); 
 the (strlen (y#ys)) < the (strlen xs);
 the (strlen xs) < the (strlen (x#xs));
 the (strstr xs (y#ys)) = (takeCString (y#ys)) @ ws; 
 x \<noteq> y \<rbrakk>
 \<Longrightarrow> the (strstr (x#xs) (y#ys)) = (takeCString (y#ys)) @ ws"
 by auto

lemma "\<lbrakk>isCString ys;
 the (strlen ys) \<le> n\<rbrakk> \<Longrightarrow>
 strnstr xs ys n = strstr xs ys" 
 by auto
 
lemma "\<lbrakk>\<not> (isCString ys) \<or> (the (strlen ys) > n)\<rbrakk> \<Longrightarrow> strnstr xs ys n = None"
 by auto

(* EXPERIMENT *)
(* TODO: *)
fun splitStr :: "nat \<Rightarrow>'a list \<Rightarrow> 'a list list" where
"splitStr 0 [] = [[]]" |
"splitStr n [] = [[]]" |
"splitStr n (x#xs) = (let l = length (x#xs); s = take n (x#xs) in
  (if l < n
   then [[]]
   else s # (splitStr n xs)))"
   
value "splitStr 0 [1,2,3,4,4]"
value "splitStr 3 []"
value "splitStr 3 [1,2,3,4,5,6,6::int]"
   
experiment
begin
 (* TODO: *)
 lemma "ys \<notin> set (sublists xs) \<Longrightarrow> listList xs ys = []"
  apply (induct xs)
   apply auto
 oops
end
  
end