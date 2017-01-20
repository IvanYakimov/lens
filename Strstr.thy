theory Strstr
imports Main "$PWD/Strlen" "$PWD/CString" List
begin

(* Author: Ivan Yakimov, ivan.yakimov.research@yandex.ru *) 
(* helper for strstr *)
fun listList :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"listList [] _ = []" |
"listList _ [] = []" |
"listList (x#xs) ys = 
 (if (take (length ys) (x#xs) = ys)
  then x#xs
  else listList xs ys)"
  
lemma
"length xs < length ys \<Longrightarrow> listList xs ys = []"
 apply (induct xs)
  apply auto
 apply (induct ys)
  apply auto
done

lemma listList_nil[simp]: "listList xs [] = []"
 by (induct xs) auto
 
lemma listList_inc[simp]:
"\<lbrakk>ys = u#us; listList xs ys = ys @ ws; x \<noteq> hd ys\<rbrakk> \<Longrightarrow> listList (x#xs) ys = ys @ ws"
 by (induct xs) simp_all
 
value "listList [0::int,1,2] [1,2]"
 
definition strstr :: "string \<Rightarrow> string \<Rightarrow> string option" where
"strstr xs ys = 
 (if (isCString xs \<and> isCString ys) 
  then
   if (the (strlen ys) \<ge> the (strlen xs)) \<or> ys = emptyString
   then Some null
   else Some (listList xs (takeCString ys))  
  else None)"
lemma strstr_simp[simp]:
"strstr xs ys = 
 (if (isCString xs \<and> isCString ys) 
  then
   if (the (strlen ys) \<ge> the (strlen xs)) \<or> ys = emptyString
   then Some null
   else Some (listList xs (takeCString ys))  
  else None)"
by (simp add: strstr_def)
  
(* TODO: check the strnstr definition *)
definition strnstr :: "string \<Rightarrow> string \<Rightarrow> int \<Rightarrow> string option" where
"strnstr xs ys n = (if \<not> isCString ys then None else (if the (strlen ys) \<le> n then strstr xs ys else None))"

lemma strnstr_simp[simp]: 
"strnstr xs ys n = (if \<not> isCString ys then None else (if the (strlen ys) \<le> n then strstr xs ys else None))"
 by (simp add: strnstr_def)

lemma strstr_nil[simp]: 
"strstr null null = None" 
 by auto
 
lemma strstr_notCString[simp]: 
"\<not> (isCString xs \<and> isCString ys) \<Longrightarrow> strstr xs ys = None" 
 by auto

lemma strstr_overflow[simp]: 
"the (strlen ys) > the (strlen xs) \<Longrightarrow> strstr xs ys = Some null" 
 apply (induct xs)
  apply auto
 apply (induct ys)
  apply auto
 quickcheck
oops (* ! ! ! *)

lemma strstr_listList[simp]:
"\<lbrakk>isCString xs; isCString ys; the (strlen (ys)) < the (strlen xs)\<rbrakk> \<Longrightarrow> the (strstr xs ys) = listList xs (takeCString ys)"
 by auto

lemma (* ! ! ! *)
"isCString xs \<Longrightarrow> strstr xs emptyString = Some xs"
quickcheck
oops
 
lemma 
"\<lbrakk>ys = u#us;
 isCString xs; 
 isCString ys; 
 the (strlen ys) < the (strlen xs);
 the (strlen xs) < the (strlen (x#xs));
 x \<noteq> hd ys;
 the (strstr xs ys) = (takeCString ys) @ ws\<rbrakk>
 \<Longrightarrow> the (strstr (x#xs) ys) = (takeCString ys) @ ws"
 by auto

value "strstr emptyString emptyString = Some emptyString" (* ! *)
 
lemma 
"\<lbrakk>isCString ys;
 the (strlen ys) \<le> n\<rbrakk> \<Longrightarrow>
 strnstr xs ys n = strstr xs ys" 
 by auto
 
lemma "\<lbrakk>\<not> (isCString ys) \<or> (the (strlen ys) > n)\<rbrakk> \<Longrightarrow> strnstr xs ys n = None"
 by auto
    
end