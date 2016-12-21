theory Strcmp
imports Main String Enum "$PWD/CString"
begin

definition pairCmp :: "(('a * 'a) \<Rightarrow> int) \<Rightarrow> ('a * 'a) list \<Rightarrow> int" where
"pairCmp CMP ps = (
 let rs = dropWhile (\<lambda>p. CMP p = 0) ps in (
  case rs of 
   [] \<Rightarrow> 0 | 
   p#ps \<Rightarrow> CMP p))"
  
lemma pairCmp_simp[simp]:
"pairCmp CMP ps = (
 let rs = dropWhile (\<lambda>p. CMP p = 0) ps in (
  case rs of 
   [] \<Rightarrow> 0 | 
   p#ps \<Rightarrow> CMP p))"
 by (simp add: pairCmp_def) 

lemma pairCmp_zero[simp]: 
"\<forall>p \<in> set ps. P p = 0 \<Longrightarrow> pairCmp P ps = 0"
 by (induct ps) auto
 
lemma pairCmp_nonzero[simp]:
"\<exists>p \<in> set ps. P p \<noteq> 0 \<Longrightarrow> pairCmp P ps \<noteq> 0"
 by (induct ps) auto

definition strcmp :: "((char * char) \<Rightarrow> int) \<Rightarrow> string \<Rightarrow> string \<Rightarrow> int option" where
"strcmp P xs ys = (
 if isCString xs \<and> isCString ys 
 then Some (pairCmp P (zip (takeFullCString xs) (takeFullCString ys))) 
 else None)"
lemma strcmp_simp[simp]:
"strcmp P xs ys = (if isCString xs \<and> isCString ys then Some (pairCmp P (zip (takeFullCString xs) (takeFullCString ys))) else None)"
by (simp add: strcmp_def)

(* The result of strcmp depends only on 'prefix' of the c-string before the null-terminator *) 
lemma strcmp_app[simp]: 
"\<lbrakk>isCString xs; isCString ys; the (strcmp P xs ys) = k\<rbrakk> \<Longrightarrow> the (strcmp P (xs @ ws) (ys @ us)) = k"
 by (induct xs) auto
 
(* Adding new equal characters to the beginning of two 'equal' (in terms of strcmp) strings we obtain new 'equal' strings *)
lemma strcmp_inc[simp]: 
"\<lbrakk>isCString xs; isCString ys; x \<noteq> terminator; P (x, x) = 0\<rbrakk> \<Longrightarrow> the (strcmp P xs ys) = the (strcmp P (x#xs) (x#ys))"
 by (induct xs) auto
 
end