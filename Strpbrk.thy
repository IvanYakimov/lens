theory Strpbrk
imports Main List "$PWD/CString"
begin

definition list_pbrk :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"list_pbrk xs ys = dropWhile (\<lambda>x. x \<notin> set ys) xs"

lemma list_pbrk_simp[simp]:
"list_pbrk xs ys = dropWhile (\<lambda>x. x \<notin> set ys) xs"
 by (simp add: list_pbrk_def)
 
lemma list_pbrk_inter[simp]:
"set xs \<inter> set ys = {} \<equiv> list_pbrk xs ys = []"
 by (induct ys) auto

lemma list_pbrk_nil[simp]:
"\<forall>y \<in> set ys. y \<notin> set xs \<Longrightarrow> list_pbrk xs ys = []" 
 by auto

lemma list_pbrk_inc[simp]:
"\<lbrakk>list_pbrk (zs @ ws) ys = ws; z \<notin> set ys\<rbrakk> \<Longrightarrow> list_pbrk (z#zs @ ws) ys = ws"
 by (induct zs) auto
 
definition strpbrk :: "char list \<Rightarrow> char list \<Rightarrow> char list option" where
"strpbrk xs ys = (
 let ws = list_pbrk (takeCString xs) (takeCString ys) in (
  if isCString xs \<and> isCString ys
  then Some ws
  else None))"

lemma strpbrk_simp[simp]:
"strpbrk xs ys = (
 let ws = list_pbrk (takeCString xs) (takeCString ys) in (
  if isCString xs \<and> isCString ys
  then Some ws
  else None))"
 by (simp add: strpbrk_def)
 
(* TODO: improve *)
lemma strpbrk_nil[simp]:
"isCString xs \<Longrightarrow> isCString ys \<Longrightarrow> \<forall>y \<in> set ys. y \<notin> set xs \<Longrightarrow> the (strpbrk xs ys) = []" 
 by auto


 

  
end