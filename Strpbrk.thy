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
 
lemma list_pbrk_inc2[simp]:
"\<lbrakk>x \<notin> set ys; list_pbrk xs ys = ws\<rbrakk> \<Longrightarrow> list_pbrk (x#xs) ys = ws"
by (induct xs) auto

lemma list_pbrk_inc3[simp]:
"set xs \<inter> set ys = {} \<Longrightarrow> u \<in> set ys \<Longrightarrow> list_pbrk (xs @ [u] @ ws) ys = [u] @ ws"
by (induct xs) auto

lemma list_pbrk_inc4[simp]:
"set xs \<inter> set ys = {} \<Longrightarrow> u \<in> set ys \<Longrightarrow> list_pbrk (xs @ (u#ws)) ys = u#ws"
by (induct xs) auto
 
definition strpbrk :: "char list \<Rightarrow> char list \<Rightarrow> char list option" where
"strpbrk xs ys = (
  if isCString xs \<and> isCString ys
  then Some (list_pbrk (takeCString xs) (takeCString ys))
  else None)"

lemma strpbrk_simp[simp]:
"strpbrk xs ys = (
  if isCString xs \<and> isCString ys
  then Some (list_pbrk (takeCString xs) (takeCString ys))
  else None)"
 by (simp add: strpbrk_def)
 
(* TODO: improve *)
lemma strpbrk_inter[simp]: 
"\<lbrakk>isCString xs; isCString ys\<rbrakk> \<Longrightarrow> set (takeCString xs) \<inter> set (takeCString ys) = {} \<equiv> the (strpbrk xs ys) = []"
 by (induct xs)  auto

lemma strpbrk_nil[simp]:
"isCString xs \<Longrightarrow> isCString ys \<Longrightarrow> \<forall>y \<in> set ys. y \<notin> set xs \<Longrightarrow> the (strpbrk xs ys) = []" 
 by auto
 
lemma strpbkr_nil2:
"strpbrk [] ys = None"
by auto

lemma strpbrk_nil3[simp]:
"strpbrk xs [] = None"
by auto

lemma strpbrk_notNone[simp]:
"\<lbrakk>isCString xs; isCString ys; set (takeCString xs) \<inter> set (takeCString ys) \<noteq> {}\<rbrakk> \<Longrightarrow> strpbrk xs ys \<noteq> None"
by (induct xs)  auto 

lemma strpbrk_some[simp]:
"\<lbrakk>isCString xs; isCString ys; set (takeCString xs) \<inter> set (takeCString ys) \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>ws::string. strpbrk xs ys = Some ws"
by simp

lemma strpbrk_list_pbrk[simp]:
"\<lbrakk>isCString xs; isCString ys\<rbrakk> \<Longrightarrow> the (strpbrk xs ys) = list_pbrk (takeCString xs) (takeCString ys)"
 by simp
 
export_code strpbrk in "Haskell"

end