theory Strcpy
imports "$PWD/CString" "$PWD/Strlen"
begin

(* Author: Ivan Yakimov, ivan.yakimov.research@yandex.ru *)

definition strcpy :: "string \<Rightarrow> string \<Rightarrow> string option" where
"strcpy xs ys = (let n = the (strlen ys) in
  (if isCString ys \<and> n < int (size xs) 
    then Some ((takeFullCString ys) @ drop (nat n + 1) xs)  
    else None))"

lemma strcpy_simp[simp]: "strcpy xs ys = (let n = the (strlen ys) in
  (if isCString ys \<and> n < int (size xs) 
    then Some ((takeFullCString ys) @ drop (nat n + 1) xs)  
    else None))" by (simp add: strcpy_def)

lemma strcpy_nil1[simp]: 
 "strcpy xs [] = None" by auto
lemma strcpy_nil2[simp]: 
 "strcpy [] xs = None" by auto
lemma strcpy_none1[simp]: 
 "\<not>isCString ys \<Longrightarrow> strcpy xs ys = None" by auto
lemma strcpy_none2[simp]: 
 "\<lbrakk>the (strlen ys) \<ge> int (size xs)\<rbrakk> \<Longrightarrow> strcpy xs ys = None" by auto
lemma strcpy_exists1[simp]:
 "\<lbrakk>isCString ys; the (strlen ys) < int (size xs)\<rbrakk> \<Longrightarrow> \<exists>zs. strcpy xs ys = zs" by auto 
lemma strcpy_exists2[simp]:
 "isCString ys \<Longrightarrow> nat (the (strlen ys)) < size xs \<Longrightarrow> \<exists>ws. the (strcpy xs ys) = (takeFullCString ys) @ ws"
 by (induct ys) auto
lemma strcpy_exists3[simp]:
 "\<lbrakk>isCString ys; nat (the (strlen ys)) < size xs\<rbrakk> \<Longrightarrow> length (the (strcpy xs ys)) = size xs"
 by (induct xs) auto
    
end