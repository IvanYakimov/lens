theory Strcat
imports "$PWD/CString" "$PWD/Strlen" "$PWD/Strstr"
begin

fun replacePrefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"replacePrefix [] ys = []" |
"replacePrefix xs [] = xs" |
"replacePrefix (x#xs) (y#ys) = y # (replacePrefix xs ys)"

value "let xs = [3,5,6,7,8,7,7]; ys = [1::int,2,3] in
replacePrefix xs ys"

lemma 
"length ys \<le> length xs \<Longrightarrow> length (replacePrefix xs ys) = length xs"
apply (induct xs)
apply auto
quickcheck
oops

lemma
"length ys \<le> length xs \<Longrightarrow> replacePrefix xs ys = ys @ (drop (length ys) xs)"
apply (induct xs) nitpick 2
apply auto
oops

(* -------------------------------- Definitions ------------------------------------ *)
definition strcat :: "string \<Rightarrow> string \<Rightarrow> string option" where
"strcat xs ys = (let ws = takeCString xs @ takeFullCString ys; n = length ws in (
 if isCString xs \<and> isCString ys \<and> n \<le> length xs
 then Some (replacePrefix xs ws)
 else None))"
  
lemma strcat_simps[simp]:
"strcat xs ys = (let ws = takeCString xs @ takeFullCString ys; n = length ws in (
 if isCString xs \<and> isCString ys \<and> n \<le> length xs then Some (replacePrefix xs ws)  else None))"
 by (simp add: strcat_def)
 
(* ------------------------------- Lemmas --------------------------------- *) 
lemma [simp]: 
"takeFullCString emptyString = emptyString"
by auto

lemma [simp]:
"takeCString emptyString = []"
by auto

lemma [simp]:
"isCString emptyString"
by simp

(* -------------------------- *)

value "let  a = Char Nibble0 Nibble0;
    xs = [Char Nibble0 Nibble0] in
    strcat (a#xs) emptyString"

value "strcat emptyString emptyString"

value "strcat (str_hello @ (replicate 10 CHR ''a'')) str_world"
value "strcat str_hello emptyString"
value "strcat emptyString emptyString"

lemma "strcat xs ys = Some (ws::string) \<Longrightarrow> length ws = length xs"
 apply (induct xs)
  apply auto
quickcheck
oops

value "strcat emptyString emptyString"

lemma
"(isCString xs \<Longrightarrow> the (strcat xs emptyString) = xs) \<Longrightarrow> isCString (a # xs) \<Longrightarrow> the (strcat (a # xs) emptyString) = a # xs"
quickcheck
oops

lemma
"isCString xs \<Longrightarrow> the (strcat xs emptyString) = xs"
quickcheck
apply (induct xs) 
apply simp
oops
(* --------------------------------- Experimental --------------------------------- *)
experiment begin 
lemma 
"strcat xs ys = Some ws \<Longrightarrow> \<exists>zs. strstr ws ys = Some (ys @ zs)"
nitpick
oops

value "let ws = [Char Nibble0 Nibble0];
    xs = [Char Nibble0 Nibble0];
    ys = [Char Nibble0 Nibble0];
    zs = [Char Nibble0 Nibble0] in
    strstr xs ys"
 
value "let ws = strcat (str_hello @ replicate 10 CHR '' '') str_world
 in strstr (the ws) str_world"
end
 
end