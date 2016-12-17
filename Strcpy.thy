theory Strcpy
imports "$PWD/CString" "$PWD/Strlen"
begin

value "takeWhile (\<lambda>x. x \<noteq> 0) [1,3,4,5,6::int]"

definition strcpy :: "string \<Rightarrow> string \<Rightarrow> string option" where
"strcpy xs ys = (let n = the (strlen ys) in
  (if isCString ys \<and> n < int (size xs) 
    then Some ((takeCString ys) @ [terminator] @ drop (nat n + 1) xs)  
    else None))"

lemma strcpy_simp[simp]: "strcpy xs ys = (let n = the (strlen ys) in
  (if isCString ys \<and> n < int (size xs) 
    then Some ((takeCString ys) @ [terminator] @ drop (nat n + 1) xs)  
    else None))" by (simp add: strcpy_def)
    
lemma isCString_tail[simp]: "isCString ys \<Longrightarrow> takeCString ((takeCString ys) @ [terminator] @ ws) = takeCString ys" 
 by (induct ys) auto
 
lemma "\<lbrakk>isCString ys; the (strlen ys) < int (size xs)\<rbrakk>
\<Longrightarrow> the (strcpy xs ys) = ((takeCString ys) @ [terminator] @ drop (nat (the (strlen ys)) + 1) xs)"
 by simp
 
lemma "the (strcpy xs ys) = ((takeCString ys) @ [terminator] @ drop (nat (the (strlen ys)) + 1) xs)
 \<Longrightarrow> the (strcpy xs ys) = takeCString ys"
 apply (induct ys)
 apply auto
    
value "let   ws = [Char Nibble0 Nibble0];
    ys = [Char Nibble0 Nibble0]
  in 
  takeCString (ys @ ws)"

lemma strcpy_nil1[simp]: "strcpy xs [] = None" by auto
lemma strcpy_nil2[simp]: "strcpy [] xs = None" by auto
lemma strcpy_none1[simp]: "\<not>isCString ys \<Longrightarrow> strcpy xs ys = None" by auto

lemma strcpy_none2[simp]: assumes s: "the (strlen ys) \<ge> int (size xs)" shows "strcpy xs ys = None"
proof -
 have "\<not>(the (strlen ys) < int (size xs))" using s by auto
 thus "strcpy xs ys = None" by simp
qed

lemma strcpy_exists[simp]: "\<lbrakk>isCString ys; the (strlen ys) < int (size xs)\<rbrakk> \<Longrightarrow> \<exists>zs. strcpy xs ys = zs" by auto 

lemma "\<lbrakk>isCString ys; the (strlen ys) < int (size xs)\<rbrakk>
\<Longrightarrow> takeCString (the (strcpy xs ys)) = takeCString ys"
 

lemma "\<lbrakk>isCString ys; the (strlen ys) < int (size xs)\<rbrakk> \<Longrightarrow> takeCString (the (strcpy xs ys)) = takeCString ys" 
 apply (induct ys)
 apply auto
oops

value "strcpy str_hello str_el"
    
end