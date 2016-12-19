theory Strcmp
imports Main String Enum "$PWD/CString"
begin

type_synonym charCmp = "char \<Rightarrow> char \<Rightarrow> int"

definition "char_a" where "char_a = CHR ''a''"

value "char_a = char_a"

(*
/**
 * strcmp - Compare two strings
 * @cs: One string
 * @ct: Another string
 */
int strcmp(const char *cs, const char *ct)
{
	unsigned char c1, c2;

	while (1) {
		c1 = *cs++;
		c2 = *ct++;
		if (c1 != c2)
			return c1 < c2 ? -1 : 1;
		if (!c1)
			break;
	}
	return 0;
}
*)

value "dropWhile (\<lambda>(x, y). x - y = 0) [(1::int,1),(2,2),(3,3),(1::int,2)]"

(*
definition pairCmp :: "('a \<Rightarrow> 'a \<Rightarrow> int) \<Rightarrow> ('a * 'a) list \<Rightarrow> int" where
"pairCmp P ps = (
 let rs = dropWhile (\<lambda>(a,b). P a b = 0) ps in (
  case rs of 
  [] \<Rightarrow> 0 | 
  (a,b)#ps \<Rightarrow> P a b))"

value "pairCmp (\<lambda>a b. a-b) [(1::int,1),(2,2),(3,3),(1,2)]"
*)

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

(*
definition listCmp :: "(('a * 'a) \<Rightarrow> int) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> int" where
"listCmp P xs ys = (
 let n1 = length xs; n2 = length ys; l = min n1 n2; ps = zip xs ys in  
  if n1 = n2
  then pairCmp P ps
  else 28)"

value "min (1::int) 2"
*)

definition strcmp :: "((char * char) \<Rightarrow> int) \<Rightarrow> string \<Rightarrow> string \<Rightarrow> int option" where
"strcmp P xs ys = (
 if isCString xs \<and> isCString ys 
 then Some (pairCmp P (zip (takeFullCString xs) (takeFullCString ys))) 
 else None)"

lemma strcmp_simp[simp]:
"strcmp P xs ys = (if isCString xs \<and> isCString ys then Some (pairCmp P (zip (takeFullCString xs) (takeFullCString ys))) else None)"
by (simp add: strcmp_def)

value "strcmp (\<lambda>(a,b). if a = b then 0 else -1) str_hello (str_hello @ [CHR ''a''])"

(* The result of strcmp depends only on 'prefix' of the c-string before the null-terminator *) 
lemma strcmp_app[simp]: 
"\<lbrakk>isCString xs; isCString ys; the (strcmp P xs ys) = k\<rbrakk> \<Longrightarrow> the (strcmp P (xs @ ws) (ys @ us)) = k"
 by (induct xs) auto
 
(* Adding new equal characters to the beginning of two 'equal' (in terms of strcmp) strings we obtain new 'equal' strings *)
lemma strcmp_inc[simp]: 
"\<lbrakk>isCString xs; isCString ys; x \<noteq> terminator; P (x, x) = 0\<rbrakk> \<Longrightarrow> the (strcmp P xs ys) = the (strcmp P (x#xs) (x#ys))"
 by (induct xs) auto
 
experiment begin

end
  
value "pairCmp (\<lambda>(a, b). a-b) [(1::int,1),(2,2),(3,3),(1,2)]"

(*
fun pairCmp :: "('a \<Rightarrow> 'a \<Rightarrow> int) \<Rightarrow> ('a * 'a) list \<Rightarrow> int" where
"pairCmp P [] = 0" |
"pairCmp P ((a,b)#ps) = (let n = P a b in (if n = 0 then pairCmp P ps else n))"
*)
 
end