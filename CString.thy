theory CString
imports String
begin

(* Author: Ivan Yakimov, Siberian Federal University, e-mail: ivan.yakimov.research@yandex.ru *)

type_synonym string = "char list"

definition terminator :: "char" where "terminator = Char Nibble0 Nibble0"

definition isCString :: "string \<Rightarrow> bool" where
"isCString xs = (terminator \<in> set xs)"

definition takeCString :: "char list \<Rightarrow> char list" where
"takeCString xs = (takeWhile (\<lambda>x. x \<noteq> terminator) xs)"

end