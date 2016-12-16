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

end