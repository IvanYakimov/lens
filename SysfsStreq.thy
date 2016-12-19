theory SysfsStreq
imports "$PWD/CString"
begin

(*
/**
 * sysfs_streq - return true if strings are equal, modulo trailing newline
 * @s1: one string
 * @s2: another string
 *
 * This routine returns true iff two strings are equal, treating both
 * NUL and newline-then-NUL as equivalent string terminations.  It's
 * geared for use with sysfs input strings, which generally terminate
 * with newlines but are compared against values without newlines.
 */
bool sysfs_streq(const char *s1, const char *s2)
{
	while (*s1 && *s1 == *s2) {
		s1++;
		s2++;
	}

	if (*s1 == *s2)
		return true;
	if (!*s1 && *s2 == '\n' && !s2[1])
		return true;
	if (*s1 == '\n' && !s1[1] && !*s2)
		return true;
	return false;
}
*)*)*)*)

definition sysfs_streq :: "string \<Rightarrow> string \<Rightarrow> bool" where
"sysfs_streq xs ys = (if isCLine xs \<and> isCLine ys then takeCLine xs = takeCLine ys else False)"
lemma sysfs_streq_simp[simp]:
"sysfs_streq xs ys = (if isCLine xs \<and> isCLine ys then takeCLine xs = takeCLine ys else False)"
 by (simp add: sysfs_streq_def)

lemma "\<lbrakk>\<not> isCLine xs \<or> \<not> isCLine ys\<rbrakk> \<Longrightarrow> \<not> sysfs_streq xs ys" by auto
lemma "\<lbrakk>isCLine xs; isCLine ys; takeCLine xs \<noteq> takeCLine ys\<rbrakk> \<Longrightarrow> \<not> sysfs_streq xs ys" by(induct xs) auto
lemma "\<lbrakk>isCLine xs; isCLine ys; takeCLine xs = takeCLine ys\<rbrakk> \<Longrightarrow> sysfs_streq xs ys" by(induct xs) auto
 
value "sysfs_streq str_hello str_hello"
value "sysfs_streq [] []"
value "sysfs_streq str_hello bad_str"
value "sysfs_streq str_hello str_el"

end