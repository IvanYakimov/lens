theory SysfsStreq
imports "$PWD/CString"
begin

definition sysfs_streq :: "string \<Rightarrow> string \<Rightarrow> bool" where
"sysfs_streq xs ys = (if isCLine xs \<and> isCLine ys then takeCLine xs = takeCLine ys else False)"
lemma sysfs_streq_simp[simp]:
"sysfs_streq xs ys = (if isCLine xs \<and> isCLine ys then takeCLine xs = takeCLine ys else False)"
 by (simp add: sysfs_streq_def)

lemma "\<lbrakk>\<not> isCLine xs \<or> \<not> isCLine ys\<rbrakk> \<Longrightarrow> \<not> sysfs_streq xs ys" by auto
lemma "\<lbrakk>isCLine xs; isCLine ys; takeCLine xs \<noteq> takeCLine ys\<rbrakk> \<Longrightarrow> \<not> sysfs_streq xs ys" by(induct xs) auto
lemma "\<lbrakk>isCLine xs; isCLine ys; takeCLine xs = takeCLine ys\<rbrakk> \<Longrightarrow> sysfs_streq xs ys" by(induct xs) auto

end