theory DigitwiseNumbers
  imports Main
begin

fun value10 :: "nat list \<Rightarrow> nat"
  where
    "value10 [] = 0"
  | "value10 (n#ns) = n + 10 * value10 ns"

definition wellformed :: "nat list \<Rightarrow> bool"
  where "wellformed ds \<equiv> set ds \<subseteq> {0..9} \<and> (ds = [] \<or> last ds \<noteq> 0)"

lemma wellformed_Nil[simp]: "wellformed []" by (simp add: wellformed_def)
lemma wellformed_ConsI: "wellformed ds \<Longrightarrow> d \<le> 9 \<Longrightarrow> (ds = [] \<Longrightarrow> 0 < d) \<Longrightarrow> wellformed (d#ds)" by (auto simp add: wellformed_def)
lemma wellformed_ConsE: "wellformed (d#ds) \<Longrightarrow> wellformed ds" by (auto simp add: wellformed_def, cases "ds = []", simp_all)


function (sequential) applyCarry1 :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  where
    "applyCarry1 0 ds = ds"
  | "applyCarry1 c [] = c mod 10 # applyCarry1 (c div 10) []"
  | "applyCarry1 c (d#ds) = ((c+d) mod 10) # applyCarry1 ((c+d) div 10) ds"
  by pat_completeness auto
termination applyCarry1 by (relation "inv_image (measure length <*lex*> measure id) prod.swap", auto)

lemma applyCarry1_induct [case_names Zero NonZero Cons]:
  fixes c :: nat
  fixes ds :: "nat list"
  assumes Zero: "\<And>ds. P 0 ds"
  assumes NonZero: "\<And>c. \<lbrakk> 0 < c; P (c div 10) []; applyCarry1 c [] = c mod 10 # applyCarry1 (c div 10) [] \<rbrakk> \<Longrightarrow> P c []"
  assumes Cons: "\<And>c d ds. \<lbrakk> 0 < c; P ((c+d) div 10) ds; applyCarry1 c (d#ds) = (c+d) mod 10 # applyCarry1 ((c+d) div 10) ds \<rbrakk> \<Longrightarrow> P c (d#ds)"
  shows "P c ds"
proof (induct c ds rule: applyCarry1.induct)
  from Zero show "\<And>ds. P 0 ds" .
next
  fix c
  assume "P (Suc c div 10) []"
  with NonZero [of "Suc c"] show "P (Suc c) []" by simp
next
  fix c d ds
  assume "P ((Suc c + d) div 10) ds"
  with Cons [of "Suc c"] show "P (Suc c) (d # ds)" by simp
qed

lemma value10_applyCarry1: "value10 (applyCarry1 c ds) = c + value10 ds"
  by (induct c ds rule: applyCarry1_induct, simp_all)

lemma applyCarry1_last[simp]: "(applyCarry1 c ds = []) \<longleftrightarrow> (c = 0 \<and> ds = [])"
  by (induct c ds rule: applyCarry1_induct, simp_all)

lemma applyCarry1_wellformed: "wellformed ds \<Longrightarrow> wellformed (applyCarry1 c ds)"
proof (induct c ds rule: applyCarry1_induct)
  case (Cons c d ds)
  thus ?case
    unfolding Cons.hyps(3) using wellformed_ConsE
  proof (intro wellformed_ConsI Cons.hyps(2))
    assume "applyCarry1 ((c + d) div 10) ds = []" "0 < c"
    thus "0 < (c + d) mod 10" by auto
  qed simp_all
qed (auto simp add: wellformed_def)

fun applyCarry2 :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list"
  where
    "applyCarry2 c [] ds = applyCarry1 c ds"
  | "applyCarry2 c ds [] = applyCarry1 c ds"
  | "applyCarry2 c (d1#ds1) (d2#ds2) = ((c+d1+d2) mod 10) # applyCarry2 ((c+d1+d2) div 10) ds1 ds2"

lemma applyCarry2_induct [case_names Nil1 Nil2 Cons]:
  fixes c :: nat
  fixes ds1 ds2 :: "nat list"
  assumes Nil1: "\<And>c ds. \<lbrakk> applyCarry2 c [] ds = applyCarry1 c ds \<rbrakk> \<Longrightarrow> P c [] ds"
  assumes Nil2: "\<And>c ds. \<lbrakk> applyCarry2 c ds [] = applyCarry1 c ds \<rbrakk> \<Longrightarrow> P c ds []"
  assumes Cons: "\<And>c d1 ds1 d2 ds2. \<lbrakk> applyCarry2 c (d1#ds1) (d2#ds2) = ((c+d1+d2) mod 10) # applyCarry2 ((c+d1+d2) div 10) ds1 ds2; P ((c+d1+d2) div 10) ds1 ds2 \<rbrakk> \<Longrightarrow> P c (d1#ds1) (d2#ds2)"
  shows "P c ds1 ds2"
proof (induct c ds1 ds2 rule: applyCarry2.induct)
  fix c ds
  from Nil1 [of c ds] show "P c [] ds" by simp
next
  fix c d ds
  from Nil2 [of c "d#ds"] show "P c (d#ds) []" by simp
next
  fix c d1 ds1 d2 ds2
  assume p: "P ((c + d1 + d2) div 10) ds1 ds2"
  show "P c (d1 # ds1) (d2 # ds2)" by (intro Cons p, simp)
qed

lemma value10_applyCarry2: "value10 (applyCarry2 c ds1 ds2) = c + value10 ds1 + value10 ds2"
  by (induct c ds1 ds2 rule: applyCarry2_induct, simp_all add: value10_applyCarry1)

lemma applyCarry2_last[simp]: "(applyCarry2 c ds1 ds2 = []) \<longleftrightarrow> (c = 0 \<and> ds1 = [] \<and> ds2 = [])"
  by (induct c ds1 ds2 rule: applyCarry2_induct, simp_all)

lemma applyCarry2_wellformed:
  assumes wf1: "wellformed ds1"
  assumes wf2: "wellformed ds2"
  shows "wellformed (applyCarry2 c ds1 ds2)"
  using applyCarry1_wellformed [OF wf1] applyCarry1_wellformed [OF wf2] assms
proof (induct c ds1 ds2 rule: applyCarry2_induct)
  case (Cons c d1 ds1 d2 ds2)
  from `wellformed (d1 # ds1)` `wellformed (d2 # ds2)` have wf12: "wellformed ds1" "wellformed ds2" by (metis wellformed_ConsE)+
  show ?case unfolding Cons
  proof (intro wellformed_ConsI Cons applyCarry1_wellformed wf12)
    assume "applyCarry2 ((c + d1 + d2) div 10) ds1 ds2 = []" hence p: "(c + d1 + d2) div 10 = 0" "ds1 = []" "ds2 = []" by simp_all
    with `wellformed (d1 # ds1)` `wellformed (d2 # ds2)`
    show "0 < (c + d1 + d2) mod 10" by (auto simp add: wellformed_def)
  qed simp
qed simp_all
