theory Prelims
  imports "../TLA-Utils"
begin

typedecl Client
typedecl Resource

definition modifyAt :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "modifyAt f a0 mb a \<equiv> if a = a0 then mb (f a) else f a"

lemma modifyAt_eq_simp[simp]: "modifyAt f a mb a = mb (f a)" by (simp add: modifyAt_def)
lemma modifyAt_ne_simp[simp]: "a \<noteq> a0 \<Longrightarrow> modifyAt f a0 mb a = f a" by (simp add: modifyAt_def)

definition updated :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> action"
  where "updated f a mb st \<equiv> f (snd st) = modifyAt (f (fst st)) a mb"

lemma "\<turnstile> updated f a mb \<longrightarrow> id<f$,#a> = (\<lambda>f a. mb (f a))<$f,#a>" by (auto simp add: updated_def modifyAt_def)
lemma "a \<noteq> a' \<Longrightarrow> \<turnstile> updated f a mb \<longrightarrow> id<f$,#a'> = id<$f,#a'>" by (auto simp add: updated_def modifyAt_def)

definition add :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where "add A B \<equiv> B \<union> A"
definition del :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where "del A B \<equiv> B - A"

lemma add_simp[simp]: "(r \<in> add A B) = (r \<in> A \<or> r \<in> B)" by (auto simp add: add_def)
lemma del_simp[simp]: "(r \<in> del A B) = (r \<notin> A \<and> r \<in> B)" by (auto simp add: del_def)

lemma wf_less_finite:
  shows "wf {(S1, S2). finite S2 \<and> S1 \<subset> S2}"
  by (rule iffD1 [OF cong [OF refl, where f = wf and x = finite_psubset]],
      simp_all, auto simp add: finite_psubset_def)

end