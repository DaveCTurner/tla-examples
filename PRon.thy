theory PRon
  imports "HOL-TLA.TLA"
begin

lemma temp_imp_trans [trans]:
  assumes "\<turnstile> F \<longrightarrow> G"
  assumes "\<turnstile> G \<longrightarrow> H"
  shows "\<turnstile> F \<longrightarrow> H"
  using assms unfolding Valid_def by auto

lemma temp_impI:
  assumes "sigma \<Turnstile> P \<Longrightarrow> sigma \<Turnstile> Q"
  shows "sigma \<Turnstile> P \<longrightarrow> Q"
  using assms by auto

locale PRon =
  fixes x :: "nat stfun"
  assumes basevars_x: "basevars x"
  fixes nxt spec
  defines "nxt \<equiv> ACT (#0 < $x \<and> x$ = $x - #1)"
  defines "spec \<equiv> TEMP \<box>[nxt]_x \<and> WF(nxt)_x"

context PRon
begin

lemma "\<turnstile> spec \<longrightarrow> \<box>[x$ < $x]_x"
proof -
  have "\<turnstile> spec \<longrightarrow> \<box>[nxt]_x" by (auto simp add: spec_def)
  also have "\<turnstile> \<box>[nxt]_x \<longrightarrow> \<box>[x$ < $x]_x" by (intro STL4, auto simp add: square_def nxt_def)
  finally show ?thesis .
qed

lemma "\<turnstile> spec \<longrightarrow> \<box>(Init (#0 < x) \<longrightarrow> \<diamond><x$ < $x>_x)"
  unfolding spec_def
  apply (fold leadsto_def)
proof (intro WF_leadsto)
  show "\<turnstile> [nxt]_x \<and> $(#0 < x) \<longrightarrow> $Enabled (<nxt>_x)"
    using basevars [OF basevars_x]
    apply (auto simp add: nxt_def square_def enabled_def angle_def)
    apply auto
    by fastforce

  show "\<turnstile> [nxt]_x \<and> <nxt>_x \<longrightarrow> <x$ < $x>_x"
    by (auto simp add: nxt_def square_def angle_def)

  have "\<turnstile> ([nxt]_x \<and> [\<not> nxt]_x) \<longrightarrow> unchanged x"
    by (auto simp add: square_def)
  from STL4 [OF this]
  show "\<turnstile> \<box>([nxt]_x \<and> [\<not> nxt]_x) \<longrightarrow> stable (#0 < x)"
    by (intro tempI temp_impI Stable [where A = "ACT unchanged x"], auto)
qed

