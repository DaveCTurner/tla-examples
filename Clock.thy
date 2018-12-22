theory Clock
  imports "TLA-Utils"
begin

definition next_hour :: "nat \<Rightarrow> nat" where "\<And>n. next_hour n \<equiv> if n = 12 then 1 else n+1"

lemma next_hour_induct [case_names base step, consumes 1]:
  fixes m :: nat
  assumes type: "m \<in> {1..12}"
  assumes base: "P 1"
  assumes step: "\<And>n. 1 \<le> n \<Longrightarrow> n < 12 \<Longrightarrow> P n \<Longrightarrow> P (next_hour n)"
  shows "P m"
  using type
proof (induct m)
  case (Suc m)
  from `Suc m \<in> {1..12}` have "m = 0 \<or> (m \<in> {1..12} \<and> 1 \<le> m \<and> m < 12)" by auto
  with base show ?case
  proof (elim disjE conjE)
    assume "m \<in> {1..12}" with Suc have "P m" "1 \<le> m" "m < 12" by simp_all
    hence "P (next_hour m)" by (intro step, auto)
    with `m < 12` show ?case by (simp add: next_hour_def)
  qed simp
qed simp

locale HourClock =
  fixes hr :: "nat stfun"
  assumes hr_basevar: "basevars hr"
  fixes HCini HCnxt HC
  assumes HCini_def: "HCini \<equiv> PRED hr \<in> #{1..12}"
  assumes HCnxt_def: "HCnxt \<equiv> ACT hr$ = next_hour<$hr>"
  assumes HC_def:    "HC    \<equiv> TEMP Init HCini \<and> \<box>[HCnxt]_hr \<and> WF(HCnxt)_hr"

context HourClock
begin

lemma HCnxt_angle[simp]: "ACT <HCnxt>_hr = ACT HCnxt"
  unfolding HCnxt_def angle_def next_hour_def by auto

lemma HCnxt_enabled[simp]: "PRED (Enabled HCnxt) = PRED #True"
  using basevars [OF hr_basevar] unfolding enabled_def HCnxt_def by auto

lemma HC_safety: "\<turnstile> HC \<longrightarrow> \<box> HCini"
  unfolding HC_def HCini_def HCnxt_def next_hour_def by (auto_invariant, auto)

lemma HC_liveness_step:
  assumes n: "n \<in> {1..12}"
  shows "\<turnstile> HC \<longrightarrow> (hr = #n \<leadsto> hr = #(next_hour n))"
proof -
  from basevars [OF hr_basevar]
  have "\<turnstile> \<box>[HCnxt]_hr \<and> WF(HCnxt)_hr \<longrightarrow> (hr = #n \<leadsto> hr = #(next_hour n))"
    apply (intro WF1, auto simp add: HCnxt_def square_def next_hour_def angle_def enabled_def, auto)
    apply fastforce
    by fastforce
  thus ?thesis
    by (auto simp add: HC_def)
qed

lemma HC_liveness_progress_forwards:
  assumes m: "m \<in> {1..12}"
  assumes n: "n \<in> {1..12}"
  assumes mn: "m \<le> n"
  shows "\<turnstile> HC \<longrightarrow> (hr = #m \<leadsto> hr = #n)"
  using n mn
proof (induct n rule: next_hour_induct)
  case base with m show ?case apply auto using LatticeReflexivity by blast
next
  case (step n)
  hence "m \<le> n \<or> m = next_hour n" by (auto simp add: next_hour_def)
  thus ?case
  proof (elim disjE)
    assume "m = next_hour n" thus ?case apply auto using LatticeReflexivity by blast
  next
    assume "m \<le> n"
    with step have "\<turnstile> HC \<longrightarrow> (hr = #m \<leadsto> hr = #n)" by blast
    also from step have "\<turnstile> HC \<longrightarrow> (hr = #n \<leadsto> hr = #(next_hour n))"
      by (intro HC_liveness_step, auto)
    finally show ?thesis .
  qed
qed

lemma HC_liveness_progress:
  assumes m: "m \<in> {1..12}"
  assumes n: "n \<in> {1..12}"
  shows "\<turnstile> HC \<longrightarrow> (hr = #m \<leadsto> hr = #n)"
proof -
  from m have "\<turnstile> HC \<longrightarrow> (hr = #m \<leadsto> hr = #12)" by (intro HC_liveness_progress_forwards, auto)
  also from HC_liveness_step [where n = 12]
  have "\<turnstile> HC \<longrightarrow> (hr = #12 \<leadsto> hr = #1)" by (simp add: next_hour_def)
  also from n have "\<turnstile> HC \<longrightarrow> (hr = #1 \<leadsto> hr = #n)" by (intro HC_liveness_progress_forwards, auto)
  finally show ?thesis .
qed

lemma HC_liveness:
  assumes n: "n \<in> {1..12}"
  shows "\<turnstile> HC \<longrightarrow> \<box>\<diamond> hr = #n"
proof -
  from HC_safety have "\<turnstile> HC \<longrightarrow> ((#True :: stpred) \<leadsto> HCini)"
    by (intro imp_leadsto_invariant, simp)

  also have "\<turnstile> HC \<longrightarrow> (HCini \<leadsto> (\<exists> h0. #(h0 \<in> {1..12}) \<and> hr = #h0))"
    by (intro imp_imp_leadsto, auto simp add: HCini_def)

  also have "\<turnstile> HC \<longrightarrow> ((\<exists> h0. #(h0 \<in> {1..12}) \<and> hr = #h0) \<leadsto> hr = #n)"
    unfolding inteq_reflection [OF leadsto_exists]
  proof (intro imp_forall_leadsto)
    fix h0
    from n show "h0 \<in> {1..12} \<Longrightarrow> \<turnstile> HC \<longrightarrow> (hr = #h0 \<leadsto> hr = #n)" by (intro HC_liveness_progress)
  qed

  finally have "\<turnstile> HC \<longrightarrow> ((#True :: stpred) \<leadsto> hr = #n)" .
  thus ?thesis unfolding leadsto_def by auto
qed

end

locale HourMinuteClock = HourClock +
  fixes mn :: "nat stfun"
  assumes hr_mn_basevars: "basevars (hr,mn)"
  fixes HMCini Mn Hr HMCnxt HMC
  assumes HMCini_def: "HMCini \<equiv> PRED HCini \<and> mn \<in> #{0..59}"
  assumes Mn_def:     "Mn     \<equiv> ACT mn$ = (if $mn = #59 then #0 else $mn + #1)"
  assumes Hr_def:     "Hr     \<equiv> ACT ($mn = #59 \<and> HCnxt) \<or> ($mn < #59 \<and> unchanged hr)"
  assumes HMCnxt_def: "HMCnxt \<equiv> ACT (Mn \<and> Hr)"
  assumes HMC_def:    "HMC    \<equiv> TEMP Init HMCini \<and> \<box>[HMCnxt]_(hr, mn) \<and> WF(HMCnxt)_(hr, mn)"

context HourMinuteClock
begin

lemma HMCnxt_eq:
  "HMCnxt = ACT ($mn < #59 \<and> mn$ = $mn + #1 \<and> hr$ = $hr)
              \<or> ($mn = #59 \<and> mn$ = #0       \<and> $hr = #12 \<and> hr$ = #1)
              \<or> ($mn = #59 \<and> mn$ = #0       \<and> $hr \<noteq> #12 \<and> hr$ = $hr + #1)"
  by (intro ext, auto simp add: HMCnxt_def Mn_def Hr_def next_hour_def HCnxt_def)

lemma HMCnxt_angle[simp]: "ACT <HMCnxt>_(hr, mn) = ACT HMCnxt"
  by (intro ext, auto simp add: angle_def HMCnxt_eq)

lemma HMCnxt_enabled[simp]: "PRED Enabled HMCnxt = PRED mn \<le> #59"
  using basevars [OF hr_mn_basevars]
  apply (intro ext, auto simp add: enabled_def HMCnxt_eq next_hour_def)
  by (meson nat_less_le)

lemma HMC_safety: "\<turnstile> HMC \<longrightarrow> \<box> (hr \<in> #{1..12} \<and> mn \<in> #{0..59})"
proof -
  have "\<turnstile> HMC \<longrightarrow> \<box>HMCini"
  proof invariant
    fix sigma assume "sigma \<Turnstile> HMC" thus "sigma \<Turnstile> stable HMCini" and "sigma \<Turnstile> Init HMCini"
      by (intro Stable [where A = "ACT [HMCnxt]_(hr, mn)"], auto simp add: HMC_def square_def HMCnxt_def Hr_def HCnxt_def next_hour_def Mn_def HMCini_def Init_simps HCini_def)
  qed
  thus ?thesis by (simp add: HMCini_def HCini_def)
qed

definition timeIs :: "nat \<times> nat \<Rightarrow> stpred" where "timeIs t \<equiv> PRED (hr, mn) = #t"

lemma timeIs[simp]: "PRED (timeIs (h,m)) = PRED (hr = #h \<and> mn = #m)"
  by (auto simp add: timeIs_def)

lemma HMC_liveness_step:
  assumes "m \<le> 59"
  shows "\<turnstile> HMC \<longrightarrow> (timeIs (h, m) \<leadsto> (timeIs (if m = 59 then (if h = 12 then (1, 0) else (h+1, 0)) else (h, m+1))))"
    (is "\<turnstile> HMC \<longrightarrow> ?P")
proof -
  from assms
  have "\<turnstile> \<box>[HMCnxt]_(hr, mn) \<and> WF(HMCnxt)_(hr,mn) \<longrightarrow> ?P"
    by (intro WF1 actionI temp_impI, auto simp add: square_def, auto simp add: HMCnxt_eq)
  thus ?thesis by (auto simp add: HMC_def)
qed

lemma HMC_liveness_step_minute:
  assumes "m < 59"
  shows "\<turnstile> HMC \<longrightarrow> (timeIs (h,m) \<leadsto> timeIs (h, Suc m))"
  using HMC_liveness_step [of m h] assms by auto

lemma HMC_liveness_step_hour:
  shows "\<turnstile> HMC \<longrightarrow> (timeIs (h,59) \<leadsto> timeIs (next_hour h, 0))"
  using HMC_liveness_step [of 59 h] unfolding next_hour_def by auto

lemma HMC_liveness_progress_forwards_minute:
  assumes m12: "m1 \<le> m2" and m2: "m2 \<le> 59"
  shows "\<turnstile> HMC \<longrightarrow> (timeIs (h,m1) \<leadsto> timeIs (h,m2))"
  using assms
proof (induct m2)
  case 0 thus ?case apply auto using LatticeReflexivity by blast
next
  case (Suc m)
  hence m59: "m \<le> 59" by simp

  from Suc have "m1 \<le> m \<or> m1 = Suc m" by auto
  thus ?case
  proof (elim disjE)
    assume "m1 = Suc m" thus ?thesis apply auto using LatticeReflexivity by blast
  next
    assume "m1 \<le> m"
    with Suc.hyps m59
    have "\<turnstile> HMC \<longrightarrow> (timeIs (h,m1) \<leadsto> timeIs (h,m))" by metis

    also from Suc have "\<turnstile> HMC \<longrightarrow> (timeIs (h,m) \<leadsto> timeIs (h, Suc m))"
      by (intro HMC_liveness_step_minute, auto)

    finally show ?thesis .
  qed
qed

lemma HMC_liveness_progress_forwards_hour:
  assumes h1: "h1 \<in> {1..12}"
  assumes h2: "h2 \<in> {1..12}"
  assumes h1h2: "h1 \<le> h2" 
  shows "\<turnstile> HMC \<longrightarrow> (timeIs (h1,59) \<leadsto> timeIs (h2,59))"
  using h2 h1h2
proof (induct h2 rule: next_hour_induct)
  case base with h1 show ?case apply auto using LatticeReflexivity by blast
next
  case (step h)
  hence "h1 \<le> h \<or> h1 = next_hour h" unfolding next_hour_def by auto
  thus ?case
  proof (elim disjE)
    assume "h1 = next_hour h" thus ?thesis apply auto using LatticeReflexivity by blast
  next
    assume "h1 \<le> h"
    with step have "\<turnstile> HMC \<longrightarrow> (timeIs (h1, 59) \<leadsto> timeIs (h, 59))" by metis

    also have "\<turnstile> HMC \<longrightarrow> (timeIs (h, 59) \<leadsto> timeIs (next_hour h, 0))" by (intro HMC_liveness_step_hour)

    also have "\<turnstile> HMC \<longrightarrow> (timeIs (next_hour h, 0) \<leadsto> timeIs (next_hour h, 59))"
      by (intro HMC_liveness_progress_forwards_minute, simp_all)

    finally show ?thesis.
  qed
qed

lemma HMC_liveness_progress:
  assumes h1: "h1 \<in> {1..12}"
  assumes h2: "h2 \<in> {1..12}"
  assumes m1: "m1 \<le> 59"
  assumes m2: "m2 \<le> 59"
  shows "\<turnstile> HMC \<longrightarrow> (timeIs (h1,m1) \<leadsto> timeIs (h2,m2))"
proof -
  from m1 have "\<turnstile> HMC \<longrightarrow> (timeIs (h1,m1) \<leadsto> timeIs (h1,59))"
    by (intro HMC_liveness_progress_forwards_minute, simp_all)

  also from h1 have "\<turnstile> HMC \<longrightarrow> (timeIs (h1,59) \<leadsto> timeIs (12,59))"
    by (intro HMC_liveness_progress_forwards_hour, simp_all)

  also from HMC_liveness_step_hour [of 12]
  have "\<turnstile> HMC \<longrightarrow> (timeIs (12,59) \<leadsto> timeIs (1,0))"
    by (simp add: next_hour_def)

  also have "\<turnstile> HMC \<longrightarrow> (timeIs (1,0) \<leadsto> timeIs (h2,0))"
  proof (cases "h2 = 1")
    case True thus ?thesis apply auto using LatticeReflexivity by blast
  next
    case False
    have "\<turnstile> HMC \<longrightarrow> (timeIs (1, 0) \<leadsto> timeIs (1, 59))"
      by (intro HMC_liveness_progress_forwards_minute, simp_all)

    also from False h2
    have "\<turnstile> HMC \<longrightarrow> (timeIs (1, 59) \<leadsto> timeIs (h2 - 1, 59))"
      by (intro HMC_liveness_progress_forwards_hour, auto)

    also from False h2 have "next_hour (h2 - 1) = h2"
      by (auto simp add: next_hour_def)

    with HMC_liveness_step_hour [of "h2 - 1"]
    have "\<turnstile> HMC \<longrightarrow> (timeIs (h2 - 1, 59) \<leadsto> timeIs (h2, 0))" by auto
    
    finally show ?thesis .
  qed

  also from m2 have "\<turnstile> HMC \<longrightarrow> (timeIs (h2, 0) \<leadsto> timeIs (h2, m2))"
    by (intro HMC_liveness_progress_forwards_minute, simp_all)

  finally show ?thesis .
qed

lemma HMC_liveness: 
  assumes h: "h \<in> {1..12}"
  assumes m: "m \<le> 59"
  shows "\<turnstile> HMC \<longrightarrow> \<box>\<diamond> timeIs (h,m)"
proof -
  from HMC_safety
  have "\<turnstile> HMC \<longrightarrow> ((#True :: stpred) \<leadsto> (hr \<in> #{1..12} \<and> mn \<in> #{0..59}))"
    by (intro imp_leadsto_invariant, simp)

  also have "\<turnstile> HMC \<longrightarrow> ((hr \<in> #{1..12} \<and> mn \<in> #{0..59}) \<leadsto> (\<exists>t. #(fst t \<in> {1..12} \<and> snd t \<le> 59) \<and> timeIs t))"
    by (intro imp_imp_leadsto, auto)

  also have "\<turnstile> HMC \<longrightarrow> ((\<exists>t. #(fst t \<in> {1..12} \<and> snd t \<le> 59) \<and> timeIs t) \<leadsto> timeIs (h,m))"
    unfolding inteq_reflection [OF leadsto_exists]
  proof (intro imp_forall_leadsto)
    fix t :: "nat \<times> nat"
    obtain h' m' where t: "t = (h', m')" by fastforce
    show "fst t \<in> {1..12} \<and> snd t \<le> 59 \<Longrightarrow> \<turnstile> HMC \<longrightarrow> (timeIs t \<leadsto> timeIs (h, m))"
      unfolding t using h m
      by (intro HMC_liveness_progress, auto)
  qed
   
  finally show ?thesis
    by (auto simp add: leadsto_def)
qed

lemma HMC_refines_HC: "\<turnstile> HMC \<longrightarrow> HC"
  unfolding HC_def
proof (intro temp_imp_conjI)
  show "\<turnstile> HMC \<longrightarrow> Init HCini" by (auto simp add: HMC_def HMCini_def Init_def)

  have "\<turnstile> HMC \<longrightarrow> \<box>[HMCnxt]_(hr, mn)" by auto (simp add: HMC_def)
  moreover have "\<turnstile> [HMCnxt]_(hr, mn) \<longrightarrow> [HCnxt]_hr"
  proof (intro intI temp_impI, clarify)
    fix before after
    assume "(before, after) \<Turnstile> [HMCnxt]_(hr, mn)"
    thus "(before, after) \<Turnstile> [HCnxt]_hr"
      by (cases "mn before = 59", auto simp add: square_def HMCnxt_eq HCnxt_def next_hour_def)
  qed
  ultimately show "\<turnstile> HMC \<longrightarrow> \<box>[HCnxt]_hr" by (metis STL4 temp_imp_trans)

  define P :: stpred   where "P \<equiv> timeIs (1,59)"
  define B :: action   where "B \<equiv> ACT $P"
  define F :: temporal where "F \<equiv> TEMP \<diamond>P"
  define N :: action   where "N \<equiv> ACT [HMCnxt]_(hr,mn)"
  define A :: action   where "A \<equiv> HMCnxt"
    
  have "\<turnstile> <$P \<and> HMCnxt>_(hr, mn) = ($P \<and> HMCnxt)" by (auto simp add: angle_def HMCnxt_eq)
  note eqs = inteq_reflection [OF this]

  have "\<turnstile> HMC \<longrightarrow> \<box>N \<and> WF(A)_(hr,mn) \<and> \<box>F"
  proof (intro temp_imp_conjI)
    show "\<turnstile> HMC \<longrightarrow> \<box>N" by (auto simp add: N_def HMC_def)
    from HMC_liveness show "\<turnstile> HMC \<longrightarrow> \<box>F" unfolding F_def P_def by auto

    show "\<turnstile> HMC \<longrightarrow> WF(A)_(hr, mn)"
      unfolding HMC_def WF_def eqs A_def by auto
  qed

  also have "\<turnstile> \<box>N \<and> WF(A)_(hr,mn) \<and> \<box>F \<longrightarrow> WF(HCnxt)_hr"
  proof (intro WF2 stable_dmd_stuck)

    show "\<turnstile> N \<and> <B>_(hr, mn) \<longrightarrow> <HCnxt>_hr"
      by (auto simp add: N_def square_def angle_def P_def B_def HMCnxt_eq HCnxt_def next_hour_def)

    show "\<turnstile> $P \<and> P$ \<and> <N \<and> A>_(hr, mn) \<longrightarrow> B"
      by (auto simp add: angle_def P_def)

    show "\<turnstile> P \<and> Enabled (<HCnxt>_hr) \<longrightarrow> Enabled (<A>_(hr, mn))"
      unfolding eqs A_def by (auto simp add: P_def)

    let ?PREM = "TEMP \<box>(N \<and> [\<not> B]_(hr, mn)) \<and> WF(A)_(hr, mn) \<and> \<box>F \<and> \<diamond>\<box>Enabled (<HCnxt>_hr)"

    show "\<turnstile> ?PREM \<longrightarrow> stable P"
      apply (intro tempI temp_impI Stable [where A = "ACT N \<and> [\<not> $P]_(hr, mn)"])
      by (auto simp add: square_def P_def N_def B_def)

    have "\<turnstile> ?PREM \<longrightarrow> \<box>\<diamond>P" unfolding F_def by auto
    also have "\<turnstile> \<box>\<diamond>P \<longrightarrow> \<diamond>P" by (intro STL2)
    finally show "\<turnstile> ?PREM \<longrightarrow> \<diamond> P" .
  qed

  finally show "\<turnstile> HMC \<longrightarrow> WF(HCnxt)_hr" .

qed

end

end
