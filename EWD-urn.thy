theory "EWD-urn"
  imports "./TLA-Utils"
begin

locale Urn =
  fixes initialBlackBallCount initialWhiteBallCount :: nat
  assumes nonempty: "0 < initialBlackBallCount + initialWhiteBallCount"
  fixes blackBallCount whiteBallCount :: "nat stfun"
  assumes bv: "basevars (blackBallCount, whiteBallCount)"
  fixes Initial :: stpred
  defines "Initial \<equiv> PRED blackBallCount = #initialBlackBallCount \<and> whiteBallCount = #initialWhiteBallCount"
  fixes DrawTwoBlack :: action
  defines "DrawTwoBlack \<equiv> ACT #2 \<le> $blackBallCount \<and> blackBallCount$ = $blackBallCount - #1 \<and> unchanged whiteBallCount"
  fixes DrawTwoWhite :: action
  defines "DrawTwoWhite \<equiv> ACT #2 \<le> $whiteBallCount \<and> whiteBallCount$ = $whiteBallCount - #2 \<and> blackBallCount$ = $blackBallCount + #1"
  fixes DrawOneOfEach :: action
  defines "DrawOneOfEach \<equiv> ACT #1 \<le> $whiteBallCount \<and> #1 \<le> $blackBallCount \<and> blackBallCount$ = $blackBallCount - #1 \<and> unchanged whiteBallCount"
  fixes Next :: action
  defines "Next \<equiv> ACT (DrawTwoBlack \<or> DrawTwoWhite \<or> DrawOneOfEach)"
  fixes Fair :: temporal
  defines "Fair \<equiv> TEMP WF(Next)_(blackBallCount, whiteBallCount)"
  fixes Spec :: temporal
  defines "Spec \<equiv> TEMP (Init Initial \<and> \<box>[Next]_(blackBallCount, whiteBallCount) \<and> Fair)"
  fixes Invariant :: stpred
  defines "Invariant \<equiv> PRED (even<whiteBallCount> = #(even initialWhiteBallCount) \<and> #1 \<le> whiteBallCount + blackBallCount)"

context Urn
begin

lemma invariant: "\<turnstile> Spec \<longrightarrow> \<box>Invariant"
proof invariant
  fix sigma
  assume "sigma \<Turnstile> Spec"
  hence initial: "sigma \<Turnstile> Init Initial" and step: "sigma \<Turnstile> \<box>[Next]_(blackBallCount, whiteBallCount)"
    unfolding Spec_def by auto

  from initial nonempty show "sigma \<Turnstile> Init Invariant"
    by (auto simp add: Init_def Initial_def Invariant_def)

  from step
  show "sigma \<Turnstile> stable Invariant"
    by (intro Stable, auto simp add: Invariant_def square_def Next_def DrawTwoBlack_def DrawTwoWhite_def DrawOneOfEach_def)
qed

lemma terminates: "\<turnstile> Spec \<longrightarrow> \<diamond>\<box>(blackBallCount + whiteBallCount = #1)"
proof (intro stable_dmd_stuck)

  have "\<turnstile> Spec \<longrightarrow> \<box>[Next]_(blackBallCount, whiteBallCount)"
    by (auto simp add: Spec_def)
  also have "\<turnstile> \<box>[Next]_(blackBallCount, whiteBallCount) \<longrightarrow> stable (blackBallCount + whiteBallCount = #1)"
    by (intro StableT, auto simp add: Next_def square_def DrawTwoBlack_def DrawTwoWhite_def DrawOneOfEach_def)
  finally show "\<turnstile> Spec \<longrightarrow> stable (blackBallCount + whiteBallCount = #1)".

  from nonempty
  have "\<turnstile> Spec \<longrightarrow> \<diamond>(\<exists> n. blackBallCount + whiteBallCount = #n \<and> #1 \<le> #n)"
    by (intro imp_eventually_init, auto simp add: Spec_def Init_def Initial_def)

  also have "\<turnstile> Spec \<longrightarrow> ((\<exists> n. blackBallCount + whiteBallCount = #n \<and> #1 \<le> #n) \<leadsto> blackBallCount + whiteBallCount = #1)"
  proof (intro wf_imp_ex_leadsto [OF wf_less])
    fix n
    show "\<turnstile> Spec \<longrightarrow> (blackBallCount + whiteBallCount = #n \<and> #1 \<le> #n
                    \<leadsto> blackBallCount + whiteBallCount = #1
                        \<or> (\<exists>n'. #((n', n) \<in> {(n', n). n' < n}) \<and> blackBallCount + whiteBallCount = #n' \<and> #1 \<le> #n'))"
    proof (cases "n \<le> 1")
      case True
      thus ?thesis by (intro imp_imp_leadsto, auto)
    next
      case False
      then obtain n' where n_Suc: "n = Suc n'" "1 \<le> n'" by (cases n, auto)

      have next_angle_eq[simp]: "(ACT <Next>_(blackBallCount, whiteBallCount)) = (ACT Next)"
        by (intro ext, auto simp add: angle_def Next_def DrawTwoBlack_def DrawTwoWhite_def DrawOneOfEach_def)

      from basevars [OF bv]
      have enabled_simp[simp]: "(PRED (Enabled Next)) = (PRED (#2 \<le> blackBallCount + whiteBallCount))"
        apply (intro ext, auto simp add: enabled_def angle_def Next_def DrawTwoBlack_def DrawTwoWhite_def DrawOneOfEach_def)
        by (metis add.left_neutral add.right_neutral diff_is_0_eq le_add_diff_inverse not_less_eq_eq zero_le)

      have "\<turnstile> Spec \<longrightarrow> \<box>[Next]_(blackBallCount, whiteBallCount) \<and> WF(Next)_(blackBallCount, whiteBallCount)"
        by (auto simp add: Spec_def Fair_def)
      also from n_Suc
      have "\<turnstile> \<box>[Next]_(blackBallCount, whiteBallCount) \<and> WF(Next)_(blackBallCount, whiteBallCount)
                  \<longrightarrow> (blackBallCount + whiteBallCount = #(Suc n') \<and> #1 \<le> #n \<leadsto> blackBallCount + whiteBallCount = #n')"
        by (intro WF1, auto, auto simp add: Next_def square_def DrawTwoBlack_def DrawTwoWhite_def DrawOneOfEach_def angle_def)
      finally have "\<turnstile> Spec \<longrightarrow> (blackBallCount + whiteBallCount = #n \<and> #1 \<le> #n \<leadsto> blackBallCount + whiteBallCount = #n')"
        by (simp add: n_Suc)
      also from n_Suc
      have "\<turnstile> Spec \<longrightarrow> (blackBallCount + whiteBallCount = #n'
        \<leadsto> blackBallCount + whiteBallCount = #1 \<or> (\<exists>n'. #((n', n) \<in> {(n', n). n' < n}) \<and> blackBallCount + whiteBallCount = #n' \<and> #1 \<le> #n'))"
        by (intro imp_imp_leadsto, auto)
      finally show "\<turnstile> Spec \<longrightarrow> (blackBallCount + whiteBallCount = #n \<and>
              #1 \<le> #n \<leadsto> blackBallCount + whiteBallCount = #1 \<or> (\<exists>n'. #((n', n) \<in> {(n', n). n' < n}) \<and> blackBallCount + whiteBallCount = #n' \<and> #1 \<le> #n'))" .
    qed
  qed

  finally show "\<turnstile> Spec \<longrightarrow> \<diamond>(blackBallCount + whiteBallCount = #1)".
qed

lemma
  shows "\<turnstile> Spec \<longrightarrow> \<diamond>\<box>((blackBallCount, whiteBallCount) = #(if even initialWhiteBallCount then (1,0) else (0,1)))"
proof (intro stable_dmd_stuck)
  have "\<turnstile> Spec \<longrightarrow> \<box>[Next]_(blackBallCount, whiteBallCount)"
    by (auto simp add: Spec_def)
  also have "\<turnstile> \<box>[Next]_(blackBallCount, whiteBallCount) \<longrightarrow> stable ((blackBallCount, whiteBallCount) = #(if even initialWhiteBallCount then (1,0) else (0,1)))"
    by (intro StableT, auto simp add: Next_def square_def DrawTwoBlack_def DrawTwoWhite_def DrawOneOfEach_def)
  finally show "\<turnstile> Spec \<longrightarrow> stable ((blackBallCount, whiteBallCount) = #(if even initialWhiteBallCount then (1,0) else (0,1)))".

  have "\<turnstile> Spec \<longrightarrow> \<diamond>(even<whiteBallCount> = #(even initialWhiteBallCount) \<and> blackBallCount + whiteBallCount = #1)"
  proof (intro imp_dmd_conj_invariant terminates imp_eventually_forever_implies_infinitely_often imp_infinitely_often_implies_eventually)
    from invariant
    show "\<turnstile> Spec \<longrightarrow> \<box>(even<whiteBallCount> = #(even initialWhiteBallCount))" by (auto simp add: Invariant_def)
  qed
  also have "\<turnstile> \<diamond>(even<whiteBallCount> = #(even initialWhiteBallCount) \<and> blackBallCount + whiteBallCount = #1)
            \<longrightarrow> \<diamond>((blackBallCount, whiteBallCount) = #(if even initialWhiteBallCount then (1,0) else (0,1)))"
    by (intro DmdImpl, auto, presburger+)
  finally show "\<turnstile> Spec \<longrightarrow> \<diamond>(blackBallCount, whiteBallCount) = #(if even initialWhiteBallCount then (1, 0) else (0, 1))".
qed

end

end

