theory HochsteinLamport
  imports "./TLA-Utils"
begin

(* see https://lorinhochstein.wordpress.com/2018/12/27/inductive-invariants/ *)

datatype Pc = Start | SetX | Finish

locale Algorithm =
  fixes N :: nat
  assumes Npos: "0 < N"
  fixes pc :: "(nat \<Rightarrow> Pc) stfun"
  fixes x :: "(nat \<Rightarrow> nat) stfun"
  fixes y :: "(nat \<Rightarrow> nat) stfun"
  assumes bvs: "basevars (pc,x,y)"
  fixes Initial :: stpred
  defines "Initial \<equiv> PRED (\<forall>n. id<pc,#n> = #Start)"
  fixes Step1 :: "nat \<Rightarrow> action"
  defines "Step1 n \<equiv> ACT (#n < #N
    \<and> id<$pc,#n> = #Start \<and> id<pc$,#n> = #SetX
    \<and> id<x$,#n> = #1
    \<and> (\<forall>n'. #n' \<noteq> #n \<longrightarrow> id<pc$,#n'> = id<$pc,#n'>)
    \<and> (\<forall>n'. #n' \<noteq> #n \<longrightarrow> id< x$,#n'> = id<$x ,#n'>)
    \<and> unchanged y)"
  fixes Step2 :: "nat \<Rightarrow> nat \<Rightarrow> action"
  defines "Step2 n j \<equiv> ACT (#n < #N \<and> #j < #N
    \<and> id<$pc,#n> = #SetX \<and> id<pc$,#n> = #Finish
    \<and> id<y$,#n> = id<$x,#j>
    \<and> (\<forall>n'. #n' \<noteq> #n \<longrightarrow> id<pc$,#n'> = id<$pc,#n'>)
    \<and> unchanged x
    \<and> (\<forall>n'. #n' \<noteq> #n \<longrightarrow> id<y$,#n'> = id<$y,#n'>))"
  fixes Step :: action
  defines "Step \<equiv> ACT (\<exists> n. Step1 n \<or> (\<exists> j. Step2 n j))"
  fixes Spec :: temporal
  defines "Spec \<equiv> TEMP (Init Initial \<and> \<box>[Step]_(pc,x,y) \<and> WF(Step)_(pc,x,y))"

context Algorithm
begin

definition xSet :: "nat set stfun" where "xSet s \<equiv> { n. pc s n \<noteq> Start }"
definition ySet :: "nat set stfun" where "ySet s \<equiv> { n. pc s n = Finish }"

lemma Step_cases[consumes 1, case_names unchanged Step1 Step2]:
  assumes sq_Step: "(s,t) \<Turnstile> [Step]_(pc,x,y)"
  assumes unchanged: "\<lbrakk> x t = x s; y t = y s; pc t = pc s; xSet t = xSet s; ySet t = ySet s \<rbrakk> \<Longrightarrow> P"
  assumes Step1: "\<And>n.   \<lbrakk> n < N;        pc s n = Start; pc t n = SetX;   x t n = 1;     \<forall> n'. n' \<noteq> n \<longrightarrow> pc t n' = pc s n'; \<forall> n'. n' \<noteq> n \<longrightarrow> x t n' = x s n'; y t = y s; xSet t = insert n (xSet s); ySet t = ySet s \<rbrakk> \<Longrightarrow> P"
  assumes Step2: "\<And>n j. \<lbrakk> n < N; j < N; pc s n = SetX;  pc t n = Finish; y t n = x s j; \<forall> n'. n' \<noteq> n \<longrightarrow> pc t n' = pc s n'; \<forall> n'. n' \<noteq> n \<longrightarrow> y t n' = y s n'; x t = x s; ySet t = insert n (ySet s); xSet t = xSet s \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from sq_Step consider
    (unchanged_case) "(s,t) \<Turnstile> unchanged (pc,x,y)"
    | (Step1_case) "\<exists>n.   (s,t) \<Turnstile> Step1 n"
    | (Step2_case) "\<exists>n j. (s,t) \<Turnstile> Step2 n j"
    unfolding square_def Step_def by auto
  thus P
  proof cases
    case unchanged_case with unchanged show P unfolding xSet_def ySet_def by simp
  next
    case Step1_case
    then obtain n where st: "(s,t) \<Turnstile> Step1 n" ..
    thus P
      apply (intro Step1 [of n], auto simp add: Step1_def xSet_def ySet_def)
      using Pc.distinct by metis+
  next
    case Step2_case
    then obtain n j where st: "(s,t) \<Turnstile> Step2 n j" by blast
    thus P apply (intro Step2 [of n j], auto simp add: Step2_def xSet_def ySet_def)
      using Pc.distinct by metis+
  qed
qed

definition Safety :: stpred
  where "Safety s \<equiv> xSet s \<subseteq> {n. n < N}
                  \<and> ySet s \<subseteq> xSet s
                  \<and> (\<forall> n \<in> xSet s. x s n = 1)
                  \<and> (ySet s = {n. n < N} \<longrightarrow> (\<exists> n < N. y s n = 1))"

lemma Safety: "\<turnstile> Spec \<longrightarrow> \<box>Safety"
proof (intro invariantI)
  show "\<turnstile> Spec \<longrightarrow> Init Safety" using Npos by (auto simp add: Spec_def Safety_def Init_def Initial_def xSet_def ySet_def)
  show "\<turnstile> Spec \<longrightarrow> \<box>[Step]_(pc,x,y)" by (auto simp add: Spec_def)

  fix s t
  assume s_Safety: "s \<Turnstile> Safety"
  assume "(s,t) \<Turnstile> [Step]_(pc,x,y)"
  thus "t \<Turnstile> Safety"
  proof (cases rule: Step_cases)
    case unchanged with s_Safety show ?thesis unfolding Safety_def by simp
  next
    case (Step1 n)
    show ?thesis
      unfolding Safety_def
    proof (intro conjI impI exI)
      show "\<forall>n\<in>xSet t. x t n = 1" "xSet t \<subseteq> {n. n < N}" "ySet t \<subseteq> xSet t" "n < N"
        using s_Safety Step1 unfolding Safety_def by fastforce+

      from Step1 have "ySet s = ySet t" by simp
      also assume "ySet t = {n. n < N}"
      moreover from s_Safety have "ySet s \<subseteq> xSet s" unfolding Safety_def by simp
      moreover from s_Safety have "xSet s \<subseteq> {n. n < N}" unfolding Safety_def by simp
      ultimately have "xSet s = {n. n < N}" by auto
      with Step1 have "n \<in> xSet s" by (auto simp add: xSet_def)
      with Step1 have False by (simp add: xSet_def)
      thus "y t n = 1" by simp_all
    qed
  next
    case (Step2 n j)
    show ?thesis
      unfolding Safety_def
    proof (intro conjI impI exI)
      show "\<forall>n\<in>xSet t. x t n = 1" "xSet t \<subseteq> {n. n < N}" "ySet t \<subseteq> xSet t" "n < N"
        using s_Safety Step2 unfolding Safety_def xSet_def ySet_def by fastforce+

      assume "ySet t = {n. n < N}"
      with `ySet t \<subseteq> xSet t` `xSet t \<subseteq> {n. n < N}` have "xSet s = {n. n < N}" using Step2 by simp
      with Step2 s_Safety have "x s j = 1" unfolding Safety_def by auto
      with Step2 show "y t n = 1" by simp
    qed
  qed
qed

lemma angle_Step_eq: "(ACT <Step>_(pc, x, y)) = Step"
proof (intro ext iffI)
  fix st
  show "st \<Turnstile> <Step>_(pc,x,y) \<Longrightarrow> st \<Turnstile> Step" unfolding angle_def by auto

  assume Step: "st \<Turnstile> Step"
  obtain s t where st: "st = (s,t)" by fastforce

  have "(s,t) \<Turnstile> <Step>_(pc,x,y)"
    unfolding angle_def
  proof (intro temp_conjI)
    from Step st show "(s,t) \<Turnstile> Step" by simp
    thus "(s,t) \<Turnstile> \<not> unchanged (pc, x, y)"
      by (auto simp add: Step_def Step1_def Step2_def)
  qed
  thus "st \<Turnstile> <Step>_(pc,x,y)" by (simp add: st)
qed

lemma enabled_StepI:
  assumes "s \<Turnstile> Safety"
  assumes "ySet s \<noteq> {n. n < N}"
  shows "s \<Turnstile> Enabled Step"
proof -
  from assms obtain n where n: "n < N" "pc s n \<noteq> Finish" unfolding ySet_def Safety_def by auto
  thus ?thesis
  proof (cases "pc s n")
    case Start
    show ?thesis unfolding Step_def enabled_ex [temp_use] enabled_disj [temp_use]
    proof (intro exI [where x = n] disjI1, enabled bvs, intro exI allI impI, elim conjE)
      fix u
      assume
        "pc u = (\<lambda>m. if m = n then SetX else pc s m)"
        "x  u = (\<lambda>m. if m = n then 1    else x s m)"
        "y  u = y s"
      with n Start show "(s,u) \<Turnstile> Step1 n" by (auto simp add: Step1_def)
    qed
  next
    case SetX
    show ?thesis unfolding Step_def enabled_ex [temp_use] enabled_disj [temp_use]
    proof (intro exI [where x = n] disjI2, enabled bvs, intro exI allI impI, elim conjE)
      fix u
      assume
        "pc u = (\<lambda>m. if m = n then Finish else pc s m)"
        "y  u = (\<lambda>m. if m = n then x s n else y s m)"
        "x  u = x s"
      with n SetX show "(s,u) \<Turnstile> Step2 n n" by (auto simp add: Step2_def)
    qed
  qed simp
qed

lemma StepFair:
  assumes "\<turnstile> $P \<and> $Safety \<and> [Step]_(pc,x,y) \<longrightarrow> P$ \<or> Q$"
  assumes "\<turnstile> $P \<and> $Safety \<and>  Step        \<longrightarrow>      Q$"
  assumes "\<turnstile> $P \<and> $Safety \<and> [Step]_(pc,x,y) \<longrightarrow> $Enabled Step"
  shows "\<turnstile> Spec \<longrightarrow> (P \<leadsto> Q)"
proof -
  from Safety have "\<turnstile> Spec \<longrightarrow> \<box>([Step]_(pc,x,y) \<and> $Safety) \<and> WF(Step)_(pc,x,y)" by (auto simp add: Spec_def more_temp_simps)
  also have "\<turnstile> \<box>([Step]_(pc,x,y) \<and> $Safety) \<and> WF(Step)_(pc,x,y) \<longrightarrow> (P \<leadsto> Q)"
    using assms angle_Step_eq by (intro WF1, auto)
  finally show ?thesis .
qed

lemma StepFair_action:
  assumes "\<And>s t. \<lbrakk> s \<Turnstile> P; s \<Turnstile> Safety; (s,t) \<Turnstile> [Step]_(pc,x,y) \<rbrakk> \<Longrightarrow> t \<Turnstile> P \<or> Q"
  assumes "\<And>s t. \<lbrakk> s \<Turnstile> P; s \<Turnstile> Safety; (s,t) \<Turnstile>  Step           \<rbrakk> \<Longrightarrow> t \<Turnstile>     Q"
  assumes "\<And>s t. \<lbrakk> s \<Turnstile> P; s \<Turnstile> Safety; (s,t) \<Turnstile> [Step]_(pc,x,y) \<rbrakk> \<Longrightarrow> s \<Turnstile> Enabled Step"
  shows "\<turnstile> Spec \<longrightarrow> (P \<leadsto> Q)"
  using assms by (intro StepFair actionI, auto)

lemma Termination: "\<turnstile> Spec \<longrightarrow> \<diamond>(ySet = #{n. n < N})"
proof -
  define F :: "(nat set \<times> nat set) \<Rightarrow> stpred" where "F \<equiv> \<lambda>(xs, ys). \<lambda>s. {n. n < N} - xSet s = xs \<and> {n. n < N} - ySet s = ys"
  define r :: "((nat set \<times> nat set) \<times> (nat set \<times> nat set)) set" where "r \<equiv> {(X, Y). X \<subset> Y \<and> Y \<subseteq> {n. n < N}} <*lex*> {(X, Y). X \<subset> Y \<and> Y \<subseteq> {n. n < N}}"

  have "\<turnstile> Spec \<longrightarrow> \<diamond>(\<exists> xsys. F xsys)"
    by (intro imp_eventually_tautology, auto simp add: F_def)
  also have "\<turnstile> Spec \<longrightarrow> ((\<exists> xsys. F xsys) \<leadsto> ySet = #{n. n < N})"
  proof (rule imp_leadsto_triangle_excl)
    show "\<turnstile> Spec \<longrightarrow> ((\<exists>xsys. F xsys) \<leadsto> (\<exists>xsys. F xsys))" by (intro imp_imp_leadsto, simp)

    have "\<turnstile> Spec \<longrightarrow> ((\<exists>xsys. F xsys) \<and> ySet \<noteq> #{n. n < N} \<leadsto> (\<exists>xsys. F xsys \<and> ySet \<noteq> #{n. n < N}))" by (intro imp_imp_leadsto, auto)
    also have "\<turnstile> Spec \<longrightarrow> ((\<exists>xsys. F xsys \<and> ySet \<noteq> #{n. n < N}) \<leadsto> ySet = #{n. n < N})"
    proof (intro wf_imp_ex_leadsto)
      show "wf r" unfolding r_def by (intro wf_lex_prod finite_subset_wf, auto)

      fix xsys
      show "\<turnstile> Spec \<longrightarrow> (F xsys \<and> ySet \<noteq> #{n. n < N} \<leadsto> ySet = #{n. n < N} \<or> (\<exists>y. #((y, xsys) \<in> r) \<and> F y \<and> ySet \<noteq> #{n. n < N}))"
      proof (intro StepFair_action)
        fix s t
        assume "s \<Turnstile> F xsys \<and> ySet \<noteq> #{n. n < N}"
        then obtain xs ys where xsys: "xsys = (xs, ys)" and running: "ySet s \<noteq> {n. n < N}"
          and xs: "xs = {n. n < N} - xSet s" and ys: "ys = {n. n < N} - ySet s"
          and s_F: "s \<Turnstile> F xsys" unfolding F_def by auto

        assume Safety: "s \<Turnstile> Safety"
        hence xSet_range: "xSet s \<subseteq> {n. n < N}" and ySet_range: "ySet s \<subseteq> {n. n < N}"
          and ySet_xSet: "ySet s \<subseteq> xSet s" and xSet_set: "\<And>n. n \<in> xSet s \<Longrightarrow> x s n = 1"
          unfolding Safety_def by auto

        show "s \<Turnstile> Enabled Step" by (intro enabled_StepI Safety running)

        show progress: "t \<Turnstile> ySet = #{n. n < N} \<or> (\<exists>y. #((y, xsys) \<in> r) \<and> F y \<and> ySet \<noteq> #{n. n < N})" if Step: "(s,t) \<Turnstile> Step"
        proof -
          from Step have "(s,t) \<Turnstile> [Step]_(pc,x,y)" unfolding square_def by simp
          thus ?thesis
          proof (cases rule: Step_cases)
            case (Step1 n)
            hence "t \<Turnstile> #(((xs - {n}, ys), xsys) \<in> r) \<and> F (xs - {n}, ys) \<and> ySet \<noteq> #{n. n < N}"
              apply (auto simp add: xsys F_def xs ys running, unfold r_def, simp)
              using Algorithm.xSet_def Algorithm_axioms by auto
            then show ?thesis by auto
          next
            case (Step2 n j)
            show ?thesis
            proof (cases "ySet t = {n. n < N}")
              case True thus ?thesis by simp
            next
              case False
              have "t \<Turnstile> #(((xs, ys - {n}), xsys) \<in> r) \<and> F (xs, ys - {n}) \<and> ySet \<noteq> #{n. n < N}"
              proof (intro temp_conjI)
                from False show "t \<Turnstile> ySet \<noteq> #{n. n < N}" by simp
                from Step2 xs ys show "t \<Turnstile> F (xs, ys - {n})" unfolding F_def by auto
                from Step2 xs ys show "t \<Turnstile> (#(((xs, ys - {n}), xsys) \<in> r))"
                  unfolding r_def xsys
                proof simp
                  assume a1: "pc s n = SetX"
                  assume "n < N"
                  then have "n \<in> {n. n < N} - ySet s"
                    using a1 by (simp add: ySet_def)
                  then show "{n. n < N} - ySet s - {n} \<subset> {n. n < N} - ySet s"
                    by blast
                qed

              qed
              then show ?thesis by auto
            qed
          next
            case unchanged
            from Step have "(s,t) \<Turnstile> <Step>_(pc,x,y)" unfolding angle_Step_eq.
            with unchanged show ?thesis by (simp add: angle_def)
          qed
        qed

        assume "(s,t) \<Turnstile> [Step]_(pc,x,y)"
        then consider (Step) "(s,t) \<Turnstile> Step" | (unchanged) "x t = x s" "y t = y s" "xSet t = xSet s" "ySet t = ySet s" unfolding square_def xSet_def ySet_def by auto
        thus "t \<Turnstile> F xsys \<and> ySet \<noteq> #{n. n < N} \<or> ySet = #{n. n < N} \<or> (\<exists>y. #((y, xsys) \<in> r) \<and> F y \<and> ySet \<noteq> #{n. n < N})"
        proof cases
          case Step with progress show ?thesis by simp
        next
          case unchanged with s_F have "t \<Turnstile> F xsys" by (auto simp add: F_def)
          thus ?thesis by simp
        qed
      qed
    qed
    finally show "\<turnstile> Spec \<longrightarrow> ((\<exists>xsys. F xsys) \<and> ySet \<noteq> #{n. n < N} \<leadsto> ySet = #{n. n < N})".
  qed
  finally show "\<turnstile> Spec \<longrightarrow> \<diamond>ySet = #{n. n < N}".
qed

lemma Termination_stops: "\<turnstile> Spec \<longrightarrow> \<diamond>\<box>(ySet = #{n. n < N})"
proof (intro stable_dmd_stuck Termination)
  from Safety have "\<turnstile> Spec \<longrightarrow> \<box>([Step]_(pc,x,y) \<and> $Safety)" unfolding Spec_def
    apply auto using Init_stp_act_rev boxInit_act boxInit_stp by auto
  also have "\<turnstile> \<box>([Step]_(pc,x,y) \<and> $Safety) \<longrightarrow> stable (ySet = #{n. n < N})"
  proof (intro StableT actionI temp_impI, elim temp_conjE, simp_all)
    fix s t
    assume "(s,t) \<Turnstile> [Step]_(pc,x,y)" "ySet s = {n. n < N}" "Safety s"
    thus "ySet t = {n. n < N}" by (cases rule: Step_cases, auto)
  qed
  finally show "\<turnstile> Spec \<longrightarrow> stable (ySet = #{n. n < N})".
qed

lemma eventually_1: "\<turnstile> Spec \<longrightarrow> \<diamond>(\<exists>n. id<y,#n> = #1)"
proof -
  note Termination
  also have "\<turnstile> Spec \<longrightarrow> ((ySet = #{n. n < N}) \<leadsto> (\<exists>n. id<y,#n> = #1))"
    by (intro imp_INV_leadsto [OF Safety imp_imp_leadsto] intI temp_impI, elim temp_conjE, auto simp add: Safety_def)
  finally show ?thesis .
qed

end
