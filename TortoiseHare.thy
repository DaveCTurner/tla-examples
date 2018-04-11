theory TortoiseHare
  imports "./TLA-Utils"
begin

locale LinkedList =
  fixes headCell :: 'Cell
  fixes nextCell :: "'Cell \<Rightarrow> 'Cell option"
  assumes finiteNext: "finite { c. nextCell c \<noteq> None }"

context LinkedList begin

definition nextNextCell :: "'Cell \<Rightarrow> 'Cell option"
  where "nextNextCell c \<equiv> case nextCell c of None \<Rightarrow> None | Some c' \<Rightarrow> nextCell c'"

end

locale TortoiseHare = LinkedList
  where headCell = headCell
  for headCell :: 'Cell
    +
  fixes tortoise :: "'Cell stfun"
  fixes hare     :: "'Cell stfun"
  fixes hasLoop  :: "bool option stfun"
  assumes bv: "basevars (tortoise, hare, hasLoop)"
  fixes Initial :: stpred
  defines "Initial \<equiv> PRED tortoise = #headCell \<and> hare = #headCell \<and> hasLoop = #None"
  fixes Step :: action
  defines "Step \<equiv> ACT $hasLoop = #None
                        \<and> Some<tortoise$> = nextCell<$tortoise>
                        \<and> Some<hare$>     = nextNextCell<$hare>
                        \<and> hasLoop$ = (if hare$ = tortoise$ then #(Some True) else #None)"
  fixes Finish :: action
  defines "Finish \<equiv> ACT $hasLoop = #None
                            \<and> nextNextCell<$hare> = #None
                            \<and> hasLoop$ = #(Some False)"
  fixes Next :: action
  defines "Next \<equiv> ACT (Step \<or> Finish)"
  fixes Spec :: temporal
  defines "Spec \<equiv> TEMP (Init Initial \<and> \<box>[Next]_(tortoise, hare, hasLoop)
      \<and> WF(Step)_(tortoise, hare, hasLoop)
      \<and> WF(Finish)_(tortoise, hare, hasLoop))"

context LinkedList begin

definition r :: "('Cell \<times> 'Cell) set"
  where "r \<equiv> {(c1, c2). nextCell c1 = Some c2}"

definition loopExists :: bool
  where "loopExists \<equiv> \<exists> c. (headCell, c) \<in> rtrancl r \<and> (c, c) \<in> trancl r"

lemma unique_successor: "(c, c1) \<in> r \<Longrightarrow> (c, c2) \<in> r \<Longrightarrow> c1 = c2" by (auto simp add: r_def)

lemma finiteList: "finite {c'. (c, c') \<in> rtrancl r}"
proof -
  define theNextCell :: "'Cell \<Rightarrow> 'Cell"
    where "\<And>c. theNextCell c \<equiv> THE c'. nextCell c = Some c'"

  have "{ c'. (c, c') \<in> rtrancl r } \<subseteq> insert c (theNextCell ` { c. nextCell c \<noteq> None })"
  proof (intro subsetI, elim CollectE)
    fix c'
    assume "(c, c') \<in> rtrancl r"
    thus "c' \<in> insert c (theNextCell ` { c. nextCell c \<noteq> None })"
    proof (induct rule: rtrancl_induct)
      case (step c c') hence cc': "(c, c') \<in> r" by simp
      show ?case
      proof (intro insertI2 image_eqI CollectI)
        from cc' show "nextCell c \<noteq> None" by (auto simp add: r_def)
        from cc' show "c' = theNextCell c"
          by (auto simp add: r_def theNextCell_def)
      qed
    qed simp
  qed
  from finite_subset [OF this] finiteNext show ?thesis by auto
qed

lemma next_step:
  assumes c12: "(c1, c2) \<in> r" and c13: "(c1, c3) \<in> trancl r"
  shows "(c2, c3) \<in> rtrancl r"
proof -
  from c13 obtain tmp where 1: "(c1, tmp) \<in> r" and 2: "(tmp, c3) \<in> rtrancl r" by (metis tranclD)
  from 1 c12 have "tmp = c2" by (intro unique_successor)
  with 2 show ?thesis by simp
qed

lemma tight_loop_eq:
  assumes cc': "(c, c') \<in> rtrancl r" and loop: "(c, c) \<in> r"
  shows "c' = c"
  using cc'
proof (induct rule: rtrancl_induct)
  case (step c' c'') hence "(c, c'') \<in> r" by simp
  with loop show ?case by (intro unique_successor)
qed simp

lemma loopExists_always_ahead:
  assumes "loopExists"
  shows "\<exists> c. (headCell, c) \<in> rtrancl r \<and> (\<forall> c'. (headCell, c') \<in> rtrancl r \<longrightarrow> (c', c) \<in> trancl r)"
proof -
  from assms obtain cLoop
    where hd_cLoop: "(headCell, cLoop) \<in> rtrancl r" and cLoop: "(cLoop, cLoop) \<in> trancl r"
    unfolding loopExists_def by auto

  show ?thesis
  proof (intro exI [where x = cLoop] conjI allI impI hd_cLoop)
    fix c assume "(headCell, c) \<in> rtrancl r"
    hence "(c, cLoop) \<in> rtrancl r"
    proof (induct c rule: rtrancl_induct)
      case base from hd_cLoop show ?case.
    next
      case (step c c')
      show ?case
      proof (intro next_step)
        from step show "(c, c') \<in> r" by simp
        from step have "(c, cLoop) \<in> r\<^sup>*" by simp
        also note cLoop finally show "(c, cLoop) \<in> trancl r".
      qed
    qed
    also note cLoop
    finally show "(c, cLoop) \<in> trancl r".
  qed
qed

lemma loopExists_no_end:
  "loopExists = (\<forall> c. (headCell, c) \<in> rtrancl r \<longrightarrow> nextCell c \<noteq> None)"
proof (cases loopExists)
  case False
  hence noLoop: "\<And>c. (headCell, c) \<in> rtrancl r \<Longrightarrow> (c,c) \<notin> trancl r" by (auto simp add: loopExists_def)

  define c where "c \<equiv> headCell"
  have hd_c: "(headCell, c) \<in> rtrancl r" by (auto simp add: c_def)

  define S where "S = { c'. (c, c') \<in> rtrancl r }"
  from finiteList have finite_S: "finite S" by (simp add: S_def)

  from wf_finite_psubset finite_S hd_c S_def have "\<exists> c' \<in> S. nextCell c' = None"
  proof (induct S arbitrary: c rule: wf_induct_rule)
    case (less S)
    show ?case
    proof (cases "nextCell c")
      case None with less show ?thesis by auto
    next
      case (Some c')
      hence cc': "(c, c') \<in> r" by (auto simp add: r_def)

      define S' where "S' = {c''. (c', c'') \<in> rtrancl r }"

      have S'_subset_S: "S' \<subseteq> S"
        unfolding S'_def
      proof (intro subsetI, elim CollectE)
        fix c'' assume "(c', c'') \<in> rtrancl r"
        with cc' show "c'' \<in> S" by (simp add: less)
      qed

      have "\<exists>c'' \<in> S'. nextCell c'' = None"
      proof (intro less iffD2 [OF in_finite_psubset] conjI psubsetI S'_subset_S notI)
        from less have "(headCell, c) \<in> rtrancl r" by simp also note cc'
        finally show "(headCell, c') \<in> rtrancl r".
        from less S'_subset_S show "finite S'" using infinite_super by blast
        have "c \<in> S" by (simp add: less)
        moreover assume "S' = S"
        ultimately have "(c', c) \<in> rtrancl r" by (auto simp add: S'_def)
        from rtranclD [OF this] show False
        proof (elim disjE conjE)
          assume "c' = c" with cc' noLoop less show False by auto
        next
          note cc' also assume "(c', c) \<in> trancl r" 
          finally show False using noLoop less by auto
        qed
      qed (simp add: S'_def)
      with S'_subset_S show ?thesis by auto
    qed
  qed
  with False show ?thesis by (auto simp add: S_def c_def)
next
  case True
  with loopExists_always_ahead obtain cLoop
    where hd_cLoop: "(headCell, cLoop) \<in> rtrancl r"
      and cLoop: "\<And>c. (headCell, c) \<in> rtrancl r \<Longrightarrow> (c, cLoop) \<in> trancl r" by auto

  show ?thesis
  proof (intro iffI allI impI notI True)
    fix c assume "(headCell, c) \<in> rtrancl r"
    hence "(c, cLoop) \<in> trancl r" by (simp add: cLoop)
    then obtain c' where "(c, c') \<in> r" by (metis tranclD)
    moreover assume "nextCell c = None"
    ultimately show False by (simp add: r_def)
  qed
qed



end

context TortoiseHare
begin

definition Invariant :: stpred
  where "Invariant \<equiv> PRED hasLoop = #None \<longrightarrow> ((#headCell, tortoise) \<in> #(rtrancl r) \<and> (tortoise, hare) \<in> #(rtrancl r))"

definition Safety :: stpred where "Safety \<equiv> PRED Invariant \<and> hasLoop \<noteq> #(Some (\<not> loopExists))"

lemma square_Next_cases [consumes 2, case_names unchanged Step FoundLoop LastHare PenultimateHare]:
  assumes s_Safety: "s \<Turnstile> Safety" and sq_Next: "(s,t) \<Turnstile> [Next]_(tortoise, hare, hasLoop)"
  assumes unchanged: "
      \<lbrakk> tortoise t = tortoise s
      ; hare t = hare s
      ; hasLoop t = hasLoop s
      ; (s,t) \<Turnstile> \<not>Step
      ; (s,t) \<Turnstile> \<not>Finish
      \<rbrakk> \<Longrightarrow> P"
  assumes Step: "\<And>h'.
      \<lbrakk> hare t \<noteq> tortoise t
      ; hasLoop s = None
      ; hasLoop t = None
      ; (headCell, tortoise s) \<in> rtrancl r
      ; (headCell, hare s) \<in> rtrancl r
      ; (headCell, tortoise t) \<in> trancl r
      ; (headCell, h') \<in> trancl r
      ; (headCell, hare t) \<in> trancl r
      ; (tortoise s, hare s) \<in> rtrancl r
      ; (tortoise s, tortoise t) \<in> r
      ; (tortoise s, h') \<in> trancl r
      ; (tortoise s, hare t) \<in> trancl r
      ; (hare s, h') \<in> r
      ; (hare s, hare t) \<in> trancl r
      ; (tortoise t, h') \<in> rtrancl r
      ; (tortoise t, hare t) \<in> trancl r
      ; (h', hare t) \<in> r
      ; (s,t) \<Turnstile> Step
      ; (s,t) \<Turnstile> \<not>Finish
      ; (s,t) \<Turnstile> \<not>unchanged(tortoise, hare, hasLoop)
      \<rbrakk> \<Longrightarrow> P"
  assumes FoundLoop: "\<And>h'.
      \<lbrakk> hare t = tortoise t
      ; hasLoop s = None
      ; hasLoop t = Some True
      ; loopExists
      ; (headCell, tortoise s) \<in> rtrancl r
      ; (headCell, hare s) \<in> rtrancl r
      ; (headCell, tortoise t) \<in> trancl r
      ; (headCell, h') \<in> trancl r
      ; (headCell, hare t) \<in> trancl r
      ; (tortoise s, hare s) \<in> rtrancl r
      ; (tortoise s, tortoise t) \<in> r
      ; (tortoise s, h') \<in> trancl r
      ; (tortoise s, hare t) \<in> trancl r
      ; (hare s, h') \<in> r
      ; (hare s, hare t) \<in> trancl r
      ; (tortoise t, h') \<in> rtrancl r
      ; (tortoise t, hare t) \<in> trancl r
      ; (h', hare t) \<in> r
      ; (s,t) \<Turnstile> Step
      ; (s,t) \<Turnstile> \<not>Finish
      ; (s,t) \<Turnstile> \<not>unchanged(tortoise, hare, hasLoop)
      \<rbrakk> \<Longrightarrow> P"
  assumes LastHare: "
      \<lbrakk> hasLoop s = None
      ; hasLoop t = Some False
      ; \<not> loopExists
      ; nextCell (hare s) = None
      ; (headCell, tortoise s) \<in> rtrancl r
      ; (headCell, hare s) \<in> rtrancl r
      ; (tortoise s, hare s) \<in> rtrancl r
      ; (s,t) \<Turnstile> \<not>Step
      ; (s,t) \<Turnstile> Finish
      ; (s,t) \<Turnstile> \<not>unchanged(tortoise, hare, hasLoop)
      \<rbrakk> \<Longrightarrow> P"
  assumes PenultimateHare: "\<And>h'.
      \<lbrakk> hasLoop s = None
      ; hasLoop t = Some False
      ; \<not> loopExists
      ; (hare s, h') \<in> r
      ; nextCell h' = None
      ; (headCell, tortoise s) \<in> rtrancl r
      ; (headCell, hare s) \<in> rtrancl r
      ; (headCell, h') \<in> trancl r
      ; (tortoise s, hare s) \<in> rtrancl r
      ; (tortoise s, h') \<in> trancl r
      ; (hare s, h') \<in> r
      ; (s,t) \<Turnstile> \<not>Step
      ; (s,t) \<Turnstile> Finish
      ; (s,t) \<Turnstile> \<not>unchanged(tortoise, hare, hasLoop)
      \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from sq_Next consider
    (unchanged) "(s,t) \<Turnstile> unchanged (tortoise, hare, hasLoop)" "(s,t) \<Turnstile> \<not>Step"
    | (Step)    "(s,t) \<Turnstile> Step"
    | (Finish)  "(s,t) \<Turnstile> Finish" "(s,t) \<Turnstile> \<not>Step"
    unfolding square_def Next_def by auto
  then show P
  proof cases
    case p: unchanged
    from p have notFinish: "(s,t) \<Turnstile> \<not>Finish" by (auto simp add: Finish_def)
    from p unchanged s_Safety notFinish show ?thesis by auto
  next
    case p: Step
    with s_Safety obtain h' where h': "(hare s, h') \<in> r" "(h', hare t) \<in> r" "(tortoise s, tortoise t) \<in> r"
      "(headCell, tortoise s) \<in> rtrancl r" "(tortoise s, hare s) \<in> rtrancl r"
      by (cases "nextCell (hare s)", auto simp add: Step_def nextNextCell_def r_def Safety_def Invariant_def)

    have "(tortoise t, h') \<in> rtrancl r"
    proof (cases "tortoise s = hare s")
      case True with h' have "tortoise t = h'"
        by (intro unique_successor [OF `(tortoise s, tortoise t) \<in> r`], simp)
      thus ?thesis by simp
    next
      case False
      with h' show ?thesis
        by (intro next_step [OF `(tortoise s, tortoise t) \<in> r`], auto)
    qed

    with h' have rels:
      "(headCell, tortoise s) \<in> rtrancl r"
      "(headCell, hare s) \<in> rtrancl r"
      "(headCell, tortoise t) \<in> trancl r"
      "(headCell, h') \<in> trancl r"
      "(headCell, hare t) \<in> trancl r"
      "(tortoise s, hare s) \<in> rtrancl r"
      "(tortoise s, tortoise t) \<in> r"
      "(tortoise s, h') \<in> trancl r"
      "(tortoise s, hare t) \<in> trancl r"
      "(hare s, h') \<in> r"
      "(hare s, hare t) \<in> trancl r"
      "(tortoise t, h') \<in> rtrancl r"
      "(tortoise t, hare t) \<in> trancl r"
      "(h', hare t) \<in> r"
      by auto

    from p have notFinish: "(s,t) \<Turnstile> \<not>Finish" by (auto simp add: Step_def Finish_def)

    show ?thesis
    proof (cases "hare t = tortoise t")
      case False
      have changed: "tortoise t \<noteq> tortoise s"
      proof (intro notI)
        assume "tortoise t = tortoise s"
        with rels have loop: "(tortoise t, tortoise t) \<in> r" by simp
        hence "\<And>c. (tortoise t, c) \<in> trancl r \<Longrightarrow> c = tortoise t" by (intro tight_loop_eq, auto)
        with rels False show False by simp
      qed

      from False p rels notFinish changed show ?thesis by (intro Step, auto simp add: Step_def)
    next
      case True 
      from rels have "(headCell, hare t) \<in> rtrancl r" "(hare t, hare t) \<in> trancl r" by (auto simp add: True)
      hence loopExists by (auto simp add: loopExists_def)
      with True p rels notFinish show ?thesis by (intro FoundLoop, auto simp add: Step_def)
    qed
  next
    case p: Finish

    with s_Safety have rels1:
      "(headCell, tortoise s) \<in> rtrancl r"
      "(headCell, hare s) \<in> rtrancl r"
      "(tortoise s, hare s) \<in> rtrancl r"
      by (auto simp add: Safety_def Invariant_def Finish_def)

    show ?thesis
    proof (cases "nextCell (hare s)")
      case None
      with rels1 have "\<not> loopExists" unfolding loopExists_no_end by auto
      with None p rels1 show ?thesis by (intro LastHare, auto simp add: Finish_def)
    next
      case (Some h')
      hence "(hare s, h') \<in> r" by (auto simp add: r_def)

      with rels1 have rels2:
        "(headCell, h') \<in> trancl r"
        "(tortoise s, h') \<in> trancl r"
        "(hare s, h') \<in> r"
        by auto

      from rels2 p Some have "\<not> loopExists"
        unfolding loopExists_no_end by (auto simp add: Finish_def nextNextCell_def)

      with rels1 rels2 p show ?thesis
        by (intro PenultimateHare, auto simp add: Finish_def nextNextCell_def Some)
    qed
  qed
qed

lemma safety: "\<turnstile> Spec \<longrightarrow> \<box>Safety"
proof invariant
  fix sigma
  assume sigma: "sigma \<Turnstile> Spec"
  thus "sigma \<Turnstile> Init Safety"
    unfolding Invariant_def Safety_def Spec_def Initial_def r_def
    by (auto simp add: Init_def)

  show "sigma \<Turnstile> stable Safety"
  proof (intro Stable)
    from sigma show "sigma \<Turnstile> \<box>[Next]_(tortoise, hare, hasLoop)"
      by (auto simp add: Spec_def)

    show "\<turnstile> $Safety \<and> [Next]_(tortoise, hare, hasLoop) \<longrightarrow> Safety$"
    proof (intro actionI temp_impI, elim temp_conjE, unfold unl_before)
      fix s t
      assume "s \<Turnstile> Safety" "(s,t) \<Turnstile> [Next]_(tortoise, hare, hasLoop)"
      thus "(s,t) \<Turnstile> Safety$"
        by (cases rule: square_Next_cases, auto simp add: Safety_def Invariant_def loopExists_no_end)
    qed
  qed
qed

end

context LinkedList begin

fun iterateNextCell :: "nat \<Rightarrow> 'Cell \<Rightarrow> 'Cell option"
  where "iterateNextCell 0       c = Some c"
  |     "iterateNextCell (Suc n) c = (case iterateNextCell n c of None \<Rightarrow> None | Some c' \<Rightarrow> nextCell c')"

lemma iterateNextCell_sum: "iterateNextCell (a + b) c = (case iterateNextCell a c of None \<Rightarrow> None | Some c' \<Rightarrow> iterateNextCell b c')"
  by (induct b, (cases "iterateNextCell a c", auto)+)

definition distanceBetween :: "'Cell \<Rightarrow> 'Cell \<Rightarrow> nat"
  where "distanceBetween c1 c2 \<equiv> LEAST n. iterateNextCell n c1 = Some c2"

definition distanceBetweenOrZero :: "'Cell \<Rightarrow> 'Cell \<Rightarrow> nat"
  where "distanceBetweenOrZero c1 c2 \<equiv> if (c1, c2) \<in> rtrancl r then LEAST n. iterateNextCell n c1 = Some c2 else 0"

lemma
  assumes "(c1, c2) \<in> rtrancl r"
  shows iterateNextCell_distanceBetween: "iterateNextCell (distanceBetween c1 c2) c1 = Some c2"
proof -
  from assms obtain n where n: "iterateNextCell n c1 = Some c2"
  proof (induct c2 arbitrary: thesis rule: rtrancl_induct)
    case base
    show thesis by (simp add: base [of 0])
  next
    case (step c2 c3)
    then obtain n where n: "iterateNextCell n c1 = Some c2" by blast
    from step have "iterateNextCell (Suc n) c1 = Some c3" by (simp add: n r_def)
    with step show thesis by blast
  qed
  thus ?thesis unfolding distanceBetween_def by (intro LeastI)
qed

lemma distanceBetween_atMost:
  assumes "iterateNextCell n c1 = Some c2" shows "distanceBetween c1 c2 \<le> n"
  unfolding distanceBetween_def by (intro Least_le assms)

lemma distanceBetween_0 [simp]: "distanceBetween c c = 0"
  unfolding distanceBetween_def by auto

lemma distanceBetween_0_eq:
  assumes "(c1, c2) \<in> rtrancl r"
  shows "(distanceBetween c1 c2 = 0) = (c1 = c2)"
  using iterateNextCell_distanceBetween [OF assms]
  by (intro iffI, simp_all)

lemma distanceBetween_le_1:
  assumes "(c1, c2) \<in> r" shows "distanceBetween c1 c2 \<le> 1"
  using assms by (intro distanceBetween_atMost, simp add: r_def)

lemma distanceBetween_triangle:
  assumes c12: "(c1, c2) \<in> rtrancl r" and c23: "(c2, c3) \<in> rtrancl r"
  shows "distanceBetween c1 c3 \<le> distanceBetween c1 c2 + distanceBetween c2 c3"
  by (intro distanceBetween_atMost, simp add: iterateNextCell_sum
      iterateNextCell_distanceBetween [OF c12] iterateNextCell_distanceBetween [OF c23])

lemma distanceBetween_eq_Suc:
  assumes c13: "(c1, c3) \<in> rtrancl r" and c13_ne: "c1 \<noteq> c3" and c12: "(c1, c2) \<in> r"
  shows "distanceBetween c1 c3 = Suc (distanceBetween c2 c3)"
  using c13 unfolding rtrancl_eq_or_trancl
proof (elim disjE conjE, simp_all add: c13_ne)
  assume "(c1, c3) \<in> trancl r"
  with c12 have c23: "(c2, c3) \<in> rtrancl r" by (intro next_step)

  from c12 have nextCell_c1[simp]: "nextCell c1 = Some c2" by (auto simp add: r_def)

  have iterateNextCell_Suc: "\<And>n. iterateNextCell (Suc n) c1 = iterateNextCell n c2"
  proof -
    fix n
    have "iterateNextCell (Suc n) c1 = iterateNextCell (1 + n) c1" by simp
    also note iterateNextCell_sum
    finally show "?thesis n" by simp
  qed

  have "distanceBetween c1 c3 = (LEAST n. iterateNextCell n c1 = Some c3)" by (simp add: distanceBetween_def)
  also have "... = Suc (distanceBetween c2 c3)"
  proof (intro Least_equality)
    have "iterateNextCell (Suc (distanceBetween c2 c3)) c1 = iterateNextCell (distanceBetween c2 c3) c2"
      by (intro iterateNextCell_Suc)
    also have "... = Some c3" by (intro iterateNextCell_distanceBetween c23)
    finally show "iterateNextCell (Suc (distanceBetween c2 c3)) c1 = Some c3".

    fix n
    assume a: "iterateNextCell n c1 = Some c3"
    from a c13_ne show "Suc (distanceBetween c2 c3) \<le> n"
    proof (cases n)
      case (Suc m)
      have "distanceBetween c2 c3 \<le> m"
        using iterateNextCell_Suc [of m] a
        unfolding distanceBetween_def Suc
        by (intro Least_le, auto)
      thus ?thesis by (simp add: Suc)
    qed simp
  qed

  finally show ?thesis .
qed

lemma loop_unique_previous:
  assumes c1c: "(c1, c) \<in> r" and c1_loop: "(c1, c1) \<in> trancl r"
  assumes c2c: "(c2, c) \<in> r" and c2_loop: "(c2, c2) \<in> trancl r"
  shows "c1 = c2"
proof -
  from assms have cc1: "(c, c1) \<in> rtrancl r" and cc2: "(c, c2) \<in> rtrancl r" by (metis next_step)+

  define n1 where "n1 \<equiv> distanceBetween c c1"
  have n1_c1: "iterateNextCell n1 c = Some c1"
    unfolding n1_def by (intro iterateNextCell_distanceBetween cc1)

  have i1_c2: "iterateNextCell 1 c2 = Some c" using c2c by (auto simp add: r_def)

  from cc2 have "iterateNextCell (1 + n1) c2 = Some c2"
  proof (induct rule: rtrancl_induct)
    case base 
    from n1_c1 c1c show ?case by (simp add: r_def)
  next
    case (step c' c'')
    hence 1: "iterateNextCell 1 c' = Some c''" by (auto simp add: r_def)

    from step have "Some c' = iterateNextCell (Suc n1) c'" by simp
    also have "... = iterateNextCell (1 + n1) c'" by simp
    also from step have "... = iterateNextCell n1 c''"
      unfolding iterateNextCell_sum 1 by simp
    finally have 2: "iterateNextCell n1 c'' = Some c'" by simp

    have "iterateNextCell (n1 + 1) c'' = Some c''"
      unfolding iterateNextCell_sum 2 using step by (simp add: r_def)
    thus ?case by simp
  qed

  hence "iterateNextCell n1 c = Some c2" unfolding iterateNextCell_sum i1_c2 by auto
  with n1_c1 show ?thesis by simp
qed

end

context TortoiseHare begin

lemma WF1_Spec:
  fixes A :: action
  fixes P Q :: stpred
  assumes 0: "\<turnstile> Spec \<longrightarrow> WF(A)_(tortoise, hare, hasLoop)"
  assumes 1: "\<And>s t. \<lbrakk> s \<Turnstile> P; s \<Turnstile> Safety; (s,t) \<Turnstile> [Next]_(tortoise, hare, hasLoop) \<rbrakk> \<Longrightarrow> t \<Turnstile> P \<or> Q"
  assumes 2: "\<And>s t. \<lbrakk> s \<Turnstile> P; s \<Turnstile> Safety; (s,t) \<Turnstile> [Next]_(tortoise, hare, hasLoop) \<rbrakk> \<Longrightarrow> s \<Turnstile> Enabled(<A>_(tortoise, hare, hasLoop))"
  assumes 3: "\<And>s t. \<lbrakk> s \<Turnstile> P; s \<Turnstile> Safety; (s,t) \<Turnstile> [Next]_(tortoise, hare, hasLoop); (s,t) \<Turnstile> A; (s,t) \<Turnstile> \<not>unchanged (tortoise, hare, hasLoop) \<rbrakk> \<Longrightarrow> t \<Turnstile> Q"
  shows "\<turnstile> Spec \<longrightarrow> (P \<leadsto> Q)"
proof -
  from safety have "\<turnstile> Spec \<longrightarrow> \<box>$Safety"
    by (auto simp add: more_temp_simps)
  moreover note 0
  moreover have "\<turnstile> Spec \<longrightarrow> \<box>[Next]_(tortoise, hare, hasLoop)" by (auto simp add: Spec_def)
  ultimately have "\<turnstile> Spec \<longrightarrow> \<box>($Safety \<and> [Next]_(tortoise, hare, hasLoop)) \<and> WF(A)_(tortoise, hare, hasLoop)"
    by (auto simp add: more_temp_simps Valid_def)
  also have "\<turnstile> \<box>($Safety \<and> [Next]_(tortoise, hare, hasLoop)) \<and> WF(A)_(tortoise, hare, hasLoop)
    \<longrightarrow> (P \<leadsto> Q)"
  proof (intro WF1 actionI temp_impI)
    from 1 show "\<And>s t. (s, t) \<Turnstile> $P \<and> $Safety \<and> [Next]_(tortoise, hare, hasLoop) \<Longrightarrow> (s, t) \<Turnstile> P$ \<or> Q$" by auto
    from 3 show "\<And>s t. (s, t) \<Turnstile> ($P \<and> $Safety \<and> [Next]_(tortoise, hare, hasLoop)) \<and> <A>_(tortoise, hare, hasLoop) \<Longrightarrow> (s,t) \<Turnstile> (Q$)" by auto
    from 2 show "\<And>s t. (s, t) \<Turnstile> $P \<and> $Safety \<and> [Next]_(tortoise, hare, hasLoop) \<Longrightarrow> (s, t) \<Turnstile> ($Enabled (<A>_(tortoise, hare, hasLoop)))" by auto
  qed
  finally show ?thesis .
qed

lemma
  assumes s_Safety: "s \<Turnstile> Safety"
  assumes nextNext: "nextNextCell (hare s) \<noteq> None"
  assumes notFinished: "hasLoop s = None"
  shows Enabled_StepI: "s \<Turnstile> Enabled (<Step>_(tortoise, hare, hasLoop))"
proof -
  from nextNext obtain h' h'' where h': "(hare s, h') \<in> r" and h'': "(h', h'') \<in> r"
    by (cases "nextCell (hare s)", auto simp add: nextNextCell_def r_def)

  obtain t' where t': "(tortoise s, t') \<in> r"
  proof -
    from notFinished s_Safety
    have t_h: "(tortoise s, hare s) \<in> rtrancl r" by (auto simp add: Safety_def Invariant_def)
    from rtranclD [OF this] show thesis
    proof (elim disjE conjE)
      assume "tortoise s = hare s"
      with h' show ?thesis by (intro that, auto)
    next
      assume "(tortoise s, hare s) \<in> trancl r"
      from tranclD [OF this] that
      show ?thesis by auto
    qed
  qed

  show "s \<Turnstile> Enabled (<Step>_(tortoise, hare, hasLoop))"
  proof (enabled bv, intro exI allI impI, elim conjE)
    fix u
    assume u: "tortoise u = t'" "hare u = h''" "hasLoop u = (if t' = h'' then Some True else None)"
    have changed: "tortoise u \<noteq> tortoise s \<or> hasLoop u \<noteq> hasLoop s"
    proof (intro disjCI notI, simp)
      assume "tortoise u = tortoise s" with t' have loop: "(tortoise s, tortoise s) \<in> r" by (simp add: u)
      from t' have "t' = tortoise s" by (intro tight_loop_eq loop, simp)
      moreover have "h'' = tortoise s"
      proof (intro tight_loop_eq loop)
        from s_Safety notFinished have "(tortoise s, hare s) \<in> rtrancl r"
          by (auto simp add: Safety_def Invariant_def)
        with h' h'' show "(tortoise s, h'') \<in> rtrancl r" by auto
      qed
      moreover assume "hasLoop u = hasLoop s"
      ultimately show False by (auto simp add: u notFinished)
    qed

    from notFinished h' h'' t' have s_simps [simp]: "nextCell (hare s) = Some h'" "nextCell h' = Some h''" "nextCell (tortoise s) = Some t'"
      by (auto simp add: r_def)

    from notFinished changed show "(s, u) \<Turnstile> <Step>_(tortoise, hare, hasLoop)"
      by (auto simp add: angle_def Step_def nextNextCell_def u)
  qed
qed

lemma hare_endgame: "\<turnstile> Spec \<longrightarrow> (nextNextCell<hare> = #None \<leadsto> hasLoop \<noteq> #None)"
proof -
  have "\<turnstile> Spec \<longrightarrow> (nextNextCell<hare> = #None
                      \<leadsto> hasLoop \<noteq> #None \<or> (nextNextCell<hare> = #None \<and> hasLoop = #None))"
    by (intro imp_imp_leadsto, auto)
  also have "\<turnstile> Spec \<longrightarrow> (hasLoop \<noteq> #None \<or> (nextNextCell<hare> = #None \<and> hasLoop = #None)
                            \<leadsto> hasLoop \<noteq> #None)"
  proof (intro imp_disj_leadstoI [OF imp_leadsto_reflexive WF1_Spec])
    show "\<turnstile> Spec \<longrightarrow> WF(Finish)_(tortoise, hare, hasLoop)" by (auto simp add: Spec_def)

    fix s t
    assume "s \<Turnstile> nextNextCell<hare> = #None \<and> hasLoop = #None"
    hence s: "hasLoop s = None" "nextNextCell (hare s) = None" by auto

    assume s_Safety: "s \<Turnstile> Safety" and Next: "(s, t) \<Turnstile> [Next]_(tortoise, hare, hasLoop)"

    from s_Safety Next s
    show "t \<Turnstile> (nextNextCell<hare> = #None \<and> hasLoop = #None) \<or> hasLoop \<noteq> #None"
    proof (cases rule: square_Next_cases)
      case (Step h')
      hence "(hare s, h') \<in> r" "(h', hare t) \<in> r" by simp_all
      with s show ?thesis by (simp add: nextNextCell_def r_def)
    next
      case (FoundLoop h')
      hence "(hare s, h') \<in> r" "(h', hare t) \<in> r" by simp_all
      with s show ?thesis by (simp add: nextNextCell_def r_def)
    qed auto

    show "s \<Turnstile> Enabled (<Finish>_(tortoise, hare, hasLoop))"
    proof (enabled bv, intro exI allI impI, elim conjE)
      fix u assume "hasLoop u = Some False" thus "(s, u) \<Turnstile> <Finish>_(tortoise, hare, hasLoop)"
        by (auto simp add: angle_def Finish_def s)
    qed

    assume "(s,t) \<Turnstile> Finish"
    thus "t \<Turnstile> hasLoop \<noteq> #None" by (auto simp add: Finish_def)
  qed
  finally show "\<turnstile> Spec \<longrightarrow> (nextNextCell<hare> = #None \<leadsto> hasLoop \<noteq> #None)" .
qed

lemma tortoise_visits_everywhere:
  assumes hd_c: "(headCell, c) \<in> rtrancl r"
  shows "\<turnstile> Spec \<longrightarrow> \<diamond>(hasLoop \<noteq> #None \<or> tortoise = #c)"
proof -
  from hd_c have "\<turnstile> Spec \<longrightarrow> \<diamond>(hasLoop \<noteq> #None \<or> (tortoise, #c) \<in> #(rtrancl r))"
    by (intro imp_eventually_init, auto simp add: Init_def Spec_def Initial_def)

  also have "\<turnstile> Spec \<longrightarrow> (hasLoop \<noteq> #None \<or> (tortoise, #c) \<in> #(rtrancl r) \<leadsto> hasLoop \<noteq> #None \<or> tortoise = #c)"
  proof (intro imp_disj_leadstoI)
    show "\<turnstile> Spec \<longrightarrow> (hasLoop \<noteq> #None \<leadsto> hasLoop \<noteq> #None \<or> tortoise = #c)" by (intro imp_imp_leadsto, auto)
    show "\<turnstile> Spec \<longrightarrow> ((tortoise, #c) \<in> #(rtrancl r) \<leadsto> hasLoop \<noteq> #None \<or> tortoise = #c)"
    proof (rule imp_leadsto_triangle_excl [OF imp_leadsto_reflexive])
      have "\<turnstile> Spec
      \<longrightarrow> ((tortoise, #c) \<in> #(rtrancl r) \<and> \<not> (hasLoop \<noteq> #None \<or> tortoise = #c)
          \<leadsto> (\<exists>n. (tortoise, #c) \<in> #(rtrancl r) \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n))"
        by (intro imp_imp_leadsto, auto)
      also have "\<turnstile> Spec
      \<longrightarrow> ((\<exists>n. (tortoise, #c) \<in> #(rtrancl r) \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n)
          \<leadsto> hasLoop \<noteq> #None \<or> tortoise = #c)"
      proof (intro wf_imp_ex_leadsto [OF wf_less imp_leadsto_diamond])
        fix n
        show "\<turnstile> Spec \<longrightarrow> ((tortoise, #c) \<in> #(rtrancl r) \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n
            \<leadsto> ((tortoise, #c) \<in> #(rtrancl r) \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n \<and> nextNextCell<hare> \<noteq> #None)
               \<or> nextNextCell<hare> = #None)"
          by (intro imp_imp_leadsto, auto)

        have "\<turnstile> Spec \<longrightarrow> (nextNextCell<hare> = #None \<leadsto> hasLoop \<noteq> #None)" by (intro hare_endgame)
        also have "\<turnstile> Spec \<longrightarrow> (hasLoop \<noteq> #None
          \<leadsto> (hasLoop \<noteq> #None \<or> tortoise = #c)
              \<or> (\<exists>n'. #((n', n) \<in> {(n, n'). n < n'}) \<and> (tortoise, #c) \<in> #(rtrancl r)
                        \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n'))"
          by (intro imp_imp_leadsto, auto)
        finally show "\<turnstile> Spec \<longrightarrow> (nextNextCell<hare> = #None \<leadsto> (hasLoop \<noteq> #None \<or> tortoise = #c)
                  \<or> (\<exists>n'. #((n', n) \<in> {(n, n'). n < n'}) \<and> (tortoise, #c) \<in> #(rtrancl r)
                        \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n'))".

        show "\<turnstile> Spec
        \<longrightarrow> ((tortoise, #c) \<in> #(rtrancl r) \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n \<and> nextNextCell<hare> \<noteq> #None
              \<leadsto> (hasLoop \<noteq> #None \<or> tortoise = #c)
                  \<or> (\<exists>n'. #((n', n) \<in> {(n, n'). n < n'}) \<and> (tortoise, #c) \<in> #(rtrancl r)
                        \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n'))"
        proof (intro WF1_Spec)
          show "\<turnstile> Spec \<longrightarrow> WF(Step)_(tortoise, hare, hasLoop)" by (auto simp add: Spec_def)

          fix s t
          assume "s \<Turnstile> (tortoise, #c) \<in> #(rtrancl r) \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n \<and> nextNextCell<hare> \<noteq> #None"
          then obtain h' h'' where s: "hasLoop s = None" "distanceBetween (tortoise s) c = n" "tortoise s \<noteq> c"
            and rels1: "(tortoise s, c) \<in> rtrancl r" "(hare s, h') \<in> r" "(h', h'') \<in> r"
            by (cases "nextCell (hare s)", auto simp add: r_def nextNextCell_def)

          assume s_Safety: "s \<Turnstile> Safety" and Next: "(s, t) \<Turnstile> [Next]_(tortoise, hare, hasLoop)"

          from rels1
          show "s \<Turnstile> Enabled (<Step>_(tortoise, hare, hasLoop))"
            by (intro Enabled_StepI s_Safety s, auto simp add: nextNextCell_def r_def)
        
          {
            assume is_Step: "(s,t) \<Turnstile> Step"
            from s_Safety Next this
            show "t \<Turnstile> (hasLoop \<noteq> #None \<or> tortoise = #c)
                   \<or> (\<exists>n'. #((n', n) \<in> {(n, n'). n < n'}) \<and> (tortoise, #c) \<in> #(rtrancl r)
                          \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n')"
            proof (cases rule: square_Next_cases)
              case (Step h1)
              from s rels1 distanceBetween_0_eq show ?thesis
              proof (cases n)
                case (Suc n')
                show ?thesis
                proof (cases "tortoise t = c")
                  case True thus ?thesis by simp
                next
                  case False
                  moreover from s rels1
                  have "(tortoise s, c) \<in> trancl r" by (metis rtranclD)
                  with Step have "(tortoise t, c) \<in> rtrancl r" by (intro next_step, auto)
                  moreover from Step have "hasLoop t = None" by simp
                  moreover from Step s rels1 have "distanceBetween (tortoise s) c = Suc (distanceBetween (tortoise t) c)"
                    by (intro distanceBetween_eq_Suc, auto)
                  with s have "distanceBetween (tortoise t) c < n" by auto
                  ultimately show ?thesis by auto
                qed
              qed auto
            qed (auto simp add: nextNextCell_def r_def)
          }
          with s_Safety Next s rels1 
          show "t \<Turnstile> ((tortoise, #c) \<in> #(rtrancl r) \<and> hasLoop = #None \<and> tortoise \<noteq> #c 
                          \<and> distanceBetween<tortoise, #c> = #n \<and> nextNextCell<hare> \<noteq> #None)
                   \<or> (hasLoop \<noteq> #None \<or> tortoise = #c)
                   \<or> (\<exists>n'. #((n', n) \<in> {(n, n'). n < n'}) \<and> (tortoise, #c) \<in> #(rtrancl r)
                          \<and> hasLoop = #None \<and> tortoise \<noteq> #c \<and> distanceBetween<tortoise, #c> = #n')"
            by (cases rule: square_Next_cases, auto simp add: nextNextCell_def r_def)
        qed
      qed
      finally show "\<turnstile> Spec \<longrightarrow> ((tortoise, #c) \<in> #(rtrancl r) \<and> \<not> (hasLoop \<noteq> #None \<or> tortoise = #c) \<leadsto> hasLoop \<noteq> #None \<or> tortoise = #c)".
    qed
  qed

  finally show ?thesis.
qed

theorem liveness: "\<turnstile> Spec \<longrightarrow> \<diamond>(hasLoop \<noteq> #None)"
proof (cases loopExists)
  case False

  with loopExists_no_end obtain cLast
    where hd_cLast: "(headCell, cLast) \<in> rtrancl r" and cLast: "nextCell cLast = None" by auto

  have "\<turnstile> Spec \<longrightarrow> \<diamond>(hasLoop \<noteq> #None \<or> tortoise = #cLast)"
    by (intro tortoise_visits_everywhere hd_cLast)
  also have "\<turnstile> Spec \<longrightarrow> (hasLoop \<noteq> #None \<or> tortoise = #cLast \<leadsto> hasLoop \<noteq> #None \<or> (tortoise = #cLast \<and> hasLoop = #None))"
    by (intro imp_imp_leadsto, auto)
  also have "\<turnstile> Spec \<longrightarrow> (hasLoop \<noteq> #None \<or> (tortoise = #cLast \<and> hasLoop = #None) \<leadsto> hasLoop \<noteq> #None)"
  proof (intro imp_disj_leadstoI imp_leadsto_reflexive)
    have "\<turnstile> Spec \<longrightarrow> (tortoise = #cLast \<and> hasLoop = #None \<leadsto> nextNextCell<hare> = #None)"
    proof (intro imp_INV_leadsto [OF safety imp_imp_leadsto] intI temp_impI, elim temp_conjE)
      fix s
      assume s: "s \<Turnstile> tortoise = #cLast" "s \<Turnstile> Safety" "s \<Turnstile> hasLoop = #None"
      hence "(cLast, hare s) \<in> rtrancl r"
        by (auto simp add: Safety_def Invariant_def)
      from rtranclD [OF this]
      have "hare s = cLast"
      proof (elim disjE conjE)
        assume "(cLast, hare s) \<in> trancl r" from tranclD [OF this] cLast show ?thesis by (auto simp add: r_def)
      qed simp
      with cLast show "s \<Turnstile> nextNextCell<hare> = #None"
        by (cases "nextCell (hare s)", auto simp add: nextNextCell_def)
    qed
    also note hare_endgame
    finally show "\<turnstile> Spec \<longrightarrow> (tortoise = #cLast \<and> hasLoop = #None \<leadsto> hasLoop \<noteq> #None)" .
  qed
  finally show ?thesis .

next
  case True
  with loopExists_always_ahead obtain cLoop where hd_cLoop: "(headCell, cLoop) \<in> rtrancl r"
    and cLoop_ahead: "\<And>c. (headCell, c) \<in> rtrancl r \<Longrightarrow> (c, cLoop) \<in> trancl r" by auto

  have "\<turnstile> Spec \<longrightarrow> \<diamond>(hasLoop \<noteq> #None \<or> tortoise = #cLoop)"
    by (intro tortoise_visits_everywhere hd_cLoop)
  also have "\<turnstile> Spec \<longrightarrow> (hasLoop \<noteq> #None \<or> tortoise = #cLoop \<leadsto> hasLoop \<noteq> #None \<or> (hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r)))"
    using cLoop_ahead by (intro imp_INV_leadsto [OF safety imp_imp_leadsto], auto simp add: Safety_def Invariant_def)
  also have "\<turnstile> Spec \<longrightarrow> (hasLoop \<noteq> #None \<or> (hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r)) \<leadsto> hasLoop \<noteq> #None)"
  proof (intro imp_disj_leadstoI imp_leadsto_reflexive)
    have "\<turnstile> Spec \<longrightarrow> (hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r)
            \<leadsto> (\<exists> inductor. hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r) \<and> #inductor = (tortoise = hare, distanceBetween<hare, tortoise>)))"
      by (intro imp_imp_leadsto, auto)
    also have "\<turnstile> Spec \<longrightarrow> ((\<exists> inductor. hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r) \<and> #inductor = (tortoise = hare, distanceBetween<hare, tortoise>))
        \<leadsto> hasLoop \<noteq> #None)"
    proof (intro wf_imp_ex_leadsto)
      show "wf ({(False, True)} <*lex*> {(i::nat,j). i < j})" by (intro wf_lex_prod wf_less, auto)

      fix inductor

      show "\<turnstile> Spec \<longrightarrow> (hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r) \<and> #inductor = (tortoise = hare, distanceBetween<hare, tortoise>)
                      \<leadsto> hasLoop \<noteq> #None \<or> (\<exists>inductor'. #((inductor', inductor) \<in> {(False, True)} <*lex*> {(i, j). i < j})
                        \<and> hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r) \<and> #inductor' = (tortoise = hare, distanceBetween<hare, tortoise>)))"
      proof (intro WF1_Spec)
        show "\<turnstile> Spec \<longrightarrow> WF(Step)_(tortoise, hare, hasLoop)"
          by (auto simp add: Spec_def)

        obtain hare_tortoise_eq hare_tortoise_distance where inductor: "inductor = (hare_tortoise_eq, hare_tortoise_distance)" by (cases inductor)

        fix s t
        assume "s \<Turnstile> hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r) \<and> #inductor = (tortoise = hare, distanceBetween<hare, tortoise>)"
        hence s: "hasLoop s = None" "(cLoop, tortoise s) \<in> trancl r" "hare_tortoise_eq = (tortoise s = hare s)" "hare_tortoise_distance = distanceBetween (hare s) (tortoise s)"
          by (simp_all add: inductor)

        assume s_Safety: "s \<Turnstile> Safety" and Next: "(s, t) \<Turnstile> [Next]_(tortoise, hare, hasLoop)"
        {
          assume Step: "(s,t) \<Turnstile> Step"

          from s_Safety Next Step
          show "t \<Turnstile> hasLoop \<noteq> #None \<or> (\<exists>inductor'. #((inductor', inductor) \<in> {(False, True)} <*lex*> {(i, j). i < j}) 
                                                              \<and> hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r)
                                                              \<and> #inductor' = (tortoise = hare, distanceBetween<hare, tortoise>))"
          proof (cases rule: square_Next_cases)
            case (Step h')

            show ?thesis
            proof (cases "hare s = tortoise s")
              case True
              with Step s show ?thesis by (simp add: inductor, intro exI [where x = False], auto)
            next
              case False

              have "distanceBetween (hare s) (tortoise s) = Suc (distanceBetween h' (tortoise s))"
              proof (intro distanceBetween_eq_Suc False Step)
                from Step have "(hare s, cLoop) \<in> trancl r" by (intro cLoop_ahead)
                also from s have "(cLoop, tortoise s) \<in> trancl r" by simp
                finally show "(hare s, tortoise s) \<in> rtrancl r" by simp
              qed

              moreover have "distanceBetween h' (tortoise t) \<le> Suc (distanceBetween h' (tortoise s))"
              proof -
                from Step have "distanceBetween h' (tortoise t) \<le> distanceBetween h' (tortoise s)
                                                                  + distanceBetween (tortoise s) (tortoise t)"
                proof (intro distanceBetween_triangle)
                  from Step have "(h', cLoop) \<in> trancl r" by (intro cLoop_ahead, simp)
                  also from s Step have "(cLoop, tortoise s) \<in> trancl r" by simp
                  finally show "(h', tortoise s) \<in> rtrancl r" by simp
                qed simp

                moreover from Step have "distanceBetween (tortoise s) (tortoise t) \<le> 1"
                  by (intro distanceBetween_le_1)

                ultimately show ?thesis by auto
              qed

              moreover have "distanceBetween h' (tortoise t) = Suc (distanceBetween (hare t) (tortoise t))"
              proof (intro distanceBetween_eq_Suc Step notI)
                from Step have "(h', cLoop) \<in> trancl r" by (intro cLoop_ahead, simp)
                also from s Step have "(cLoop, tortoise t) \<in> trancl r" by simp
                finally show "(h', tortoise t) \<in> rtrancl r" by simp

                assume eq: "h' = tortoise t"
                have "hare s = tortoise s"
                proof (intro loop_unique_previous)
                  from Step show "(hare s, h') \<in> r" "(tortoise s, h') \<in> r" by (auto simp add: eq)
                  from Step have "(hare s, cLoop) \<in> trancl r" by (intro cLoop_ahead)
                  also from s have "(cLoop, tortoise s) \<in> trancl r" by simp
                  also from Step have "(tortoise s, hare s) \<in> rtrancl r" by simp
                  finally show "(hare s, hare s) \<in> trancl r".

                  from Step have "(tortoise s, cLoop) \<in> trancl r" by (intro cLoop_ahead)
                  also from s have "(cLoop, tortoise s) \<in> trancl r" by simp
                  finally show "(tortoise s, tortoise s) \<in> trancl r".
                qed
                with False show False by simp
              qed

              moreover from s Step have "(cLoop, tortoise t) \<in> trancl r" by auto
              ultimately show ?thesis using Step False by (simp add: inductor s, auto)
            qed
          qed simp_all
        }
        note Step_lemma = this

        from s_Safety Next Step_lemma True
        show "t \<Turnstile> hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r) \<and> #inductor = (tortoise = hare, distanceBetween<hare, tortoise>) \<or>
                                          hasLoop \<noteq> #None \<or>
                                          (\<exists>inductor'. #((inductor', inductor) \<in> {(False, True)} <*lex*> {(i, j). i < j}) \<and>
                                                       hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r) \<and> #inductor' = (tortoise = hare, distanceBetween<hare, tortoise>))"
        proof (cases rule: square_Next_cases)
          case unchanged with s show ?thesis by (auto simp add: inductor)
        qed simp_all

        from s_Safety s have hd_h: "(headCell, hare s) \<in> rtrancl r" by (auto simp add: Safety_def Invariant_def)
        then obtain h' where h': "(hare s, h') \<in> r" by (metis tranclD cLoop_ahead)
        note hd_h also note h' finally obtain h'' where h'': "(h', h'') \<in> r" by (metis tranclD cLoop_ahead)

        from h' h'' show "s \<Turnstile> Enabled (<Step>_(tortoise, hare, hasLoop))"
          by (intro Enabled_StepI s_Safety s, auto simp add: nextNextCell_def r_def)
      qed
    qed
    finally show "\<turnstile> Spec \<longrightarrow> (hasLoop = #None \<and> (#cLoop, tortoise) \<in> #(trancl r) \<leadsto> hasLoop \<noteq> #None)" .
  qed
  finally show ?thesis .
qed

end

end
