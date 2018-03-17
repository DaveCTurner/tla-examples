theory Refinement
  imports SimpleAllocator SchedulingAllocator
begin

locale Refinement
  = Simple: SimpleAllocator
  where InitState = InitState_Simple
    and Request = Request_Simple
    and Allocate = Allocate_Simple
    and Return = Return_Simple
    and Next = Next_Simple
    and ReturnFair = ReturnFair_Simple
    and AllocateFair = AllocateFair_Simple
    and Safety = Safety_Simple
    + SchedulingAllocator
  for InitState_Simple Request_Simple Allocate_Simple Return_Simple Next_Simple
    ReturnFair_Simple AllocateFair_Simple Safety_Simple

context Refinement
begin

lemma refinement: "\<turnstile> SchedulingAllocator \<longrightarrow> SimpleAllocator"
  unfolding Simple.SimpleAllocator_def
proof (intro temp_imp_conjI imp_forall)
  have "\<turnstile> SchedulingAllocator \<longrightarrow> Init InitState" by (auto simp add: SchedulingAllocator_def)
  also have "\<turnstile> Init InitState \<longrightarrow> Init InitState_Simple"
    by (auto simp add: Init_def InitState_def Simple.InitState_def)
  finally show "\<turnstile> SchedulingAllocator \<longrightarrow> Init InitState_Simple".

  have "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>[Next]_vars" by (auto simp add: SchedulingAllocator_def)
  also have "\<turnstile> \<box>[Next]_vars \<longrightarrow> \<box>[Next_Simple]_(unsat, alloc)"
  proof (intro STL4 actionI temp_impI)
    fix s t
    assume "(s,t) \<Turnstile> [Next]_vars"
    thus "(s,t) \<Turnstile> [Next_Simple]_(unsat, alloc)"
      apply (cases rule: square_Next_cases, unfold Simple.Next_def Simple.Request_def Simple.Return_def Simple.Allocate_def updated_def square_def)
      by (simp+, blast)+
  qed
  finally show "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>[Next_Simple]_(unsat, alloc)".

  fix c
  have "\<turnstile> SchedulingAllocator \<longrightarrow> (Enabled (<\<exists>S. id<$alloc, #c> = #S \<and> Return_Simple c S>_(unsat,alloc)) \<leadsto> id<alloc,#c> \<noteq> #{})"
    by (intro imp_imp_leadsto, auto simp add: enabled_def angle_def Simple.Return_def)
  also have "\<turnstile> SchedulingAllocator \<longrightarrow> (id<alloc,#c> \<noteq> #{} \<leadsto> ($(id<alloc,#c> \<noteq> #{}) \<and> \<not>(id<alloc,#c> \<noteq> #{})$))"
  proof (intro imp_unstable_leadsto_change)
    have "\<turnstile> SchedulingAllocator \<longrightarrow> (id<alloc, #c> \<noteq> #{} \<leadsto> (#True :: stpred))" by (intro imp_imp_leadsto, simp)
    also from infinitely_often_freed
    have "\<turnstile> SchedulingAllocator \<longrightarrow> ((#True :: stpred) \<leadsto> id<alloc, #c> = #{})" unfolding leadsto_def by simp
    finally show "\<turnstile> SchedulingAllocator \<longrightarrow> (id<alloc, #c> \<noteq> #{} \<leadsto> \<not> id<alloc, #c> \<noteq> #{})" by simp
  qed
  also have "\<turnstile> SchedulingAllocator \<longrightarrow> ($(id<alloc,#c> \<noteq> #{}) \<and> \<not>(id<alloc,#c> \<noteq> #{})$
                  \<leadsto> <\<exists>S. id<$alloc, #c> = #S \<and> Return_Simple c S>_(unsat,alloc))"
  proof (intro imp_leadsto_add_precondition [OF _ imp_imp_leadsto] actionI temp_impI)
    show "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>[Next]_vars" unfolding SchedulingAllocator_def by auto
    fix s t
    assume "(s, t) \<Turnstile> ($(id<alloc, #c> \<noteq> #{}) \<and> \<not> (id<alloc, #c> \<noteq> #{})$) \<and> [Next]_vars"
    hence s: "alloc s c \<noteq> {}" and t: "alloc t c = {}" and Next: "(s,t) \<Turnstile> [Next]_vars" by simp_all

    from Next s t show "(s, t) \<Turnstile> <\<exists>S. id<$alloc, #c> = #S \<and> Return_Simple c S>_(unsat, alloc)"
    proof (cases rule: square_Next_cases)
      case (Return c' S')
      with s t have c_eq[simp]: "c = c'" by auto
      have alloc_eq: "alloc t c = alloc s c - S'" unfolding Return by auto
      with s t Return have S'_eq[simp]: "S' = alloc s c" by auto
      have "modifyAt (alloc s) c' (del (alloc s c')) \<noteq> alloc s"
      proof (intro notI)
        assume "modifyAt (alloc s) c' (del (alloc s c')) = alloc s"
        from Return cong [OF this refl, where x = c] show False
          by (auto simp add: del_def)
      qed
      with Return show ?thesis
        by (auto simp add: angle_def Simple.Return_def updated_def)
    next
      case (Allocate c' S')
      with s t have "c' \<noteq> c" by auto
      with s t Allocate show ?thesis by auto
    qed auto
  qed
  finally have "\<turnstile> SchedulingAllocator \<longrightarrow> (SF(\<exists>S. id<$alloc, #c> = #S \<and> Return_Simple c S)_(unsat, alloc))" by (intro imp_SFI)
  also note SFImplWF
  finally show "\<turnstile> SchedulingAllocator \<longrightarrow> ReturnFair_Simple c"
    unfolding Simple.ReturnFair_def.

  have "\<turnstile> SchedulingAllocator \<longrightarrow> (Enabled (<\<exists>S. Allocate_Simple c S>_(unsat, alloc)) \<leadsto> id<unsat,#c> \<noteq> #{})"
    by (intro imp_imp_leadsto, auto simp add: enabled_def angle_def Simple.Allocate_def)
  also note unsatisfied_leadsto_scheduled
  also have "\<turnstile> SchedulingAllocator \<longrightarrow> (#c \<in> set<sched> \<leadsto> ($(#c \<in> set<sched>) \<and> \<not>(#c \<in> set<sched>)$))"
  proof (intro imp_unstable_leadsto_change)
    have "\<turnstile> SchedulingAllocator \<longrightarrow> (#c \<in> set<sched> \<leadsto> (#True :: stpred))" by (intro imp_imp_leadsto, simp)
    also have "\<turnstile> SchedulingAllocator \<longrightarrow> ((#True :: stpred) \<leadsto> #c \<notin> set<sched>)"
      using infinitely_often_unscheduled unfolding leadsto_def by auto
    finally show "\<turnstile> SchedulingAllocator \<longrightarrow> (#c \<in> set<sched> \<leadsto> \<not> (#c \<in> set<sched>))".
  qed
  also have "\<turnstile> SchedulingAllocator \<longrightarrow> (($(#c \<in> set<sched>) \<and> \<not>(#c \<in> set<sched>)$) \<leadsto> <\<exists>S. Allocate_Simple c S>_(unsat,alloc))"
  proof (intro imp_leadsto_add_precondition [OF _ imp_imp_leadsto] actionI temp_impI)
    show "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>[Next]_vars" by (auto simp add: SchedulingAllocator_def)
    fix s t
    assume "(s,t) \<Turnstile> ($(#c \<in> set<sched>) \<and> \<not> (#c \<in> set<sched>)$) \<and> [Next]_vars"
    hence c: "c \<in> set (sched s)" "c \<notin> set (sched t)" and Next: "(s,t) \<Turnstile> [Next]_vars" by simp_all
    from Next c show "(s,t) \<Turnstile> <\<exists>S. Allocate_Simple c S>_(unsat,alloc)"
    proof (cases rule: square_Next_cases)
      case (Allocate c' S')
      with c have "c = c' \<and> S' = unsat s c" by (cases "S' = unsat s c'", auto)
      thus ?thesis
        unfolding Simple.Allocate_def updated_def angle_def
        using Allocate apply clarsimp
        apply (intro conjI exI [where x = "unsat s c'"], auto)
        using Allocate(10) by auto
    qed auto
  qed
  finally show "\<turnstile> SchedulingAllocator \<longrightarrow> AllocateFair_Simple c"
    unfolding Simple.AllocateFair_def by (intro imp_SFI, auto)
qed

end