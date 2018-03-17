theory SchedulingAllocator
  imports AllocatorPrelims
begin

locale SchedulingAllocator =
  (* variables *)
  fixes unsat :: "(Client \<Rightarrow> Resource set) stfun"
  fixes alloc :: "(Client \<Rightarrow> Resource set) stfun"
  fixes pool  :: "Client set stfun"
  fixes sched :: "Client list stfun"
  fixes vars defines "vars \<equiv> LIFT (unsat,alloc,pool,sched)"
  assumes bv: "basevars (unsat, alloc, pool, sched)"
    (* set of available resources *)
  fixes available :: "Resource set stfun"
  defines "available s \<equiv> - (\<Union>c. alloc s c)"
  fixes higherPriorityClients :: "Client \<Rightarrow> Client set stfun"
  defines "higherPriorityClients c s \<equiv> set (takeWhile (op \<noteq> c) (sched s))"
    (* initial state *)
  fixes InitState :: stpred
  defines "InitState \<equiv> PRED ((\<forall>c. id<alloc,#c> = #{} \<and> id<unsat,#c> = #{}) \<and> pool = #{} \<and> sched = #[])"
    (* client requests resources *)
  fixes Request :: "Client \<Rightarrow> Resource set \<Rightarrow> action"
  defines "Request c S \<equiv> ACT #S \<noteq> #{} \<and> id<$unsat,#c> = #{} \<and> id<$alloc,#c> = #{}
                    \<and> #(finite S)
                    \<and> updated unsat c (add S)
                    \<and> pool$ = (insert c)<$pool>
                    \<and> unchanged (alloc, sched)"
    (* schedule waiting pool *)
  fixes Schedule :: action
  defines "Schedule \<equiv> ACT ($pool \<noteq> #{} \<and> pool$ = #{}
      \<and> (\<exists> poolOrder. #(set poolOrder) = $pool \<and> #(distinct poolOrder) \<and> sched$ = $sched @ #poolOrder)
      \<and> unchanged (unsat, alloc))"
    (* allocator allocates resources *)
  fixes Allocate :: "Client \<Rightarrow> Resource set \<Rightarrow> action"
  defines "Allocate c S \<equiv> ACT (#S \<noteq> #{} \<and> (#S \<subseteq> ($available \<inter> id<$unsat,#c>))
                    \<and> #c \<in> set<$sched>
                    \<and> (\<forall>c'. #c' \<in> $higherPriorityClients c \<longrightarrow> id<$unsat,#c'> \<inter> #S = #{})
                    \<and> sched$ = (if #S = id<$unsat,#c> then (filter (op \<noteq> c))<$sched> else $sched)
                    \<and> (updated alloc c (add S))
                    \<and> (updated unsat c (del S))
                    \<and> unchanged pool)"
    (* client returns resources *)
  fixes Return :: "Client \<Rightarrow> Resource set \<Rightarrow> action"
  defines "Return c S \<equiv> ACT (#S \<noteq> #{} \<and> #S \<subseteq> id<$alloc,#c>
                    \<and> updated alloc c (del S)
                    \<and> unchanged (unsat, pool, sched))"
    (* next-state relation *)
  fixes Next :: action
  defines "Next \<equiv> ACT ((\<exists> c S. Request c S \<or> Allocate c S \<or> Return c S) \<or> Schedule)"
    (* fairness of Return *)
  fixes ReturnFair :: "Client \<Rightarrow> temporal"
  defines "ReturnFair c \<equiv> TEMP WF(\<exists>S. id<$unsat,#c> = #{} \<and> id<$alloc,#c> = #S \<and> Return c S)_vars"
    (* fairness of Allocate *)
  fixes AllocateHeadFair :: temporal
  defines "AllocateHeadFair \<equiv> TEMP WF(\<exists>S c. #c = hd<$sched> \<and> Allocate c S)_vars"
    (* fairness of Schedule *)
  fixes ScheduleFair :: temporal
  defines "ScheduleFair \<equiv> TEMP WF(Schedule)_vars"
    (* full specification *)
  fixes SchedulingAllocator :: temporal
  defines "SchedulingAllocator \<equiv> TEMP (Init InitState \<and> \<box>[Next]_vars \<and>  (\<forall>c. ReturnFair c) \<and> AllocateHeadFair \<and> ScheduleFair)"
    (* mutual exclusion safety property *)
  fixes MutualExclusion :: stpred
  defines "MutualExclusion \<equiv> PRED \<forall> c1 c2. #c1 \<noteq> #c2 \<longrightarrow> id<alloc,#c1> \<inter> id<alloc,#c2> = #{}"
    (* lower-level invariant of allocator *)
  fixes AllocatorInvariant :: stpred
  defines "AllocatorInvariant \<equiv> PRED
    ( (\<forall>c. #c \<in> pool \<longrightarrow> id<unsat,#c> \<noteq> #{})
    \<and> (\<forall>c. #c \<in> pool \<longrightarrow> id<alloc,#c> = #{})
    \<and> (\<forall>c. #c \<in> set<sched> \<longrightarrow> id<unsat,#c> \<noteq> #{})
    \<and> (\<forall>c. #c \<in> set<sched>
          \<longrightarrow> (\<forall>c'. #c' \<in> higherPriorityClients c
          \<longrightarrow> id<alloc,#c> \<inter> id<unsat,#c'> = #{}))
    \<and> (\<forall>c. #c \<notin> pool \<longrightarrow> #c \<notin> set<sched> \<longrightarrow> id<unsat,#c> = #{})
    \<and> (\<forall>c. id<alloc,#c> \<inter> id<unsat,#c> = #{})
    \<and> (pool \<inter> set<sched> = #{})
    \<and> finite<pool>
    \<and> (\<forall>c. finite<id<unsat,#c>>)
    \<and> (\<forall>c. finite<id<alloc,#c>>)
    \<and> distinct<sched>)"
    (* overall safety property *)
  fixes Safety :: stpred
  defines "Safety \<equiv> PRED (MutualExclusion \<and> AllocatorInvariant)"

context SchedulingAllocator
begin

lemma SafetyI:
  assumes "\<And>c1 c2. c1 \<noteq> c2 \<Longrightarrow> alloc s c1 \<inter> alloc s c2 = {}"
  assumes "\<And>c. c \<in> pool s \<Longrightarrow> unsat s c \<noteq> {}"
  assumes "\<And>c. c \<in> pool s \<Longrightarrow> alloc s c = {}"
  assumes "\<And>c. c \<in> set (sched s) \<Longrightarrow> unsat s c \<noteq> {}"
  assumes "\<And>c1 c2. c1 \<in> set (sched s)
                  \<Longrightarrow> c2 \<in> higherPriorityClients c1 s
                  \<Longrightarrow> alloc s c1 \<inter> unsat s c2 = {}"
  assumes "\<And>c. alloc s c \<inter> unsat s c = {}"
  assumes "\<And>c. c \<notin> pool s \<Longrightarrow> c \<notin> set (sched s) \<Longrightarrow> unsat s c = {}"
  assumes "pool s \<inter> set (sched s) = {}"
  assumes "finite (pool s)"
  assumes "distinct (sched s)"
  assumes "\<And>c. finite (unsat s c)"
  assumes "\<And>c. finite (alloc s c)"
  shows "s \<Turnstile> Safety"
  unfolding Safety_def AllocatorInvariant_def MutualExclusion_def
  using assms by simp

lemma square_Next_cases [consumes 1, case_names unchanged Request Schedule Allocate Return]:
  assumes Next: "(s,t) \<Turnstile> [Next]_vars"
  assumes unchanged: "
    \<lbrakk> unsat t = unsat s;
      alloc t = alloc s;
      pool t = pool s;
      sched t = sched s;
      available t = available s;
      \<And>c'. higherPriorityClients c' t = higherPriorityClients c' s
    \<rbrakk> \<Longrightarrow> P"
  assumes Request: "\<And>c S.
    \<lbrakk> S \<noteq> {};
      finite S;
      unsat s c = {};
      alloc s c = {};
      unsat t = modifyAt (unsat s) c (add S);
      unsat t c = S;
      pool t = insert c (pool s);
      alloc t = alloc s;
      sched t = sched s;
      available t = available s;
      \<And>c'. higherPriorityClients c' t = higherPriorityClients c' s
    \<rbrakk> \<Longrightarrow> P"
  assumes Schedule: "\<And>poolOrder.
    \<lbrakk> pool s \<noteq> {};
      pool t = {};
      set poolOrder = pool s;
      distinct poolOrder;
      sched t = sched s @ poolOrder;
      unsat t = unsat s;
      alloc t = alloc s;
      available t = available s;
      \<And>c'. c' \<in> set (sched s) \<Longrightarrow> higherPriorityClients c' t = higherPriorityClients c' s
    \<rbrakk> \<Longrightarrow> P"
  assumes Allocate: "\<And>c S.
    \<lbrakk> S \<noteq> {};
      S \<subseteq> available s;
      S \<subseteq> unsat s c;
      c \<in> set (sched s);
      \<And>c' r'. c' \<in> higherPriorityClients c s \<Longrightarrow> r' \<in> unsat s c' \<Longrightarrow> r' \<in> S \<Longrightarrow> False;
      sched t = (if S = unsat s c then filter (op \<noteq> c) (sched s) else sched s);
      alloc t = modifyAt (alloc s) c (add S);
      alloc t c = alloc s c \<union> S;
      unsat t = modifyAt (unsat s) c (del S);
      unsat t c = unsat s c - S;
      pool t = pool s;
      available t = available s - S;
      \<And>c'. higherPriorityClients c' t
          = (if S = unsat s c
              then if c' = c
                then set (sched t)
                else higherPriorityClients c' s - {c}
              else higherPriorityClients c' s)
    \<rbrakk> \<Longrightarrow> P"
  assumes Return: "\<And>c S.
    \<lbrakk> S \<noteq> {};
      S \<subseteq> alloc s c;
      alloc t = modifyAt (alloc s) c (del S);
      unsat t = unsat s;
      pool t = pool s;
      sched t = sched s;
      available s \<subseteq> available t;
      \<And>c'. higherPriorityClients c' t = higherPriorityClients c' s
    \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from Next have "((s,t) \<Turnstile> Next) \<or> ((s,t) \<Turnstile> unchanged vars)" by (auto simp add: square_def)
  thus P
  proof (elim disjE)
    assume "(s,t) \<Turnstile> Next"
    then consider
      (Request)    "\<exists> c S. (s,t) \<Turnstile> Request c S"
      | (Schedule)        "(s,t) \<Turnstile> Schedule"
      | (Allocate) "\<exists> c S. (s,t) \<Turnstile> Allocate c S"
      | (Return)   "\<exists> c S. (s,t) \<Turnstile> Return c S"
      unfolding Next_def apply auto by blast
    thus P
    proof cases
      case p: Request with Request show P unfolding Request_def updated_def
        by (auto simp add: add_def available_def higherPriorityClients_def)
    next
      case p: Allocate
      then obtain c S where p: "(s,t) \<Turnstile> Allocate c S" by auto
      from p show P
      proof (intro Allocate)
        from p show "S \<subseteq> available s" "alloc t = modifyAt (alloc s) c (add S)"
          "sched t = (if S = unsat s c then filter (op \<noteq> c) (sched s) else sched s)"
          by (auto simp add: Allocate_def updated_def)
        thus "available t = available s - S"
          unfolding available_def
          apply auto
            apply (metis add_simp modifyAt_eq_simp modifyAt_ne_simp)
           apply (metis add_simp modifyAt_eq_simp)
          by (metis add_simp modifyAt_eq_simp modifyAt_ne_simp)

        have simp2: "\<And>c cs. set (takeWhile (op \<noteq> c) (filter (op \<noteq> c) cs)) = {x \<in> set cs. c \<noteq> x}"
          by (metis filter_set member_filter set_filter takeWhile_eq_all_conv)
        have simp3: "\<And>c c' cs. c' \<noteq> c \<Longrightarrow> set (takeWhile (op \<noteq> c') (filter (op \<noteq> c) cs)) = set (takeWhile (op \<noteq> c') cs) - {c}"
        proof -
          fix c c' cs show "c' \<noteq> c \<Longrightarrow> ?thesis c c' cs" by (induct cs, auto)
        qed

        define cs where "cs \<equiv> sched s"

        show "\<And>c'. higherPriorityClients c' t = (if S = unsat s c then if c' = c then set (sched t) else higherPriorityClients c' s - {c} else higherPriorityClients c' s)"
          unfolding higherPriorityClients_def `sched t = (if S = unsat s c then filter (op \<noteq> c) (sched s) else sched s)`
          by (fold cs_def, induct cs, auto simp add: simp2 simp3)
      qed (auto simp add: Allocate_def updated_def)
    next 
      case p: Schedule

      then obtain poolOrder where "set poolOrder = pool s" "distinct poolOrder" "sched t = sched s @ poolOrder"
        by (auto simp add: Schedule_def)

      with p show P
        apply (intro Schedule [of poolOrder])
        by (auto simp add: Schedule_def available_def higherPriorityClients_def)
    next
      case p: Return 
      then obtain c S where "(s,t) \<Turnstile> Return c S" by auto
      thus P
        apply (intro Return [where S = S and c = c])
               apply (simp_all add: Return_def updated_def higherPriorityClients_def,
            auto simp add: available_def Return_def updated_def)
        by (metis del_simp modifyAt_eq_simp modifyAt_ne_simp)
    qed
  next
    assume "(s,t) \<Turnstile> unchanged vars" with unchanged show P by (auto simp add: vars_def available_def higherPriorityClients_def)
  qed
qed

lemma safety: "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>Safety"
proof invariant
  fix sigma
  assume sigma: "sigma \<Turnstile> SchedulingAllocator"
  thus "sigma \<Turnstile> Init Safety"
    by (auto simp add: Init_def Safety_def SchedulingAllocator_def InitState_def MutualExclusion_def AllocatorInvariant_def)

  show "sigma \<Turnstile> stable Safety"
  proof (intro Stable)
    from sigma show "sigma \<Turnstile> \<box>[Next]_vars"
      by (simp add: SchedulingAllocator_def)

    show "\<turnstile> $Safety \<and> [Next]_vars \<longrightarrow> Safety$"
    proof (intro actionI temp_impI, elim temp_conjE, unfold unl_before unl_after)
      fix s t
      assume Safety: "s \<Turnstile> Safety"
      hence MutualExclusion:    "s \<Turnstile> MutualExclusion"
        and AllocatorInvariant: "s \<Turnstile> AllocatorInvariant"
        by (simp_all add: Safety_def)

      assume "(s,t) \<Turnstile> [Next]_vars"
      thus "t \<Turnstile> Safety"
      proof (cases rule: square_Next_cases)
        case [simp]: unchanged
        from Safety show ?thesis
          by (simp add: Safety_def MutualExclusion_def AllocatorInvariant_def
              higherPriorityClients_def)
      next
        case [simp]: (Request c S)

        from AllocatorInvariant
        show ?thesis
        proof (intro SafetyI)
          from MutualExclusion
          show "\<And>c1 c2. c1 \<noteq> c2 \<Longrightarrow> alloc t c1 \<inter> alloc t c2 = {}"
            by (simp add: MutualExclusion_def)

          fix c1 c2
          assume     "c1 \<in> set (sched t)"         "c2 \<in> higherPriorityClients c1 t"
          hence  c1: "c1 \<in> set (sched s)" and c2: "c2 \<in> higherPriorityClients c1 s"
            by (simp_all add: higherPriorityClients_def)

          from c2 have "c2 : set (sched s)" unfolding higherPriorityClients_def using set_takeWhileD by metis
          with AllocatorInvariant have ne: "c2 \<noteq> c" by (auto simp add: AllocatorInvariant_def)

          from c1 c2 AllocatorInvariant have "alloc s c1 \<inter> unsat s c2 = {}" by (simp add: AllocatorInvariant_def)
          with ne show "alloc t c1 \<inter> unsat t c2 = {}" by simp
        qed (auto simp add: AllocatorInvariant_def add_def modifyAt_def)
      next
        case [simp]: (Schedule poolOrder)

        from AllocatorInvariant
        show ?thesis
        proof (intro SafetyI)
          from MutualExclusion
          show "\<And>c1 c2. c1 \<noteq> c2 \<Longrightarrow> alloc t c1 \<inter> alloc t c2 = {}"
            by (auto simp add: MutualExclusion_def)

          show "\<And>c. c \<in> pool t \<Longrightarrow> unsat t c \<noteq> {}"
            "\<And>c. c \<in> pool t \<Longrightarrow> alloc t c = {}"
            "pool t \<inter> set (sched t) = {}"
            "finite (pool t)"
            by auto

          fix c1 c2
          assume c1: "c1 \<in> set (sched t)"
          assume c2: "c2 \<in> higherPriorityClients c1 t"

          show "alloc t c1 \<inter> unsat t c2 = {}"
          proof (cases "c1 \<in> set (sched s)")
            case True
            with c2 have "c2 \<in> higherPriorityClients c1 s"
              unfolding higherPriorityClients_def by auto
            with True AllocatorInvariant show ?thesis
              by (auto simp add: AllocatorInvariant_def)
          next
            case False
            with c1 have "c1 \<in> pool s" by auto
            with AllocatorInvariant show ?thesis
              by (auto simp add: AllocatorInvariant_def)
          qed
        qed (auto simp add: AllocatorInvariant_def)
      next
        case [simp]: (Allocate c S)

          from AllocatorInvariant
        show ?thesis
        proof (intro SafetyI)
          have "\<And>c'. c' \<noteq> c \<Longrightarrow> alloc t c \<inter> alloc t c' = {}"
          proof -
            fix c' assume ne: "c' \<noteq> c"
            with MutualExclusion `S \<subseteq> available s` show "?thesis c'"
              by (auto simp add: available_def MutualExclusion_def, blast+)
          qed
          with MutualExclusion show "\<And>c1 c2. c1 \<noteq> c2 \<Longrightarrow> alloc t c1 \<inter> alloc t c2 = {}"
            by (auto simp add: MutualExclusion_def modifyAt_def)

          from AllocatorInvariant
          show "\<And>c. finite (unsat t c)" "\<And>c. finite (alloc t c)"
             apply (auto simp add: AllocatorInvariant_def modifyAt_def del_def add_def)
            by (meson `S \<subseteq> unsat s c` infinite_super)

          from AllocatorInvariant have "distinct (sched s)" by (simp add: AllocatorInvariant_def)
          thus "distinct (sched t)" by auto

          show "\<And>c. alloc t c \<inter> unsat t c = {}"
            unfolding Allocate
          proof -
            fix c'
            from AllocatorInvariant have "alloc s c' \<inter> unsat s c' = {}"
              by (auto simp add: AllocatorInvariant_def)
            thus "modifyAt (alloc s) c (add S) c' \<inter> modifyAt (unsat s) c (del S) c' = {}"
              by (cases "c = c'", auto)
          qed

        next
          fix c'
          assume c': "c' \<in> set (sched t)"
          show "unsat t c' \<noteq> {}"
          proof (cases "c' = c")
            case [simp]: True
            from c' have "S \<noteq> unsat s c" by auto
            with `S \<subseteq> unsat s c` show ?thesis
              apply (auto simp add: del_def) using Allocate(3) by auto
          next
            case False
            from c' have "c' \<in> set (sched s)" by (cases "S = unsat s c", auto)
            with AllocatorInvariant False show ?thesis
              unfolding AllocatorInvariant_def by simp
          qed
        next
          fix c'
          assume c': "c' \<notin> pool t" "c' \<notin> set (sched t)"
          show "unsat t c' = {}"
          proof (cases "c' = c")
            case [simp]: True
            from c' `c \<in> set (sched s)` show ?thesis by (cases "S = unsat s c", auto)
          next
            case False
            with c' have "c' \<notin> pool s \<and> c' \<notin> set (sched s)"
              unfolding AllocatorInvariant_def by (cases "S = unsat s c", auto)
            with AllocatorInvariant False show ?thesis
              unfolding AllocatorInvariant_def by simp
          qed
        next
          fix c1 c2
          assume c1: "c1 \<in> set (sched t)" and c2: "c2 \<in> higherPriorityClients c1 t"

          {
            fix r
            assume r1: "r \<in> alloc t c1" and r2t: "r \<in> unsat t c2"
            {
              from AllocatorInvariant
              have "c1 \<in> set (sched s) \<Longrightarrow> c2 \<in> higherPriorityClients c1 s \<Longrightarrow> alloc s c1 \<inter> unsat s c2 = {}"
                unfolding AllocatorInvariant_def by auto
              moreover from c1 have "c1 \<in> set (sched s)" by (cases "S = unsat s c", auto)
              moreover assume "c2 \<in> higherPriorityClients c1 s" "r \<in> alloc s c1"
              moreover from r2t have "r \<in> unsat s c2" by (cases "c2 = c", auto simp add: modifyAt_def)
              ultimately have False by auto
            }
            note hyp = this

            have False
            proof (cases "S = unsat s c")
              case True
              show False
              proof (intro hyp)
                from True c1 have ne1: "c1 \<noteq> c" by auto
                with r1 show "r \<in> alloc s c1" by auto

                define cs where "cs \<equiv> sched s"

                from c2 have "c2 \<in> set (takeWhile (op \<noteq> c1) (filter (op \<noteq> c) (sched s)))"
                  by (auto simp add: higherPriorityClients_def True)
                also have "... \<subseteq> higherPriorityClients c1 s"
                  unfolding higherPriorityClients_def
                  apply (fold cs_def) using ne1 by (induct cs, auto)
                finally show c2: "c2 \<in> ..." .
              qed

            next
              case False
              hence sched_eq[simp]: "sched t = sched s" by simp
              hence higherPriorityClients_eq[simp]: "\<And>c'. higherPriorityClients c' t = higherPriorityClients c' s"
                unfolding higherPriorityClients_def by simp

              from c2 False have hyp: "r \<in> alloc s c1 \<Longrightarrow> False" by (intro hyp, simp)

              show ?thesis
              proof (cases "c1 = c")
                case [simp]: True
                have p1: "alloc t c1 = S \<union> alloc s c" by (auto simp add: add_def)

                from r1 have "r \<in> S \<union> alloc s c" by (auto simp add: add_def)
                thus ?thesis
                proof (elim UnE)
                  assume r: "r \<in> alloc s c"
                  thus ?thesis by (intro hyp, simp)
                next
                  from c2 False have "unsat s c2 \<inter> S = {}" using Allocate(5) by auto
                  moreover note r2t
                  moreover assume "r \<in> S"
                  ultimately show False by (cases "c2 = c", auto simp add: modifyAt_def)                
                qed
              next
                case False
                hence "alloc t c1 = alloc s c1" by simp
                with r1 hyp show False by simp
              qed
            qed
          }
          thus "alloc t c1 \<inter> unsat t c2 = {}" by auto
        qed (auto simp add: AllocatorInvariant_def modifyAt_def)
      next
        case [simp]: (Return c S)

        from AllocatorInvariant
        show ?thesis
        proof (intro SafetyI)
          from MutualExclusion
          show "\<And>c1 c2. c1 \<noteq> c2 \<Longrightarrow> alloc t c1 \<inter> alloc t c2 = {}"
            apply (auto simp add: MutualExclusion_def modifyAt_def)
            by blast+

          from AllocatorInvariant
          show "\<And>c1 c2. c1 \<in> set (sched t) \<Longrightarrow> c2 \<in> higherPriorityClients c1 t \<Longrightarrow> alloc t c1 \<inter> unsat t c2 = {}"
            by (auto simp add: modifyAt_def AllocatorInvariant_def, blast)
        qed (auto simp add: AllocatorInvariant_def modifyAt_def del_def)
      qed
    qed
  qed
qed

lemma WF1_SchedulingAllocator:
  assumes 1: "\<turnstile> SchedulingAllocator \<longrightarrow> WF(A)_v"
  assumes 2: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> s \<Turnstile> Enabled (<A>_v)"
  assumes 3: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> t \<Turnstile> P \<or> Q"
  assumes 4: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> (s,t) \<Turnstile> <A>_v \<Longrightarrow> t \<Turnstile> Q"
  shows      "\<turnstile> SchedulingAllocator \<longrightarrow> (P \<leadsto> Q)"
proof -
  from 1 safety have "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>($Safety \<and> [Next]_vars) \<and> WF(A)_v"
    by (auto simp add: SchedulingAllocator_def more_temp_simps Valid_def)
  also from 2 3 4 have "\<turnstile> \<box>($Safety \<and> [Next]_vars) \<and> WF(A)_v \<longrightarrow> (P \<leadsto> Q)"
    apply (intro WF1 assms) by (auto simp add: Valid_def)
  finally show ?thesis .
qed

lemma WF1_SchedulingAllocator_Schedule:
  assumes 1: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> s \<Turnstile> pool \<noteq> #{}"
  assumes 2: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> s \<Turnstile> finite<pool>"
  assumes 3: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> t \<Turnstile> P \<or> Q"
  assumes 4: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> (s,t) \<Turnstile> <Schedule>_vars \<Longrightarrow> t \<Turnstile> Q"
  shows      "\<turnstile> SchedulingAllocator \<longrightarrow> (P \<leadsto> Q)"
proof (intro WF1_SchedulingAllocator 3 4)
  show "\<turnstile> SchedulingAllocator \<longrightarrow> WF(Schedule)_vars"
    unfolding SchedulingAllocator_def ScheduleFair_def by auto

  fix s t
  assume "s \<Turnstile> P" "s \<Turnstile> Safety" "(s,t) \<Turnstile> [Next]_vars"
  with 1 2 have s: "s \<Turnstile> pool \<noteq> #{}" "s \<Turnstile> finite<pool>" by auto

  then obtain poolOrder
    where po: "distinct poolOrder" "set poolOrder = pool s"
    using finite_distinct_list by auto

  from basevars [OF bv]
  obtain t where t:
    "sched t = sched s @ poolOrder"
    "alloc t = alloc s"
    "unsat t = unsat s"
    "pool  t = {}" by (auto, blast)

  from po s have ne: "vars t \<noteq> vars s" by (auto simp add: vars_def t)

  from s t ne po show "s \<Turnstile> Enabled (<Schedule>_vars)" unfolding enabled_def angle_def Schedule_def by auto
qed

lemma WF1_SchedulingAllocator_Allocate:
  assumes 1: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> s \<Turnstile> available \<inter> id<unsat,hd<sched>> \<noteq> #{}"
  assumes 2: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> s \<Turnstile> sched \<noteq> #[]"
  assumes 3: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> t \<Turnstile> P \<or> Q"
  assumes 4: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> (s,t) \<Turnstile> <\<exists>S c. #c = hd<$sched> \<and> Allocate c S>_vars \<Longrightarrow> t \<Turnstile> Q"
  shows      "\<turnstile> SchedulingAllocator \<longrightarrow> (P \<leadsto> Q)"
proof (intro WF1_SchedulingAllocator 3 4)
  show "\<turnstile> SchedulingAllocator \<longrightarrow> WF(\<exists>S c. #c = hd<$sched> \<and> Allocate c S)_vars"
    unfolding SchedulingAllocator_def AllocateHeadFair_def by auto

  fix s t
  assume "s \<Turnstile> P" "s \<Turnstile> Safety" "(s,t) \<Turnstile> [Next]_vars"
  with 1 2 have s: "s \<Turnstile> available \<inter> id<unsat,hd<sched>> \<noteq> #{}" "s \<Turnstile> sched \<noteq> #[]" by auto

  define c where "c \<equiv> hd (sched s)"
  define S where "S \<equiv> available s \<inter> unsat s c"
  from s have S_nonempty: "S \<noteq> {}" unfolding S_def c_def by simp
  from s have c_mem: "c \<in> set (sched s)" unfolding c_def by (cases "sched s", simp_all)
  have hpc_empty: "higherPriorityClients c s = {}" unfolding higherPriorityClients_def c_def by (cases "sched s", simp_all)

  from basevars [OF bv]
  obtain t where t:
    "sched t = (if S = unsat s c then filter (op \<noteq> c) (sched s) else sched s)"
    "alloc t = modifyAt (alloc s) c (add S)"
    "unsat t = modifyAt (unsat s) c (del S)"
    "pool  t = pool s" by (auto, blast)

  have vars_ne: "vars t \<noteq> vars s"
    unfolding vars_def apply simp unfolding t
    by (metis Diff_disjoint S_def S_nonempty del_def inf.absorb_iff1 inf_le2 modifyAt_eq_simp)

  show "s \<Turnstile> Enabled (<\<exists>S c. #c = hd<$sched> \<and> Allocate c S>_vars)"
    unfolding angle_def enabled_def Allocate_def updated_def
    apply clarsimp
    apply (fold c_def)
    apply (intro exI [where x = t] conjI exI [where x = S])
    using S_nonempty c_mem hpc_empty vars_ne
      apply (unfold S_def t) by auto
qed

lemma WF1_SchedulingAllocator_Return:
  assumes 1: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> s \<Turnstile> id<alloc,#c> \<noteq> #{}"
  assumes 2: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> s \<Turnstile> id<unsat,#c> = #{}"
  assumes 3: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> t \<Turnstile> P \<or> Q"
  assumes 4: "\<And>s t. s \<Turnstile> P \<Longrightarrow> s \<Turnstile> Safety \<Longrightarrow> (s,t) \<Turnstile> [Next]_vars \<Longrightarrow> (s,t) \<Turnstile> <\<exists>S. id<$unsat,#c> = #{} \<and> id<$alloc,#c> = #S \<and> Return c S>_vars \<Longrightarrow> t \<Turnstile> Q"
  shows      "\<turnstile> SchedulingAllocator \<longrightarrow> (P \<leadsto> Q)"
proof (intro WF1_SchedulingAllocator 3 4)
  show "\<turnstile> SchedulingAllocator \<longrightarrow> WF(\<exists>S. id<$unsat,#c> = #{} \<and> id<$alloc,#c> = #S \<and> Return c S)_vars"
    unfolding SchedulingAllocator_def ReturnFair_def by auto

  fix s t
  assume "s \<Turnstile> P" "s \<Turnstile> Safety" "(s,t) \<Turnstile> [Next]_vars"
  with 1 2 have s: "s \<Turnstile> id<alloc,#c> \<noteq> #{}" "s \<Turnstile> id<unsat,#c> = #{}" by auto

  from basevars [OF bv]
  obtain t where t:
    "sched t = sched s"
    "alloc t = modifyAt (alloc s) c (del (alloc s c))"
    "unsat t = unsat s"
    "pool  t = pool s" by (auto, blast)

  from s have vars_ne: "vars t \<noteq> vars s"
    unfolding vars_def apply simp unfolding t apply auto by (metis del_simp modifyAt_eq_simp)

  from s t vars_ne
  show "s \<Turnstile> Enabled (<\<exists>S. id<$unsat,#c> = #{} \<and> id<$alloc,#c> = #S \<and> Return c S>_vars)"
    unfolding angle_def enabled_def Return_def updated_def by auto
qed

lemma unsatisfied_leadsto_scheduled:
  "\<turnstile> SchedulingAllocator \<longrightarrow> (id<unsat, #c> \<noteq> #{} \<leadsto> #c \<in> set<sched>)"
proof (rule imp_leadsto_diamond [OF imp_imp_leadsto imp_imp_leadsto])
  show "\<turnstile> id<unsat, #c> \<noteq> #{} \<longrightarrow> #c \<in> set<sched> \<or> (id<unsat, #c> \<noteq> #{} \<and> #c \<notin> set<sched>)"
    by auto
  show "\<turnstile> #c \<in> set<sched> \<longrightarrow> #c \<in> set<sched>" by simp

  show "\<turnstile> SchedulingAllocator \<longrightarrow> (id<unsat, #c> \<noteq> #{} \<and> #c \<notin> set<sched> \<leadsto> #c \<in> set<sched>)"
  proof (intro WF1_SchedulingAllocator_Schedule)
    fix s t
    assume Safety: "s \<Turnstile> Safety" and Next: "(s,t) \<Turnstile> [Next]_vars"
    assume "s \<Turnstile> id<unsat, #c> \<noteq> #{} \<and> #c \<notin> set<sched>"
    hence s: "unsat s c \<noteq> {}" "c \<notin> set (sched s)" by auto

    from s Safety show "s \<Turnstile> pool \<noteq> #{}" "s \<Turnstile> finite<pool>" by (auto simp add: Safety_def AllocatorInvariant_def)

    from s Safety show "(s, t) \<Turnstile> <Schedule>_vars \<Longrightarrow> t \<Turnstile> #c \<in> set<sched>"
      by (simp, auto simp add: Schedule_def Safety_def AllocatorInvariant_def angle_def)

    from Next have "unsat t c \<noteq> {}"
    proof (cases rule: square_Next_cases)
      case unchanged with s show ?thesis by simp
    next
      case (Request c' S') with s have "c' \<noteq> c" by auto with Request s show ?thesis by auto
    next
      case (Schedule poolOrder) with s show ?thesis by simp
    next
      case (Allocate c' S') with s have "c' \<noteq> c" by auto with Allocate s show ?thesis by auto
    next
      case (Return c' S') with s show ?thesis by simp
    qed
    thus "t \<Turnstile> id<unsat, #c> \<noteq> #{} \<and> #c \<notin> set<sched> \<or> #c \<in> set<sched>" by auto
  qed
qed

end

record Inductor =
  higherSched :: "Client set"
  hd_unsats   :: "Resource set"
  hd_blockers :: "Client set"

definition prec_Inductor_rel :: "(Inductor \<times> Inductor) set"
  where "prec_Inductor_rel \<equiv> inv_image
              (finite_psubset <*lex*> finite_psubset <*lex*> finite_psubset)
              (\<lambda>i. (higherSched i, hd_unsats i, hd_blockers i))"

definition prec_Inductor :: "Inductor \<Rightarrow> Inductor \<Rightarrow> bool" (infix "\<prec>" 50)
  where "i1 \<prec> i2 \<equiv> (i1,i2) \<in> prec_Inductor_rel"

definition prec_eq_Inductor :: "Inductor \<Rightarrow> Inductor \<Rightarrow> bool" (infix "\<preceq>" 50)
  where "i1 \<preceq> i2 \<equiv> i1 = i2 \<or> i1 \<prec> i2"

lemma inductor_prec_simp: "((i1, i2) \<in> {(i1, i2). i1 \<prec> i2}) = (i1 \<prec> i2)" by auto

lemma wf_prec_Inductor: "wf {(i1 :: Inductor, i2 :: Inductor). i1 \<prec> i2}"
proof -
  have "wf prec_Inductor_rel"
    unfolding prec_Inductor_rel_def by (intro wf_inv_image wf_lex_prod wf_finite_psubset)
  thus ?thesis by (simp add: prec_Inductor_def)
qed

context SchedulingAllocator
begin

definition inductor :: "Client \<Rightarrow> Inductor stfun"
  where "inductor c s \<equiv> \<lparr> higherSched = higherPriorityClients c s
                         , hd_unsats   = unsat s (hd (sched s))
                         , hd_blockers = { c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {} }
                         \<rparr>"

lemma higherSched_inductor[simp]: "higherSched (inductor c s) = higherPriorityClients c s"
  and hd_unsats_inductor[simp]:   "hd_unsats   (inductor c s) = unsat s (hd (sched s))"
  and hd_blockers_inductor[simp]: "hd_blockers (inductor c s) = { c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {} }"
  by (simp_all add: inductor_def)

lemma inductor_prec_eq:
  assumes "s \<Turnstile> Safety"
  shows "(inductor c t \<prec> inductor c s)
    = (   higherPriorityClients c t \<subset> higherPriorityClients c s
       \<or> (higherPriorityClients c t = higherPriorityClients c s
          \<and> unsat t (hd (sched t)) \<subset> unsat s (hd (sched s)))
       \<or> (higherPriorityClients c t = higherPriorityClients c s
          \<and> unsat t (hd (sched t)) = unsat s (hd (sched s))
          \<and> { c'. alloc t c' \<inter> unsat t (hd (sched t)) \<noteq> {} } \<subset> { c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {} }))"
  (is "?LHS = ?RHS")
proof (intro iffI)
  assume "?LHS" thus "?RHS" by (auto simp add: inductor_def prec_Inductor_def prec_Inductor_rel_def)
next
  assume rhs: "?RHS"
  have "finite (higherPriorityClients c s)" unfolding higherPriorityClients_def by auto
  moreover from assms have "finite (unsat s (hd (sched s)))" unfolding Safety_def AllocatorInvariant_def by auto
  moreover from assms
  have 1: "{c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {}} = (\<Union> r \<in> unsat s (hd (sched s)). {c'. r \<in> alloc s c'})" by auto

  from assms
  have "\<And>r. {c'. r \<in> alloc s c'} \<subseteq> {THE c'. r \<in> alloc s c'}"
    by (intro subsetI, elim CollectE, simp, intro sym [OF the_equality], auto simp add: Safety_def MutualExclusion_def)
  hence "\<And>r. finite {c'. r \<in> alloc s c'}" by (meson finite.emptyI finite_insert infinite_super)
  hence "finite {c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {}}"
    unfolding 1 using assms
    by (intro finite_UN_I, auto simp add: Safety_def AllocatorInvariant_def)

  ultimately show "?LHS" using rhs
    by (auto simp add: inductor_def prec_Inductor_def prec_Inductor_rel_def)
qed

lemma
  assumes Safety_s: "s \<Turnstile> Safety"
    and Next: "(s,t) \<Turnstile> [Next]_vars"
    and scheduled: "c \<in> set (sched s)"
  shows scheduled_progress: "(s,t) \<Turnstile> (op \<preceq>)<(inductor c)$,$(inductor c)> \<or> #c \<notin> set<sched$>"
proof -
  note inductor_precI = iffD2 [OF inductor_prec_eq [OF Safety_s]]

  from Next show ?thesis
  proof (cases rule: square_Next_cases)
    case unchanged
    hence "inductor c t = inductor c s" by (simp add: inductor_def)
    thus ?thesis by (simp add: prec_eq_Inductor_def)
  next
    case [simp]: (Request c' S')
    with Safety_s have "c' \<notin> set (sched s)" by (auto simp add: Safety_def AllocatorInvariant_def)
    moreover from scheduled have "hd (sched s) \<in> set (sched s)" by (cases "sched s", auto)
    ultimately have "c' \<noteq> hd (sched s)" by auto
    hence "inductor c t = inductor c s" unfolding inductor_def by simp
    thus ?thesis by (simp add: prec_eq_Inductor_def)
  next
    case [simp]: (Schedule poolOrder)
    from scheduled have "hd (sched s @ poolOrder) = hd (sched s)"
      "higherPriorityClients c t = higherPriorityClients c s" by (cases "sched s", auto)
    hence "inductor c t = inductor c s" by (simp add: inductor_def)
    thus ?thesis by (simp add: prec_eq_Inductor_def)
  next
    case (Allocate c' S')

    note inductor_precI = iffD2 [OF inductor_prec_eq [OF Safety_s]]

    show ?thesis
    proof (cases "S' = unsat s c'")
      case fully_satisfied: True
      show ?thesis
      proof (cases "c' = c")
        case True with fully_satisfied show ?thesis by (auto simp add: Allocate)
      next
        case c'_ne_c: False
        show ?thesis
        proof (cases "c' \<in> higherPriorityClients c s")
          case True
          with c'_ne_c fully_satisfied
          have "inductor c t \<prec> inductor c s"
            by (intro inductor_precI disjI1, unfold Allocate, auto)
          thus ?thesis by (simp add: prec_eq_Inductor_def)
        next
          case False

          have hpc_eq[simp]: "higherPriorityClients c t = higherPriorityClients c s"
            using False c'_ne_c scheduled
            unfolding Allocate by auto

          have c'_ne_hd[simp]: "(c' = hd (sched s)) = False"
            using False c'_ne_c scheduled unfolding higherPriorityClients_def
            by (cases "sched s", auto)

          have hd_eq[simp]: "hd (sched t) = hd (sched s)"
            unfolding Allocate fully_satisfied using c'_ne_hd by (cases "sched s", auto)

          have unsat_hd_eq[simp]: "unsat t (hd (sched s)) = unsat s (hd (sched s))"
            unfolding Allocate using c'_ne_hd modifyAt_ne_simp by metis

          have blocker_eq[simp]: "{c'. alloc t c' \<inter> unsat s (hd (sched s)) \<noteq> {}} = {c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {}}"
            (is "?LHS = ?RHS")
          proof (intro equalityI subsetI)
            fix c'' assume "c'' \<in> ?RHS" thus "c'' \<in> ?LHS" unfolding Allocate modifyAt_def by auto
          next
            fix c''
            assume c'': "c'' \<in> ?LHS"
            show "c'' \<in> ?RHS"
            proof (cases "c'' = c'")
              case False with c'' show ?thesis unfolding Allocate by auto
            next
              case True

              from c'_ne_hd scheduled
              have hd_hpc: "hd (sched s) \<in> higherPriorityClients c' s"
                unfolding higherPriorityClients_def by (cases "sched s", auto)

              from hd_hpc Safety_s Allocate have "alloc s c' \<inter> unsat s (hd (sched s)) = {}" 
                unfolding Safety_def AllocatorInvariant_def by auto

              moreover from hd_hpc Allocate have "S' \<inter> unsat s (hd (sched s)) = {}" by auto

              ultimately show ?thesis
                using True c'' unfolding Allocate by auto
            qed
          qed

          have "inductor c t = inductor c s" by (simp add: inductor_def)
          thus ?thesis by (simp add: prec_eq_Inductor_def)
        qed
      qed
    next
      case not_fully_satisfied: False

      from not_fully_satisfied
      have hpc_eq: "sched t = sched s" "\<And>c''. higherPriorityClients c'' t = higherPriorityClients c'' s"
        by (simp_all add: Allocate)

      have blockers_eq: "{ c'. alloc t c' \<inter> unsat t (hd (sched t)) \<noteq> {} } = { c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {} }"
        (is "?LHS = ?RHS")
      proof (intro equalityI subsetI)
        fix c'' assume "c'' \<in> ?LHS"
        then obtain r where r: "r \<in> alloc t c''" "r \<in> unsat t (hd (sched t))" by auto

        from r have r_unsat: "r \<in> unsat s (hd (sched s))" unfolding hpc_eq Allocate by (cases "hd (sched s) = c'", auto)

        moreover have "r \<in> alloc s c''"
        proof (cases "r \<in> S'")
          case False with r show ?thesis unfolding Allocate by (cases "c' = c''", auto)
        next
          case True
          have False
          proof (intro Allocate)
            from True show "r \<in> S'".
            from r_unsat show "r \<in> unsat s (hd (sched s))".
            from True r not_fully_satisfied have c'_ne_hd: "c' \<noteq> hd (sched s)" unfolding Allocate by auto
            thus "hd (sched s) \<in> higherPriorityClients c' s"
              using scheduled unfolding higherPriorityClients_def by (cases "sched s", auto)
          qed
          thus ?thesis by simp
        qed

        ultimately show "c'' \<in> ?RHS" by auto
      next
        fix c'' assume "c'' \<in> ?RHS"
        then obtain r where r: "r \<in> alloc s c''" "r \<in> unsat s (hd (sched s))" by auto
        from r Allocate have "r \<notin> S'" unfolding available_def by auto
        with r have "r \<in> alloc t c'' \<inter> unsat t (hd (sched t))"
          unfolding hpc_eq Allocate by (auto simp add: modifyAt_def)
        thus "c'' \<in> ?LHS" by auto
      qed

      have unsats_subset: "unsat t (hd (sched s)) \<subseteq> unsat s (hd (sched s))"
        unfolding Allocate modifyAt_def by auto
      thus ?thesis
      proof (unfold subset_iff_psubset_eq, elim disjE)
        assume "unsat t (hd (sched s)) \<subset> unsat s (hd (sched s))"
        with hpc_eq blockers_eq have "inductor c t \<prec> inductor c s" by (intro inductor_precI, auto)
        thus ?thesis by (simp add: prec_eq_Inductor_def)
      next
        assume "unsat t (hd (sched s)) = unsat s (hd (sched s))"
        with hpc_eq blockers_eq have "inductor c t = inductor c s" by (simp add: inductor_def)
        thus ?thesis by (simp add: prec_eq_Inductor_def)
      qed
    qed
  next
    case (Return c' S')

    have blockers_subset: "{ c'. alloc t c' \<inter> unsat t (hd (sched t)) \<noteq> {} } \<subseteq> { c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {} }"
      (is "?LHS \<subseteq> ?RHS") by (auto simp add: Return modifyAt_def)
    thus ?thesis
    proof (unfold subset_iff_psubset_eq, elim disjE)
      assume "?LHS = ?RHS" with Return have "inductor c t = inductor c s" by (simp add: inductor_def)
      thus ?thesis by (simp add: prec_eq_Inductor_def)
    next
      assume "?LHS \<subset> ?RHS" with Return have "inductor c t \<prec> inductor c s" by (intro inductor_precI, auto)
      thus ?thesis by (simp add: prec_eq_Inductor_def)
    qed
  qed
qed

lemma infinitely_often_unscheduled: "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>\<diamond>(#c \<notin> set<sched>)"
proof -
  have "\<turnstile> SchedulingAllocator \<longrightarrow> ((#True :: stpred) \<leadsto> (#c \<notin> set<sched>))"
  proof (rule imp_leadsto_diamond)
    show "\<turnstile> SchedulingAllocator \<longrightarrow> ((#True :: stpred) \<leadsto> #c \<notin> set<sched> \<or> #c \<in> set<sched>)"
      "\<turnstile> SchedulingAllocator \<longrightarrow> (#c \<notin> set<sched> \<leadsto> #c \<notin> set<sched>)"
      by (intro imp_imp_leadsto, simp)+

    have inductor_lt_simp: "\<And>i1 i2. ((i1, i2) \<in> {(i1, i2). i1 < i2}) = (i1 < i2)" by auto

    have "\<turnstile> SchedulingAllocator \<longrightarrow> (#c \<in> set<sched> \<leadsto> (\<exists>i. #i = inductor c \<and> #c \<in> set<sched>))"
      by (intro imp_imp_leadsto, auto)
    also have "\<turnstile> SchedulingAllocator \<longrightarrow> ((\<exists>i. #i = inductor c \<and> #c \<in> set<sched>) \<leadsto> #c \<notin> set<sched>)"
    proof (intro wf_imp_ex_leadsto [OF wf_prec_Inductor], rule imp_leadsto_diamond, unfold inductor_prec_simp)
      fix i
      show "\<turnstile> SchedulingAllocator
              \<longrightarrow> (#i = inductor c \<and> #c \<in> set<sched>
                \<leadsto> (#i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat,hd<sched>> \<inter> available = #{})
                  \<or> (#i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat,hd<sched>> \<inter> available \<noteq> #{}))"
        by (intro imp_imp_leadsto, auto)

      have "\<turnstile> SchedulingAllocator
            \<longrightarrow> (#i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available = #{}
              \<leadsto> (Safety \<and> #i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available = #{}))"
        by (intro imp_INV_leadsto [OF safety imp_imp_leadsto], auto)
      also have "\<turnstile> SchedulingAllocator
            \<longrightarrow> (Safety \<and> #i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available = #{}
              \<leadsto> (\<exists> blocker. #i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> id<alloc,#blocker> \<noteq> #{}))"
      proof (intro imp_imp_leadsto intI temp_impI, clarsimp)
        fix s
        assume s_Safety: "s \<Turnstile> Safety" and scheduled: "c \<in> set (sched s)" and blocked: "unsat s (hd (sched s)) \<inter> available s = {}"
        from scheduled have "hd (sched s) \<in> set (sched s)" by (cases "sched s", auto)
        with s_Safety have "unsat s (hd (sched s)) \<noteq> {}" by (auto simp add: Safety_def AllocatorInvariant_def)
        with blocked show "\<exists>blocker. unsat s (hd (sched s)) \<inter> alloc s blocker \<noteq> {}" by (auto simp add: available_def)
      qed
      also have "\<turnstile> SchedulingAllocator
            \<longrightarrow> ((\<exists> blocker. #i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> id<alloc,#blocker> \<noteq> #{})
              \<leadsto> #c \<notin> set<sched> \<or> (\<exists>i'. #(i' \<prec> i) \<and> #i' = inductor c \<and> #c \<in> set<sched>))"
      proof (intro imp_exists_leadstoI WF1_SchedulingAllocator_Return)
        fix blocker s t
        assume "s \<Turnstile> #i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> id<alloc, #blocker> \<noteq> #{}"
        hence s: "i = inductor c s" "c \<in> set (sched s)" "unsat s (hd (sched s)) \<inter> alloc s blocker \<noteq> {}"
          by simp_all

        thus "s \<Turnstile> id<alloc, #blocker> \<noteq> #{}" by auto

        assume s_Safety: "s \<Turnstile> Safety"
        assume Next: "(s,t) \<Turnstile> [Next]_vars"

        have blocker_unscheduled: "blocker \<notin> set (sched s)"
        proof (intro notI)
          assume blocker_scheduled: "blocker \<in> set (sched s)"
          show False
          proof (cases "blocker = hd (sched s)")
            case True
            with s s_Safety show False unfolding Safety_def AllocatorInvariant_def by (simp, blast)
          next
            case False
            with s have "hd (sched s) \<in> higherPriorityClients blocker s"
              unfolding higherPriorityClients_def by (cases "sched s", auto)
            with s blocker_scheduled s_Safety show False unfolding Safety_def AllocatorInvariant_def by (simp, blast)
          qed
        qed

        from s_Safety s
        have blocker_unpooled: "blocker \<notin> pool s"
          unfolding Safety_def AllocatorInvariant_def by auto

        from s_Safety blocker_unscheduled blocker_unpooled have blocker_satisfied: "unsat s blocker = {}"
          unfolding Safety_def AllocatorInvariant_def by auto
        thus "s \<Turnstile> id<unsat, #blocker> = #{}" by simp

        have "(s, t) \<Turnstile> (op \<preceq>)<inductor c$,$inductor c> \<or> #c \<notin> set<sched$>"
          by (intro scheduled_progress s_Safety Next s)
        with s_Safety consider
          (alloc) "c \<notin> set (sched t)"
          | (progress) "c \<in> set (sched t)" "inductor c t \<prec> inductor c s"
          | (same) "c \<in> set (sched t)" "inductor c t = inductor c s"
            "{c'. alloc t c' \<inter> unsat t (hd (sched t)) \<noteq> {}} = {c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {}}"
          by (cases "c \<in> set (sched t)", auto simp add: prec_eq_Inductor_def inductor_def)
        note progress_cases = this

        from progress_cases
        show "t \<Turnstile> #i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> id<alloc, #blocker> \<noteq> #{} \<or> #c \<notin> set<sched> \<or> (\<exists>i'. #(i' \<prec> i) \<and> #i' = inductor c \<and> #c \<in> set<sched>)"
        proof cases
          case alloc thus ?thesis by simp
        next
          case progress thus ?thesis by (auto simp add: s)
        next
          case same

          from Next have "unsat t (hd (sched t)) \<inter> alloc t blocker \<noteq> {}"
          proof (cases rule: square_Next_cases)
            case unchanged with s show ?thesis by simp
          next
            case (Request c' S')
            with s have "hd (sched s) \<noteq> c'" by auto
            with Request s show ?thesis by auto
          next
            case (Schedule poolOrder)
            from s have "hd (sched t) = hd (sched s)" by (cases "sched s", auto simp add: Schedule)
            with s show ?thesis by (simp add: Schedule)
          next
            case (Allocate c' S')
            from Allocate blocker_satisfied have blocker_ne: "blocker \<noteq> c'" by auto
            show ?thesis
            proof (cases "c' = hd (sched s)")
              case True
              with Allocate s have "S' \<noteq> unsat s c'" by (auto simp add: available_def)
              with blocker_ne True Allocate have "unsat t (hd (sched t)) \<inter> alloc t blocker = unsat s (hd (sched s)) \<inter> alloc s blocker"
                by (auto simp add: True del_def available_def)
              with s show ?thesis by simp
            next
              case False
              moreover from False s have "hd (sched t) = hd (sched s)" by (cases "sched s", auto simp add: Allocate)
              moreover from blocker_ne have alloc_blocker_eq: "alloc t blocker = alloc s blocker" by (simp add: Allocate)
              moreover note s
              ultimately show ?thesis by (simp add: Allocate)
            qed
          next
            case (Return c' S')
            with same s show ?thesis by auto
          qed

          with same s show ?thesis by auto
        qed

        assume "(s, t) \<Turnstile> <\<exists>S. id<$unsat, #blocker> = #{} \<and> id<$alloc, #blocker> = #S \<and> Return blocker S>_vars"
        hence  alloc_t_blocker_eq: "alloc t blocker = {}"
          by (auto simp add: Return_def angle_def vars_def updated_def)

        from progress_cases
        show "t \<Turnstile> #c \<notin> set<sched> \<or> (\<exists>i'. #(i' \<prec> i) \<and> #i' = inductor c \<and> #c \<in> set<sched>)"
        proof cases
          case alloc thus ?thesis by simp
        next
          case progress thus ?thesis by (auto simp add: s)
        next
          case same with s alloc_t_blocker_eq show ?thesis by auto
        qed
      qed
      finally show "\<turnstile> SchedulingAllocator \<longrightarrow> (#i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available = #{} \<leadsto> #c \<notin> set<sched> \<or> (\<exists>i'. #(i' \<prec> i) \<and> #i' = inductor c \<and> #c \<in> set<sched>)) ".

      have "\<turnstile> SchedulingAllocator \<longrightarrow> (#i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{} \<leadsto> (\<exists> topPriority. #i = inductor c \<and> #topPriority = hd<sched> \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{}))"
        by (intro imp_imp_leadsto, auto)
      also have "\<turnstile> SchedulingAllocator \<longrightarrow> ((\<exists> topPriority. #i = inductor c \<and> #topPriority = hd<sched> \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{}) 
                        \<leadsto> #c \<notin> set<sched> \<or> (\<exists>y. #(y \<prec> i) \<and> #y = inductor c \<and> #c \<in> set<sched>))"
      proof (intro imp_exists_leadstoI WF1_SchedulingAllocator_Allocate)
        fix s t
        assume s_Safety: "Safety s" and Next: "(s,t) \<Turnstile> [Next]_vars"

        fix topPriority
        assume "s \<Turnstile> #i = inductor c \<and> #topPriority = hd<sched> \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{}"
        hence s: "i = inductor c s" "topPriority = hd (sched s)" "c \<in> set (sched s)" "unsat s (hd (sched s)) \<inter> available s \<noteq> {}" by auto
        from s have hpc_topPriority: "higherPriorityClients topPriority s = {}" unfolding higherPriorityClients_def by (cases "sched s", auto)

        from s show "s \<Turnstile> available \<inter> id<unsat, hd<sched>> \<noteq> #{}" "s \<Turnstile> sched \<noteq> #[]" by auto

        have "(s, t) \<Turnstile> (op \<preceq>)<inductor c$,$inductor c> \<or> #c \<notin> set<sched$>"
          by (intro scheduled_progress s_Safety Next s)
        with s_Safety consider
          (alloc) "c \<notin> set (sched t)"
          | (progress) "c \<in> set (sched t)" "inductor c t \<prec> inductor c s"
          | (same) "c \<in> set (sched t)" "inductor c t = inductor c s"
            "higherPriorityClients c t = higherPriorityClients c s"
            "{c'. alloc t c' \<inter> unsat t (hd (sched t)) \<noteq> {}} = {c'. alloc s c' \<inter> unsat s (hd (sched s)) \<noteq> {}}"
            "unsat t (hd (sched t)) = unsat s (hd (sched s))"
          by (cases "c \<in> set (sched t)", auto simp add: prec_eq_Inductor_def inductor_def)
        note progress_cases = this

        from progress_cases
        show "t \<Turnstile> #i = inductor c \<and> #topPriority = hd<sched> \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{} \<or> #c \<notin> set<sched> \<or> (\<exists>y. #(y \<prec> i) \<and> #y = inductor c \<and> #c \<in> set<sched>)"
        proof cases
          case alloc then show ?thesis by auto
        next
          case progress with s show ?thesis by auto
        next
          case same
          from Next show ?thesis
          proof (cases rule: square_Next_cases)
            case unchanged with s same show ?thesis by (auto simp add: available_def)
          next
            case (Request c' S')
            with s have c'_ne_hd: "c' \<noteq> hd (sched s)" by auto
            with s Request same show ?thesis by auto
          next
            case (Schedule poolOrder) with s same show ?thesis by (cases "sched s", auto)
          next
            case (Return c' S') with s same show ?thesis by auto
          next
            case (Allocate c' S')
            from s have hd_scheduled: "hd (sched s) \<in> set (sched s)" by (cases "sched s", auto)
            show ?thesis
            proof (cases "c' = hd (sched s)")
              case False
              with hd_scheduled have hd_eq: "hd (sched t) = hd (sched s)"
                unfolding Allocate by (cases "S' = unsat s c'", auto, cases "sched s", auto)
              have unsat_hd_eq: "unsat t (hd (sched s)) = unsat s (hd (sched s))"
                unfolding Allocate using False by auto
              from False have hd_hpc: "hd (sched s) \<in> higherPriorityClients c' s"
                unfolding higherPriorityClients_def using hd_scheduled by (cases "sched s", auto)

              have unavailable_eq: "unsat s (hd (sched s)) \<inter> available t = unsat s (hd (sched s)) \<inter> available s"
                using hd_hpc Allocate by auto

              from s show ?thesis by (auto simp add: hd_eq unsat_hd_eq unavailable_eq same)
            next
              case c'_hd[simp]: True
              show ?thesis
              proof (cases "S' = unsat s c'")
                case False with s same Allocate show ?thesis by auto
              next
                case True
                moreover from True same have "c \<noteq> hd (sched s)" unfolding Allocate by auto
                moreover from same have "higherPriorityClients c t = higherPriorityClients c s" by simp
                ultimately have False unfolding higherPriorityClients_def Allocate
                  using s apply (cases "sched s") apply auto using set_takeWhileD by fastforce
                thus ?thesis by simp
              qed
            qed
          qed
        qed

        assume "(s,t) \<Turnstile> <\<exists>S ct. #ct = hd<$sched> \<and> Allocate ct S>_vars"
        hence assm_Allocate: "(s,t) \<Turnstile> \<exists>S. <Allocate topPriority S>_vars" using s by (auto simp add: angle_def)

        from progress_cases
        show "t \<Turnstile> #c \<notin> set<sched> \<or> (\<exists>y. #(y \<prec> i) \<and> #y = inductor c \<and> #c \<in> set<sched>)"
        proof cases
          case alloc then show ?thesis by auto
        next
          case progress with s show ?thesis by auto
        next
          case same
          from Next show ?thesis
          proof (cases rule: square_Next_cases)
            case unchanged with assm_Allocate show ?thesis by (simp add: angle_def vars_def)
          next
            case (Request c' S') with assm_Allocate show ?thesis apply (auto simp add: angle_def Allocate_def updated_def)
              by (metis Int_emptyI Request(6) equals0D modifyAt_ne_simp s(2) s(4))
          next
            case (Schedule poolOrder) with assm_Allocate show ?thesis by (auto simp add: angle_def Allocate_def updated_def)
          next
            case (Return c' S') with assm_Allocate show ?thesis apply (auto simp add: angle_def Allocate_def updated_def)
              by (metis del_simp modifyAt_eq_simp subset_iff)
          next
            case (Allocate c' S')
            with assm_Allocate have c'_eq: "c' = topPriority" apply (auto simp add: angle_def Allocate_def updated_def)
              using Allocate(10) by auto
            have unsat_eq: "unsat s c' = unsat t c'"
            proof (cases "S' = unsat s c'")
              case False
              with same show ?thesis unfolding c'_eq s Allocate by simp
            next
              case True
              with `c \<in> set (sched t)` have ne: "c \<noteq> c'" unfolding Allocate by auto
              have "c' \<in> higherPriorityClients c s" 
                using ne s unfolding higherPriorityClients_def c'_eq s by (cases "sched s", simp_all)
              also from same have "... = higherPriorityClients c t" by simp
              also have "... \<subseteq> set (sched t)" unfolding higherPriorityClients_def using set_takeWhileD by fastforce
              finally have False unfolding Allocate True by auto
              thus ?thesis by simp
            qed
            from Allocate have "unsat s c' \<noteq> unsat t c'" by auto
            with unsat_eq show ?thesis by simp
          qed
        qed
      qed
      finally
      show "\<turnstile> SchedulingAllocator \<longrightarrow> (#i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{} \<leadsto> #c \<notin> set<sched> \<or> (\<exists>y. #(y \<prec> i) \<and> #y = inductor c \<and> #c \<in> set<sched>))" .
    qed
    finally show "\<turnstile> SchedulingAllocator \<longrightarrow> (#c \<in> set<sched> \<leadsto> #c \<notin> set<sched>) ".
  qed
  thus ?thesis by (simp add: leadsto_def)
qed

lemma infinitely_often_freed: "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>\<diamond>(id<alloc,#c> = #{})"
proof -
  from infinitely_often_unscheduled
  have "\<turnstile> SchedulingAllocator \<longrightarrow> ((#True :: stpred) \<leadsto> #c \<notin> set<sched>)"
    by (simp add: leadsto_def)

  also have "\<turnstile> SchedulingAllocator \<longrightarrow> (#c \<notin> set<sched> \<leadsto> id<alloc,#c> = #{})"
  proof (rule imp_leadsto_triangle_excl [OF imp_leadsto_reflexive])
    have "\<turnstile> SchedulingAllocator \<longrightarrow> (#c \<notin> set<sched> \<and> id<alloc, #c> \<noteq> #{} \<leadsto> (\<exists>S. #S \<noteq> #{} \<and> id<unsat,#c> = #{} \<and> id<alloc, #c> = #S))"
    proof (rule imp_INV_leadsto [OF safety imp_imp_leadsto], intro intI, clarsimp)
      fix w
      assume w: "c \<notin> set (sched w)" "alloc w c \<noteq> {}" "Safety w"
      hence "c \<notin> pool w" by (auto simp add: Safety_def AllocatorInvariant_def)
      with w show "unsat w c = {}" by (auto simp add: Safety_def AllocatorInvariant_def)
    qed
    also have "\<turnstile> SchedulingAllocator \<longrightarrow> ((\<exists>S. #S \<noteq> #{} \<and> id<unsat,#c> = #{} \<and> id<alloc, #c> = #S) \<leadsto> id<alloc, #c> = #{})"
    proof (intro wf_imp_ex_leadsto [OF wf_finite_psubset WF1_SchedulingAllocator_Return])
      fix S s t
      assume s: "s \<Turnstile> #S \<noteq> #{} \<and> id<unsat, #c> = #{} \<and> id<alloc, #c> = #S"
        and s_Safety: "s \<Turnstile> Safety" and Next: "(s, t) \<Turnstile> [Next]_vars"

      from s show "s \<Turnstile> id<alloc, #c> \<noteq> #{}" "s \<Turnstile> id<unsat, #c> = #{}" by auto

      from Next
      show "t \<Turnstile> #S \<noteq> #{} \<and> id<unsat, #c> = #{} \<and> id<alloc, #c> = #S \<or> id<alloc, #c> = #{} \<or> (\<exists>S'. #((S', S) \<in> finite_psubset) \<and> #S' \<noteq> #{} \<and> id<unsat, #c> = #{} \<and> id<alloc, #c> = #S')"
      proof (cases rule: square_Next_cases)
        case unchanged with s show ?thesis by simp
      next
        case (Request c' S') with s have "c' \<noteq> c" by auto
        with Request s show ?thesis by auto
      next
        case (Schedule poolOrder) with s show ?thesis by auto
      next
        case (Allocate c' S') with s have "c' \<noteq> c" by auto
        with Allocate s show ?thesis by auto
      next
        case (Return c' S')
        show ?thesis
        proof (cases "c' = c")
          case False with Return s show ?thesis by auto
        next
          case c_eq[simp]: True
          show ?thesis
          proof (cases "S' = alloc s c")
            case True with Return show ?thesis by auto
          next
            case False with Return s s_Safety
            have "t \<Turnstile> (\<exists>S'. #((S', S) \<in> finite_psubset) \<and> #S' \<noteq> #{} \<and> id<unsat, #c> = #{} \<and> id<alloc, #c> = #S')"
              apply (auto simp add: Return del_def Safety_def AllocatorInvariant_def)
              using Return(1) by auto
            thus ?thesis by simp
          qed
        qed
      qed

      assume "(s, t) \<Turnstile> <\<exists>S'. id<$unsat, #c> = #{} \<and> id<$alloc, #c> = #S' \<and> Return c S'>_vars"
      thus "t \<Turnstile> id<alloc, #c> = #{} \<or> (\<exists>S'. #((S', S) \<in> finite_psubset) \<and> #S' \<noteq> #{} \<and> id<unsat, #c> = #{} \<and> id<alloc, #c> = #S')"
        by (auto simp add: angle_def Return_def updated_def)
    qed
    finally show "\<turnstile> SchedulingAllocator \<longrightarrow> (#c \<notin> set<sched> \<and> id<alloc, #c> \<noteq> #{} \<leadsto> id<alloc, #c> = #{}) ".
  qed
  finally show "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>\<diamond>id<alloc, #c> = #{}" by (simp add: leadsto_def)
qed


end

end