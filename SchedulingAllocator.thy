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
  assumes "\<And>c. finite (unsat s c)"
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

lemma higherPriorityClients_unscheduled:
  assumes "c \<notin> set (sched s)"
  shows "higherPriorityClients c s = set (sched s)"
  unfolding higherPriorityClients_def
  by (metis (mono_tags, lifting) assms takeWhile_eq_all_conv)

lemma higherPriorityClients_irreflexive:
  shows "c \<notin> higherPriorityClients c s"
  unfolding higherPriorityClients_def
  by (metis (full_types) set_takeWhileD)

lemma higherPriorityClients_antisymmetric:
  assumes "c2 \<in> set (sched s)" "c1 \<noteq> c2" "c1 \<notin> higherPriorityClients c2 s"
  shows "c2 \<in> higherPriorityClients c1 s"
proof -
  define cs where "cs \<equiv> sched s"

  from assms have "c2 \<in> set cs" "c1 \<noteq> c2" "c1 \<notin> set (takeWhile (op \<noteq> c2) cs)"
    by (simp_all add: cs_def higherPriorityClients_def)
  hence "c2 \<in> set (takeWhile (op \<noteq> c1) cs)"
    by (induct cs, auto)
  thus ?thesis by (simp add: higherPriorityClients_def cs_def)
qed

lemma higherPriorityClients_transitive:
  assumes "c1 \<in> higherPriorityClients c2 s"
  assumes "c2 \<in> higherPriorityClients c3 s"
  shows   "c1 \<in> higherPriorityClients c3 s"
proof -
  define cs where "cs \<equiv> sched s"
  from assms have "c1 \<in> set (takeWhile (op \<noteq> c2) cs)" "c2 \<in> set (takeWhile (op \<noteq> c3) cs)"
    by (simp_all add: cs_def higherPriorityClients_def)
  hence "c1 \<in> set (takeWhile (op \<noteq> c3) cs)"
    by (induct cs, auto)
  thus ?thesis by (simp add: higherPriorityClients_def cs_def)
qed

lemma higherPriorityClients_cases [case_names eq lt gt unscheduled]:
  assumes eq: "c1 = c2 \<Longrightarrow> P"
  assumes lt: "c1 \<in> higherPriorityClients c2 s \<Longrightarrow> c2 \<notin> higherPriorityClients c1 s \<Longrightarrow> c1 \<noteq> c2 \<Longrightarrow> c1 \<in> set (sched s) \<Longrightarrow> P"
  assumes gt: "c2 \<in> higherPriorityClients c1 s \<Longrightarrow> c1 \<notin> higherPriorityClients c2 s \<Longrightarrow> c1 \<noteq> c2 \<Longrightarrow> c2 \<in> set (sched s) \<Longrightarrow> P"
  assumes unscheduled: "c1 \<notin> set (sched s) \<Longrightarrow> c2 \<notin> set (sched s) \<Longrightarrow> P"
  shows P
proof (cases "c1 = c2")
  case True with eq show P by simp
next
  case neq: False
  show P
  proof (cases "c1 \<in> higherPriorityClients c2 s")
    case True 
    hence "c2 \<notin> higherPriorityClients c1 s"
      using higherPriorityClients_irreflexive higherPriorityClients_transitive by blast
    with True neq lt show P apply (auto simp add: higherPriorityClients_def) by (meson set_takeWhileD)
  next
    case nlt: False
    show P
    proof (cases "c2 \<in> set (sched s)")
      case True
      with neq nlt show P by (metis higherPriorityClients_antisymmetric gt)
    next
      case nsch2: False
      show P
      proof (cases "c1 \<in> set (sched s)")
        case True
        define cs where "cs \<equiv> sched s"
        from True nsch2 have "c1 \<in> higherPriorityClients c2 s"
          by (unfold higherPriorityClients_def, fold cs_def, induct cs, auto)
        thus P by (metis nlt)
      next
        case False with nsch2 show P by (metis unscheduled)
      qed
    qed
  qed
qed

lemma set_takeWhile_filter_subset:
  "x1 \<noteq> x2 \<Longrightarrow> set (takeWhile (op \<noteq> x1) (filter (op \<noteq> x2) xs)) \<subseteq> set (takeWhile (op \<noteq> x1) xs)"
  by (induct xs, auto)

lemma RequestE:
  assumes "(s,t) \<Turnstile> Request c S"
  assumes "\<lbrakk> S \<noteq> {}; finite S; unsat s c = {}; alloc s c = {};
              unsat t = modifyAt (unsat s) c (add S); unsat t c = S; pool t = insert c (pool s);
              alloc t = alloc s; sched t = sched s; available t = available s;
              \<And>c'. higherPriorityClients c' t = higherPriorityClients c' s \<rbrakk> \<Longrightarrow> P"
  shows P
  using assms unfolding Request_def updated_def
    by (auto simp add: add_def available_def higherPriorityClients_def)

lemma enabled_RequestI:
  assumes "S \<noteq> {}" "finite S" "unsat s c = {}" "alloc s c = {}"
  shows "s \<Turnstile> Enabled (Request c S)"
  using assms basevars [OF bv]
  unfolding enabled_def Request_def updated_def by (auto, blast)

lemma enabled_Request_eq[simp]:
  shows "(PRED Enabled (Request c S)) = (PRED #S \<noteq> #{} \<and> #(finite S) \<and> id<unsat,#c> = #{} \<and> id<alloc,#c> = #{})"
  by (intro ext iffI enabled_RequestI, auto simp add: enabled_def Request_def)

lemma angle_Request[simp]:
  "(ACT <Request c S>_vars) = Request c S"
  apply (intro ext, auto simp add: angle_def Request_def vars_def updated_def)
  by (metis add_simp empty_iff modifyAt_eq_simp)

lemma ScheduleE:
  assumes "(s,t) \<Turnstile> Schedule"
  assumes "\<And>poolOrder. \<lbrakk> pool s \<noteq> {}; pool t = {}; set poolOrder = pool s; distinct poolOrder;
                          sched t = sched s @ poolOrder; unsat t = unsat s; alloc t = alloc s;
                          available t = available s;
                          \<And>c'. c' \<in> set (sched s) \<Longrightarrow> higherPriorityClients c' t = higherPriorityClients c' s \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from assms(1)
  obtain poolOrder where po: "set poolOrder = pool s" "distinct poolOrder" "sched t = sched s @ poolOrder"
    by (auto simp add: Schedule_def)

  from assms(1) po show P
    apply (intro assms(2) [of poolOrder])
    by (auto simp add: Schedule_def available_def higherPriorityClients_def)
qed

lemma enabled_ScheduleI:
  assumes "pool s \<noteq> {}" "finite (pool s)"
  shows "s \<Turnstile> Enabled Schedule"
  using assms basevars [OF bv]
  unfolding enabled_def Schedule_def updated_def apply auto by (metis finite_distinct_list)

lemma enabled_Schedule_eq[simp]:
  shows "(PRED Enabled Schedule) = (PRED pool \<noteq> #{} \<and> finite<pool>)"
  apply (intro ext iffI enabled_ScheduleI, auto simp add: enabled_def Schedule_def)
  by (metis List.finite_set)

lemma angle_Schedule[simp]:
  "(ACT <Schedule>_vars) = Schedule"
  by (intro ext, auto simp add: angle_def Schedule_def vars_def updated_def)

lemma AllocateE:
  assumes "(s,t) \<Turnstile> Allocate c S"
  assumes "\<lbrakk> S \<noteq> {}; S \<subseteq> available s; S \<subseteq> unsat s c; c \<in> set (sched s);
            \<And>c' r'. c' \<in> higherPriorityClients c s \<Longrightarrow> r' \<in> unsat s c' \<Longrightarrow> r' \<in> S \<Longrightarrow> False;
            sched t = (if S = unsat s c then filter (op \<noteq> c) (sched s) else sched s);
            alloc t = modifyAt (alloc s) c (add S); alloc t c = alloc s c \<union> S;
            unsat t = modifyAt (unsat s) c (del S); unsat t c = unsat s c - S;
            pool t = pool s;
            available t = available s - S;
            \<And>c'. higherPriorityClients c' t
                = (if S = unsat s c
                    then if c' = c
                      then set (sched t)
                      else higherPriorityClients c' s - {c}
                    else higherPriorityClients c' s) \<rbrakk> \<Longrightarrow> P"
  shows P
  using assms(1)
proof (intro assms, simp_all add: Allocate_def updated_def add_def del_def, blast, clarify)
  assume "S \<subseteq> available s" "alloc t = modifyAt (alloc s) c (add S)"
  thus "available t = available s - S"
    unfolding available_def
    apply auto
    apply (metis add_simp modifyAt_eq_simp modifyAt_ne_simp)
    apply (metis add_simp modifyAt_eq_simp)
    by (metis add_simp modifyAt_eq_simp modifyAt_ne_simp)

next
  fix c'
  from assms(1) have "sched t = (if S = unsat s c then filter (op \<noteq> c) (sched s) else sched s)"
    by (simp add: Allocate_def)
  thus "(c' = c \<longrightarrow>
           (S = unsat s c \<longrightarrow> higherPriorityClients c t = {x \<in> set (sched s). c \<noteq> x}) \<and> (S \<noteq> unsat s c \<longrightarrow> higherPriorityClients c t = higherPriorityClients c s)) \<and>
          (c' \<noteq> c \<longrightarrow>
           (S = unsat s c \<longrightarrow> higherPriorityClients c' t = higherPriorityClients c' s - {c}) \<and>
           (S \<noteq> unsat s c \<longrightarrow> higherPriorityClients c' t = higherPriorityClients c' s))"
  proof (intro conjI impI, simp_all add: higherPriorityClients_def)
    show "set (takeWhile (op \<noteq> c) (filter (op \<noteq> c) (sched s))) = {x \<in> set (sched s). c \<noteq> x}"
      by (metis filter_set member_filter set_filter takeWhile_eq_all_conv)

    show "\<And>cs. c' \<noteq> c \<Longrightarrow> set (takeWhile (op \<noteq> c') (filter (op \<noteq> c) cs)) = set (takeWhile (op \<noteq> c') cs) - {c}"
    proof -
      fix cs show "c' \<noteq> c \<Longrightarrow> ?thesis cs" by (induct cs, auto)
    qed
  qed
qed

lemma enabled_AllocateI:
  assumes "S \<noteq> {}" "S \<subseteq> available s" "S \<subseteq> unsat s c" "c \<in> set (sched s)"
    "\<And>c' r'. c' \<in> higherPriorityClients c s \<Longrightarrow> r' \<in> unsat s c' \<Longrightarrow> r' \<in> S \<Longrightarrow> False"
  shows "s \<Turnstile> Enabled (Allocate c S)"
  using assms basevars [OF bv]
  unfolding enabled_def Allocate_def updated_def apply auto by meson

lemma enabled_Allocate_eq[simp]:
  shows "(PRED Enabled (Allocate c S)) = (PRED #S \<noteq> #{} \<and> #S \<subseteq> available \<and> #S \<subseteq> id<unsat,#c>
    \<and> #c \<in> set<sched> \<and> (\<forall>c' r'. #c' \<in> higherPriorityClients c \<longrightarrow> id<unsat,#c'> \<inter> #S = #{}))"
  by (intro ext iffI enabled_AllocateI, auto simp add: enabled_def Allocate_def)

lemma angle_Allocate[simp]:
  "(ACT <Allocate c S>_vars) = Allocate c S"
  apply (intro ext, auto simp add: angle_def Allocate_def updated_def vars_def)
   apply (metis del_simp modifyAt_eq_simp)
  by (metis del_simp modifyAt_eq_simp subsetCE)

lemma ReturnE:
  assumes "(s,t) \<Turnstile> Return c S"
  assumes "\<lbrakk> S \<noteq> {}; S \<subseteq> alloc s c; alloc t = modifyAt (alloc s) c (del S);
            unsat t = unsat s; pool t = pool s; sched t = sched s;
            available s \<subseteq> available t;
            \<And>c'. higherPriorityClients c' t = higherPriorityClients c' s \<rbrakk> \<Longrightarrow> P"
  shows P
  using assms(1)
  apply (intro assms, simp_all add: Return_def updated_def higherPriorityClients_def,
      auto simp add: available_def Return_def updated_def)
  by (metis del_simp modifyAt_eq_simp modifyAt_ne_simp)

lemma enabled_ReturnI:
  assumes "S \<noteq> {}" "S \<subseteq> alloc s c"
  shows "s \<Turnstile> Enabled (Return c S)"
  using assms basevars [OF bv]
  unfolding enabled_def Return_def updated_def by (auto, blast)

lemma enabled_Return_eq[simp]:
  shows "(PRED Enabled (Return c S)) = (PRED #S \<noteq> #{} \<and> #S \<subseteq> id<alloc,#c>)"
  by (intro ext iffI enabled_ReturnI, auto simp add: enabled_def Return_def)

lemma angle_Return[simp]:
  "(ACT <Return c S>_vars) = Return c S"
  apply (intro ext, auto simp add: angle_def Return_def vars_def updated_def)
  by (metis del_simp modifyAt_eq_simp subsetCE)

lemma Next_cases [consumes 1, case_names Request Schedule Allocate Return]:
  assumes Next: "(s,t) \<Turnstile> Next"
  assumes Request: "\<And>c S.
    \<lbrakk> S \<noteq> {}; finite S; unsat s c = {}; alloc s c = {};
      unsat t = modifyAt (unsat s) c (add S); unsat t c = S; pool t = insert c (pool s);
      alloc t = alloc s; sched t = sched s; available t = available s;
      \<And>c'. higherPriorityClients c' t = higherPriorityClients c' s \<rbrakk> \<Longrightarrow> P"
  assumes Schedule: "\<And>poolOrder.
    \<lbrakk> pool s \<noteq> {}; pool t = {}; set poolOrder = pool s; distinct poolOrder;
      sched t = sched s @ poolOrder; unsat t = unsat s; alloc t = alloc s;
      available t = available s;
      \<And>c'. c' \<in> set (sched s) \<Longrightarrow> higherPriorityClients c' t = higherPriorityClients c' s \<rbrakk> \<Longrightarrow> P"
  assumes Allocate: "\<And>c S.
    \<lbrakk> S \<noteq> {}; S \<subseteq> available s; S \<subseteq> unsat s c; c \<in> set (sched s);
      \<And>c' r'. c' \<in> higherPriorityClients c s \<Longrightarrow> r' \<in> unsat s c' \<Longrightarrow> r' \<in> S \<Longrightarrow> False;
      sched t = (if S = unsat s c then filter (op \<noteq> c) (sched s) else sched s);
      alloc t = modifyAt (alloc s) c (add S); alloc t c = alloc s c \<union> S;
      unsat t = modifyAt (unsat s) c (del S); unsat t c = unsat s c - S;
      pool t = pool s; available t = available s - S;
            \<And>c'. higherPriorityClients c' t
                = (if S = unsat s c
                    then if c' = c
                      then set (sched t)
                      else higherPriorityClients c' s - {c}
                    else higherPriorityClients c' s) \<rbrakk> \<Longrightarrow> P"
  assumes Return: "\<And>c S.
    \<lbrakk> S \<noteq> {}; S \<subseteq> alloc s c; alloc t = modifyAt (alloc s) c (del S);
      unsat t = unsat s; pool t = pool s; sched t = sched s;
      available s \<subseteq> available t;
      \<And>c'. higherPriorityClients c' t = higherPriorityClients c' s \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from Next consider
    (Request)    "\<exists> c S. (s,t) \<Turnstile> Request c S"
    | (Schedule)        "(s,t) \<Turnstile> Schedule"
    | (Allocate) "\<exists> c S. (s,t) \<Turnstile> Allocate c S"
    | (Return)   "\<exists> c S. (s,t) \<Turnstile> Return c S"
    unfolding Next_def apply auto by blast
  thus P
  proof cases
  next case p: Request with Request show P by (elim exE RequestE, blast)
  next case p: Allocate with Allocate show P by (elim exE AllocateE, blast)
  next case p: Schedule with Schedule show P by (elim exE ScheduleE, blast)
  next case p: Return with Return show P by (elim exE ReturnE, blast)
  qed
qed

lemma square_Next_cases [consumes 1, case_names unchanged Request Schedule Allocate Return]:
  assumes Next: "(s,t) \<Turnstile> [Next]_vars"
  assumes unchanged: "\<lbrakk> unsat t = unsat s; alloc t = alloc s; pool t = pool s; sched t = sched s \<rbrakk> \<Longrightarrow> P"
  assumes Request: "\<And>c S.
    \<lbrakk> S \<noteq> {}; finite S; unsat s c = {}; alloc s c = {};
      unsat t = modifyAt (unsat s) c (add S); unsat t c = S; pool t = insert c (pool s);
      alloc t = alloc s; sched t = sched s; available t = available s;
      \<And>c'. higherPriorityClients c' t = higherPriorityClients c' s  \<rbrakk> \<Longrightarrow> P"
  assumes Schedule: "\<And>poolOrder.
    \<lbrakk> pool s \<noteq> {}; pool t = {}; set poolOrder = pool s; distinct poolOrder;
      sched t = sched s @ poolOrder; unsat t = unsat s; alloc t = alloc s;
      \<And>c'. c' \<in> set (sched s) \<Longrightarrow> higherPriorityClients c' t = higherPriorityClients c' s \<rbrakk> \<Longrightarrow> P"
  assumes Allocate: "\<And>c S.
    \<lbrakk> S \<noteq> {}; S \<subseteq> available s; S \<subseteq> unsat s c; c \<in> set (sched s);
      \<And>c' r'. c' \<in> higherPriorityClients c s \<Longrightarrow> r' \<in> unsat s c' \<Longrightarrow> r' \<in> S \<Longrightarrow> False;
      sched t = (if S = unsat s c then filter (op \<noteq> c) (sched s) else sched s);
      alloc t = modifyAt (alloc s) c (add S); alloc t c = alloc s c \<union> S;
      unsat t = modifyAt (unsat s) c (del S); unsat t c = unsat s c - S;
      pool t = pool s; available t = available s - S;
            \<And>c'. higherPriorityClients c' t
                = (if S = unsat s c
                    then if c' = c
                      then set (sched t)
                      else higherPriorityClients c' s - {c}
                    else higherPriorityClients c' s) \<rbrakk> \<Longrightarrow> P"
  assumes Return: "\<And>c S.
    \<lbrakk> S \<noteq> {}; S \<subseteq> alloc s c; alloc t = modifyAt (alloc s) c (del S);
      unsat t = unsat s; pool t = pool s; sched t = sched s;
      available s \<subseteq> available t;
      \<And>c'. higherPriorityClients c' t = higherPriorityClients c' s \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from Next have "((s,t) \<Turnstile> Next) \<or> ((s,t) \<Turnstile> unchanged vars)" by (auto simp add: square_def)
  thus P
  proof (elim disjE)
    assume "(s,t) \<Turnstile> Next"
    thus P
    proof (cases rule: Next_cases)
    next case p: Request with Request show P by blast
    next case p: Allocate with Allocate show P by blast
    next case p: Schedule with Schedule show P by blast
    next case p: Return with Return show P by blast
    qed
  next
    assume "(s,t) \<Turnstile> unchanged vars" with unchanged show P by (auto simp add: vars_def)
  qed
qed

lemma Safety_step: "\<turnstile> $Safety \<and> [Next]_vars \<longrightarrow> Safety$"
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

    show ?thesis
    proof (intro SafetyI)
      from MutualExclusion
      show "\<And>c1 c2. c1 \<noteq> c2 \<Longrightarrow> alloc t c1 \<inter> alloc t c2 = {}"
        by (simp add: MutualExclusion_def)

      from Request AllocatorInvariant
      show "\<And>c'. finite (unsat t c')"
        by (simp add: AllocatorInvariant_def modifyAt_def)

      from AllocatorInvariant
      show
        "\<And>c. c \<in> pool t \<Longrightarrow> unsat t c \<noteq> {}"
        "\<And>c. c \<in> pool t \<Longrightarrow> alloc t c = {}"
        "\<And>c. c \<in> set (sched t) \<Longrightarrow> unsat t c \<noteq> {}"
        "\<And>c. c \<notin> pool t \<Longrightarrow> c \<notin> set (sched t) \<Longrightarrow> unsat t c = {}"
        "pool t \<inter> set (sched t) = {}"
        "distinct (sched t)"
        "finite (pool t)"
        "\<And>c. finite (unsat t c)"
        "\<And>c. finite (alloc t c)"
        "\<And>c. alloc t c \<inter> unsat t c = {}"
        by (auto simp add: AllocatorInvariant_def add_def modifyAt_def)
    next
      fix c1 c2
      assume     "c1 \<in> set (sched t)"         "c2 \<in> higherPriorityClients c1 t"
      hence  c1: "c1 \<in> set (sched s)" and c2: "c2 \<in> higherPriorityClients c1 s"
        by (simp_all add: higherPriorityClients_def)

      from c2 have "c2 : set (sched s)" unfolding higherPriorityClients_def using set_takeWhileD by metis
      with AllocatorInvariant have ne: "c2 \<noteq> c" by (auto simp add: AllocatorInvariant_def)

      from c1 c2 AllocatorInvariant have "alloc s c1 \<inter> unsat s c2 = {}" by (simp add: AllocatorInvariant_def)
      with ne show "alloc t c1 \<inter> unsat t c2 = {}" by simp
    qed
  next
    case [simp]: (Schedule poolOrder)

    show ?thesis
    proof (intro SafetyI)
      from MutualExclusion
      show "\<And>c1 c2. c1 \<noteq> c2 \<Longrightarrow> alloc t c1 \<inter> alloc t c2 = {}"
        by (auto simp add: MutualExclusion_def)

      from AllocatorInvariant
      show "\<And>c. finite (unsat t c)" by (simp add: AllocatorInvariant_def)

      show "\<And>c. c \<in> pool t \<Longrightarrow> unsat t c \<noteq> {}"
        "\<And>c. c \<in> pool t \<Longrightarrow> alloc t c = {}"
        "pool t \<inter> set (sched t) = {}"
        "finite (pool t)"
        by auto

      from AllocatorInvariant
      show "\<And>c. c \<in> set (sched t) \<Longrightarrow> unsat t c \<noteq> {}"
        "\<And>c. c \<notin> pool t \<Longrightarrow> c \<notin> set (sched t) \<Longrightarrow> unsat t c = {}"
        "\<And>c. finite (unsat t c)"
        "\<And>c. finite (alloc t c)"
        "distinct (sched t)"
        "\<And>c. alloc t c \<inter> unsat t c = {}"
        by (auto simp add: AllocatorInvariant_def)

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
    qed
  next
    case [simp]: (Allocate c S)

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
      show "\<And>c. finite (unsat t c)"
        by (simp add: AllocatorInvariant_def modifyAt_def del_def)

      from AllocatorInvariant
      show
        "\<And>c. c \<in> pool t \<Longrightarrow> unsat t c \<noteq> {}"
        "\<And>c. c \<in> pool t \<Longrightarrow> alloc t c = {}"
        "pool t \<inter> set (sched t) = {}"
        "finite (pool t)"
        by (auto simp add: AllocatorInvariant_def modifyAt_def)

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

            from c2 have "c2 \<in> set (takeWhile (op \<noteq> c1) (filter (op \<noteq> c) (sched s)))"
              by (auto simp add: higherPriorityClients_def True)
            also have "... \<subseteq> higherPriorityClients c1 s"
              unfolding higherPriorityClients_def
              by (intro set_takeWhile_filter_subset ne1)
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
    qed
  next
    case [simp]: (Return c S)

    show ?thesis
    proof (intro SafetyI)
      from MutualExclusion
      show "\<And>c1 c2. c1 \<noteq> c2 \<Longrightarrow> alloc t c1 \<inter> alloc t c2 = {}"
        apply (auto simp add: MutualExclusion_def modifyAt_def)
        by blast+

      from AllocatorInvariant
      show "\<And>c. finite (unsat t c)" by (simp add: AllocatorInvariant_def)

      from AllocatorInvariant
      show
        "\<And>c. c \<in> pool t \<Longrightarrow> unsat t c \<noteq> {}"
        "\<And>c. c \<in> pool t \<Longrightarrow> alloc t c = {}"
        "pool t \<inter> set (sched t) = {}"
        "\<And>c. c \<in> set (sched t) \<Longrightarrow> unsat t c \<noteq> {}"
        "\<And>c. c \<notin> pool t \<Longrightarrow> c \<notin> set (sched t) \<Longrightarrow> unsat t c = {}"
        "distinct (sched t)"
        "finite (pool t)"
        "\<And>c. finite (unsat t c)"
        "\<And>c. finite (alloc t c)"
        "\<And>c. alloc t c \<inter> unsat t c = {}"
        by (auto simp add: AllocatorInvariant_def modifyAt_def del_def)

      from AllocatorInvariant
      show "\<And>c1 c2. c1 \<in> set (sched t) \<Longrightarrow> c2 \<in> higherPriorityClients c1 t \<Longrightarrow> alloc t c1 \<inter> unsat t c2 = {}"
        by (auto simp add: modifyAt_def AllocatorInvariant_def, blast)
    qed
  qed
qed

lemma safety: "\<turnstile> SchedulingAllocator \<longrightarrow> \<box>Safety"
proof invariant
  fix sigma
  assume sigma: "sigma \<Turnstile> SchedulingAllocator"
  thus "sigma \<Turnstile> Init Safety"
    by (auto simp add: Init_def Safety_def SchedulingAllocator_def InitState_def MutualExclusion_def AllocatorInvariant_def)

  show "sigma \<Turnstile> stable Safety"
  proof (intro Stable [OF _ Safety_step])
    from sigma show "sigma \<Turnstile> \<box>[Next]_vars"
      by (simp add: SchedulingAllocator_def)
  qed
qed

end

typedef Inductor = "{(crs :: (Client \<times> Resource) set, rs :: Resource set). finite crs \<and> finite rs}" by auto

definition unsats :: "Inductor \<Rightarrow> (Client \<times> Resource) set" where "unsats \<equiv> fst o Rep_Inductor"
definition allocs :: "Inductor \<Rightarrow> Resource set" where "allocs \<equiv> snd o Rep_Inductor"

definition mkInductor :: "(Client \<times> Resource) set \<Rightarrow> Resource set \<Rightarrow> Inductor"
  where "mkInductor crs rs \<equiv> Abs_Inductor (crs, rs)"

lemma finite_unsats[simp]: "finite (unsats i)" unfolding unsats_def apply auto by (metis Product_Type.Collect_case_prodD Rep_Inductor)
lemma finite_allocs[simp]: "finite (allocs i)" unfolding allocs_def apply auto by (metis Product_Type.Collect_case_prodD Rep_Inductor)

lemma
  assumes "finite crs" "finite rs"
  shows unsats_mkInductor[simp]: "unsats (mkInductor crs rs) = crs"
    and allocs_mkInductor[simp]: "allocs (mkInductor crs rs) =  rs"
  using assms unfolding unsats_def allocs_def mkInductor_def
  by (auto simp add: Abs_Inductor_inverse)

lemma
  assumes "unsats i1 = unsats i2" "allocs i1 = allocs i2"
  shows Inductor_eqI: "i1 = i2"
  using assms unfolding unsats_def allocs_def apply simp using Rep_Inductor_inject prod_eqI by blast

lemma shows Inductor_eq: "(i1 = i2) = (unsats i1 = unsats i2 \<and> allocs i1 = allocs i2)"
  by (intro iffI Inductor_eqI, auto)

definition Inductor_prec :: "Inductor \<Rightarrow> Inductor \<Rightarrow> bool"
  where "Inductor_prec i1 i2 \<equiv> (i1,i2) \<in> inv_image (finite_psubset <*lex*> finite_psubset) (\<lambda>i. (unsats i, allocs i))"

instantiation Inductor :: order begin
definition less_Inductor :: "Inductor \<Rightarrow> Inductor \<Rightarrow> bool" where "i1 < i2 \<equiv> Inductor_prec i1 i2"
definition less_eq_Inductor :: "Inductor \<Rightarrow> Inductor \<Rightarrow> bool" where "less_eq_Inductor i1 i2 \<equiv> i1 = i2 \<or> i1 < i2"
instance
  apply intro_classes
  unfolding less_Inductor_def less_eq_Inductor_def Inductor_prec_def by auto
end

lemma less_Inductor_simp: "i1 < i2 \<equiv> unsats i1 \<subset> unsats i2 \<or> (unsats i1 = unsats i2 \<and> allocs i1 \<subset> allocs i2)"
  by (simp add: less_Inductor_def Inductor_prec_def)

lemma wf_less_Inductor: "wf {(i1, i2 :: Inductor). i1 < i2}"
proof -
  define r where "r \<equiv> inv_image (finite_psubset <*lex*> finite_psubset) (\<lambda>i. (unsats i, allocs i))"
  show ?thesis
  unfolding less_Inductor_def Inductor_prec_def
  apply (fold r_def, simp)
  unfolding r_def by (intro wf_inv_image wf_lex_prod wf_finite_psubset)
qed

context SchedulingAllocator
begin

definition relevantSchedule :: "Client \<Rightarrow> Client set stfun"
  where "relevantSchedule c s \<equiv> insert c (higherPriorityClients c s)"

definition inductor :: "Client \<Rightarrow> Inductor stfun"
  where "inductor c s \<equiv> mkInductor { (c',r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c' }
                                   (unsat s (hd (sched s)) - available s)"

lemma
  assumes Safety: "s \<Turnstile> Safety"
  shows unsats_inductor[simp]: "unsats (inductor c s) = { (c',r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c' }"
    and allocs_inductor[simp]: "allocs (inductor c s) = (unsat s (hd (sched s)) - available s)"
proof -
  have sub1: "{(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'} \<subseteq> (\<Union> c' \<in> relevantSchedule c s. (Pair c') ` unsat s c')"
    by auto

  have frs: "finite (relevantSchedule c s)"
    unfolding relevantSchedule_def higherPriorityClients_def by auto

  from Safety have f1: "finite {(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'}"
    by (intro finite_subset [OF sub1] finite_Union finite_imageI frs, auto simp add: Safety_def AllocatorInvariant_def)

  from Safety have f2: "finite (unsat s (hd (sched s)) - available s)"
    by (auto simp add: Safety_def AllocatorInvariant_def)

  from f1 f2 show
    "unsats (inductor c s) = { (c',r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c' }"
    "allocs (inductor c s) = (unsat s (hd (sched s)) - available s)"
    unfolding inductor_def by simp_all
qed

lemma
  assumes Safety_s: "s \<Turnstile> Safety"
    and Next: "(s,t) \<Turnstile> [Next]_vars"
    and scheduled: "c \<in> set (sched s)"
  shows scheduled_progress: "(s,t) \<Turnstile> (inductor c)$ \<le> $(inductor c) \<or> #c \<notin> set<sched$>"
  using Next
proof (cases rule: square_Next_cases)
  case unchanged thus ?thesis
    by (simp add: inductor_def relevantSchedule_def higherPriorityClients_def available_def)
next
  case (Request c' S')
  from Request Safety_s have unscheduled: "c' \<notin> set (sched s)" by (auto simp add: Safety_def AllocatorInvariant_def)

  have relevantSchedule_eq[simp]: "relevantSchedule c t = relevantSchedule c s"
    unfolding relevantSchedule_def
    by (simp add: Request)

  {
    fix c''
    assume "c'' \<in> relevantSchedule c s"
    with scheduled have "c'' \<in> set (sched s)"
      unfolding relevantSchedule_def
      using higherPriorityClients_cases higherPriorityClients_def
      by auto
    with unscheduled have "c'' \<noteq> c'" by auto
    hence "modifyAt (unsat s) c' (add S') c'' = unsat s c''" by simp
  }
  note modifyAt_eq[simp] = this

  from scheduled have hd_relevant: "hd (sched s) \<in> relevantSchedule c s"
    unfolding relevantSchedule_def higherPriorityClients_def
    by (cases "sched s", auto)

  from Request scheduled unscheduled have "inductor c t = inductor c s"
    unfolding inductor_def
    apply (intro cong [OF cong [OF refl, where f = mkInductor]])
    using hd_relevant by auto

  thus ?thesis by simp
next
  case (Schedule poolOrder)

  have relevantSchedule_eq[simp]: "relevantSchedule c t = relevantSchedule c s"
    unfolding relevantSchedule_def
    by (intro cong [OF refl, where f = "insert c"] Schedule scheduled)

  from scheduled have hd_eq[simp]: "hd (sched s @ poolOrder) = hd (sched s)" by (cases "sched s", auto)

  from Schedule scheduled show ?thesis unfolding inductor_def available_def by auto
next
  case (Allocate c' S')

  from Safety_s Safety_step Next have Safety_t: "t \<Turnstile> Safety" by auto

  show ?thesis
  proof (cases "c' \<in> relevantSchedule c s")
    case c'_relevant: True

    show ?thesis
    proof (cases "c' = c \<and> S' = unsat s c'")
      case True
      with Allocate have "c \<notin> set (sched t)" by auto
      thus ?thesis by simp
    next
      case c_not_fully_allocated: False

      from Allocate obtain r where r: "r \<in> S'" by auto
      have psubset_exI: "\<And>A B b. A \<subseteq> B \<Longrightarrow> b \<in> B - A \<Longrightarrow> A \<subset> B" by auto

      have "{(c', r). c' \<in> relevantSchedule c t \<and> r \<in> unsat t c'} \<subset> {(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'}"
      proof (intro psubset_exI subsetI DiffI, clarsimp)
        from Allocate r c'_relevant show "(c', r) \<in> {(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'}" by auto
        from Allocate r show "(c', r) \<notin> {(c', r). c' \<in> relevantSchedule c t \<and> r \<in> unsat t c'}"
          by (auto simp add: relevantSchedule_def del_def)

        fix c'' r''
        assume c'': "c'' \<in> relevantSchedule c t " and r'': "r'' \<in> unsat t c''"
        show "c'' \<in> relevantSchedule c s \<and> r'' \<in> unsat s c''"
        proof (intro conjI)
          from r'' show "r'' \<in> unsat s c''" by (cases "c' = c''", simp_all add: Allocate)
          from c'' c_not_fully_allocated show "c'' \<in> relevantSchedule c s"
            by (cases "S' = unsat s c'", auto simp add: relevantSchedule_def Allocate)
        qed
      qed

      hence "inductor c t < inductor c s"
        using Safety_s Safety_t by (simp add: less_Inductor_simp)
      thus ?thesis by (simp add: less_eq_Inductor_def)
    qed
  next
    case c'_irrelevant: False

    with scheduled have hd_sched_eq[simp]: "hd (sched t) = hd (sched s)"
      by (cases "sched s", auto simp add: Allocate relevantSchedule_def higherPriorityClients_def)

    from c'_irrelevant have relevantSchedule_eq[simp]: "relevantSchedule c t = relevantSchedule c s"
      by (auto simp add: relevantSchedule_def Allocate)

    {
      fix c''
      assume c''_relevant: "c'' \<in> relevantSchedule c s"
      with c'_irrelevant have "c' \<noteq> c''" by auto
      hence "unsat t c'' = unsat s c''" by (simp add: Allocate)
    }
    note relevant_unsat_eq = this

    hence unsats_eq: "{(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat t c'} = {(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'}"
      by auto

    from scheduled
    have unsat_hd_eq[simp]: "unsat t (hd (sched s)) = unsat s (hd (sched s))"
      by (intro relevant_unsat_eq, cases "sched s", auto simp add: relevantSchedule_def higherPriorityClients_def)

    have allocs_eq: "unsat s (hd (sched s)) - available t = unsat s (hd (sched s)) - available s"
    proof (auto simp add: Allocate)
      fix r assume r: "r \<in> unsat s (hd (sched s))" "r \<in> S'"
      from c'_irrelevant scheduled have "hd (sched s) \<in> higherPriorityClients c' s"
        by (cases "sched s", auto simp add: relevantSchedule_def higherPriorityClients_def)
      with r show False using Allocate by metis
    qed

    have "inductor c t = inductor c s"
      apply (intro Inductor_eqI) using Safety_s Safety_t by (simp_all add: unsats_eq allocs_eq)
    thus ?thesis by simp
  qed
next
  case (Return c' S')

  from Safety_s Safety_step Next have Safety_t: "t \<Turnstile> Safety" by auto

  have unsats_eq: "unsats (inductor c t) = unsats (inductor c s)"
    using Safety_s Safety_t by (simp add: Return relevantSchedule_def)

  have "allocs (inductor c t) \<subseteq> allocs (inductor c s)" using Safety_s Safety_t Return by auto
  hence "inductor c t \<le> inductor c s"
    by (auto simp add: less_eq_Inductor_def less_Inductor_simp Inductor_eq unsats_eq)
  then show ?thesis by simp
qed

lemma WF1_SchedulingAllocator_states:
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
    proof (intro wf_imp_ex_leadsto [OF wf_less_Inductor], rule imp_leadsto_diamond, unfold inductor_lt_simp)
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
              \<leadsto> #c \<notin> set<sched> \<or> (\<exists>i'. #(i' < i) \<and> #i' = inductor c \<and> #c \<in> set<sched>))"
      proof (intro imp_exists_leadstoI WF1_SchedulingAllocator_states)
        fix blocker
        show "\<turnstile> SchedulingAllocator \<longrightarrow> WF(\<exists>S. id<$unsat, #blocker> = #{} \<and> id<$alloc, #blocker> = #S \<and> Return blocker S)_vars"
          by (auto simp add: SchedulingAllocator_def ReturnFair_def)

        fix s t
        assume "s \<Turnstile> #i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> id<alloc, #blocker> \<noteq> #{}"
        hence s: "i = inductor c s" "c \<in> set (sched s)" "unsat s (hd (sched s)) \<inter> alloc s blocker \<noteq> {}"
          by simp_all

        assume s_Safety: "s \<Turnstile> Safety"
        assume Next: "(s,t) \<Turnstile> [Next]_vars"

        from s_Safety Next Safety_step[temp_use] have t_Safety: "t \<Turnstile> Safety" by simp

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

        have simp1: "(ACT <\<exists>S. id<$unsat, #blocker> = #{} \<and> id<$alloc, #blocker> = #S \<and> Return blocker S>_vars)
          = (ACT (\<exists>S. id<$unsat, #blocker> = #{} \<and> id<$alloc, #blocker> = #S \<and> <Return blocker S>_vars))"
          unfolding angle_def by auto

        show "s \<Turnstile> Enabled (<\<exists>S. id<$unsat, #blocker> = #{} \<and> id<$alloc, #blocker> = #S \<and> Return blocker S>_vars)"
          unfolding simp1 angle_Return using s blocker_satisfied
        proof (intro enabled_exI enabled_guard_conjI enabled_ReturnI)
          show "alloc s blocker \<subseteq> alloc s blocker" by simp
        qed auto

        have "(s, t) \<Turnstile> inductor c$ \<le> $inductor c \<or> #c \<notin> set<sched$>"
          by (intro scheduled_progress s_Safety Next s)
        with s_Safety t_Safety consider
          (alloc) "c \<notin> set (sched t)"
          | (progress) "c \<in> set (sched t)" "inductor c t < inductor c s"
          | (same) "c \<in> set (sched t)" "inductor c t = inductor c s"
            "unsat t (hd (sched t)) - available t = unsat s (hd (sched s)) - available s"
          by (cases "c \<in> set (sched t)", auto simp add: less_eq_Inductor_def Inductor_eq)
        note progress_cases = this

        from progress_cases
        show "t \<Turnstile> #i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> id<alloc, #blocker> \<noteq> #{} \<or> #c \<notin> set<sched> \<or> (\<exists>i'. #(i' < i) \<and> #i' = inductor c \<and> #c \<in> set<sched>)"
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
            have "unsat t (hd (sched t)) \<inter> alloc t blocker = unsat s (hd (sched s)) \<inter> alloc s blocker"
            proof (cases "c' = blocker")
              case False
              with Return s show ?thesis by auto
            next
              case True
              have "unsat t (hd (sched t)) = unsat s (hd (sched s))" by (simp add: Return)
              have "alloc t blocker \<subseteq> alloc s blocker" by (auto simp add: Return True del_def)
              show ?thesis
              proof (intro equalityI subsetI IntI)
                fix r
                assume "r \<in> unsat t (hd (sched t)) \<inter> alloc t blocker"
                thus "r \<in> unsat s (hd (sched s))" "r \<in> alloc s blocker" by (auto simp add: Return True)
              next
                fix r assume "r \<in> unsat s (hd (sched s)) \<inter> alloc s blocker"
                hence r: "r \<in> unsat s (hd (sched s))" "r \<in> alloc s blocker" by simp_all
                thus "r \<in> unsat t (hd (sched t))" by (simp add: Return)
                from r have "r \<notin> available s" by (auto simp add: available_def)
                with `unsat t (hd (sched t)) - available t = unsat s (hd (sched s)) - available s` r
                have "r \<notin> available t" by auto
                then obtain c'' where r_alloc: "r \<in> alloc t c''" by (auto simp add: available_def)
                show "r \<in> alloc t blocker"
                proof (cases "c'' = blocker")
                  case True with r_alloc show ?thesis by simp
                next
                  case False
                  with r_alloc have "r \<in> alloc s c''" by (auto simp add: Return True)
                  with s_Safety r have "c'' = blocker"
                    by (auto simp add: Safety_def MutualExclusion_def)
                  with False show ?thesis by simp
                qed
              qed
            qed
            with s show ?thesis by simp
          qed

          with same s show ?thesis by auto
        qed

        assume "(s, t) \<Turnstile> <\<exists>S. id<$unsat, #blocker> = #{} \<and> id<$alloc, #blocker> = #S \<and> Return blocker S>_vars"
        hence blocker_satisfied: "unsat s blocker = {}"
          and blocker_allocated: "alloc s blocker \<noteq> {}"
          and alloc_t_eq: "alloc t = modifyAt (alloc s) blocker (del (alloc s blocker))"
          and alloc_t_blocker_eq: "alloc t blocker = {}"
          and unchanged[simp]: "unsat t = unsat s" "pool t = pool s" "sched t = sched s"
          by (auto simp add: Return_def angle_def vars_def updated_def)

        from progress_cases
        show "t \<Turnstile> #c \<notin> set<sched> \<or> (\<exists>i'. #(i' < i) \<and> #i' = inductor c \<and> #c \<in> set<sched>)"
        proof cases
          case alloc thus ?thesis by simp
        next
          case progress thus ?thesis by (auto simp add: s)
        next
          case same
          from s obtain r where r_hd: "r \<in> unsat s (hd (sched s))" and r_blocker: "r \<in> alloc s blocker" by auto
          from r_blocker have r_unavailable: "r \<notin> available s" unfolding available_def by auto
          from r_blocker s_Safety have r_available: "r \<in> available t" unfolding available_def alloc_t_eq Safety_def MutualExclusion_def
            apply auto by (metis alloc_t_blocker_eq alloc_t_eq disjoint_iff_not_equal empty_iff modifyAt_ne_simp)
          from r_hd `unsat t (hd (sched t)) - available t = unsat s (hd (sched s)) - available s`
            r_unavailable r_available
          show ?thesis by auto
        qed
      qed
      finally show "\<turnstile> SchedulingAllocator \<longrightarrow> (#i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available = #{} \<leadsto> #c \<notin> set<sched> \<or> (\<exists>i'. #(i' < i) \<and> #i' = inductor c \<and> #c \<in> set<sched>)) ".

      have "\<turnstile> SchedulingAllocator \<longrightarrow> (#i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{} \<leadsto> (\<exists> topPriority. #i = inductor c \<and> #topPriority = hd<sched> \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{}))"
        by (intro imp_imp_leadsto, auto)
      also have "\<turnstile> SchedulingAllocator \<longrightarrow> ((\<exists> topPriority. #i = inductor c \<and> #topPriority = hd<sched> \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{}) 
                        \<leadsto> #c \<notin> set<sched> \<or> (\<exists>y. #(y < i) \<and> #y = inductor c \<and> #c \<in> set<sched>))"
      proof (intro imp_exists_leadstoI WF1_SchedulingAllocator_states)
        fix topPriority
        show "\<turnstile> SchedulingAllocator \<longrightarrow>  WF(\<exists>S ct. #ct = hd<$sched> \<and> Allocate ct S)_vars"
          by (auto simp add: SchedulingAllocator_def AllocateHeadFair_def)

        fix s t
        assume s_Safety: "Safety s" and Next: "(s,t) \<Turnstile> [Next]_vars"

        from s_Safety Next Safety_step[temp_use] have t_Safety: "t \<Turnstile> Safety" by simp

        assume "s \<Turnstile> #i = inductor c \<and> #topPriority = hd<sched> \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{}"
        hence s: "i = inductor c s" "topPriority = hd (sched s)" "c \<in> set (sched s)" "unsat s (hd (sched s)) \<inter> available s \<noteq> {}" by auto
        from s have hpc_topPriority: "higherPriorityClients topPriority s = {}" unfolding higherPriorityClients_def by (cases "sched s", auto)

        have simp1: "(ACT (<\<exists>S ct. #ct = hd<$sched> \<and> Allocate ct S>_vars)) = (ACT \<exists>S ct. #ct = hd<$sched> \<and> (<Allocate ct S>_vars))" by (auto simp add: angle_def)
        show "s \<Turnstile> Enabled (<\<exists>S ct. #ct = hd<$sched> \<and> Allocate ct S>_vars)"
          unfolding simp1 angle_Allocate proof (intro enabled_exI enabled_AllocateI enabled_guard_conjI)
          from s show "unsat s (hd (sched s)) \<inter> available s \<noteq> {}" by simp
          from s show "topPriority \<in> set (sched s)" by (cases "sched s", auto)
        qed (unfold hpc_topPriority, auto simp add: s)

        have "(s, t) \<Turnstile> inductor c$ \<le> $inductor c \<or> #c \<notin> set<sched$>"
          by (intro scheduled_progress s_Safety Next s)
        with s_Safety t_Safety consider
          (alloc) "c \<notin> set (sched t)"
          | (progress) "c \<in> set (sched t)" "inductor c t < inductor c s"
          | (same) "c \<in> set (sched t)" "inductor c t = inductor c s"
            "unsat t (hd (sched t)) - available t = unsat s (hd (sched s)) - available s"
            "{(c', r). c' \<in> relevantSchedule c t \<and> r \<in> unsat t c'} = {(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'}"
          by (cases "c \<in> set (sched t)", auto simp add: less_eq_Inductor_def Inductor_eq)
        note progress_cases = this

        from progress_cases
        show "t \<Turnstile> #i = inductor c \<and> #topPriority = hd<sched> \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{} \<or> #c \<notin> set<sched> \<or> (\<exists>y. #(y < i) \<and> #y = inductor c \<and> #c \<in> set<sched>)"
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
              case True
              with s have c'_relevant: "c' \<in> relevantSchedule c s"
                unfolding relevantSchedule_def higherPriorityClients_def
                by (cases "sched s", auto)

              hence "Pair c' ` unsat s c' \<subseteq> {(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'}" by auto
              also from same have "{(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'} = {(c', r). c' \<in> relevantSchedule c t \<and> r \<in> unsat t c'}" by simp
              finally have unsat_eq: "unsat s c' = unsat t c'" by (auto simp add: Allocate)

              from Allocate have "unsat s c' \<noteq> unsat t c'" by auto
              with unsat_eq show ?thesis by simp
            qed
          qed
        qed

        assume "(s,t) \<Turnstile> <\<exists>S ct. #ct = hd<$sched> \<and> Allocate ct S>_vars"
        hence assm_Allocate: "(s,t) \<Turnstile> \<exists>S. <Allocate topPriority S>_vars" using s by (auto simp add: angle_def)

        from progress_cases
        show "t \<Turnstile> #c \<notin> set<sched> \<or> (\<exists>y. #(y < i) \<and> #y = inductor c \<and> #c \<in> set<sched>)"
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
            with s have c'_relevant: "c' \<in> relevantSchedule c s"
              unfolding relevantSchedule_def higherPriorityClients_def
              by (cases "sched s", auto)

            hence "Pair c' ` unsat s c' \<subseteq> {(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'}" by auto
            also from same have "{(c', r). c' \<in> relevantSchedule c s \<and> r \<in> unsat s c'} = {(c', r). c' \<in> relevantSchedule c t \<and> r \<in> unsat t c'}" by simp
            finally have unsat_eq: "unsat s c' = unsat t c'" by (auto simp add: Allocate)

            from Allocate have "unsat s c' \<noteq> unsat t c'" by auto
            with unsat_eq show ?thesis by simp
          qed
        qed
      qed
      finally
      show "\<turnstile> SchedulingAllocator \<longrightarrow> (#i = inductor c \<and> #c \<in> set<sched> \<and> id<unsat, hd<sched>> \<inter> available \<noteq> #{} \<leadsto> #c \<notin> set<sched> \<or> (\<exists>y. #(y < i) \<and> #y = inductor c \<and> #c \<in> set<sched>))" .
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
    proof (intro wf_imp_ex_leadsto [OF wf_finite_psubset WF1_SchedulingAllocator_states])
      show "\<turnstile> SchedulingAllocator \<longrightarrow> WF(\<exists>S. id<$unsat, #c> = #{} \<and> id<$alloc, #c> = #S \<and> Return c S)_vars"
        by (auto simp add: SchedulingAllocator_def ReturnFair_def)
      fix S s t
      assume s: "s \<Turnstile> #S \<noteq> #{} \<and> id<unsat, #c> = #{} \<and> id<alloc, #c> = #S"
        and s_Safety: "s \<Turnstile> Safety" and Next: "(s, t) \<Turnstile> [Next]_vars"

      have simp1: "(ACT (<\<exists>S. id<$unsat, #c> = #{} \<and> id<$alloc, #c> = #S \<and> Return c S>_vars))
        = (ACT (\<exists>S. id<$unsat, #c> = #{} \<and> id<$alloc, #c> = #S \<and> <Return c S>_vars))"
        by (auto simp add: angle_def)

      show "s \<Turnstile> Enabled (<\<exists>S. id<$unsat, #c> = #{} \<and> id<$alloc, #c> = #S \<and> Return c S>_vars)"
        unfolding simp1 angle_Return using s
      proof (intro enabled_exI enabled_guard_conjI enabled_ReturnI)
        show "alloc s c \<subseteq> alloc s c" by simp
      qed auto

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