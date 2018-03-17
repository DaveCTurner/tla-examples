theory SimpleAllocator
  imports Prelims
begin

locale SimpleAllocator =
  (* variables *)
  fixes unsat :: "(Client \<Rightarrow> Resource set) stfun"
  fixes alloc :: "(Client \<Rightarrow> Resource set) stfun"
  assumes bv: "basevars (unsat, alloc)"
    (* set of available resources *)
  fixes available :: "Resource set stfun"
  defines "available s \<equiv> - (\<Union>c. alloc s c)"
    (* initial state *)
  fixes InitState :: stpred
  defines "InitState \<equiv> PRED (\<forall>c. id<alloc,#c> = #{} \<and> id<unsat,#c> = #{})"
    (* client requests resources *)
  fixes Request :: "Client \<Rightarrow> Resource set \<Rightarrow> action"
  defines "Request c S \<equiv> ACT #S \<noteq> #{} \<and> id<$unsat,#c> = #{} \<and> id<$alloc,#c> = #{}
                    \<and> #(finite S)
                    \<and> updated unsat c (add S)
                    \<and> unchanged alloc"
    (* allocator allocates resources *)
  fixes Allocate :: "Client \<Rightarrow> Resource set \<Rightarrow> action"
  defines "Allocate c S \<equiv> ACT (#S \<noteq> #{} \<and> (#S \<subseteq> ($available \<inter> id<$unsat,#c>))
                    \<and> (updated alloc c (add S))
                    \<and> (updated unsat c (del S)))"
    (* client returns resources *)
  fixes Return :: "Client \<Rightarrow> Resource set \<Rightarrow> action"
  defines "Return c S \<equiv> ACT (#S \<noteq> #{} \<and> #S \<subseteq> id<$alloc,#c>
                    \<and> updated alloc c (del S)
                    \<and> unchanged unsat)"
    (* next-state relation *)
  fixes Next :: action
  defines "Next \<equiv> ACT (\<exists> c S. Request c S \<or> Allocate c S \<or> Return c S)"
    (* fairness of Return *)
  fixes ReturnFair :: "Client \<Rightarrow> temporal"
  defines "ReturnFair c \<equiv> TEMP WF(\<exists>S. id<$alloc,#c> = #S \<and> Return c S)_(unsat,alloc)"
    (* fairness of Allocate *)
  fixes AllocateFair :: "Client \<Rightarrow> temporal"
  defines "AllocateFair c \<equiv> TEMP SF(\<exists>S. Allocate c S)_(unsat,alloc)"
    (* full specification *)
  fixes SimpleAllocator :: temporal
  defines "SimpleAllocator \<equiv> TEMP (Init InitState \<and> \<box>[Next]_(unsat,alloc) \<and>  (\<forall>c. ReturnFair c) \<and> (\<forall>c. AllocateFair c))"
    (* mutual exclusion safety property *)
  fixes MutualExclusion :: stpred
  defines "MutualExclusion \<equiv> PRED \<forall> c1 c2. #c1 \<noteq> #c2 \<longrightarrow> id<alloc,#c1> \<inter> id<alloc,#c2> = #{}"
    (* finiteness safety property *)
  fixes FiniteRequests :: stpred
  defines "FiniteRequests \<equiv> PRED \<forall> c. \<exists>S. id<unsat,#c> = #S \<and> #(finite S)"
    (* overall safety property *)
  fixes Safety :: stpred
  defines "Safety \<equiv> PRED (MutualExclusion \<and> FiniteRequests)"
    (* allocation liveness property *)
  fixes Liveness :: temporal
  defines "Liveness \<equiv> TEMP (\<forall> c r. #r \<in> id<unsat,#c> \<leadsto> #r \<in> id<alloc,#c>)"

context SimpleAllocator
begin

theorem safety: "\<turnstile> SimpleAllocator \<longrightarrow> \<box>Safety"
proof invariant
  fix sigma
  assume sigma: "sigma \<Turnstile> SimpleAllocator"

  from sigma show "sigma \<Turnstile> Init Safety"
    by (auto simp add: Safety_def FiniteRequests_def MutualExclusion_def SimpleAllocator_def InitState_def Init_def)

  show "sigma \<Turnstile> stable Safety"
  proof (intro Stable)
    from sigma show "sigma \<Turnstile> \<box>[Next]_(unsat,alloc)" by (simp add: SimpleAllocator_def)

    show "\<turnstile> $Safety \<and> [Next]_(unsat, alloc) \<longrightarrow> Safety$"
    proof (intro actionI temp_impI, clarsimp)
      fix s t
      assume s: "s \<Turnstile> Safety" and st: "(s,t) \<Turnstile> [Next]_(unsat, alloc)"

      show "t \<Turnstile> Safety"
      proof (cases "(s,t) \<Turnstile> unchanged (unsat,alloc)")
        case True with s show ?thesis
          by (auto simp add: Safety_def MutualExclusion_def FiniteRequests_def)
      next
        case False
        with st have st: "(s,t) \<Turnstile> Next" by (auto simp add: square_def)
        then obtain c S where "((s,t) \<Turnstile> Request c S) \<or> ((s,t) \<Turnstile> Allocate c S) \<or> ((s,t) \<Turnstile> Return c S)"
          by (auto simp add: Next_def)
        thus ?thesis
        proof (elim disjE)
          assume "(s,t) \<Turnstile> Request c S"
          with s show ?thesis
            by (auto simp add: Safety_def MutualExclusion_def Request_def FiniteRequests_def updated_def add_def modifyAt_def)
        next
          assume "(s,t) \<Turnstile> Allocate c S"
          with s show ?thesis
            by (auto simp add: Safety_def MutualExclusion_def Allocate_def available_def updated_def modifyAt_def add_def FiniteRequests_def del_def)
        next
          assume "(s,t) \<Turnstile> Return c S" with s show ?thesis
            by (auto simp add: Safety_def MutualExclusion_def FiniteRequests_def Return_def modifyAt_def updated_def del_def)
        qed
      qed
    qed
  qed
qed

lemma infinitely_often_available: "\<turnstile> SimpleAllocator \<longrightarrow> \<box>\<diamond>(#r \<in> available)"
proof (intro unstable_implies_infinitely_often)
  have "\<turnstile> SimpleAllocator \<longrightarrow> (#r \<notin> available \<leadsto> (\<exists>c. #r \<in> id<alloc,#c>))"
    by (intro imp_imp_leadsto, auto simp add: available_def)
  also have "\<turnstile> SimpleAllocator \<longrightarrow> ((\<exists>c. #r \<in> id<alloc,#c>) \<leadsto> #r \<in> available)"
  proof (intro imp_exists_leadstoI)
    fix c

    define SqN where "SqN \<equiv> ACT [Next]_(unsat,alloc)"
    define Saf where "Saf \<equiv> ACT $Safety"
    define E   where "E \<equiv> ACT (\<exists>S. id<$alloc,#c> = #S \<and> Return c S)"
    define L   where "L \<equiv> TEMP WF(E)_(unsat,alloc)"
    define P   where "P \<equiv> PRED (#r \<in> id<alloc, #c>)"
    define Q   where "Q \<equiv> PRED (#r \<in> available)"

    have "\<turnstile> SimpleAllocator \<longrightarrow> \<box>(SqN \<and> Saf) \<and> L"
    proof (intro temp_imp_conjI temp_imp_box_conjI)
      show "\<turnstile> SimpleAllocator \<longrightarrow> L"
        "\<turnstile> SimpleAllocator \<longrightarrow> \<box>SqN"
        by (auto simp add: SimpleAllocator_def ReturnFair_def L_def SqN_def E_def)
      from safety show "\<turnstile> SimpleAllocator \<longrightarrow> \<box>Saf" by (simp add: more_temp_simps Saf_def)
    qed

    also have "\<turnstile> \<box>(SqN \<and> Saf) \<and> L \<longrightarrow> (P \<leadsto> Q)"
      unfolding L_def
    proof (intro WF1)
      show "\<turnstile> $P \<and> SqN \<and> Saf \<longrightarrow> P$ \<or> Q$"
      proof (intro actionI temp_impI, elim temp_conjE)
        fix s t
        assume "(s,t) \<Turnstile> $P" hence r: "r \<in> alloc s c" by (simp add: P_def)
        assume "(s,t) \<Turnstile> Saf" hence s: "s \<Turnstile> Safety" by (simp add: Saf_def)
        assume B: "(s,t) \<Turnstile> SqN"
        show "(s,t) \<Turnstile> P$ \<or> Q$"
        proof (cases "(s,t) \<Turnstile> unchanged (unsat,alloc)")
          case True with r show ?thesis by (simp add: P_def)
        next
          case False
          with B obtain c' S where "((s,t) \<Turnstile> Request c' S) \<or> ((s,t) \<Turnstile> Allocate c' S) \<or> ((s,t) \<Turnstile> Return c' S)"
            by (auto simp add: square_def Next_def SqN_def)
          thus ?thesis
          proof (elim disjE)
            assume "(s,t) \<Turnstile> Request c' S"
            with r show ?thesis by (auto simp add: Request_def P_def)
          next
            assume "(s,t) \<Turnstile> Allocate c' S"
            with r show ?thesis
              by (auto simp add: Allocate_def updated_def add_def P_def modifyAt_def)
          next
            assume "(s,t) \<Turnstile> Return c' S"
            hence [simp]: "\<And>c''. alloc t c'' = (if c' = c'' then del S else id) (alloc s c'')"
              by (simp add: updated_def Return_def)
            from r s show ?thesis
              by (auto simp add: available_def del_def Safety_def MutualExclusion_def P_def Q_def)
          qed
        qed
      qed

      show "\<turnstile> ($P \<and> SqN \<and> Saf) \<and> <E>_(unsat, alloc) \<longrightarrow> Q$"
      proof (intro actionI temp_impI, elim temp_conjE)
        fix s t
        assume "(s,t) \<Turnstile> <E>_(unsat, alloc)"
        hence [simp]: "\<And>c'. alloc t c' = (if c = c' then del (alloc s c) else id) (alloc s c')"
          by (auto simp add: angle_def Return_def E_def updated_def)

        assume "(s,t) \<Turnstile> Saf" hence mutex: "s \<Turnstile> MutualExclusion" by (simp add: Saf_def Safety_def)
        assume "(s,t) \<Turnstile> $P"
        with mutex show "(s,t) \<Turnstile> Q$"
          by (auto simp add: P_def Q_def available_def del_def MutualExclusion_def)
      qed

      show "\<turnstile> $P \<and> SqN \<and> Saf \<longrightarrow> $Enabled (<E>_(unsat, alloc))"
      proof (intro actionI temp_impI, elim temp_conjE)
        fix s t
        assume "(s,t) \<Turnstile> ($P)" hence r: "r \<in> alloc s c" by (simp add: P_def)

        from basevars [OF bv]
        obtain u where
          "alloc u = (\<lambda>a'. (if c = a' then del (alloc s c) else id) (alloc s a'))"
          and u: "unsat u = unsat s" by auto

        hence [simp]: "\<And>c'. alloc u c' = (if c = c' then del (alloc s c) else id) (alloc s c')" by auto

        from r have "alloc u c \<noteq> alloc s c" by (auto simp add: del_def)
        hence ne: "alloc u \<noteq> alloc s" by force

        from u ne r show "(s,t) \<Turnstile> $Enabled (<E>_(unsat, alloc))"
          by (simp add: enabled_def angle_def E_def, unfold Return_def, intro exI [where x = u],
              auto simp add: updated_def, intro ext, auto simp add: modifyAt_def)
      qed
    qed

    finally show "\<turnstile> SimpleAllocator \<longrightarrow> (#r \<in> id<alloc, #c> \<leadsto> #r \<in> available)"
      by (simp add: P_def Q_def)
  qed
  finally show "\<turnstile> SimpleAllocator \<longrightarrow> (#r \<notin> available \<leadsto> #r \<in> available)".
qed

definition isWaitingFor :: "Client \<Rightarrow> Resource \<Rightarrow> Resource set \<Rightarrow> stpred"
  where "isWaitingFor c r S \<equiv> PRED id<unsat,#c> = #S \<and> #r \<in> #S"

definition hasResource :: "Client \<Rightarrow> Resource \<Rightarrow> stpred"
  where "hasResource c r \<equiv> PRED #r \<in> id<alloc,#c>"

definition less_finite_Resource_set where "less_finite_Resource_set \<equiv> {(S1 :: Resource set, S2). finite S2 \<and> S1 \<subset> S2}"

lemma wf_less_finite_Resource_set: "wf less_finite_Resource_set"
  unfolding less_finite_Resource_set_def by (intro wf_less_finite)

lemma less_Resource_set_simp[simp]:
  "((S1,S2) \<in> less_finite_Resource_set) = ((S1 \<subset> S2) \<and> finite S2)"
  by (auto simp add: less_finite_Resource_set_def)

lemma Liveness: "\<turnstile> SimpleAllocator \<longrightarrow> Liveness" unfolding Liveness_def
proof (intro imp_forall)
  fix c r

  define N   where "N  \<equiv> ACT [Next]_(unsat,alloc)"
  define A   where "A  \<equiv> ACT (\<exists>S. Allocate c S)"
  define F   where "F  \<equiv> TEMP (\<diamond>(#r \<in> available) \<and> \<box>Safety)"
  define Sp  where "Sp \<equiv> TEMP \<box>N \<and> SF(A)_(unsat,alloc) \<and> \<box>F"

  from safety
  have "\<turnstile> SimpleAllocator \<longrightarrow> Sp"
    unfolding Sp_def
  proof (intro temp_imp_conjI)
    show "\<turnstile> SimpleAllocator \<longrightarrow> \<box>N" by (auto simp add: N_def SimpleAllocator_def)
    show "\<turnstile> SimpleAllocator \<longrightarrow> SF(A)_(unsat, alloc)"
      by (auto simp add: A_def SimpleAllocator_def AllocateFair_def)

    from infinitely_often_available split_box_conj boxInit_stp safety
    show "\<turnstile> SimpleAllocator \<longrightarrow> \<box>F"
      unfolding F_def by (auto simp add: Valid_def more_temp_simps)
  qed

  also have "\<turnstile> Sp \<longrightarrow> (#r \<in> id<unsat, #c> \<leadsto> (\<exists>S. isWaitingFor c r S))"
    unfolding isWaitingFor_def
    by (intro imp_imp_leadsto, auto)

  moreover have "\<turnstile> Sp \<longrightarrow> ((\<exists>S. isWaitingFor c r S) \<leadsto> hasResource c r)"
  proof (intro imp_exists_leadstoI wf_imp_leadsto[where G = "hasResource c r", OF wf_less_finite_Resource_set], simp)
    fix S0
    define P where "P \<equiv> PRED isWaitingFor c r S0 \<and> #(finite S0)"

    have "\<turnstile> Sp \<longrightarrow> (isWaitingFor c r S0 \<leadsto> P)"
    proof (intro imp_box_imp_leadsto)
      have "\<turnstile> Sp \<longrightarrow> \<box>FiniteRequests"
        unfolding Sp_def F_def Safety_def by (auto simp add: more_temp_simps)

      also have "\<turnstile> \<box>FiniteRequests \<longrightarrow> \<box>(isWaitingFor c r S0 \<longrightarrow> P)"
        by (intro STL4, auto simp add: FiniteRequests_def isWaitingFor_def P_def)

      finally show  "\<turnstile> Sp \<longrightarrow> \<box>(isWaitingFor c r S0 \<longrightarrow> P)".
    qed

    also have "\<turnstile> Sp \<longrightarrow> (P \<leadsto> hasResource c r \<or> (\<exists>y. #(y \<subset> S0 \<and> finite S0) \<and> isWaitingFor c r y))"
      unfolding Sp_def
    proof (intro SF1)
      show "\<turnstile> $P \<and> N \<longrightarrow> P$ \<or> (hasResource c r \<or> (\<exists>y. #(y \<subset> S0 \<and> finite S0) \<and> isWaitingFor c r y))$"
        unfolding N_def square_def
      proof (intro actionI temp_impI, elim temp_conjE temp_disjE)
        fix s t
        assume "(s,t) \<Turnstile> $P" "(s,t) \<Turnstile> unchanged (unsat, alloc)"
        thus "(s,t) \<Turnstile> P$ \<or> (hasResource c r \<or> (\<exists>y. #(y \<subset> S0 \<and> finite S0) \<and> isWaitingFor c r y))$"
          by (auto simp add: isWaitingFor_def P_def)
      next
        fix s t
        assume "(s,t) \<Turnstile> $P"
        hence waiting: "s \<Turnstile> isWaitingFor c r S0" and finite_S0: "finite S0" unfolding P_def by auto
        assume "(s,t) \<Turnstile> Next"
        thus "(s,t) \<Turnstile> P$ \<or> (hasResource c r \<or> (\<exists>y. #(y \<subset> S0 \<and> finite S0) \<and> isWaitingFor c r y))$"
        proof (unfold Next_def, elim temp_exE temp_disjE)
          fix c' S
          assume "(s,t) \<Turnstile> Request c' S"
          with waiting have "t \<Turnstile> isWaitingFor c r S0"
            by (auto simp add: isWaitingFor_def Request_def updated_def modifyAt_def)
          with finite_S0 show ?thesis unfolding P_def by simp
        next
          fix c' S
          assume "(s,t) \<Turnstile> Return c' S"
          with waiting have "t \<Turnstile> isWaitingFor c r S0"
            by (auto simp add: isWaitingFor_def Return_def)
          with finite_S0 show ?thesis unfolding P_def by simp
        next
          fix c' S
          assume Allocate: "(s,t) \<Turnstile> Allocate c' S"
          show ?thesis
          proof (cases "c = c'")
            case False
            with waiting Allocate have "t \<Turnstile> isWaitingFor c r S0"
              by (auto simp add: isWaitingFor_def Allocate_def updated_def)
            with finite_S0 show ?thesis unfolding P_def by simp
          next
            case True
            with Allocate have Allocate: "(s,t) \<Turnstile> Allocate c S" by simp

            show ?thesis
            proof (cases "r \<in> S")
              case False
              with waiting Allocate
              have "(s,t) \<Turnstile> (isWaitingFor c r (S0-S))$"
                by (auto simp add: Allocate_def updated_def isWaitingFor_def)
              hence "(s,t) \<Turnstile> (\<exists>y. #(y \<subset> S0 \<and> finite S0) \<and> isWaitingFor c r y)$"
              proof (intro action_afterI temp_exI [of _ "S0-S"] temp_conjI, auto)
                assume "S0-S = S0" with Allocate waiting
                show False by (auto simp add: isWaitingFor_def Allocate_def)
              qed (intro finite_S0)
              thus ?thesis by simp
            next
              case True
              with Allocate have "t \<Turnstile> hasResource c r"
                by (auto simp add: Allocate_def hasResource_def updated_def)
              thus ?thesis by simp
            qed
          qed
        qed
      qed

      have "\<turnstile> (($P \<and> N) \<and> <A>_(unsat, alloc))
        \<longrightarrow> (\<exists>S. $isWaitingFor c r S0 \<and> $#(finite S0) \<and> Allocate c S)" unfolding P_def A_def angle_def by auto
      also have "\<turnstile> (\<exists>S. $isWaitingFor c r S0 \<and> $#(finite S0) \<and> Allocate c S)
        \<longrightarrow> ((hasResource c r \<or> (\<exists>y. #(y \<subset> S0 \<and> finite S0) \<and> isWaitingFor c r y))$)"
      proof (intro temp_ex_impI)
        fix S
        show "\<turnstile> $isWaitingFor c r S0 \<and> $#(finite S0) \<and> Allocate c S \<longrightarrow> (hasResource c r \<or> (\<exists>y. #(y \<subset> S0 \<and> finite S0) \<and> isWaitingFor c r y))$"
        proof (cases "r \<in> S")
          case True
          hence "\<turnstile> $isWaitingFor c r S0 \<and> Allocate c S \<longrightarrow> (hasResource c r)$"
            by (auto simp add: isWaitingFor_def Allocate_def hasResource_def updated_def)
          thus ?thesis by auto
        next
          case False
          hence "\<turnstile> $isWaitingFor c r S0 \<and> Allocate c S \<longrightarrow> (isWaitingFor c r (S0-S))$"
            by (auto simp add: isWaitingFor_def Allocate_def updated_def)
          moreover from False have "\<turnstile> $isWaitingFor c r S0 \<and> Allocate c S \<longrightarrow> #(S0-S \<subset> S0)"
            by (auto simp add: isWaitingFor_def Allocate_def updated_def available_def, blast)
          ultimately show ?thesis
            apply auto
            by (smt Valid_def unl_after unl_before unl_con unl_lift2)
        qed
      qed
      finally show "\<turnstile> ($P \<and> N) \<and> <A>_(unsat, alloc) \<longrightarrow> (hasResource c r \<or> (\<exists>y. #(y \<subset> S0 \<and> finite S0) \<and> isWaitingFor c r y))$".

      have "\<turnstile> \<box>P \<and> \<box>N \<and> \<box>F \<longrightarrow> (\<box>P \<and> \<box>\<diamond>(#r \<in> available))"
        by (auto simp add: isWaitingFor_def F_def more_temp_simps split_box_conj)

      also have "\<turnstile> (\<box>P \<and> \<box>\<diamond>(#r \<in> available)) \<longrightarrow> \<diamond>(P \<and> #r \<in> available)"
        by (intro imp_infinitely_often_implies_eventually box_conj_box_dmd)

      also have "\<turnstile> \<diamond>(P \<and> #r \<in> available) \<longrightarrow> \<diamond>(Enabled (<A>_(unsat, alloc)))"
      proof (intro DmdImpl, intro intI temp_impI, elim temp_conjE)
        fix w
        assume "w \<Turnstile> P" hence w: "w \<Turnstile> isWaitingFor c r S0" "finite S0" by (simp_all add: P_def)
        assume "w \<Turnstile> #r \<in> available" note w = w this

        from basevars [OF bv]
        obtain u where u:
          "alloc u = modifyAt (alloc w) c (add {r})"
          "unsat u = modifyAt (unsat w) c (del {r})" by auto

        show "w \<Turnstile> Enabled (<A>_(unsat, alloc))"
        proof (auto simp add: angle_def enabled_def A_def Allocate_def updated_def modifyAt_def,
            intro exI [of _ u] conjI exI [of _ "{r}"] u impI)
          from w show "{r} \<noteq> {}" "{r} \<subseteq> available w" "{r} \<subseteq> unsat w c"
            by (auto simp add: isWaitingFor_def)

          assume "unsat u = unsat w"
          hence "unsat u c = unsat w c" by simp
          with u w show "alloc u \<noteq> alloc w"
            by (auto simp add: isWaitingFor_def)
        qed
      qed
      finally show "\<turnstile> \<box>P \<and> \<box>N \<and> \<box>F \<longrightarrow> \<diamond>Enabled (<A>_(unsat, alloc))" .
    qed
    finally show "\<turnstile> Sp \<longrightarrow> (isWaitingFor c r S0 \<leadsto> hasResource c r \<or> (\<exists>y. #(y \<subset> S0 \<and> finite S0) \<and> isWaitingFor c r y))".
  qed
  ultimately show "\<turnstile> SimpleAllocator \<longrightarrow> (#r \<in> id<unsat, #c> \<leadsto> #r \<in> id<alloc, #c>)"
    unfolding hasResource_def
    by (meson imp_leadsto_transitive temp_imp_trans)
qed

end

end