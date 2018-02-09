theory EWD840
  imports "HOL-TLA.TLA"
begin

section Utilities

text \<open>A handful of general lemmas that were useful along the way.\<close>

lemma temp_impI:
  assumes "sigma \<Turnstile> P \<Longrightarrow> sigma \<Turnstile> Q"
  shows "sigma \<Turnstile> P \<longrightarrow> Q"
  using assms by simp

lemma imp_leadsto_reflexive: "\<turnstile> S \<longrightarrow> (F \<leadsto> F)" using LatticeReflexivity [where F = F] by auto

lemma imp_leadsto_transitive:
  assumes "\<turnstile> S \<longrightarrow> (F \<leadsto> G)" "\<turnstile> S \<longrightarrow> (G \<leadsto> H)"
  shows "\<turnstile> S \<longrightarrow> (F \<leadsto> H)"
proof (intro tempI temp_impI)
  fix sigma
  assume S: "S sigma"
  with assms have 1: "sigma \<Turnstile> (F \<leadsto> G)" "sigma \<Turnstile> (G \<leadsto> H)"
    by (auto simp add: Valid_def)

  from 1 LatticeTransitivity [where F = F and G = G and H = H]
  show "sigma \<Turnstile> F \<leadsto> H"
    by (auto simp add: Valid_def)
qed

lemma imp_leadsto_diamond:
  assumes "\<turnstile> S \<longrightarrow> (A \<leadsto> (B \<or> C))"
  assumes "\<turnstile> S \<longrightarrow> (B \<leadsto> D)"
  assumes "\<turnstile> S \<longrightarrow> (C \<leadsto> D)"
  shows   "\<turnstile> S \<longrightarrow> (A \<leadsto> D)"
proof (intro tempI temp_impI)
  fix sigma
  assume S: "sigma \<Turnstile> S"
  with assms have
    ABC: "sigma \<Turnstile> A \<leadsto> (B \<or> C)" and
    BD:  "sigma \<Turnstile> B \<leadsto> D" and
    CD:  "sigma \<Turnstile> C \<leadsto> D"
    by (auto simp add: Valid_def)
  with LatticeDiamond [where A = A and B = B and C = C and D = D]
  show "sigma \<Turnstile> A \<leadsto> D"
    by (auto simp add: Valid_def)
qed

lemma temp_conj_eq_imp:
  assumes "\<turnstile> P \<longrightarrow> (Q = R)"
  shows "\<turnstile> (P \<and> Q) = (P \<and> R)"
  using assms by (auto simp add: Valid_def)

text \<open>The following lemma is particularly useful for a system that makes
some progress which either reaches the desired state directly or which leaves it in
a state that is definitely not the desired state but from which it can reach the desired state via
some further progress.\<close>

lemma imp_leadsto_triangle_excl:
  assumes AB: "\<turnstile> S \<longrightarrow> (A \<leadsto> B)"
  assumes BC: "\<turnstile> S \<longrightarrow> ((B \<and> \<not>C) \<leadsto> C)"
  shows "\<turnstile> S \<longrightarrow> (A \<leadsto> C)"
proof -
  have "\<turnstile> ((B \<and> \<not>C) \<or> (B \<and> C)) = B" by auto
  from inteq_reflection [OF this] AB have ABCBC: "\<turnstile> S \<longrightarrow> (A \<leadsto> ((B \<and> \<not>C) \<or> (B \<and> C)))" by simp

  show ?thesis
  proof (intro imp_leadsto_diamond [OF ABCBC] BC)
    from ImplLeadsto_simple [where F = "LIFT (B \<and> C)"]
    show "\<turnstile> S \<longrightarrow> (B \<and> C \<leadsto> C)"
      by (auto simp add: Valid_def)
  qed
qed

text \<open>An action that updates a single value of a function.\<close>

definition updatedFun :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> 'b trfun \<Rightarrow> action" where
  "updatedFun f x v \<equiv> ACT (\<forall>n. id<f$,#n> = (if #n = #x then v else id<$f,#n>))"

section Nodes

text \<open>There is a fixed, finite, set of nodes, which are numbered. Introduce a distinct type
for node identifiers, and an ordering relation, and an induction principle.\<close>

axiomatization NodeCount :: nat where NodeCount_positive: "NodeCount > 0"

typedef Node = "{0..<NodeCount}" using NodeCount_positive by auto

definition FirstNode    :: Node where "FirstNode == Abs_Node 0"
definition LastNode     :: Node where "LastNode  == Abs_Node (NodeCount-1)"
definition PreviousNode :: "Node \<Rightarrow> Node" where "PreviousNode == \<lambda>n. Abs_Node (Rep_Node n - 1)"

instantiation Node :: linorder
begin
definition less_eq_Node :: "Node \<Rightarrow> Node \<Rightarrow> bool" where "n \<le> m \<equiv> Rep_Node n \<le> Rep_Node m"
definition less_Node    :: "Node \<Rightarrow> Node \<Rightarrow> bool" where "n < m \<equiv> Rep_Node n < Rep_Node m"

instance proof
  show "\<And>(x::Node) y. (x < y) = (x \<le> y \<and> \<not> y \<le> x)" using less_Node_def less_eq_Node_def by force
  show "\<And>(x::Node). x \<le> x" using less_eq_Node_def by force
  show "\<And>(x::Node) y z. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" using less_eq_Node_def by force
  show "\<And>(x::Node) y. x \<le> y \<or> y \<le> x" using less_eq_Node_def by force
  show "\<And>(x::Node) y. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" using less_Node_def less_eq_Node_def
    by (simp add: Rep_Node_inject)
qed
end

lemma PreviousNode_fixed_point:
  assumes "n = PreviousNode n"
  shows "n = FirstNode"
  using assms
  unfolding PreviousNode_def FirstNode_def
  by (metis Abs_Node_inject One_nat_def Rep_Node Rep_Node_inverse atLeastLessThan_iff cancel_comm_monoid_add_class.diff_cancel diff_Suc_less diff_le_self le_less_trans le_neq_implies_less not_le)

lemma Node_gt_PreviousNode:
  assumes "n \<noteq> FirstNode"
  shows "m > (PreviousNode n) = (m > n \<or> m = n)"
  using assms unfolding PreviousNode_def less_Node_def FirstNode_def
  by (smt Abs_Node_inverse Rep_Node Rep_Node_inject atLeastLessThan_iff diff_Suc_1 diff_is_0_eq' diff_le_self le_add_diff_inverse less_Suc_eq_le not_le_imp_less not_less_iff_gr_or_eq)

lemma Node_gt_ne: "(m::Node) > n \<Longrightarrow> m \<noteq> n" unfolding less_Node_def by blast

lemma Node_gt_LastNode [simp]: "n > LastNode = False"
  unfolding LastNode_def less_Node_def
  using Abs_Node_inverse NodeCount_positive Rep_Node not_less_eq by auto

lemma Node_induct [case_names FirstNode PreviousNode]:
  assumes FirstNode: "P FirstNode"
  assumes PreviousNode: "\<And>n. n \<noteq> FirstNode \<Longrightarrow> P (PreviousNode n) \<Longrightarrow> P n"
  shows "P n"
proof -
  define n_num where "n_num == Rep_Node n"
  have n_eq: "n = Abs_Node n_num"
    by (simp add: Rep_Node_inverse n_num_def)

  have "n_num < NodeCount" using Rep_Node n_num_def by auto
  thus ?thesis
    unfolding n_eq
  proof (induct n_num)
    case 0 with FirstNode show ?case by (simp add: FirstNode_def)
  next
    case (Suc n_num)
    hence hyp: "P (Abs_Node n_num)" by auto

    show ?case
    proof (rule PreviousNode)
      show "Abs_Node (Suc n_num) \<noteq> FirstNode" unfolding FirstNode_def
        by (simp add: Abs_Node_inject NodeCount_positive Suc.prems)
      from hyp Suc.prems show " P (PreviousNode (Abs_Node (Suc n_num)))"
        unfolding PreviousNode_def by (simp add: Abs_Node_inverse)
    qed
  qed
qed

datatype TerminationState = MaybeTerminated | NotTerminated

axiomatization
  isNodeActive  :: "(Node \<Rightarrow> bool) stfun" and
  nodeState     :: "(Node \<Rightarrow> TerminationState) stfun" and
  tokenPosition :: "Node stfun" and
  tokenState    :: "TerminationState stfun"
  where
  ewd_basevars: "basevars (isNodeActive, nodeState, tokenPosition, tokenState)"

definition StartState :: stpred where
  "StartState == PRED tokenPosition = #FirstNode \<and> tokenState = #NotTerminated"

definition InitiateProbe :: action where
  "InitiateProbe == ACT
    (($tokenPosition = #FirstNode)
    \<and> ($tokenState = #NotTerminated \<or> id<$nodeState,#FirstNode> = #NotTerminated)
    \<and> tokenPosition$ = #LastNode
    \<and> tokenState$ = #MaybeTerminated
    \<and> (unchanged isNodeActive)
    \<and> (updatedFun nodeState FirstNode (const MaybeTerminated)))"

definition PassToken :: "Node \<Rightarrow> action" where
  "PassToken i == ACT
    (($tokenPosition = #i)
    \<and> ($tokenPosition \<noteq> #FirstNode)
    \<and> (\<not> id<$isNodeActive,#i> \<or> id<$nodeState,#i> = #NotTerminated \<or> $tokenState = #NotTerminated)
    \<and> (tokenPosition$ = PreviousNode<$tokenPosition>)
    \<and> (tokenState$ = (if id<$nodeState,#i> = #NotTerminated then #NotTerminated else $tokenState))
    \<and> (unchanged isNodeActive)
    \<and> (updatedFun nodeState i (const MaybeTerminated)))"

definition SendMsg :: "Node \<Rightarrow> action" where
  "SendMsg i == ACT
    id<$isNodeActive,#i>
    \<and> (\<exists> j. #j \<noteq> #i \<and> (updatedFun isNodeActive j (const True))
                     \<and> (updatedFun nodeState i (ACT if #i < #j then #NotTerminated else id<$nodeState,#i>)))
    \<and> unchanged (tokenPosition, tokenState)"

definition Deactivate :: "Node \<Rightarrow> action" where
  "Deactivate i == ACT
    id<$isNodeActive,#i>
    \<and> (updatedFun isNodeActive i (const False))
    \<and> unchanged (tokenPosition, tokenState, nodeState)"

definition Controlled :: action where
  "Controlled \<equiv> ACT (InitiateProbe \<or> (\<exists> n. PassToken n))"

definition Environment :: action where
  "Environment \<equiv> ACT (\<exists> n. SendMsg n \<or> Deactivate n)"

definition Next :: action where
  "Next \<equiv> ACT (Controlled \<or> Environment)"

definition Fairness :: temporal where
  "Fairness \<equiv> TEMP WF(Controlled)_(isNodeActive,nodeState,tokenPosition,tokenState)"

definition Spec :: temporal where
  "Spec \<equiv> TEMP (Init StartState \<and> \<box>[Next]_(isNodeActive,nodeState,tokenPosition,tokenState) \<and> Fairness)"

definition TerminationDetected :: stpred where
  "TerminationDetected \<equiv> PRED
    (tokenPosition = #FirstNode
    \<and> tokenState = #MaybeTerminated
    \<and> id<nodeState,#FirstNode> = #MaybeTerminated
    \<and> \<not> id<isNodeActive,#FirstNode>)"

lemma angle_Controlled_lifted: "\<turnstile> <Controlled>_(isNodeActive, nodeState, tokenPosition, tokenState) = Controlled"
  unfolding angle_def Controlled_def InitiateProbe_def PassToken_def updatedFun_def
  using PreviousNode_fixed_point by auto

lemmas angle_Controlled = inteq_reflection [OF angle_Controlled_lifted]

lemma basevars_arbitrary:
  assumes "\<And>u. \<lbrakk> tokenPosition u = A; tokenState u = B; isNodeActive u = C; nodeState u = D \<rbrakk> \<Longrightarrow> P"
  shows P
  using assms ewd_basevars unfolding basevars_def surj_def apply auto by metis

lemma enabled_controlled_lifted:
  "\<turnstile> Enabled Controlled
      = (tokenState = #NotTerminated \<or> id<nodeState, tokenPosition> = #NotTerminated \<or> (tokenPosition \<noteq> #FirstNode \<and> \<not> id<isNodeActive, tokenPosition>))"
proof -
  have 1: "\<turnstile> Enabled Controlled = (Enabled InitiateProbe \<or> Enabled (\<exists>n. PassToken n))"
    unfolding Controlled_def
    using enabled_disj by simp

  have 2: "\<turnstile> Enabled InitiateProbe = (tokenPosition = #FirstNode \<and> (tokenState = #NotTerminated \<or> id<nodeState, #FirstNode> = #NotTerminated))"
  proof (intro intI)
    fix w
    show "w \<Turnstile> Enabled InitiateProbe = (tokenPosition = #FirstNode \<and> (tokenState = #NotTerminated \<or> id<nodeState, #FirstNode> = #NotTerminated))"
      apply (rule basevars_arbitrary [of LastNode MaybeTerminated "isNodeActive w" "\<lambda>n. if n = FirstNode then MaybeTerminated else nodeState w n"])
      unfolding InitiateProbe_def enabled_def updatedFun_def
      by auto
  qed

  have 3: "\<turnstile> Enabled (\<exists>n. PassToken n) = ((tokenPosition \<noteq> #FirstNode \<and> (\<not> id<isNodeActive, tokenPosition> \<or> id<nodeState, tokenPosition> = #NotTerminated \<or> tokenState = #NotTerminated)))"
  proof (intro intI)
    fix w
    show "w \<Turnstile> Enabled (\<exists>n. PassToken n) = ((tokenPosition \<noteq> #FirstNode \<and> (\<not> id<isNodeActive, tokenPosition> \<or> id<nodeState, tokenPosition> = #NotTerminated \<or> tokenState = #NotTerminated)))"
      apply (rule basevars_arbitrary [of "PreviousNode (tokenPosition w)" "if nodeState w (tokenPosition w) = NotTerminated then NotTerminated else tokenState w" "isNodeActive w" "\<lambda>n. if n = tokenPosition w then MaybeTerminated else nodeState w n"])
      unfolding PassToken_def enabled_def updatedFun_def
      by auto
  qed

  have 4:
    "\<turnstile> Enabled Controlled = ((tokenPosition = #FirstNode \<and> (tokenState = #NotTerminated \<or> id<nodeState, #FirstNode> = #NotTerminated))
          \<or> (tokenPosition \<noteq> #FirstNode \<and> (\<not> id<isNodeActive, tokenPosition> \<or> id<nodeState, tokenPosition> = #NotTerminated \<or> tokenState = #NotTerminated)))"
    unfolding inteq_reflection [OF 1]
      inteq_reflection [OF 2]
      inteq_reflection [OF 3]
    by auto

  show ?thesis
    unfolding inteq_reflection [OF 4] by auto
qed

lemmas enabled_controlled = inteq_reflection [OF enabled_controlled_lifted]

section Safety

text \<open>The safety property of the algorithm says that termination is detected only if all nodes
are inactive. The proof works by showing that the safety invariant is actually an invariant,
and that this invariant implies the desired safety property.\<close>

definition AllNodesInactive :: stpred where
  "AllNodesInactive \<equiv> PRED (\<forall> n. \<not> id<isNodeActive,#n>)"

definition SafetyInvariant where
  "SafetyInvariant \<equiv> PRED
    (\<forall> n. (tokenPosition < #n) \<longrightarrow> \<not> id<isNodeActive,#n>)
    \<or> (\<exists> n. #n \<le> tokenPosition \<and> id<nodeState,#n> = #NotTerminated)
    \<or> tokenState = #NotTerminated"

lemma safety:
  shows "\<turnstile> Spec \<longrightarrow> \<box>(TerminationDetected \<longrightarrow> AllNodesInactive)"
proof -
  have "\<turnstile> Spec \<longrightarrow> \<box>SafetyInvariant"
  proof invariant
    fix sigma
    assume s: "Spec sigma"
    thus "sigma \<Turnstile> Init SafetyInvariant"
      by (auto simp add: Spec_def SafetyInvariant_def StartState_def Init_def)

    show "sigma \<Turnstile> stable SafetyInvariant"
    proof (intro Stable)
      from s show "sigma \<Turnstile> \<box>[Next]_(isNodeActive, nodeState, tokenPosition, tokenState)"
        by (simp add: Spec_def)

      show "\<turnstile> $SafetyInvariant \<and> [Next]_(isNodeActive, nodeState, tokenPosition, tokenState) \<longrightarrow> SafetyInvariant$"
      proof clarsimp
        fix s t
        assume s: "SafetyInvariant s"
          and st: "(s, t) \<Turnstile> [Next]_(isNodeActive, nodeState, tokenPosition, tokenState)"

        from st have
          "((s, t) \<Turnstile> InitiateProbe)
           \<or> (\<exists>n. (s, t) \<Turnstile> PassToken n)
           \<or> (\<exists>n. (s, t) \<Turnstile> SendMsg n)
           \<or> (\<exists>n. (s, t) \<Turnstile> Deactivate n)
           \<or> ((s, t) \<Turnstile> unchanged (isNodeActive, nodeState, tokenPosition, tokenState))"
          by (auto simp add: square_def Next_def Controlled_def Environment_def)

        thus "SafetyInvariant t"
        proof (elim disjE conjE exE)
          assume "(s, t) \<Turnstile> unchanged (isNodeActive, nodeState, tokenPosition, tokenState)"
          with s show "SafetyInvariant t" by (simp add: SafetyInvariant_def)
        next
          assume "InitiateProbe (s, t)"
          hence step:
                "tokenPosition s = FirstNode" "tokenState s = NotTerminated \<or> nodeState s FirstNode = NotTerminated"
                "tokenPosition t = LastNode" "tokenState t = MaybeTerminated" "isNodeActive t = isNodeActive s"
                "\<And>n. nodeState t n = (if n = FirstNode then MaybeTerminated else nodeState s n)"
            unfolding InitiateProbe_def updatedFun_def
            by auto

          note step_simps[simp] = `tokenPosition s = FirstNode` `tokenPosition t = LastNode` `tokenState t = MaybeTerminated` `isNodeActive t = isNodeActive s`
            `\<And>n. nodeState t n = (if n = FirstNode then MaybeTerminated else nodeState s n)`

          show "SafetyInvariant t"
            unfolding SafetyInvariant_def
            apply (auto simp add: less_Node_def LastNode_def)
            by (metis Abs_Node_inverse Rep_Node Suc_pred atLeastLessThan_iff diff_Suc_less less_or_eq_imp_le neq0_conv not_less_eq)

        next
          fix n assume "Deactivate n (s, t)"
          hence step:
            "tokenPosition t = tokenPosition s" "tokenState t = tokenState s" "nodeState t = nodeState s" "\<And>n. isNodeActive t n \<Longrightarrow> isNodeActive s n"
            unfolding Deactivate_def updatedFun_def apply auto
            by (metis id_apply unl_before unl_con unl_lift2)

          from s show "SafetyInvariant t" by (auto simp add: less_Node_def LastNode_def SafetyInvariant_def step)

        next
          fix sender assume step: "SendMsg sender (s, t)"
          from step have step_simps[simp]: "tokenPosition t = tokenPosition s" "tokenState t = tokenState s" by (auto simp add: SendMsg_def)
          from step have n_active: "isNodeActive s sender" by (simp add: SendMsg_def)

          from step obtain receiver where receiver: "receiver \<noteq> sender"
            "\<And>m. isNodeActive t m = (m = receiver \<or> isNodeActive s m)"
            "\<And>m. nodeState t m = (if m = sender \<and> receiver > sender then NotTerminated else nodeState s m)"
            unfolding SendMsg_def updatedFun_def by auto

          show ?thesis
          proof (cases "receiver < tokenPosition s")
            case False
            with s show ?thesis
              unfolding SafetyInvariant_def less_Node_def
              apply auto
                apply (metis le_less_trans less_Node_def n_active not_le receiver(2) receiver(3))
              by (metis receiver(3))
          next
            case True
            with s receiver show ?thesis unfolding SafetyInvariant_def less_Node_def by fastforce
          qed

        next
          fix n assume step: "PassToken n (s,t)"

          hence step_tokenPosition[simp]: "tokenPosition s = n" "tokenPosition t = PreviousNode n" "n \<noteq> FirstNode" unfolding PassToken_def by auto

          from step have step_active[simp]: "isNodeActive t = isNodeActive s" unfolding PassToken_def by auto

          from step have step_colour: "\<And>m. nodeState t m = (if m = n then MaybeTerminated else nodeState s m)"
            by (simp add: PassToken_def updatedFun_def)

          from step have step_tokenState: "tokenState t = (if nodeState s n = NotTerminated then NotTerminated else tokenState s)"
            unfolding PassToken_def by simp

          show ?thesis
          proof (cases "nodeState s n = NotTerminated \<or> tokenState s = NotTerminated")
            case True with step_tokenState show ?thesis by (auto simp add: SafetyInvariant_def)
          next
            case False
            with TerminationState.exhaust have whites: "nodeState s n = MaybeTerminated" "tokenState s = MaybeTerminated" by auto

            from whites step_colour step_tokenState have step_simps[simp]:
              "nodeState t = nodeState s" "tokenState t = tokenState s" by auto

            from step whites have n_inactive: "\<not>isNodeActive s n" unfolding PassToken_def by auto

            from step_tokenPosition(3)
            have gt1: "\<And>m. m < n = (m < (PreviousNode n) \<or> m = PreviousNode n)"
              using Node_gt_PreviousNode not_less_iff_gr_or_eq by blast

            have gt2: "\<And>m. n < m = ((PreviousNode n) < m \<and> m \<noteq> n)"
              using Node_gt_PreviousNode step_tokenPosition(3) by blast

            from s n_inactive show ?thesis
              unfolding SafetyInvariant_def
              apply (clarsimp simp add: gt1 gt2)
              by (metis TerminationState.simps(2) gt2 leD leI whites(1))
          qed
        qed
      qed
    qed
  qed

  moreover have "\<turnstile> \<box>SafetyInvariant \<longrightarrow> \<box>(TerminationDetected \<longrightarrow> AllNodesInactive)"
    unfolding SafetyInvariant_def
  proof (intro STL4, clarsimp, intro conjI impI)
    fix w
    assume inactive_gt: "\<forall>n. (tokenPosition w < n) \<longrightarrow> \<not> isNodeActive w n"
    show "TerminationDetected w \<Longrightarrow> AllNodesInactive w"
      unfolding TerminationDetected_def AllNodesInactive_def
    proof clarsimp
      fix n assume a: "isNodeActive w n" "tokenPosition w = FirstNode" "\<not> isNodeActive w FirstNode"
      with inactive_gt have "\<not> n > FirstNode" by auto
      hence "n = FirstNode"
        unfolding less_Node_def FirstNode_def
        by (metis Abs_Node_inverse NodeCount_positive Rep_Node Rep_Node_inject atLeastLessThan_iff le_numeral_extra(3) nat_less_le)
      with a show False by simp
    qed
  next
    fix w
    assume "tokenState w = NotTerminated"
    thus "TerminationDetected w \<Longrightarrow> AllNodesInactive w"
      unfolding TerminationDetected_def
      by auto
  next
    fix w
    assume "\<exists>n. (n \<le> tokenPosition w) \<and> nodeState w n = NotTerminated"
    then obtain n where n: "n \<le> tokenPosition w" "nodeState w n = NotTerminated" by auto
    thus "TerminationDetected w \<Longrightarrow> AllNodesInactive w"
      unfolding TerminationDetected_def AllNodesInactive_def
    proof clarsimp
      assume "tokenPosition w = FirstNode" "nodeState w FirstNode = MaybeTerminated"
      with n show False
        by (metis Abs_Node_inverse TerminationState.distinct(2) FirstNode_def NodeCount_positive Rep_Node_inverse atLeastLessThan_iff le_zero_eq less_eq_Node_def)
    qed
  qed

  ultimately show ?thesis by (simp add: Valid_def)
qed

section Liveness

text \<open>When all nodes become inactive the algorithm runs through up to three further distinct
phases before detecting termination. The first phase is simply to return the token to the first
node, without any constraints on its state or the states of the nodes. The second phase
passes the token around the ring once more which sets each node's state to $MaybeTerminated$,
although the token itself may be ``contaminated'' by a $NotTerminated$ state. The third phase
passes the token around the ring one last time to remove any such contamination.\<close>

text \<open>The following predicates correspond to each step of each of these phases.\<close>

definition AllNodesInactiveAndTokenAt where "AllNodesInactiveAndTokenAt n \<equiv> PRED
  (AllNodesInactive \<and> tokenPosition = #n)"

definition NodeCleaningRunAt where "NodeCleaningRunAt n \<equiv> PRED
  (AllNodesInactiveAndTokenAt n
  \<and> id<nodeState,#FirstNode> = #MaybeTerminated
  \<and> (\<forall> m. #n < #m \<longrightarrow> id<nodeState,#m> = #MaybeTerminated))"

definition TokenCleaningRunAt where "TokenCleaningRunAt n \<equiv> PRED
  (AllNodesInactiveAndTokenAt n
  \<and> tokenState = #MaybeTerminated
  \<and> (\<forall> m. id<nodeState,#m> = #MaybeTerminated))"

text \<open>The liveness proof now shows that each phase completes and either detects termination
or leads to the next phase.\<close>

lemma step:
  assumes "\<turnstile> P \<longrightarrow> AllNodesInactive"
  assumes "\<turnstile> P \<longrightarrow> \<not> TerminationDetected"
  assumes "\<turnstile> $P \<and> unchanged (isNodeActive, nodeState, tokenPosition, tokenState) \<longrightarrow> P$"
  assumes "\<turnstile> $P \<and> Controlled \<longrightarrow> Q$"
  shows   "\<turnstile> Spec \<longrightarrow> (P \<leadsto> Q)"
proof -
  have "\<turnstile> (\<box>[Next]_(isNodeActive, nodeState, tokenPosition, tokenState)
    \<and> WF(Controlled)_(isNodeActive, nodeState, tokenPosition, tokenState)) \<longrightarrow> (P \<leadsto> Q)"
  proof (intro WF1)
    from assms have no_Environment: "\<And>s t. s \<Turnstile> P \<Longrightarrow> (s, t) \<Turnstile> Environment \<Longrightarrow> False"
      by (auto simp add: Environment_def AllNodesInactive_def Valid_def SendMsg_def Deactivate_def)

    with assms
    show "\<turnstile> $P \<and> [Next]_(isNodeActive, nodeState, tokenPosition, tokenState) \<longrightarrow> P$ \<or> Q$"
      "\<turnstile> ($P \<and> [Next]_(isNodeActive, nodeState, tokenPosition, tokenState)) \<and> <Controlled>_(isNodeActive, nodeState, tokenPosition, tokenState) \<longrightarrow> Q$"
      "\<turnstile> $P \<and> [Next]_(isNodeActive, nodeState, tokenPosition, tokenState) \<longrightarrow> $Enabled (<Controlled>_(isNodeActive, nodeState, tokenPosition, tokenState))"
      unfolding angle_Controlled enabled_controlled Next_def square_def Valid_def AllNodesInactive_def TerminationDetected_def
        apply simp_all
        apply (meson TerminationState.exhaust, blast)
      by (metis (full_types) TerminationState.exhaust)
  qed

  thus ?thesis
    by (auto simp add: Spec_def Fairness_def)
qed

lemma liveness: "\<turnstile> Spec \<longrightarrow> (AllNodesInactive \<leadsto> TerminationDetected)"
proof -
  note [simp] = TokenCleaningRunAt_def NodeCleaningRunAt_def
            AllNodesInactiveAndTokenAt_def AllNodesInactive_def
            square_def Controlled_def InitiateProbe_def PassToken_def updatedFun_def
            TerminationDetected_def

  have "\<turnstile> Spec \<longrightarrow> (AllNodesInactive \<leadsto> AllNodesInactiveAndTokenAt FirstNode)"
  proof -
    have "\<turnstile> AllNodesInactive = (\<exists>n. AllNodesInactiveAndTokenAt n)" unfolding AllNodesInactiveAndTokenAt_def by auto
    hence "\<turnstile> (AllNodesInactive \<leadsto> AllNodesInactiveAndTokenAt FirstNode)
            = (\<forall>n. (AllNodesInactiveAndTokenAt n \<leadsto> AllNodesInactiveAndTokenAt FirstNode))"
      by (metis inteq_reflection leadsto_exists)

    moreover {
      fix n
      have "\<turnstile> Spec \<longrightarrow> (AllNodesInactiveAndTokenAt n \<leadsto> AllNodesInactiveAndTokenAt FirstNode)"
      proof (induct n rule: Node_induct)
        case FirstNode show ?case by (intro imp_leadsto_reflexive)
      next
        case (PreviousNode n)
        hence "\<turnstile> Spec \<longrightarrow> (AllNodesInactiveAndTokenAt n \<leadsto> AllNodesInactiveAndTokenAt (PreviousNode n))"
          by (intro step, auto)
        with PreviousNode show ?case by (metis imp_leadsto_transitive)
      qed
    }

    ultimately show ?thesis by (auto simp add: Valid_def)
  qed

  moreover have "\<turnstile> Spec \<longrightarrow> ((AllNodesInactiveAndTokenAt FirstNode \<and> \<not> TerminationDetected) \<leadsto> NodeCleaningRunAt LastNode)"
    by (intro step, auto)

  moreover have "\<And>n. \<turnstile> Spec \<longrightarrow> (NodeCleaningRunAt n \<leadsto> NodeCleaningRunAt FirstNode)"
  proof -
    fix n show "?thesis n"
    proof (induct n rule: Node_induct)
      case FirstNode
      with LatticeReflexivity show ?case by auto
    next
      case (PreviousNode n)
      with Node_gt_PreviousNode Node_gt_ne
      have "\<turnstile> Spec \<longrightarrow> (NodeCleaningRunAt n \<leadsto> NodeCleaningRunAt (PreviousNode n))"
        by (intro step, auto)
      with PreviousNode show ?case by (metis imp_leadsto_transitive)
    qed
  qed

  moreover have "\<turnstile> Spec \<longrightarrow> (NodeCleaningRunAt FirstNode \<and> \<not> TerminationDetected \<leadsto> TokenCleaningRunAt LastNode)"
  proof -
    have firstNode_min: "\<And>n. n = FirstNode \<or> FirstNode < n"
      using Abs_Node_inverse FirstNode_def NodeCount_positive le_less less_eq_Node_def by fastforce

    hence "\<turnstile> NodeCleaningRunAt FirstNode
      = (AllNodesInactiveAndTokenAt FirstNode \<and> (\<forall> m. id<nodeState,#m> = #MaybeTerminated))"
      by (auto, force)
    thus ?thesis by (intro step, auto, metis firstNode_min)
  qed

  moreover have "\<And>n. \<turnstile> Spec \<longrightarrow> (TokenCleaningRunAt n \<leadsto> TerminationDetected)"
  proof -
    fix n
    show "?thesis n"
    proof (induct n rule: Node_induct)
      case FirstNode
      have "\<turnstile> TokenCleaningRunAt FirstNode \<longrightarrow> TerminationDetected" by auto
      hence "\<turnstile> TokenCleaningRunAt FirstNode \<leadsto> TerminationDetected"
        using ImplLeadsto_simple by auto
      thus ?case by (auto simp add: ImplLeadsto_simple intI tempD)
    next
      case (PreviousNode n)
      hence "\<turnstile> Spec \<longrightarrow> (TokenCleaningRunAt n \<leadsto> TokenCleaningRunAt (PreviousNode n))"
        by (intro step, auto, blast)
      with PreviousNode show ?case by (metis imp_leadsto_transitive)
    qed
  qed

  ultimately show ?thesis
    by (metis imp_leadsto_transitive imp_leadsto_triangle_excl)
qed

end
