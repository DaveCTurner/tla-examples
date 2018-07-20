theory "EWD-pairings"
  imports Main Real NthRoot "./TLA-Utils" "HOL-Analysis.Product_Vector"
begin

type_synonym point = "real \<times> real"

definition lineseg :: "point \<Rightarrow> point \<Rightarrow> real \<Rightarrow> point"
  where "lineseg p0 p1 l \<equiv> (1-l) *\<^sub>R p0 + l *\<^sub>R p1"

definition closed_01 :: "real set"
  where "closed_01 \<equiv> {x. 0 \<le> x \<and> x \<le> 1}"

definition segment_between :: "point \<Rightarrow> point \<Rightarrow> point set"
  where "segment_between p0 p1 \<equiv> lineseg p0 p1 ` closed_01"

definition segments_cross :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool"
  where "segments_cross r0 b0 r1 b1 \<equiv> segment_between r0 b0 \<inter> segment_between r1 b1 \<noteq> {}"

lemma segment_between_subset: "segment_between p1 p0 \<subseteq> segment_between p0 p1"
proof (intro subsetI)
  fix p assume "p \<in> segment_between p1 p0"
  then obtain lp where p: "p = lineseg p1 p0 lp" and lp: "lp \<in> closed_01" unfolding segment_between_def by auto
  show "p \<in> segment_between p0 p1"
    unfolding p segment_between_def using lp
    by (intro image_eqI [where x = "1 - lp"], auto simp add: lineseg_def closed_01_def)
qed

lemma segment_between_swap[simp]: "segment_between p1 p0 = segment_between p0 p1"
  by (intro equalityI segment_between_subset)

lemma segments_cross_swaps[simp]:
  "segments_cross b0 r0 r1 b1 = segments_cross r0 b0 r1 b1" 
  "segments_cross r0 b0 b1 r1 = segments_cross r0 b0 r1 b1" 
  "segments_cross r1 b1 r0 b0 = segments_cross r0 b0 r1 b1"
  by (auto simp add: segments_cross_def)

definition signedArea :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> real"
  where "signedArea p0 p1 p2 \<equiv> case (p0, p1, p2) of
    ((x0,y0), (x1,y1), (x2,y2)) \<Rightarrow> ((x1-x0)*(y2-y0) - (x2-x0)*(y1-y0))"

lemma signedArea_left_example:  "signedArea (0,0) (1,0) (1, 1) > 0" by (simp add: signedArea_def)
lemma signedArea_right_example: "signedArea (0,0) (1,0) (1,-1) < 0" by (simp add: signedArea_def)

datatype Turn = Left | Right | Collinear

definition turn :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> Turn"
  where "turn p0 p1 p2 \<equiv> if 0 < signedArea p0 p1 p2 then Left else if signedArea p0 p1 p2 < 0 then Right else Collinear"

lemma signedArea_swap: "signedArea p0 p2 p1 = - signedArea p0 p1 p2"
  by (cases p0, cases p1, cases p2, simp add: signedArea_def)

lemma signedArea_rotate1[simp]: "signedArea p0 p1 p2 = signedArea p1 p2 p0"
  unfolding signedArea_def
  by (cases p0, cases p1, cases p2, simp add: left_diff_distrib right_diff_distrib)

lemma signedArea_rotate2[simp]: "signedArea p0 p1 p2 = signedArea p2 p0 p1" by simp

lemma signedArea_trivial[simp]: "signedArea p0 p0 p1 = 0" "signedArea p0 p1 p0 = 0" "signedArea p0 p1 p1 = 0"
  unfolding signedArea_def by (cases p0, cases p1, simp)+

lemma turn_swap: "turn p0 p2 p1 = (case turn p0 p1 p2 of Left \<Rightarrow> Right | Right \<Rightarrow> Left | Collinear \<Rightarrow> Collinear)"
  using signedArea_swap [of p0 p1 p2] unfolding turn_def by simp

lemma turn_Left:      "(turn p0 p1 p2 = Left)      = (0 < signedArea p0 p1 p2)"
  and turn_Right:     "(turn p0 p1 p2 = Right)     = (signedArea p0 p1 p2 < 0)"
  and turn_Collinear: "(turn p0 p1 p2 = Collinear) = (signedArea p0 p1 p2 = 0)"
  by (auto simp add: turn_def linorder_less_linear [of "signedArea p0 p1 p2" 0])

lemma turn_trivial[simp]: "turn p0 p0 p1 = Collinear" "turn p0 p1 p0 = Collinear" "turn p0 p1 p1 = Collinear"
  unfolding turn_def by simp_all

definition collinear :: "point set \<Rightarrow> bool"
  where "collinear ps \<equiv> \<forall> p0 p1 p2. {p0, p1, p2} \<subseteq> ps \<longrightarrow> turn p0 p1 p2 = Collinear"

lemma collinear_singleton[simp]: "collinear {p}" by (simp add: collinear_def)
lemma collinear_doubleton[simp]: "collinear {p0,p1}" by (auto simp add: collinear_def)
lemma collinear_tripleton: "collinear {p0,p1,p2} = (turn p0 p1 p2 = Collinear)"
  unfolding collinear_def
  by (metis empty_iff insert_iff insert_subset order_refl signedArea_rotate2 turn_Collinear turn_swap turn_trivial(1))

lemma collinearI[intro]:
  assumes "\<And>p0 p1 p2. p0 \<in> ps \<Longrightarrow> p1 \<in> ps \<Longrightarrow> p2 \<in> ps \<Longrightarrow> turn p0 p1 p2 = Collinear"
  shows "collinear ps"
  using assms unfolding collinear_def by auto

lemma collinear_subset: "ps \<subseteq> qs \<Longrightarrow> collinear qs \<Longrightarrow> collinear ps" unfolding collinear_def by fastforce

lemma turn_rotate1[simp]: "turn p0 p1 p2 = turn p1 p2 p0" unfolding turn_def by simp

lemma Collinear_lineseg:
  assumes "turn p0 p1 q = Collinear"
  assumes "p0 \<noteq> p1"
  shows "q \<in> range (lineseg p0 p1)"
proof -
  obtain x0 y0 x1 y1 x y where p0: "p0 = (x0,y0)" and p1: "p1 = (x1,y1)" and q: "q = (x,y)" by fastforce

  from assms have gradient_eq: "(x1-x0)*(y-y0) = (x-x0)*(y1-y0)" unfolding turn_Collinear signedArea_def by (auto simp add: p0 p1 q)

  define l where "l \<equiv> if x1 = x0 then (y-y0) / (y1-y0) else (x-x0) / (x1-x0)"

  have xl: "(x1-x0) * l = (x-x0)" using assms gradient_eq by (auto simp add: l_def p0 p1)
  have yl: "(y1-y0) * l = (y-y0)" using assms gradient_eq
    apply (auto simp add: l_def p0 p1)
    by (metis eq_iff_diff_eq_0 linordered_field_class.sign_simps(24) nonzero_mult_div_cancel_left)+

  from xl yl have "q - p0 = l *\<^sub>R (p1 - p0)" by (auto simp add: p0 p1 q mult.commute)
  thus ?thesis
    apply (intro image_eqI [where x = l], auto simp add: lineseg_def)
    by (smt add.assoc add.commute diff_add_cancel real_vector.scale_right_diff_distrib scaleR_collapse)
qed

lemma lineseg_collinear:
  assumes "collinear ps"
  assumes "p1 \<in> ps" "p2 \<in> ps" "p1 \<noteq> p2"
  shows "ps \<subseteq> range (lineseg p1 p2)"
proof (intro subsetI)
  fix p3 assume "p3 \<in> ps"
  with assms have "turn p1 p2 p3 = Collinear" unfolding collinear_def by blast
  with assms show "p3 \<in> range (lineseg p1 p2)" by (metis Collinear_lineseg)
qed

lemma collinear_lineseg: "collinear (range (lineseg p0 p1))"
proof (intro collinearI, elim imageE, simp)
  fix la lb lc
  show "turn (lineseg p0 p1 la) (lineseg p0 p1 lb) (lineseg p0 p1 lc) = Collinear"
    by (cases p0, cases p1, auto simp add: turn_Collinear lineseg_def signedArea_def left_diff_distrib right_diff_distrib distrib_left distrib_right)
qed

lemma collinear_insert:
  assumes "p \<in> range (lineseg p0 p1)"
  assumes "p0 \<in> ps" "p1 \<in> ps"
  assumes "collinear ps"
  shows "collinear (insert p ps)"
proof (cases "p0 = p1")
  case True with assms show ?thesis by (auto simp add: lineseg_def insert_absorb)
next
  case False
  have "ps \<subseteq> range (lineseg p0 p1)" by (intro lineseg_collinear assms False)
  with assms have "insert p ps \<subseteq> range (lineseg p0 p1)" by auto
  from collinear_subset [OF this collinear_lineseg] show ?thesis by simp
qed

lemma range_lineseg_p0:
  "p0 \<in> range (lineseg p0 p1)" by (intro image_eqI [where x = 0], auto simp add: lineseg_def)

lemma range_lineseg_p1:
  "p1 \<in> range (lineseg p0 p1)" by (intro image_eqI [where x = 1], auto simp add: lineseg_def)

lemma lineseg_Collinear:
  assumes "q \<in> range (lineseg p0 p1)"
  shows "turn p0 p1 q = Collinear"
  using range_lineseg_p0 range_lineseg_p1 assms collinear_lineseg unfolding collinear_def by blast

lemma Collinear_trans:
  assumes pq: "p \<noteq> q"
  assumes pqr: "turn p q r = Collinear"
  assumes pqs: "turn p q s = Collinear"
  shows "turn p r s = Collinear"
proof -
  from Collinear_lineseg [OF pqr pq] obtain lr where lr: "r = lineseg p q lr" by auto
  from Collinear_lineseg [OF pqs pq] obtain ls where ls: "s = lineseg p q ls" by auto

  from lr show ?thesis
  proof (cases "lr = 0")
    case False
    thus ?thesis
      apply (intro lineseg_Collinear image_eqI [where x = "ls/lr"])
      apply (auto simp add: lineseg_def lr ls)
      by (smt add.assoc add_diff_cancel_left' add_diff_eq eq_vector_fraction_iff real_vector.scale_left_commute scaleR_add_right scaleR_collapse)
  qed (simp add: lineseg_def)
qed

lemma collinear_union:
  assumes "collinear (ps \<union> qs)"
  assumes "collinear (ps \<union> rs)"
  assumes "p1 \<in> ps" "p2 \<in> ps" "p1 \<noteq> p2"
  shows "collinear (ps \<union> qs \<union> rs)"
proof -
  from assms have 1: "ps \<union> qs \<subseteq> range (lineseg p1 p2)" by (intro lineseg_collinear, auto)
  from assms have 2: "ps \<union> rs \<subseteq> range (lineseg p1 p2)" by (intro lineseg_collinear, auto)
  from 1 2 have 3: "ps \<union> qs \<union> rs \<subseteq> range (lineseg p1 p2)" by auto
  show ?thesis by (intro collinear_subset [OF 3] collinear_lineseg)
qed

lemma signedArea_lineseg: "signedArea r0 b0 (lineseg r1 b1 l) = (1-l) * signedArea r0 b0 r1 + l * signedArea r0 b0 b1"
  unfolding signedArea_def lineseg_def
  by (cases r0, cases b0, cases r1, cases b1, simp add: left_diff_distrib right_diff_distrib distrib_left distrib_right)

lemma collinear_lineseg_subset:
  assumes "r0 \<noteq> b0"
  assumes "collinear {r0, b0, r1, b1}"
  shows "range (lineseg r1 b1) \<subseteq> range (lineseg r0 b0)"
proof (intro subsetI)
  fix q assume "q \<in> range (lineseg r1 b1)"
  then obtain lq where q: "q = lineseg r1 b1 lq" by auto

  have "{r0, b0, r1, b1} \<subseteq> range (lineseg r0 b0)" by (intro lineseg_collinear assms, auto)
  then obtain lq0 lq1 where q0: "r1 = lineseg r0 b0 lq0" and q1: "b1 = lineseg r0 b0 lq1" by auto

  show "q \<in> range (lineseg r0 b0)"
    by (intro image_eqI [where x = "lq * lq1 + (1-lq) * lq0"],
        simp_all add: q q0 q1 lineseg_def scaleR_diff_left left_diff_distrib scaleR_add_right scaleR_diff_right scaleR_add_left)
qed

lemma turns_segments_cross:
  assumes "turn r0 b0 r1 \<noteq> turn r0 b0 b1"
  assumes "turn r1 b1 r0 \<noteq> turn r1 b1 b0"
  shows "segments_cross r0 b0 r1 b1"
proof -
  define sr1 sb1 sr0 sb0 where s_defs:
    "sr1 \<equiv> signedArea r0 b0 r1"
    "sb1 \<equiv> signedArea r0 b0 b1"
    "sr0 \<equiv> signedArea r1 b1 r0"
    "sb0 \<equiv> signedArea r1 b1 b0"

  from assms have s_ne: "sr1 \<noteq> sb1" "sr0 \<noteq> sb0" unfolding s_defs turn_def by smt+

  define l1 where "l1 \<equiv> sr1 / (sr1 - sb1)"

  have "signedArea r0 b0 (lineseg r1 b1 l1) = (1 - l1) * sr1 + l1 * sb1" unfolding signedArea_lineseg by (simp add: s_defs)
  also have "\<dots> = sr1 - l1 * (sr1 - sb1)" by (simp add: left_diff_distrib right_diff_distrib)
  also have "\<dots> = 0" using s_ne by (auto simp add: l1_def)
  finally have lq_range: "lineseg r1 b1 l1 \<in> range (lineseg r0 b0)"
    using assms by (intro Collinear_lineseg iffD2 [OF turn_Collinear] notI, simp_all)
  then obtain l0 where l0: "lineseg r1 b1 l1 = lineseg r0 b0 l0" by auto

  have "0 = signedArea r1 b1 (lineseg r1 b1 l1)" unfolding signedArea_lineseg by simp
  also have "\<dots> = signedArea r1 b1 (lineseg r0 b0 l0)" by (simp add: l0)
  also have "\<dots> = (1 - l0) * sr0 + l0 * sb0" unfolding signedArea_lineseg by (simp add: s_defs)
  also have "\<dots> = sr0 - l0 * (sr0 - sb0)" by (simp add: left_diff_distrib right_diff_distrib)
  finally have l0_def: "l0 = sr0 / (sr0 - sb0)"
    using s_ne nonzero_eq_divide_eq by smt

  have nonemptyI: "\<And>a S. a \<in> S \<Longrightarrow> S \<noteq> {}" by auto

  show ?thesis
    unfolding segments_cross_def segment_between_def
  proof (intro nonemptyI IntI image_eqI)
    from l0 show "lineseg r1 b1 l1 = lineseg r0 b0 l0".

    from assms have "0 \<le> l1 \<and> l1 \<le> 1 \<and> 0 \<le> l0 \<and> l0 \<le> 1"
      unfolding l0_def l1_def s_defs turn_def
      by (smt divide_le_eq_1 divide_nonneg_nonneg divide_nonpos_nonpos)
    thus "l0 \<in> closed_01" "l1 \<in> closed_01" unfolding closed_01_def by auto
  qed simp
qed

lemma Left_Left_not_segments_cross:
  assumes "turn r0 b0 r1 = Left"
  assumes "turn r0 b0 b1 = Left"
  shows "\<not> segments_cross r0 b0 r1 b1"
proof (intro notI)
  assume "segments_cross r0 b0 r1 b1"
  then obtain l0 l1 where l1: "l1 \<in> closed_01" and l0_l1: "lineseg r0 b0 l0 = lineseg r1 b1 l1"
    unfolding segments_cross_def segment_between_def by fastforce

  have "0 = signedArea r0 b0 (lineseg r0 b0 l0)" unfolding signedArea_lineseg by simp
  also have "\<dots> = signedArea r0 b0 (lineseg r1 b1 l1)" by (simp add: l0_l1)
  also have "\<dots> = (1-l1) * signedArea r0 b0 r1 + l1 * signedArea r0 b0 b1" unfolding signedArea_lineseg by simp
  also have "\<dots> > 0" using assms l1 unfolding turn_Left closed_01_def by (auto, smt mult_nonneg_nonneg no_zero_divisors)
  finally show False by simp
qed

lemma Right_Right_not_segments_cross:
  assumes "turn r0 b0 r1 = Right"
  assumes "turn r0 b0 b1 = Right"
  shows "\<not> segments_cross r0 b0 r1 b1"
proof -
  from assms have "turn b0 r0 r1 = Left" "turn b0 r0 b1 = Left"
    using turn_swap by (metis Turn.simps(8) turn_rotate1)+
  hence "\<not> segments_cross b0 r0 r1 b1" by (intro Left_Left_not_segments_cross)
  thus ?thesis by simp
qed

lemma card_4_or_not_distinct: "card {a,b,c,d} = 4 \<or> a = b \<or> a = c \<or> a = d \<or> b = c \<or> b = d \<or> c = d"
  using n_not_Suc_n by fastforce

lemma segments_cross_turns:
  assumes "segments_cross r0 b0 r1 b1"
  shows "collinear {r0, b0, r1, b1} \<or> (turn r0 b0 r1 \<noteq> turn r0 b0 b1 \<and> turn r1 b1 r0 \<noteq> turn r1 b1 b0)"
proof (intro disjCI)
  assume "\<not> (turn r0 b0 r1 \<noteq> turn r0 b0 b1 \<and> turn r1 b1 r0 \<noteq> turn r1 b1 b0)"
  then consider
    "turn r0 b0 r1 = Left"      "turn r0 b0 b1 = Left"
    | (CC0) "turn r0 b0 r1 = Collinear" "turn r0 b0 b1 = Collinear"
    |       "turn r0 b0 r1 = Right"     "turn r0 b0 b1 = Right"
    |       "turn r1 b1 r0 = Left"      "turn r1 b1 b0 = Left"
    | (CC1) "turn r1 b1 r0 = Collinear" "turn r1 b1 b0 = Collinear" "turn r0 b0 r1 \<noteq> turn r0 b0 b1"
    |       "turn r1 b1 r0 = Right"     "turn r1 b1 b0 = Right"
    apply auto by (metis Turn.exhaust)+
  from this assms Left_Left_not_segments_cross Right_Right_not_segments_cross segments_cross_swaps(3)
  show "collinear {r0, b0, r1, b1}"
  proof cases
    case CC1 with assms have ne: "r1 \<noteq> b1" by blast
    from ne CC1 have "turn r1 r0 b0 = Collinear" by (metis Collinear_trans)
    moreover from CC1 have "turn b1 r1 r0 = Collinear" "turn b1 r1 b0 = Collinear"
      by (smt Collinear_trans turn_rotate1)+
    with ne have "turn b1 r0 b0 = Collinear" by (metis Collinear_trans)
    ultimately show ?thesis using CC1 by (metis turn_rotate1)
  next
    case CC0
    hence p: "collinear ({r0,b0} \<union> {r1})" "collinear ({r0,b0} \<union> {b1})"
       apply (simp_all add: collinear_tripleton) by (metis turn_rotate1)

    from card_4_or_not_distinct [of r0 b0 r1 b1] p
    have "collinear ({r0,b0} \<union> {r1} \<union> {b1})"
    proof (elim disjE)
      assume 4: "card {r0, b0, r1, b1} = 4"
      have card_ne_4: "\<And>a b c. card {a,b,c} \<noteq> 4" by (simp add: card_insert_if)
      show ?thesis using CC0 4 by (intro collinear_union [of _ _ _ r0 b0] p, auto simp add: card_ne_4)
    next
      assume eq: "r0 = b0"
      hence segment_between_p1: "segment_between r0 b0 = {b0}" by (auto simp add: segment_between_def lineseg_def closed_01_def image_def)
      with assms obtain l where l: "b0 = lineseg r1 b1 l"
        by (smt disjoint_iff_not_equal image_iff segment_between_def segments_cross_def singletonD)
      thus ?thesis
        by (intro collinear_subset [OF _ collinear_lineseg], auto simp add: range_lineseg_p0 range_lineseg_p1 eq)
    qed (simp_all add: insert_commute)
    thus ?thesis by (simp add: insert_commute)
  qed blast+
qed

lemma dist_lineseg: "dist (lineseg p0 p1 la) (lineseg p0 p1 lb) = \<bar>lb-la\<bar> * dist p0 p1"
proof -
  have [simp]: "\<bar>lb-la\<bar> = \<bar>la-lb\<bar>" by simp
  have "dist (lineseg p0 p1 la) (lineseg p0 p1 lb) = norm ((lb - la) *\<^sub>R (p0 - p1))"
    unfolding dist_norm lineseg_def
    by (intro cong [OF refl, where f = norm], simp add: scaleR_diff_left scaleR_diff_right)
  also have "\<dots> = \<bar>lb-la\<bar> * dist p0 p1" by (simp add: dist_norm)
  finally show ?thesis .
qed

lemma dist_split:
  assumes "l \<in> closed_01"
  shows "dist p0 p1 = dist p0 (lineseg p0 p1 l) + dist (lineseg p0 p1 l) p1"
proof -
  from assms have 1: "\<bar>l\<bar> + \<bar>1-l\<bar> = 1" unfolding closed_01_def by auto

  have "dist p0 (lineseg p0 p1 l) = dist (lineseg p0 p1 0) (lineseg p0 p1 l)" by (simp add: lineseg_def)
  also note dist_lineseg
  finally have 2: "dist p0 (lineseg p0 p1 l) = \<bar>l\<bar> * dist p0 p1" by simp

  have "dist (lineseg p0 p1 l) p1 = dist (lineseg p0 p1 l) (lineseg p0 p1 1)" by (simp add: lineseg_def)
  also note dist_lineseg
  finally have 3: "dist (lineseg p0 p1 l) p1 = \<bar>1-l\<bar> * dist p0 p1" by simp

  have "dist p0 (lineseg p0 p1 l) + dist (lineseg p0 p1 l) p1 = (\<bar>l\<bar> + \<bar>1-l\<bar>) * dist p0 p1"
    by (simp add: 2 3 distrib_right)
  thus ?thesis by (simp add: 1)
qed

lemma Collinear_dist:
  assumes "dist p0 p1 = dist p0 p2 + dist p2 p1"
  shows "collinear {p0, p1, p2}"
proof (cases "p0 = p1")
  case True thus ?thesis by simp
next
  case False

  define par where "par \<equiv> p1 - p0"
  define perp where "perp \<equiv> (case par of (dx, dy) \<Rightarrow> (dy, -dx))"

  from False have inner_par_par_positive: "0 < inner par par" unfolding par_def by auto

  have  perp_is_perp1[simp]: "inner perp par = 0" by (cases par, simp add: perp_def)
  hence perp_is_perp2[simp]: "inner par perp = 0" by (simp add: inner_commute)
  have inner_perp_perp[simp]: "inner perp perp = inner par par" by (cases par, simp add: perp_def)

  have dist_norm_par: "dist p0 p1 = norm par" unfolding par_def by (metis dist_commute dist_norm)

  define p02 where "p02 \<equiv> p2 - p0"

  have inner_par_p02_commute[simp]: "inner par p02 = inner p02 par" by (simp add: inner_commute)

  define lpar  where "lpar  \<equiv> inner p02 par  / inner par par"
  define lperp where "lperp \<equiv> inner p02 perp / inner par par"

  have "inner par par *\<^sub>R p02 = inner p02 par *\<^sub>R par + inner p02 perp *\<^sub>R perp"
    by (cases par, cases p02, simp add: perp_def distrib_left distrib_right left_diff_distrib)
  hence p02_components: "p02 = lpar *\<^sub>R par + lperp *\<^sub>R perp"
    unfolding lpar_def lperp_def
    using inner_par_par_positive
    by (smt divide_inverse_commute left_inverse real_vector.scale_scale scaleR_collapse scaleR_left_distrib scaleR_right.add)

  show ?thesis
  proof (cases "lperp = 0")
    case True
    hence "p02 = lpar *\<^sub>R par" by (simp add: p02_components)
    hence p2_eq: "p2 = lineseg p0 p1 lpar" apply (simp add: p02_def lineseg_def par_def)
      by (smt ab_semigroup_add_class.add_ac(1) add.commute diff_add_cancel real_vector.scale_right_diff_distrib scaleR_collapse)

    show ?thesis unfolding collinear_tripleton by (intro lineseg_Collinear, simp add: p2_eq)
  next

    case offline: False

    have pythagoras0: "inner p02 p02 = (lpar * lpar + lperp * lperp) * inner par par"
      unfolding p02_components by (simp add: inner_add_left inner_add_right distrib_right)

    define p12 where "p12 \<equiv> p2 - p1"
    have p12_eq: "p12 = p02 - par" by (simp add: p02_def par_def p12_def)

    have p12_components: "p12 = (lpar - 1) *\<^sub>R par + lperp *\<^sub>R perp" unfolding p12_eq p02_components by (simp add: scaleR_left.diff)

    have pythagoras1: "inner p12 p12 = ((lpar - 1) * (lpar - 1) + lperp * lperp) * inner par par"
      unfolding p12_components by (simp add: inner_add_left inner_add_right distrib_right)

    have "lpar * dist p1 p0 \<le> sqrt ((lpar * dist p1 p0)\<^sup>2)" by simp
    also have "\<dots> = sqrt (lpar * lpar * inner par par)"
      by (intro cong [OF refl, where f = sqrt], simp add: power2_eq_square par_def dist_norm dot_square_norm)
    also have "\<dots> < sqrt (inner p02 p02)"
      apply (intro real_sqrt_less_mono, simp add: pythagoras0 distrib_right)
      using inner_par_par_positive mult_pos_pos not_real_square_gt_zero offline by blast
    also have "\<dots> = dist p2 p0" by (simp add: p02_def dist_norm norm_eq_sqrt_inner)
    finally have d02: "lpar * dist p1 p0 < dist p0 p2" by (simp add: dist_commute)

    have p: "(lpar-1) * (lpar-1) = (1-lpar) * (1-lpar)" by (auto simp add: left_diff_distrib right_diff_distrib)

    have "(1-lpar) * dist p1 p0 \<le> sqrt (((1-lpar) * dist p1 p0)\<^sup>2)" by simp
    also have "\<dots> = sqrt ((1-lpar) * (1-lpar) * inner par par)"
      by (intro cong [OF refl, where f = sqrt], simp add: power2_eq_square par_def dist_norm dot_square_norm)
    also have "\<dots> = sqrt ((lpar-1) * (lpar-1) * inner par par)" by (simp add: p)
    also have "\<dots> < sqrt (inner p12 p12)"
      apply (intro real_sqrt_less_mono, simp add: pythagoras1 distrib_right)
      using inner_par_par_positive mult_pos_pos not_real_square_gt_zero offline by blast
    also have "\<dots> = dist p2 p1" by (simp add: p12_def dist_norm norm_eq_sqrt_inner)
    finally have d12: "(1 - lpar) * dist p1 p0 < dist p1 p2" by (simp add: dist_commute)

    have "dist p1 p0 = lpar * dist p1 p0 + (1 - lpar) * dist p1 p0" by (auto simp add: left_diff_distrib)
    also from d02 d12 have "\<dots> < dist p0 p2 + dist p1 p2" by auto
    also from assms have "\<dots> = dist p1 p0" by (simp add: dist_commute)
    finally show ?thesis by simp
  qed
qed

lemma non_collinear_swap_decreases_length:
  assumes distinct:       "r0 \<noteq> r1" "b0 \<noteq> b1"
  assumes distinct_turns: "turn r0 b0 r1 \<noteq> turn r0 b0 b1"
                          "turn r1 b1 r0 \<noteq> turn r1 b1 b0"
  shows "dist r0 b1 + dist r1 b0 < dist r0 b0 + dist r1 b1"
proof -
  have segments_cross: "segments_cross r0 b0 r1 b1" by (intro turns_segments_cross assms)
  then obtain lp lq pq where pq_lp: "pq = lineseg r0 b0 lp" and pq_lq: "pq = lineseg r1 b1 lq"
    and lp: "lp \<in> closed_01" and lq: "lq \<in> closed_01"
    unfolding segments_cross_def segment_between_def by blast

  have "dist r0 pq + dist pq b1 + dist r1 pq + dist pq b0
     = dist r0 (lineseg r0 b0 lp) + dist (lineseg r0 b0 lp) b0 + dist r1 (lineseg r1 b1 lq) + dist (lineseg r1 b1 lq) b1" using pq_lp pq_lq by simp
  also have "\<dots> = dist r0 b0 + dist r1 b1" using dist_split [OF lp, of r0 b0] dist_split [OF lq, of r1 b1] by simp
  finally have "dist r0 pq + dist pq b1 + dist r1 pq + dist pq b0 = dist r0 b0 + dist r1 b1" .

  moreover have "dist r0 b1 \<le> dist r0 pq + dist pq b1" using dist_triangle.
  moreover have "dist r1 b0 \<le> dist r1 pq + dist pq b0" using dist_triangle.

  moreover have "dist r0 b1 \<noteq> dist r0 pq + dist pq b1 \<or> dist r1 b0 \<noteq> dist r1 pq + dist pq b0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence p0q1: "dist r0 b1 = dist r0 pq + dist pq b1" and q0p1: "dist r1 b0 = dist r1 pq + dist pq b0" by simp_all

    have p0_p1_pq: "collinear {r0, b0, pq}" unfolding collinear_tripleton using pq_lp by (intro lineseg_Collinear, simp)
    have q0_q1_pq: "collinear {r1, b1, pq}" unfolding collinear_tripleton using pq_lq by (intro lineseg_Collinear, simp)

    have p0_q1_pq: "collinear {r0, b1, pq}" using p0q1 by (intro Collinear_dist)
    have q0_p1_pq: "collinear {r1, b0, pq}" using q0p1 by (intro Collinear_dist)

    have p0_pq: "r0 \<noteq> pq"
    proof (intro notI)
      assume eq: "r0 = pq"
      from assms have "collinear ({r0,r1} \<union> {b1} \<union> {b0})"
      proof (intro collinear_union [of _ _ _ r0 r1])
        from eq have "{r1, b1, pq} = {r0, r1} \<union> {b1}" "{r1, b0, pq} = {r0, r1} \<union> {b0}" by auto
        with q0_q1_pq q0_p1_pq show "collinear ({r0, r1} \<union> {b1})" "collinear  ({r0, r1} \<union> {b0})" by simp_all
      qed simp_all
      with assms show False unfolding collinear_def by auto
    qed

    have q0_pq: "r1 \<noteq> pq"
    proof (intro notI)
      assume eq: "r1 = pq"
      from assms have "collinear ({r0,r1} \<union> {b1} \<union> {b0})"
      proof (intro collinear_union [of _ _ _ r0 r1])
        from eq have "{r0, b0, pq} = {r0, r1} \<union> {b0}" "{r0, b1, pq} = {r0, r1} \<union> {b1}" by auto
        with p0_p1_pq p0_q1_pq show "collinear ({r0, r1} \<union> {b0})" "collinear  ({r0, r1} \<union> {b1})" by simp_all
      qed simp_all
      with distinct_turns show False unfolding collinear_def by auto
    qed

    note lineseg_collinear collinear_lineseg_subset

    have "collinear ({r0, pq} \<union> {b0} \<union> {b1})"
      using p0_pq p0_p1_pq p0_q1_pq by (intro collinear_union [of _ _ _ r0 pq], auto simp add: insert_commute)
    hence "range (lineseg r0 pq) = range (lineseg b0 b1)"
      using assms p0_pq by (intro equalityI collinear_lineseg_subset, auto simp add: insert_commute)

    moreover
    have "collinear ({r1, pq} \<union> {b0} \<union> {b1})"
      using q0_pq q0_q1_pq q0_p1_pq by (intro collinear_union [of _ _ _ r1 pq], auto simp add: insert_commute)
    hence "range (lineseg r1 pq) = range (lineseg b0 b1)"
      using assms q0_pq by (intro equalityI collinear_lineseg_subset, auto simp add: insert_commute)

    ultimately
    have "collinear {r0,b0,r1,b1}"
      using range_lineseg_p0 range_lineseg_p1
      apply (intro collinear_subset [of "{r0, b0, r1, b1}" "range (lineseg b0 b1)"] subsetI collinear_lineseg)
      by (metis empty_iff insert_iff)

    with distinct_turns show False unfolding collinear_def by auto
  qed

  ultimately show ?thesis by auto
qed

definition badly_collinear :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool"
  where "badly_collinear r0 b0 r1 b1 \<equiv> ({b0,b1} \<subseteq> lineseg r0 r1 ` { l. 1 < l } \<or> {b0,b1} \<subseteq> lineseg r1 r0 ` { l. 1 < l })"

lemma badly_collinear_intersects_prelim:
  assumes bad: "{b0, b1} \<subseteq> lineseg r0 r1 ` {l. 1 < l}"
  shows "segments_cross r0 b0 r1 b1"
proof -
  from bad obtain lp1 lq1 where b0: "b0 = lineseg r0 r1 lp1" and b1: "b1 = lineseg r0 r1 lq1"
    and lp1: "1 < lp1" and lq1: "1 < lq1" unfolding badly_collinear_def by auto

  have "r1 \<in> segment_between r1 b1" unfolding segment_between_def
    by (intro image_eqI [where x=0], auto simp add: lineseg_def closed_01_def)

  moreover from lp1 have "r1 \<in> segment_between r0 b0" unfolding segment_between_def
    by (intro image_eqI [where x="1/lp1"], auto simp add: lineseg_def closed_01_def b0 scaleR_diff_left scaleR_diff_right scaleR_add_right)

  ultimately show ?thesis unfolding segments_cross_def by auto
qed

lemma badly_collinear_intersects:
  assumes "badly_collinear r0 b0 r1 b1"
  shows "segments_cross r0 b0 r1 b1"
  using badly_collinear_intersects_prelim assms
  unfolding badly_collinear_def segments_cross_def
  by (metis (full_types) Int_commute insert_commute)

lemma badly_collinear_swap_still_badly_collinear:
  assumes "badly_collinear r0 b0 r1 b1"
  shows   "badly_collinear r0 b1 r1 b0"
  using assms unfolding badly_collinear_def by auto

lemma badly_collinear_swap_preserves_length_prelim:
  assumes bad: "{b0, b1} \<subseteq> lineseg r0 r1 ` {l. 1 < l}"
  shows "dist r0 b1 + dist r1 b0 = dist r0 b0 + dist r1 b1"
proof -
  from bad obtain lp1 lq1 where b0: "b0 = lineseg r0 r1 lp1" and b1: "b1 = lineseg r0 r1 lq1"
    and lp1: "1 < lp1" and lq1: "1 < lq1" by auto

  have "dist (lineseg r0 r1 0) (lineseg r0 r1 lq1) = \<bar>lq1\<bar> * dist r0 r1" unfolding dist_lineseg by simp
  hence dist_p0_q1: "dist r0 b1 = lq1 * dist r0 r1" using b1 lq1 by (simp add: lineseg_def)

  have "dist (lineseg r0 r1 1) (lineseg r0 r1 lp1) = (lp1-1) * dist r0 r1" unfolding dist_lineseg using lp1 by simp
  hence dist_q0_p1: "dist r1 b0 = (lp1-1) * dist r0 r1" by (simp add: b0 lineseg_def)

  have "dist (lineseg r0 r1 0) (lineseg r0 r1 lp1) = lp1 * dist r0 r1" unfolding dist_lineseg using lp1 by simp
  hence dist_p0_p1: "dist r0 b0 = lp1 * dist r0 r1" using lp1 b0 by (simp add: lineseg_def)

  have "dist (lineseg r0 r1 1) (lineseg r0 r1 lq1) = (lq1-1) * dist r0 r1" unfolding dist_lineseg using lq1 by simp
  hence dist_q0_q1: "dist r1 b1 = (lq1-1) * dist r0 r1" using lq1 b1 by (simp add: lineseg_def)

  show ?thesis unfolding dist_p0_q1 dist_q0_p1 dist_p0_p1 dist_q0_q1 by (simp add: left_diff_distrib)
qed

lemma badly_collinear_swap_preserves_length:
  assumes bad: "badly_collinear r0 b0 r1 b1"
  shows "dist r0 b1 + dist r1 b0 = dist r0 b0 + dist r1 b1"
  using bad
  unfolding badly_collinear_def
proof (elim disjE)
  assume "{b0, b1} \<subseteq> lineseg r0 r1 ` {l. 1 < l}"
  thus ?thesis by (intro badly_collinear_swap_preserves_length_prelim)
next
  assume "{b0, b1} \<subseteq> lineseg r1 r0 ` {l. 1 < l}"
  hence "{b1, b0} \<subseteq> lineseg r1 r0 ` {l. 1 < l}" by simp
  hence "dist r1 b0 + dist r0 b1 = dist r1 b1 + dist r0 b0"
    by (intro badly_collinear_swap_preserves_length_prelim, auto)
  thus ?thesis by simp
qed

lemma swap_decreases_length:
  assumes distinct:       "distinct [r0, b0, r1, b1]"
  assumes segments_cross: "segments_cross r0 b0 r1 b1"
  assumes not_bad:        "\<not> badly_collinear r0 b0 r1 b1"
  shows "dist r0 b1 + dist r1 b0 < dist r0 b0 + dist r1 b1"
  using segments_cross_turns [OF segments_cross]
proof (elim conjE disjE)
  assume distinct_turns: "turn r0 b0 r1 \<noteq> turn r0 b0 b1" "turn r1 b1 r0 \<noteq> turn r1 b1 b0"
  with distinct show ?thesis
    by (intro non_collinear_swap_decreases_length, auto)
next
  assume collinear: "collinear {r0, b0, r1, b1}"
  hence "{r0,b0,r1,b1} \<subseteq> range (lineseg r0 b0)" using distinct by (intro lineseg_collinear, auto)
  then obtain lq0 lq1 where r1: "r1 = lineseg r0 b0 lq0" and b1: "b1 = lineseg r0 b0 lq1" by auto

  from segments_cross obtain lp lq
    where lp_lq: "lineseg r0 b0 lp = lineseg r1 b1 lq"
      and lp01: "0 \<le> lp" "lp \<le> 1" and lq01: "0 \<le> lq" "lq \<le> 1"
    unfolding segments_cross_def segment_between_def closed_01_def r1 b1 apply auto by presburger

  from lp_lq have "lp *\<^sub>R (b0 - r0) = (lq0 - (lq * lq0) + (lq * lq1)) *\<^sub>R (b0 - r0)"
    by (simp add: r1 b1 lineseg_def scaleR_diff_left scaleR_diff_right scaleR_add_right left_diff_distrib scaleR_add_left)
  hence "(lp - lq0 + lq * lq0 - lq * lq1) *\<^sub>R (b0 - r0) = 0" by auto
  with distinct have eq0: "lp - lq0 + lq * lq0 - lq * lq1 = 0" by auto

  from distinct b1 have lq1_ne: "lq1 \<noteq> 0" "lq1 \<noteq> 1" by (auto simp add: lineseg_def)
  then consider (lq1_lt_0) "lq1 < 0" | (lq1_01) "0 < lq1" "lq1 < 1" | (lq1_gt_1) "1 < lq1" by linarith
  note lq1_cases = this

  from distinct r1 have lq0_ne: "lq0 \<noteq> 0" "lq0 \<noteq> 1" by (auto simp add: lineseg_def)
  then consider (lq0_lt_0) "lq0 < 0" | (lq0_01) "0 < lq0" "lq0 < 1" | (lq0_gt_1) "1 < lq0" by linarith
  note lq0_cases = this

  have lineseg_eq: "\<And>l. lineseg r0 r1 l = lineseg r0 b0 (l*lq0)"
    by (auto simp add: lineseg_def r1 scaleR_diff_left scaleR_diff_right scaleR_add_right)

  have b0': "b0 = lineseg r0 r1   (1/lq0)" unfolding lineseg_eq    using lq0_ne by (simp add: lineseg_def)
  have b1': "b1 = lineseg r0 r1 (lq1/lq0)" unfolding lineseg_eq b1 using lq0_ne by (simp add: lineseg_def)

  show ?thesis
  proof (cases "lq1 < lq0")
    case True      

    have "dist r0 b1 = dist (lineseg r0 b0 0) (lineseg r0 b0 lq1)" by (simp add: lineseg_def b1)
    hence dist_p0_q1: "dist r0 b1 = \<bar>lq1\<bar> * dist r0 b0" unfolding dist_lineseg by simp

    have "dist r1 b0 = dist (lineseg r0 b0 lq0) (lineseg r0 b0 1)" by (simp add: lineseg_def r1)
    hence dist_q0_p1: "dist r1 b0 = \<bar>1-lq0\<bar> * dist r0 b0" unfolding dist_lineseg by simp

    have dist_q0_q1: "dist r1 b1 = \<bar>lq1-lq0\<bar> * dist r0 b0" unfolding dist_lineseg r1 b1 by simp

    from eq0 True lp01 lq01 lq0_ne have lq0_0: "0 < lq0" apply auto by (smt mult_left_mono)
    from eq0 True lp01 lq01 lq1_ne have lq1_1: "lq1 < 1" apply auto by (smt mult_left_le_one_le right_diff_distrib')

    from True have abs_lq1_lq0: "\<bar>lq1-lq0\<bar> = lq0 - lq1" by simp

    have "\<bar>lq1\<bar> + \<bar>1-lq0\<bar> < 1 + \<bar>lq1-lq0\<bar>" unfolding abs_lq1_lq0 using lq0_0 lq1_1 True by auto
    with distinct have "(\<bar>lq1\<bar> + \<bar>1-lq0\<bar>) * dist r0 b0 < (1 + \<bar>lq1-lq0\<bar>) * dist r0 b0" by auto
    thus ?thesis unfolding dist_p0_q1 dist_q0_p1 dist_q0_q1 by (simp add: distrib_right)
  next
    case False
    from distinct have "lq0 \<noteq> lq1" unfolding r1 b1 by auto
    with False have lq0_lt_lq1: "lq0 < lq1" unfolding r1 b1 by auto (* --- r1 --- b1 --- *)

    from lq0_cases have False
    proof cases
      case lq0_lt_0
      with lp01 lq01 eq0 have lq1_gt_0: "0 < lq1" by (smt lq1_cases mult_left_le_one_le mult_minus_right zero_less_mult_iff)
          (* --- r1 --- r0 --- {b1, b0} --- is bad *)
      with lq0_lt_0 have "{b0,b1} \<subseteq> lineseg r0 r1 ` { l. l < 0 }"
        unfolding b0' b1'
        apply auto using divide_pos_neg by blast
      also have "... \<subseteq> lineseg r1 r0 ` { l. 1 < l }"
      proof (intro subsetI)
        fix p assume "p \<in> lineseg r0 r1 ` {l. l < 0}" then obtain l where l: "p = lineseg r0 r1 l" "l < 0" by auto
        thus "p \<in> lineseg r1 r0 ` {l. 1 < l}" by (intro image_eqI [where x = "1-l"], auto simp add: lineseg_def)
      qed
      finally show ?thesis using not_bad unfolding badly_collinear_def by simp
    next
      case lq0_01
        (* --- r0 --- r1 --- {b0,b1} --- is bad *)
      with lq0_lt_lq1 have "{b0,b1} \<subseteq> lineseg r0 r1 ` {l. 1 < l}" unfolding b0' b1' by auto
      thus ?thesis using not_bad unfolding badly_collinear_def by simp
    next
      case lq0_gt_1
      with lp01 lq01 eq0 have lq1_lt_1: "lq1 < 1"
        by (smt lq1_cases mult_minus_left ordered_comm_semiring_class.comm_mult_left_mono semiring_normalization_rules(2))
      with lq0_gt_1 lq0_lt_lq1 show ?thesis by simp
    qed
    thus ?thesis by simp
  qed
qed

locale UncrossingSetup =
  fixes redPoints bluePoints :: "point set"
  assumes finite_redPoints:  "finite redPoints"
  assumes finite_bluePoints: "finite bluePoints"
  assumes cards_eq:  "card redPoints = card bluePoints"
  assumes red_blue_disjoint: "redPoints \<inter> bluePoints = {}"
  assumes not_badly_collinear:
      "\<And>r1 r2. \<lbrakk> r1 \<in> redPoints; r2 \<in> redPoints \<rbrakk>
          \<Longrightarrow> card (bluePoints \<inter> lineseg r1 r2 ` {l. 1 < l}) \<le> 1"

context UncrossingSetup
begin

lemma uncross_reduces_length:
  fixes r1 r2 b1 b2
  assumes colours: "r1 \<in> redPoints" "r2 \<in> redPoints" "b1 \<in> bluePoints" "b2 \<in> bluePoints"
  assumes distinct: "r1 \<noteq> r2" "b1 \<noteq> b2"
  assumes segments_cross: "segments_cross r1 b1 r2 b2"
  shows "dist r1 b2 + dist r2 b1 < dist r1 b1 + dist r2 b2"
proof (intro swap_decreases_length segments_cross)
  show "distinct [r1, b1, r2, b2]" using distinct colours red_blue_disjoint by auto
  show " \<not> badly_collinear r1 b1 r2 b2"
    unfolding badly_collinear_def
  proof (intro notI, elim disjE)
    assume "{b1, b2} \<subseteq> lineseg r1 r2 ` {l. 1 < l}"
    with colours have "{b1, b2} \<subseteq> bluePoints \<inter> lineseg r1 r2 ` {l. 1 < l}" by auto
    hence "card {b1, b2} \<le> card (bluePoints \<inter> lineseg r1 r2 ` {l. 1 < l})"
      using finite_bluePoints by (intro card_mono, auto)
    also have "\<dots> \<le> 1" by (intro not_badly_collinear colours)
    finally show False using distinct by simp
  next
    assume "{b1, b2} \<subseteq> lineseg r2 r1 ` {l. 1 < l}"
    with colours have "{b1, b2} \<subseteq> bluePoints \<inter> lineseg r2 r1 ` {l. 1 < l}" by auto
    hence "card {b1, b2} \<le> card (bluePoints \<inter> lineseg r2 r1 ` {l. 1 < l})"
      using finite_bluePoints by (intro card_mono, auto)
    also have "\<dots> \<le> 1" by (intro not_badly_collinear colours)
    finally show False using distinct by simp
  qed
qed

definition valid_total_lengths :: "real set"
  where "valid_total_lengths \<equiv> (\<lambda>pairs. \<Sum> pair \<in> pairs. dist (fst pair) (snd pair)) ` Pow (redPoints \<times> bluePoints)"

lemma finite_valid_total_lengths: "finite valid_total_lengths"
  unfolding valid_total_lengths_def
  by (intro finite_imageI iffD2 [OF finite_Pow_iff] finite_cartesian_product finite_redPoints finite_bluePoints)

definition valid_length_transitions :: "(real \<times> real) set"
  where "valid_length_transitions \<equiv> Restr {(x,y). x < y} valid_total_lengths"

lemma wf_less_valid_total_length: "wf valid_length_transitions"
proof (intro finite_acyclic_wf)
  have "valid_length_transitions \<subseteq> valid_total_lengths \<times> valid_total_lengths" by (auto simp add: valid_length_transitions_def)
  thus "finite valid_length_transitions" using finite_subset finite_valid_total_lengths by blast

  have "\<And>x y::real. (x,y) \<in> {(x, y). x < y}\<^sup>+ \<Longrightarrow> x < y"
  proof -
    fix x y :: real
    assume "(x,y) \<in> {(x, y). x < y}\<^sup>+"
    thus "x < y" by (induct y rule: trancl_induct, simp_all)
  qed
  hence "acyclic {(x, y). x < (y::real)}" by (intro acyclicI, auto)

  moreover have "valid_length_transitions \<subseteq> {(x, y). x < y}" by (auto simp add: valid_length_transitions_def)
  ultimately show "acyclic valid_length_transitions" using acyclic_subset by blast
qed

end

definition swapPoints :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point"
  where "swapPoints p0 p1 p \<equiv> if p = p0 then p1 else if p = p1 then p0 else p"

locale Uncrossing = UncrossingSetup +
  fixes blueFromRed :: "(point \<Rightarrow> point) stfun"
  assumes bv: "basevars blueFromRed"
  fixes blueFromRed_range :: stpred
  defines "blueFromRed_range \<equiv> PRED ((op `)<blueFromRed,#redPoints> = #bluePoints)" 
  fixes step :: action
  defines "step \<equiv> ACT (\<exists> r0 r1 b0 b1. #r0 \<in> #redPoints \<and> #r1 \<in> #redPoints \<and> #r0 \<noteq> #r1
            \<and> #b0 = id<$blueFromRed,#r0>
            \<and> #b1 = id<$blueFromRed,#r1>
            \<and> #(segments_cross r0 b0 r1 b1)
            \<and> blueFromRed$ = (op \<circ>)<$blueFromRed,#(swapPoints r0 r1)>)"
  fixes Spec :: temporal
  defines "Spec \<equiv> TEMP (Init blueFromRed_range \<and> \<box>[step]_blueFromRed \<and> WF(step)_blueFromRed)"

context Uncrossing
begin

lemma blueFromRed_range_preserved: "\<turnstile> step \<longrightarrow> $blueFromRed_range \<longrightarrow> blueFromRed_range$"
  apply (intro actionI)
  apply (auto simp add: blueFromRed_range_def square_def step_def swapPoints_def)
  by (metis (no_types, hide_lams) imageI image_comp swapPoints_def)+

lemma blueFromRed_range_Invariant: "\<turnstile> Spec \<longrightarrow> \<box>blueFromRed_range"
proof invariant
  fix sigma
  assume Spec: "sigma \<Turnstile> Spec"
  thus "sigma \<Turnstile> stable blueFromRed_range"
  proof (intro Stable)
    show "\<turnstile> $blueFromRed_range \<and> [step]_blueFromRed \<longrightarrow> blueFromRed_range$"
      using blueFromRed_range_preserved [temp_use]
      by (auto simp add: square_def, simp add: blueFromRed_range_def)
  qed (simp add: Spec_def)
qed (simp add: Spec_def)

definition total_length :: "real stfun"
  where "total_length s \<equiv> \<Sum> r \<in> redPoints. dist r (blueFromRed s r)"

lemma blueFromRed_range_valid_total_length: "\<turnstile> blueFromRed_range \<longrightarrow> total_length \<in> #valid_total_lengths"
  unfolding valid_total_lengths_def
proof (clarsimp, intro image_eqI)
  fix w
  assume "blueFromRed_range w"
  thus "(\<lambda>r. (r, blueFromRed w r)) ` redPoints \<in> Pow (redPoints \<times> bluePoints)"
    by (auto simp add: blueFromRed_range_def)

  have "sum (\<lambda>pair. dist (fst pair) (snd pair)) ((\<lambda>r. (r, blueFromRed w r)) ` redPoints)
      = sum ((\<lambda>pair. dist (fst pair) (snd pair)) o ((\<lambda>r. (r, blueFromRed w r)))) redPoints"
    by (intro sum.reindex inj_onI, simp)
  thus "total_length w = (\<Sum>pair\<in>(\<lambda>r. (r, blueFromRed w r)) ` redPoints. dist (fst pair) (snd pair))"
    by (simp add: total_length_def)
qed

definition all_uncrossed :: stpred
  where "all_uncrossed \<equiv> PRED (\<forall> r0 r1 b0 b1. #r0 \<in> #redPoints \<and> #r1 \<in> #redPoints \<and> #r0 \<noteq> #r1
            \<and> #b0 = id<blueFromRed,#r0>
            \<and> #b1 = id<blueFromRed,#r1>
            \<longrightarrow> \<not> #(segments_cross r0 b0 r1 b1))"

lemma stops_when_all_uncrossed: "\<turnstile> Spec \<longrightarrow> \<box>($all_uncrossed \<longrightarrow> blueFromRed$ = $blueFromRed)"
proof -
  have "\<turnstile> Spec \<longrightarrow> \<box>[step]_blueFromRed" by (auto simp add: Spec_def)
  also have "\<turnstile> \<box>[step]_blueFromRed \<longrightarrow> \<box>($all_uncrossed \<longrightarrow> blueFromRed$ = $blueFromRed)"
    by (intro STL4, auto simp add: square_def step_def all_uncrossed_def)
  finally show ?thesis .
qed

lemma step_valid_length_transition:
  assumes "(s,t) \<Turnstile> step"
  assumes "s \<Turnstile> blueFromRed_range"
  shows "(total_length t, total_length s) \<in> valid_length_transitions"
  unfolding valid_length_transitions_def
proof (intro IntI)
  from assms blueFromRed_range_preserved [temp_use] have "blueFromRed_range t" by simp
  with assms blueFromRed_range_valid_total_length [temp_use]
  show "(total_length t, total_length s) \<in> valid_total_lengths \<times> valid_total_lengths" by simp

  from assms have blueFromRed_range: "blueFromRed s ` redPoints = bluePoints"
    unfolding blueFromRed_range_def by auto

  from assms obtain r0 r1
    where r0: "r0 \<in> redPoints" and r1: "r1 \<in> redPoints" and r0_r1_ne: "r0 \<noteq> r1"
      and segments_cross: "segments_cross r0 (blueFromRed s r0) r1 (blueFromRed s r1)"
      and blueFromRed: "blueFromRed t = blueFromRed s \<circ> swapPoints r0 r1"
    unfolding step_def by clarsimp

  have total_length_eq: "\<And>u. total_length u = (\<Sum>r\<in>(redPoints - {r0,r1}). dist r (blueFromRed u r))
            + dist r0 (blueFromRed u r0)
            + dist r1 (blueFromRed u r1)"
  proof -
    fix u
    define g where "g \<equiv> \<lambda>r. dist r (blueFromRed u r)"

    have 1: "redPoints - {r0} - {r1} = redPoints - {r0, r1}" by auto

    from finite_redPoints r1 r0_r1_ne
    have 2: "sum g (redPoints - {r0}) = g r1 + sum g (redPoints - {r0} - {r1})"
      by (intro sum.remove, auto)

    have "total_length u = sum g redPoints" by (simp add: total_length_def g_def)
    also have "\<dots> = g r0 + sum g (redPoints - {r0})" by (intro sum.remove finite_redPoints r0)
    also have "\<dots> = g r0 + g r1 + sum g (redPoints - {r0, r1})" unfolding 1 2 by simp
    finally show "?thesis u" by (simp add: g_def)
  qed

  have reduced_part: "dist r0 (blueFromRed t r0) + dist r1 (blueFromRed t r1)
                    < dist r0 (blueFromRed s r0) + dist r1 (blueFromRed s r1)"
    unfolding blueFromRed using r0_r1_ne
  proof (simp add: swapPoints_def, intro uncross_reduces_length r0 r1 r0_r1_ne segments_cross)
    from blueFromRed_range r0 r1
    show "blueFromRed s r0 \<in> bluePoints" "blueFromRed s r1 \<in> bluePoints" by auto

    have "inj_on (blueFromRed s) redPoints"
      by (intro eq_card_imp_inj_on finite_redPoints, simp add: blueFromRed_range cards_eq)
    with r0 r1 r0_r1_ne show "blueFromRed s r0 \<noteq> blueFromRed s r1" by (meson inj_on_eq_iff)
  qed

  have unchanged_part: "(\<Sum>r\<in>redPoints - {r0, r1}. dist r (blueFromRed t r)) = (\<Sum>r\<in>redPoints - {r0, r1}. dist r (blueFromRed s r))"
    by (intro sum.cong refl, auto simp add: blueFromRed swapPoints_def)

  show "(total_length t, total_length s) \<in> {(x, y). x < y}"
    apply simp
    unfolding total_length_eq unchanged_part
    using reduced_part by simp
qed

lemma "\<turnstile> Spec \<longrightarrow> \<diamond>\<box>all_uncrossed"
proof -
  have "\<turnstile> Spec \<longrightarrow> stable all_uncrossed"
    by (intro tempI temp_impI Stable, auto simp add: Spec_def all_uncrossed_def square_def step_def)
  moreover have "\<turnstile> Spec \<longrightarrow> \<diamond>all_uncrossed"
  proof -
    have "\<turnstile> Spec \<longrightarrow> \<diamond>(\<exists>tl. all_uncrossed \<or> total_length = #tl)" by (intro imp_eventually_init, auto simp add: Init_def)
    also have "\<turnstile> Spec \<longrightarrow> ((\<exists>tl. all_uncrossed \<or> total_length = #tl) \<leadsto> all_uncrossed)" 
    proof (intro wf_imp_ex_leadsto [OF wf_less_valid_total_length] imp_disj_excl_leadstoI [OF imp_imp_leadsto])
      fix tl

      from blueFromRed_range_Invariant
      have "\<turnstile> Spec \<longrightarrow> \<box>([step]_blueFromRed \<and> $blueFromRed_range) \<and> WF(step)_blueFromRed"
        unfolding Spec_def apply auto using Init_stp_act_rev boxInit_act boxInit_stp by auto
      also have "\<turnstile> \<box>([step]_blueFromRed \<and> $blueFromRed_range) \<and> WF(step)_blueFromRed
                  \<longrightarrow> (\<not> all_uncrossed \<and> total_length = #tl
                      \<leadsto> all_uncrossed \<or> (\<exists>t'. #((t', tl) \<in> valid_length_transitions) \<and> (all_uncrossed \<or> total_length = #t')))"
      proof (intro WF1 actionI temp_impI)
        fix s t
        assume "(s, t) \<Turnstile> $(\<not> all_uncrossed \<and> total_length = #tl) \<and> [step]_blueFromRed \<and> $blueFromRed_range"
        hence maybe_step: "((s,t) \<Turnstile> step) \<or> blueFromRed t = blueFromRed s"
          and some_crossed: "\<not> all_uncrossed s"
          and tl: "tl = total_length s"
          and blueFromRed_range: "blueFromRed s ` redPoints = bluePoints"
          by (auto simp add: square_def blueFromRed_range_def)

        from some_crossed maybe_step consider (unchanged) "blueFromRed t = blueFromRed s"
          | (finish) "all_uncrossed t"
          | (step) "(s,t) \<Turnstile> step" "\<not> all_uncrossed t" by auto
        note cases = this

        from maybe_step
        show "(s, t) \<Turnstile> (\<not> all_uncrossed \<and> total_length = #tl)$
                          \<or> (all_uncrossed \<or> (\<exists>t'. #((t', tl) \<in> valid_length_transitions)
                                \<and> (all_uncrossed \<or> total_length = #t')))$"
        proof (elim disjE)
          assume "blueFromRed t = blueFromRed s"
          with some_crossed tl some_crossed tl show ?thesis by (auto simp add: all_uncrossed_def total_length_def)
        next
          assume "(s,t) \<Turnstile> step"
          with blueFromRed_range
          have "(total_length t, total_length s) \<in> valid_length_transitions"
            by (intro step_valid_length_transition, auto simp add: blueFromRed_range_def)
          with tl show ?thesis by auto
        qed

        show "(s,t) \<Turnstile> $Enabled (<step>_blueFromRed)"
          unfolding unl_before enabled_def
        proof -
          from some_crossed obtain r0 r1 where r0: "r0 \<in> redPoints" and r1: "r1 \<in> redPoints" and r0_r1_ne: "r0 \<noteq> r1"
            and crossed: "segments_cross r0 (blueFromRed s r0) r1 (blueFromRed s r1)"
            unfolding all_uncrossed_def by auto

          from basevars [OF bv] obtain u where u: "blueFromRed u = blueFromRed s \<circ> swapPoints r0 r1" by auto

          have blueFromRed_changed: "blueFromRed u \<noteq> blueFromRed s"
          proof (intro notI)
            assume "blueFromRed u = blueFromRed s"
            with u have "blueFromRed s r0 = (blueFromRed s \<circ> swapPoints r0 r1) r0" by simp
            hence "blueFromRed s r0 = blueFromRed s r1" by (simp add: swapPoints_def)
            moreover from blueFromRed_range
            have "inj_on (blueFromRed s) redPoints"
              by (intro eq_card_imp_inj_on finite_redPoints, simp add: blueFromRed_range_def cards_eq)
            with r0 r1 r0_r1_ne have "blueFromRed s r0 \<noteq> blueFromRed s r1" by (meson inj_on_eq_iff)
            ultimately show False by simp
          qed

          from r0 r1 r0_r1_ne crossed u
          show "\<exists>u. (s, u) \<Turnstile> <step>_blueFromRed"
            by (cases r0, cases r1, intro exI [where x = u], auto simp add: angle_def blueFromRed_changed step_def)
        qed

      next
        fix s t
        assume "(s,t) \<Turnstile> ($(\<not> all_uncrossed \<and> total_length = #tl) \<and> [step]_blueFromRed \<and> $blueFromRed_range) \<and> <step>_blueFromRed"
        hence step: "(s,t) \<Turnstile> step" and tl: "tl = total_length s" and blueFromRed_range: "blueFromRed_range s" by (auto simp add: angle_def)
        hence "(total_length t, total_length s) \<in> valid_length_transitions" by (intro step_valid_length_transition)
        thus "(s,t) \<Turnstile> ((all_uncrossed \<or> (\<exists>t'. #((t', tl) \<in> valid_length_transitions) \<and> (all_uncrossed \<or> total_length = #t')))$)"
          by (auto simp add: tl)
      qed
      finally show "\<turnstile> Spec \<longrightarrow> (\<not> all_uncrossed \<and> total_length = #tl \<leadsto> all_uncrossed \<or> (\<exists>t'. #((t', tl) \<in> valid_length_transitions) \<and> (all_uncrossed \<or> total_length = #t')))" .
    qed auto
    finally show ?thesis .
  qed
  ultimately show ?thesis using DmdStable by fastforce
qed

end

end
