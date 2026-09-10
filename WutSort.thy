theory WutSort
  imports Main "HOL-Library.Multiset"
begin

definition maybeSwap :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where "maybeSwap xs i j \<equiv> if xs ! i < xs ! j then xs[i := xs ! j, j := xs ! i] else xs"

lemma maybeSwap_length[simp]: "length (maybeSwap xs i j) = length xs" by (simp add: maybeSwap_def)

lemma maybeSwap_permute:
  assumes "i < length xs" "j < length xs"
  shows "mset (maybeSwap xs i j) = mset xs"
  using assms unfolding maybeSwap_def by (auto intro: mset_swap)

lemma maybeSwap_order:
  assumes "i < length xs" "j < length xs"
  shows "maybeSwap xs i j ! j \<le> maybeSwap xs i j ! i"
  using assms by (cases "i = j", auto simp add: maybeSwap_def)



fun innerLoop :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where
    "innerLoop xs i  0      = xs"
  | "innerLoop xs i (Suc j) = maybeSwap (innerLoop xs i j) i j"

lemma innerLoop_length[simp]: "length (innerLoop xs i j) = length xs" by (induct j, simp_all)

lemma innerLoop_permute:
  assumes "i < length xs" "j \<le> length xs"
  shows "mset (innerLoop xs i j) = mset xs"
  using assms
proof (induct j)
  case (Suc j)
  have "mset (innerLoop xs i (Suc j)) = mset (maybeSwap (innerLoop xs i j) i j)" by (simp add: Suc)
  also have "\<dots> = mset (innerLoop xs i j)" using Suc by (intro maybeSwap_permute, auto)
  also have "\<dots> = mset xs" using Suc by (intro cong [OF refl Suc.hyps], auto)
  finally show ?case .
qed simp

lemma innerLoop_max:
  assumes "i < length xs" "j \<le> length xs" "k < j"
  shows "innerLoop xs i j ! k \<le> innerLoop xs i j ! i"
  using `j \<le> length xs` `k < j`
proof (induct j arbitrary: k)
  case (Suc j)
  show ?case
  proof (cases "k = i")
    case ki: False
    have ij_length: "i < length (innerLoop xs i j)" "j < length (innerLoop xs i j)" using assms Suc.prems by auto
    have "innerLoop xs i (Suc j) ! k \<le> innerLoop xs i j ! i"
    proof (cases "k = j")
      case kj: True
      hence "innerLoop xs i (Suc j) ! k = maybeSwap (innerLoop xs i j) i j ! j" by simp
      also have "\<dots> \<le> innerLoop xs i j ! i" unfolding maybeSwap_def using ij_length by auto
      finally show ?thesis .
    next
      case kj: False
      with ki have "innerLoop xs i (Suc j) ! k = innerLoop xs i j ! k" by (simp add: maybeSwap_def)
      also have "\<dots> \<le> innerLoop xs i j ! i" using  `k \<noteq> j` `Suc j \<le> length xs` `k < Suc j` by (intro Suc, auto)
      finally show ?thesis .
    qed
    also have "innerLoop xs i j ! i \<le> max (innerLoop xs i j ! i) (innerLoop xs i j ! j)" by simp
    also have "\<dots> = maybeSwap (innerLoop xs i j) i j ! i" using  ij_length by (simp add: maybeSwap_def nth_list_update)
    also have "\<dots> = innerLoop xs i (Suc j) ! i" by simp
    finally show ?thesis .
  qed simp
qed simp

lemma innerLoop_insertion_sort:
  assumes i_lt: "i < length xs"
  assumes j_le: "j \<le> length xs"
  assumes start_order: "\<And>k. Suc k < i \<Longrightarrow> xs ! k \<le> xs ! Suc k"
  assumes ki: "Suc k < i"
  shows "innerLoop xs i j ! k \<le> innerLoop xs i j ! Suc k"
  using j_le
proof (induct j)
  case 0 thus ?case using ki start_order by force
next
  case (Suc j)
  consider "Suc k < j" | "j = Suc k" | "j = k" | "j < k" by force
  thus ?case using ki i_lt Suc by (cases, auto simp add: maybeSwap_def)
qed




fun outerLoop :: "nat list \<Rightarrow> nat \<Rightarrow> nat list"
  where
    "outerLoop xs 0 = xs"
  | "outerLoop xs (Suc i) = innerLoop (outerLoop xs i) i (length xs)"

lemma outerLoop_length[simp]: "length (outerLoop xs i) = length xs" by (induct i, auto)

lemma outerLoop_permute:
  assumes "i \<le> length xs"
  shows "mset (outerLoop xs i) = mset xs"
  using assms
proof (induct i)
  case (Suc i)
  have "mset (outerLoop xs (Suc i)) = mset (innerLoop (outerLoop xs i) i (length xs))" by simp
  also have "\<dots> = mset (outerLoop xs i)" using Suc by (intro innerLoop_permute, auto)
  also have "\<dots> = mset xs" using Suc by (intro Suc, simp)
  finally show ?case.
qed simp

lemma outerLoop_partial_sort:
  assumes i_lt: "i \<le> length xs"
  assumes ki: "Suc k < i"
  shows "outerLoop xs i ! k \<le> outerLoop xs i ! Suc k"
  using assms
proof (induct i arbitrary: k)
  case (Suc i k)
  have "innerLoop (outerLoop xs i) i (length xs) ! k \<le> innerLoop (outerLoop xs i) i (length xs) ! Suc k"
  proof (cases "i = Suc k")
    case True with Suc.prems show ?thesis unfolding True by (intro innerLoop_max, auto)
  next
    case False with Suc.prems show ?thesis by (intro innerLoop_insertion_sort Suc.hyps, auto)
  qed
  thus ?case by simp
qed simp




definition wutsort :: "nat list \<Rightarrow> nat list"
  where "wutsort xs \<equiv>
          foldl (\<lambda>xs i.
                    foldl (\<lambda>xs j.
                        if xs ! i < xs ! j
                        then xs[i := xs ! j, j := xs ! i]
                        else xs
                    ) xs [0..<length xs]
                ) xs [0..<length xs]"

lemma wutsort_sort: "wutsort = sort"
proof (intro ext)
  have [simp]: "(if xs ! i < xs ! j then xs[i := xs ! j, j := xs ! i] else xs) = maybeSwap xs i j" for i j xs by (simp add: maybeSwap_def)
  have [simp]: "foldl (\<lambda>xs2 j. maybeSwap xs2 i j)            xs [0..<j] = innerLoop xs i j"        for i j xs by (induct j, auto)
  have [simp]: "foldl (\<lambda>xs1 i. innerLoop xs1 i (length xs1)) xs [0..<i] = outerLoop xs i"          for i   xs by (induct i, auto)
  fix xs
  have "wutsort xs = outerLoop xs (length xs)" unfolding wutsort_def by simp
  also have "\<dots> = sort xs"
    by (cases "length xs", simp, metis le_Suc_eq outerLoop_length outerLoop_partial_sort outerLoop_permute properties_for_sort sorted_iff_nth_Suc)
  thus "wutsort xs = sort xs" by (simp add: wutsort_def)
qed

end
