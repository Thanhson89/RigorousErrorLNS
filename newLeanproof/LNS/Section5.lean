import LNS.Common
import LNS.Basic
import LNS.Tactic

namespace LNS

open Real

/- E(i, r) is strictly monotone on r ≥ 0 for all fixed i -/

lemma strictMonoOn_E_r {i} : StrictMonoOn (Ep i) (Set.Ici 0) := by
  have diffE : Differentiable ℝ (Ep i) := by
    apply Differentiable.add _ (by simp : _)
    apply Differentiable.sub_const
    intro x
    apply DifferentiableAt.comp_const_sub.mpr
    apply differentiable_phi
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
  · apply Continuous.continuousOn
    exact Differentiable.continuous diffE
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx
    unfold Ep
    rw [deriv_add]
    · rw [deriv_mul_const (by simp : _), deriv_sub_const, deriv_id'', deriv_comp_const_sub, one_mul]
      simp only [deriv_phi, lt_neg_add_iff_add_lt, add_zero]
      rw [div_lt_div_iff (one_plus_two_pow_pos _) (one_plus_two_pow_pos _)]
      rw [← lt_neg_add_iff_lt]; ring_nf
      rw [lt_neg_add_iff_lt]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : _)
      linarith
    · apply DifferentiableAt.sub_const
      apply DifferentiableAt.comp_const_sub.mpr
      apply differentiable_phi
    · simp

lemma monotoneOn_E_r {i} : MonotoneOn (E i) (Set.Ici 0) :=
  StrictMonoOn.monotoneOn strictMonoOn_E_r

/- First part of Lemma 5.1: E(i, r) ≥ 0 when r ≥ 0 -/

lemma err_nonneg {i r} (hr : 0 ≤ r) : 0 ≤ E i r := by
  rw [(by simp [E] : 0 = E i 0)]
  rcases eq_or_gt_of_le hr with h | h
  · rw [h]
  · apply le_of_lt
    exact strictMonoOn_E_r Set.left_mem_Ici hr h

/- Auxiliary definitions and lemmas for the proof of the second part of Lemma 5.1 -/

private noncomputable def f (a : ℝ) := a * exp (-a) + exp (-a) - 1

private noncomputable def h a := (a + 2) * exp (-a) + (a - 2)

private lemma hasDerivAt_f : HasDerivAt f (-a * exp (-a)) a := by
  get_deriv (fun a => a * exp (-a) + exp (-a) - 1) at a
  · simp only [List.Forall];
  · simp only [toFun, one_mul, mul_neg, mul_one, add_neg_cancel_comm, sub_zero] at h
    convert h using 1
    ring

private lemma differentiable_f : Differentiable ℝ f := fun _ => hasDerivAt_f.differentiableAt

private lemma f_zero : f 0 = 0 := by simp [f]

private lemma f_neg {a} (ha : a ≠ 0) : f a < 0 := by
  rw [← f_zero]
  rcases lt_or_gt_of_ne ha with h | h
  · apply strictMonoOn_of_deriv_pos (convex_Iic 0) _ _ (Set.mem_Iic_of_Iio h) Set.right_mem_Iic h
    · apply Continuous.continuousOn
      exact Differentiable.continuous differentiable_f
    · simp only [Set.nonempty_Ioi, interior_Iic', Set.mem_Iio, hasDerivAt_f.deriv]
      intro x x_neg
      exact mul_pos (neg_pos.mpr x_neg) (exp_pos _)
  · apply strictAntiOn_of_deriv_neg (convex_Ici 0) _ _ Set.left_mem_Ici (Set.mem_Ici_of_Ioi h) h
    · apply Continuous.continuousOn
      exact Differentiable.continuous differentiable_f
    · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, hasDerivAt_f.deriv]
      intro x x_pos
      simp only [neg_mul, Left.neg_neg_iff]
      exact mul_pos x_pos (exp_pos _)

private lemma h_nonneg (ha : 0 ≤ a) : 0 ≤ h a := by
  get_deriv (fun a => (a + 2) * exp (-a) + (a - 2))
  · intro; trivial
  dsimp [toFun] at h
  have ⟨dh, deriv_h⟩ := h; clear h
  have h0 : h 0 = 0 := by
    simp only [h, zero_add, neg_zero, exp_zero, mul_one, zero_sub, add_neg_cancel]
  rw [← h0]
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · apply Continuous.continuousOn
    exact Differentiable.continuous dh
  · exact Differentiable.differentiableOn dh
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx; unfold h
    rw [deriv_h]
    simp only [add_zero, one_mul, mul_neg, mul_one, sub_zero]
    calc
      exp (-x) + -((x + 2) * exp (-x)) + 1 = -(f x) := by unfold f; ring
      _ ≥ 0 := le_of_lt $ neg_pos_of_neg $ f_neg $ ne_of_gt hx
  · exact Set.left_mem_Ici
  · exact ha
  · exact ha

-- TODO: simplify

lemma strictMonoOn_E_i {r} (hr : 0 < r) : StrictMonoOn (fun i => E i r) (Set.Iic 0) := by
  -- set a := r * log 2
  -- set x := (2 : ℝ) ^ (-r)
  -- have dE : ∀ i, HasDerivAt (fun i => E i r) (2^i / ((2^i + 1) * (2^i + 1) * (2^(i - r) + 1)) * (2^i * f a + h a)) i := by
  --   intro i
  --   unfold E
  --   simp [deriv_phi]
  --   unfold f h Φ logb
  --   get_deriv (fun i ↦ log (1 + 2 ^ (i - r)) / log 2 - log (1 + 2 ^ i) / log 2 + r * (2 ^ i / (1 + 2 ^ i))) at i
  --   · simp [toFun, one_plus_two_pow_ne_zero]
  --     norm_num
  --   · have : exp (-(r * log 2)) = 2 ^ (-r) := by
  --       rw [← neg_mul, mul_comm, exp_mul, exp_log two_pos]
  --     rw [this]
  --     -- have : (2 : ℝ) ^ (i - r) = 2 ^ i * 2 ^ (-r) := by
  --     simp [toFun] at h
  --     convert h using 1
  --     simp only [rpow_sub zero_lt_two]
  --     field_simp
  have diff1 : Differentiable ℝ fun y ↦ Φ (y - r) := by
    intro x
    rw [DifferentiableAt.comp_sub_const]
    exact differentiable_phi _
  have diff2 : Differentiable ℝ fun y ↦ Φ (y - r) - Φ y := Differentiable.sub diff1 differentiable_phi
  have diff3 : Differentiable ℝ (deriv Φ) := by
    rw [deriv_phi]
    apply Differentiable.div _ diff_aux1 one_plus_two_pow_ne_zero
    exact fun x => (hasDerivAt_two_pow x).differentiableAt
  have diff4 : Differentiable ℝ (fun y ↦ r * deriv Φ y) := Differentiable.const_mul diff3 _
  have diffE : Differentiable ℝ (fun i => E i r) := Differentiable.add diff2 diff4
  apply strictMonoOn_of_deriv_pos (convex_Iic 0)
  · apply Continuous.continuousOn
    exact Differentiable.continuous diffE
  · simp only [Set.nonempty_Ioi, interior_Iic', Set.mem_Iio]
    intro i i_neg
    unfold E
    rw [deriv_add (diff2 _) (diff4 _), deriv_sub (diff1 _) (differentiable_phi _),
        deriv_const_mul _ (diff3 _), deriv_phi2, deriv_comp_sub_const, deriv_phi]
    simp only
    rw [rpow_sub two_pos, div_eq_inv_mul _ (2 ^ r), ← rpow_neg (le_of_lt two_pos)]
    field_simp
    set x := (2 : ℝ) ^ (-r)
    set y := (2 : ℝ) ^ i
    have ypos1 : 0 < 1 + y := one_plus_two_pow_pos i
    apply div_pos
    · have : (x * y * (1 + y) - (1 + x * y) * y) * (1 + y) ^ 2 + r * (y * log 2) * ((1 + x * y) * (1 + y)) =
             (1 + y) * y * (y * (r * log 2 * x + x - 1) + (x + r * log 2 - 1)) := by ring
      rw [this]; clear this
      apply mul_pos (mul_pos ypos1 (rpow_pos_of_pos two_pos _))
      set a := r * log 2
      have a_pos : 0 < a := mul_pos hr (log_pos one_lt_two)
      have exp_a : x = exp (-a) := by
        rw [← neg_mul, mul_comm, exp_mul, exp_log two_pos]
      rw [exp_a]
      let N t := t * f a + (exp (-a) + a - 1)
      have : N y = y * (a * exp (-a) + exp (-a) - 1) + (exp (-a) + a - 1) := by simp [f]
      rw [← this]; clear this
      have : 0 ≤ N 1 := by
        have h1 : h a = N 1 := by simp [f, h]; ring
        rw [← h1]
        exact h_nonneg (le_of_lt a_pos)
      apply lt_of_le_of_lt this
      apply strictAntiOn_of_deriv_neg (convex_Ici 0)
      · apply Continuous.continuousOn
        apply Continuous.add (continuous_mul_right _) continuous_const
      · simp; intro x _
        exact f_neg (ne_of_gt a_pos)
      · simp [rpow_nonneg (le_of_lt two_pos)]
      · simp only [Set.mem_Ici, zero_le_one]
      · exact rpow_lt_one_of_one_lt_of_neg one_lt_two i_neg
    · apply mul_pos (mul_pos _ ypos1) (pow_pos ypos1 2)
      rw [← rpow_add two_pos]
      exact one_plus_two_pow_pos _

lemma monotoneOn_E_i {r} (hr : 0 ≤ r) : MonotoneOn (fun i => E i r) (Set.Iic 0) := by
  rcases lt_or_eq_of_le hr with h | h
  · exact StrictMonoOn.monotoneOn $ strictMonoOn_E_i h
  · simp [← h, err_eq_zero]
    exact monotoneOn_const

/- Lemma 5.1 -/

lemma err_bound {i r Δ} (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) : |E i r| ≤ E 0 Δ := by
  rw [abs_of_nonneg (err_nonneg hr1)]
  have := monotoneOn_E_i hr1 hi Set.right_mem_Iic hi
  apply le_trans this
  exact monotoneOn_E_r hr1 (le_trans hr1 hr2) hr2

end LNS
