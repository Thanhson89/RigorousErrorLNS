import LNS.Common
import LNS.Tactic
import LNS.Basic

open LNS

open Real

open Real Filter Topology

noncomputable section


private def f a r := a * r * log 2 - (a + 1) * log (a + 1) + (a + 1) * log (a * 2 ^ (-r) + 1)


lemma q_eq (hr: r > 0) (hi: i<0) (hΔ : Δ > 0): Qp Δ i r = f (2 ^ i) r / f (2 ^ i) Δ := by sorry


lemma q_hi_denom_valid (hΔ : Δ > 0): 2 ^ (-Δ) + Δ * log 2 - 1 > 0 := by sorry



lemma tendsto_f_mul_inv_x : Tendsto (fun a => f a r * a⁻¹) (𝓝[≠] 0) (𝓝 (2 ^ (-r) + r * log 2 - 1)) := by
  simp only [f, add_mul, sub_mul, mul_right_comm]
  rw [(by norm_num; ring : 2 ^ (-r) + r * log 2 - 1 = 1 * (log 2 * r) - (1 * log (0 + 1) + 1) + (1 * log (0 * 2 ^ (-r) + 1) + 2 ^ (-r)))]
  apply Tendsto.add
  · apply Tendsto.sub
    · simp only [mul_right_comm _ r, mul_assoc _ (log 2)]
      exact Tendsto.mul_const _ tendsto_x_mul_inv_x
    · apply Tendsto.add
      · apply Tendsto.mul tendsto_x_mul_inv_x
        apply tendsto_nhdsWithin_of_tendsto_nhds
        apply ContinuousAt.tendsto
        apply ContinuousAt.log _ (by norm_num)
        exact Continuous.continuousAt (continuous_add_right 1)
      · simpa [mul_comm] using tendsto_log_mul_inv_x 1
  · apply Tendsto.add
    · apply Tendsto.mul tendsto_x_mul_inv_x
      apply tendsto_nhdsWithin_of_tendsto_nhds
      apply ContinuousAt.tendsto
      apply ContinuousAt.log _ (by norm_num)
      apply Continuous.continuousAt
      exact Continuous.add (continuous_mul_right _) continuous_const
    · simpa [mul_comm] using tendsto_log_mul_inv_x (2 ^ (-r))



lemma lemma61sub (hΔ : Δ > 0): Tendsto (fun (i:ℝ)=> f (2 ^ i) r / f (2 ^ i) Δ) atBot (𝓝 (Qp_hi Δ r)) := by
  unfold Qp_hi;
  have : (fun (i:ℝ)=> f (2 ^ i) r / f (2 ^ i) Δ )= (fun i=>f (2 ^ i) r * (2 ^ i)⁻¹ / (f (2 ^ i) Δ * (2 ^ i)⁻¹)) := by
    ext i; field_simp
  simp only [this]; clear this
  have h : ∀ r, Tendsto (fun i : ℝ => f (2 ^ i) r * (2 ^ i)⁻¹) atBot (𝓝 (2 ^ (-r) + r * log 2 - 1)) :=by
    intro r
    apply Tendsto.comp tendsto_f_mul_inv_x
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_rpow_atTop_of_base_gt_one _ one_lt_two
    · simp; use 0; intro x _
      exact ne_of_gt (rpow_pos_of_pos zero_lt_two _)
  apply Tendsto.div (h r) (h Δ) (ne_of_gt (q_hi_denom_valid hΔ))




lemma lemma61 (hr: r>0) (hΔ : Δ > 0): Tendsto (fun i => Qp Δ i r) atBot (𝓝 (Qp_hi Δ r)) := by
  have : Tendsto (fun (i:ℝ)=> f (2 ^ i) r / f (2 ^ i) Δ) atBot (𝓝 (Qp_hi Δ r)) := by apply lemma61sub ; assumption
  apply Filter.Tendsto.congr' _  this;
  have h: Set.EqOn (fun i ↦ f (2 ^ i) r / f (2 ^ i) Δ) (fun i ↦ Qp Δ i r) (Set.Iic (-1:ℝ)):=by
    unfold Set.EqOn; simp; intro x hx; rw[← q_eq]; assumption; linarith; assumption
  apply Filter.eventuallyEq_of_mem _ h; apply Filter.Iic_mem_atBot;
