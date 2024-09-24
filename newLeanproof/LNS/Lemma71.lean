import LNS.Common
import LNS.Basic
set_option maxHeartbeats 10000000

noncomputable section

open LNS
open Real
open Real Filter Topology



private def F (x:ℝ) (t:ℝ) :=  Φm (x-t)  -  Φm x

noncomputable def Fx t x := F x t

lemma F_t_StrictMono  (hx: x ≤ (-1:ℝ)) : StrictMonoOn (F x) (Set.Ici (0:ℝ)) :=by
  unfold F
  have ec2 : (fun y ↦ Φm (x - y)) = (fun y=> Φm y) ∘ (fun y=>x -y) :=by ext y; simp only [Function.comp_apply];
  apply strictMonoOn_of_deriv_pos_Ici0
  apply ContinuousOn.sub _ (by apply continuousOn_const);
  rw[ec2];
  have:= DifferentiableOn.continuousOn differentiable_Φm
  apply ContinuousOn.comp this
  apply ContinuousOn.sub (by apply continuousOn_const) (by apply continuousOn_id);
  simp only [Set.MapsTo, Set.mem_Ici, Set.mem_Iio, sub_neg]; intro t ht; linarith
  intro t ht
  rw[deriv_sub, deriv_const, deriv_comp_const_sub, deriv_Φm]; simp only [sub_zero, gt_iff_lt,Left.neg_pos_iff]
  apply div_neg_of_neg_of_pos (by simp only [Left.neg_neg_iff, Nat.ofNat_pos, rpow_pos_of_pos])
  simp only [sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)
  simp only [Set.mem_Iio, sub_neg]; linarith
  rw[ec2]; apply DifferentiableAt.comp
  apply DifferentiableOn.differentiableAt differentiable_Φm (Iio_mem_nhds (by linarith))
  apply DifferentiableAt.sub (by apply differentiableAt_const) (by apply differentiableAt_id);
  simp only [differentiableAt_const]


lemma F_x_StrictMono (ht: 0 < t) : StrictMonoOn (fun x => F x t) (Set.Iic (-1:ℝ)) :=by
  unfold F
  have ec2 : (fun y ↦ Φm (y - t)) = (fun y=> Φm y) ∘ (fun y=>y-t) :=by ext y; simp only [Function.comp_apply];
  have:= DifferentiableOn.continuousOn differentiable_Φm
  apply strictMonoOn_of_deriv_pos (convex_Iic (-1:ℝ))
  apply ContinuousOn.sub
  rw[ec2];
  apply ContinuousOn.comp this
  apply ContinuousOn.sub (by apply continuousOn_id) (by apply continuousOn_const) ;
  simp only [Set.MapsTo, Set.mem_Iic, Set.mem_Iio, sub_neg]; intro t ht; linarith
  apply ContinuousOn.mono this
  rw[Set.Iic_subset_Iio]; simp only [Left.neg_neg_iff, zero_lt_one]
  intro x hx; simp only [Set.nonempty_Ioi, interior_Iic', Set.mem_Iio] at hx
  rw[deriv_sub, deriv_comp_sub_const, deriv_Φm, deriv_Φm];
  simp only
  have : 1 - (2:ℝ)^x > 0 :=by simp only [gt_iff_lt, sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)
  have : 1 - (2:ℝ)^(x-t) > 0 :=by simp only [gt_iff_lt, sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)
  have : (2:ℝ)^x - (2:ℝ)^(x-t) > 0 :=by simp only [gt_iff_lt, sub_pos, Nat.one_lt_ofNat, rpow_lt_rpow_left_iff, sub_lt_self_iff]; exact ht
  have : - (2:ℝ) ^ (x - t) / (1 - 2 ^ (x - t)) - -2 ^ x / (1 - 2 ^ x) = (2^x - 2^ (x-t)) / ((1 -2 ^ x)* (1 -2 ^ (x-t)) ):=by
    field_simp; ring_nf
  rw[this]; positivity
  simp only [Set.mem_Iio]; linarith; simp only [Set.mem_Iio, sub_neg]; linarith
  rw[ec2]; apply DifferentiableAt.comp
  apply DifferentiableOn.differentiableAt differentiable_Φm (Iio_mem_nhds (by linarith))
  simp only [differentiableAt_id', differentiableAt_const, DifferentiableAt.sub]
  apply DifferentiableOn.differentiableAt differentiable_Φm (Iio_mem_nhds (by linarith))

lemma max_of_F (hx: x ≤ (-1:ℝ)) (ht: 0 ≤ t) (htp: t ≤ m): F x t ≤ F (-1) m :=by
  have first  :  F x t ≤ F (-1) t :=by
    rw[le_iff_lt_or_eq] at ht; cases ht
    apply (StrictMonoOn.monotoneOn (F_x_StrictMono (by assumption))) (by simp only [Set.mem_Iic]; exact hx) (by simp only [Set.mem_Iic,
      le_refl]) hx
    rename_i h; simp only [F, ← h, sub_zero, sub_self, le_refl]
  have second :  F (-1) t ≤ F (-1) m :=by
    apply (StrictMonoOn.monotoneOn (F_t_StrictMono (by simp only [le_refl])))
    simp only [Set.mem_Ici]; exact ht; simp only [Set.mem_Ici]; linarith; assumption
  linarith


lemma Φm_strictAnti : StrictAntiOn Φm (Set.Iio 0):= by
    apply strictAntiOn_of_deriv_neg (convex_Iio 0)
    exact DifferentiableOn.continuousOn differentiable_Φm
    simp only [interior_Iio]; intro t ht; simp only [deriv_Φm ht]
    simp only [Set.mem_Iio] at ht
    apply div_neg_of_neg_of_pos; simp only [Left.neg_neg_iff, Nat.ofNat_pos, rpow_pos_of_pos]
    simp only [gt_iff_lt, sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)


lemma Lemma71 (hx: x ≤ (-1:ℝ)) (hxs: xs ≤ (-1:ℝ)) (hd: |x-xs| ≤ m) : |Φm x - Φm xs| ≤ Φm (-1-m) - Φm (-1) :=by
  have e: Φm (-1 - m) - Φm (-1) = F (-1) m :=by unfold F; simp only
  rw[e]
  by_cases x > xs; rename_i h
  have i1: |Φm x - Φm xs| = - (Φm x - Φm xs) := by
    apply abs_of_neg; simp only [sub_neg]; apply Φm_strictAnti; simp only [Set.mem_Iio]; linarith; simp only [Set.mem_Iio]; linarith; assumption
  have i2: Φm x - Φm xs = - F x (x -xs):=by simp only [sub_sub_cancel, F, neg_sub]
  rw[i1, i2]; simp only [neg_neg, ge_iff_le]
  rw[abs_of_pos (by linarith)] at hd
  apply max_of_F hx (by linarith) hd
  have i1: |Φm x - Φm xs| = Φm x - Φm xs := by
    apply abs_of_nonneg; simp only [sub_nonneg];
    apply StrictAntiOn.antitoneOn Φm_strictAnti; simp only [Set.mem_Iio]; linarith; simp only [Set.mem_Iio]; linarith; linarith
  have i2: Φm x - Φm xs = F xs (xs -x):=by simp only [F, sub_sub_cancel]
  rw[i1, i2]; rw[abs_of_nonpos (by linarith)] at hd
  apply max_of_F hxs (by linarith) (by linarith)



