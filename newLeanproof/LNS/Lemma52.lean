import LNS.Common
import LNS.Tactic
import LNS.Basic

open LNS

lemma Lemma52 (hi : i ≤ (-1:ℝ)) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) : |Em i r| ≤ Em (-1) Δ := by
  rw [abs_of_nonneg (Em_r_nonneg _ hr1)]
  have ieq1:= Em_i_monotone hr1 (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio,
    Left.neg_neg_iff, zero_lt_one]) hi
  simp only [Em_i] at ieq1
  have ieq2: Em (-1) r ≤ Em (-1) Δ :=by
    apply StrictMonoOn.monotoneOn (Em_r_strictMono _)
    simp only [Set.mem_Ici, hr1]
    simp only [Set.mem_Ici]; linarith
    exact hr2
    simp only [Set.mem_Iio, Left.neg_neg_iff, zero_lt_one]
  linarith
  simp only [Set.mem_Iio]; linarith
