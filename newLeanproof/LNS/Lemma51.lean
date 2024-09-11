import LNS.Common
import LNS.Tactic
import LNS.Basic

open LNS

lemma Lemma51 (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) : |Ep i r| ≤ Ep 0 Δ := by
  rw [abs_of_nonneg (Ep_r_nonneg hr1)]
  have ieq1:= Ep_i_monotone hr1 hi Set.right_mem_Iic hi
  simp only [Ep_i] at ieq1
  have ieq2: Ep 0 r ≤ Ep 0 Δ :=by
    apply Ep_r_monotone _ _ hr2
    simp only [Set.mem_Ici, hr1]
    simp only [Set.mem_Ici]; linarith
  linarith
