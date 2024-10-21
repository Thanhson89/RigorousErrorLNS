import LNS.Common
import LNS.Tactic
import LNS.Basic
import LNS.Lemma63
import LNS.Lemma64
import LNS.Lemma67
import LNS.Lemma51
import LNS.Lemma52
set_option maxHeartbeats 10000000

noncomputable section
open LNS
open Real


def EMp Δ := Ep 0 Δ

def QRp Δ :=  Qp_hi Δ (Rp_opt Δ) - Qp_lo Δ (Rp_opt Δ)

def QIp Δ ΔP := 1 - Qp_lo Δ (Δ - ΔP)

def EMm Δ := Em (-1) Δ

def QRm Δ :=  Qm_hi Δ (Rm_opt Δ) - Qm_lo Δ (Rm_opt Δ)

def QIm Δ ΔP := 1 - Qm_lo Δ (Δ - ΔP)

noncomputable def EECp (Δ ΔP c i r  : ℝ) := rnd (Φp i) - rnd (r * rnd (deriv Φp i) ) +
                      rnd (rnd (Ep i Δ) * rnd (Qp Δ c (Int.floor (r / ΔP) * ΔP)))

noncomputable def EECfixp (Δ ΔP c i r  : ℝ):= |Φp (i - r) - EECp Δ ΔP c i r|

noncomputable def EECm (Δ ΔP c i r  : ℝ) := rnd (Φm i) - rnd (r * rnd (deriv Φm i) ) -
                      rnd (rnd (Em i Δ) * rnd (Qm Δ c (Int.floor (r / ΔP) * ΔP)))

noncomputable def EECfixm (Δ ΔP c i r  : ℝ):= |Φm (i - r) - EECm  Δ ΔP c i r|

lemma Φp_eq_EC  (hr1 : 0 < r) (hr2 : r < Δ):
        Φp (i - r) = Φp i - r * (deriv Φp i) + (Ep i Δ)*(Qp Δ i r) :=by
  have ep : Ep i Δ > 0 := by apply Ep_r_pos; linarith
  unfold Qp; field_simp; unfold Ep; ring_nf

lemma Φm_eq_EC (hi: i ≤ -1) (hr1 : 0 < r) (hr2 : r < Δ):
        Φm (i - r) = Φm i - r * (deriv Φm i) - (Em i Δ)*(Qm Δ i r) :=by
  have ep : Em i Δ > 0 := by apply Em_r_pos; simp only [Set.mem_Iio]; linarith; linarith
  unfold Qm; field_simp; unfold Em; ring_nf

lemma hrndn :  |rnd x - x| ≤ ε := by
  have : |rnd x - x| = |x - rnd x| :=by apply abs_sub_comm
  rw[this]
  apply hrnd


lemma Qp_lt_1 (hr1 : 0 ≤ r) (hr2 : r < Δ): |rnd (Qp Δ c r)| ≤ (1:ℝ) :=by
  have i1: Qp Δ c r ≥ 0:= by
    unfold Qp; apply div_nonneg; apply Ep_r_nonneg; linarith; apply Ep_r_nonneg; linarith
  have i2: rnd (Qp Δ c r) ≥ 0 :=by
    rw[← rnd_0]; apply rnd_mono; assumption
  have e1: |rnd (Qp Δ c r)| = rnd (Qp Δ c r):= by apply abs_of_nonneg; assumption;
  rw[e1, ← rnd_1];  apply rnd_mono;
  unfold Qp; apply le_of_lt;
  have i3:  Ep c Δ >0 := by apply Ep_r_pos; linarith
  apply (div_lt_one i3).mpr
  apply Ep_r_strictMonotone;
  any_goals simp;
  any_goals linarith;

lemma Qm_lt_1 (hc: c ≤ -1) (hr1 : 0 ≤ r) (hr2 : r < Δ): |rnd (Qm Δ c r)| ≤ (1:ℝ) :=by
  have i1: Qm Δ c r ≥ 0:= by
    unfold Qm; apply div_nonneg;
    apply Em_r_nonneg; simp only [Set.mem_Iio]; linarith; assumption;
    apply Em_r_nonneg; simp only [Set.mem_Iio]; linarith; linarith;
  have i2: rnd (Qm Δ c r) ≥ 0 :=by
    rw[← rnd_0]; apply rnd_mono; assumption
  have e1: |rnd (Qm Δ c r)| = rnd (Qm Δ c r):= by apply abs_of_nonneg; assumption;
  rw[e1, ← rnd_1];  apply rnd_mono;
  unfold Qm; apply le_of_lt;
  have i3:  Em c Δ >0 := by apply Em_r_pos; simp only [Set.mem_Iio]; linarith; linarith
  apply (div_lt_one i3).mpr
  apply Em_r_strictMonotone;
  any_goals simp;
  any_goals linarith;


lemma sum_8_abs1 (a1 a2 a3 a4 a5 a6 a7 a8 :ℝ) :
  |a1+a2+a3+a4+a5+a6+a7+a8| ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8|:=by
  have i1 :  |a1+a2+a3+a4+a5+a6+a7+a8|  ≤  |a1+a2+a3+a4+a5+a6+a7|+|a8|:= by  apply abs_add
  have i2 :  |a1+a2+a3+a4+a5+a6+a7|  ≤  |a1+a2+a3+a4+a5+a6|+|a7|:= by  apply abs_add
  have i3 :  |a1+a2+a3+a4+a5+a6|  ≤  |a1+a2+a3+a4+a5|+|a6|:= by  apply abs_add
  have i4 :  |a1+a2+a3+a4+a5|  ≤  |a1+a2+a3+a4|+|a5|:= by  apply abs_add
  have i5 :  |a1+a2+a3+a4|  ≤  |a1+a2+a3|+|a4|:= by  apply abs_add
  have i6 :  |a1+a2+a3|  ≤  |a1+a2|+|a3|:= by  apply abs_add
  have i7 :  |a1+a2|  ≤  |a1|+|a2|:= by  apply abs_add
  linarith;

lemma sum_8_abs2 (a1 a2 a3 a4 a5 a6 a7 a8 :ℝ) :
  |a1+ a2 + a3 - (a4 + a5 + a6 + a7 + a8)| ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8|:=by
  have i1 :  |a1+a2+a3-(a4 + a5 + a6 + a7 + a8)|  ≤  |a1+a2+a3| + |a4+a5+a6+a7+a8|:= by  apply abs_sub
  have i2 :  |a1+a2+a3|  ≤  |a1+a2|+|a3|:= by  apply abs_add
  have i3 :  |a1+a2|  ≤  |a1|+|a2|:= by  apply abs_add
  have i4 :  |a4+a5+a6+a7+a8|  ≤  |a4+a5+a6+a7|+|a8|:= by  apply abs_add
  have i5 :  |a4+a5+a6+a7|  ≤  |a4+a5+a6|+|a7|:= by  apply abs_add
  have i6 :  |a4+a5+a6|  ≤  |a4+a5|+|a6|:= by  apply abs_add
  have i7 :  |a4+a5|  ≤  |a4|+|a5|:= by  apply abs_add
  linarith;

lemma Theorem68p (hi : i ≤ 0)(hc : c ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) (hΔ:  ΔP < Δ ) (hΔP:  ΔP > 0 ):
    EECfixp Δ ΔP c i r ≤ (4+Δ)*ε + (EMp Δ) * (QRp Δ + QIp Δ ΔP + ε) := by
    set rr := (Int.floor (r / ΔP) * ΔP)
    set a1 := Φp i - rnd (Φp i)
    set a2 := rnd (r * rnd (deriv Φp i) ) - r * rnd (deriv Φp i)
    set a3 := r * (rnd (deriv Φp i) -  (deriv Φp i))
    set a4 := (Ep i Δ)*((Qp Δ i r) - (Qp Δ c r))
    set a5 := (Ep i Δ)*((Qp Δ c r) - (Qp Δ c rr))
    set a6 := (Ep i Δ)*((Qp Δ c rr) - (rnd (Qp Δ c rr)))
    set a7 := (rnd (Qp Δ c rr)) * ((Ep i Δ) - (rnd (Ep i Δ) ) )
    set a8 := (rnd (Ep i Δ) ) * (rnd (Qp Δ c rr)) - rnd (rnd (Ep i Δ) * rnd (Qp Δ c rr))

    have irr0: rr ≥ 0:= by
      apply mul_nonneg; simp; apply Int.floor_nonneg.mpr;
      apply div_nonneg;
      any_goals linarith;

    have irr1: r - rr ≥ 0:= by
      simp only [ge_iff_le, sub_nonneg];
      have i2: Int.floor (r / ΔP) * ΔP ≤ r / ΔP * ΔP := by
        apply mul_le_mul; apply Int.floor_le; simp only [le_refl]; linarith
        apply div_nonneg;
        any_goals linarith;
      have e0: r / ΔP * ΔP = r := by field_simp
      rw[e0] at i2; exact i2

    have eq0: Φp (i - r) - EECp  Δ ΔP c i r = a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 := by
      rw[Φp_eq_EC hr1 hr2]; unfold EECp; ring_nf
    have i0 : |Ep i Δ| ≤ (EMp Δ) := by unfold EMp; apply Lemma51 hi ; linarith; linarith
    have i01 :  (EMp Δ) ≥ 0 :=by
      have : |Ep i Δ| ≥ 0 := by simp;
      linarith
    have i1 : |a1| ≤ ε := by apply hrnd
    have i2 : |a2| ≤ ε := by apply hrndn;
    have i3 : |a3| ≤ Δ * ε := by
      have e1 : |a3| = |r| * |rnd (deriv Φp i) -  (deriv Φp i)| :=by apply abs_mul
      have e2 : |r| = r := by apply abs_of_pos hr1;
      rw[e1,e2]; apply mul_le_mul; linarith; apply hrndn; simp only [abs_nonneg]; linarith;
    have i4 : |a4| ≤ (EMp Δ) * (QRp Δ) :=by
      have e1: |a4| = |Ep i Δ| * |(Qp Δ i r) - (Qp Δ c r)| := by apply  abs_mul
      have i1: |(Qp Δ i r) - (Qp Δ c r)| ≤ (QRp Δ):= by apply lemma63; any_goals linarith
      rw[e1] ; apply mul_le_mul; assumption;  assumption;  simp; assumption;
    have i5: |a5| ≤ (EMp Δ) * (QIp Δ ΔP) :=by
      have e1: |a5| = |Ep i Δ| * |(Qp Δ c r) - (Qp Δ c rr)| := by apply  abs_mul
      have i1: |(Qp Δ c r) - (Qp Δ c rr)| ≤ QIp Δ ΔP := by apply lemma64; any_goals linarith
      rw[e1] ; apply mul_le_mul; assumption;  assumption;  simp; assumption;
    have i6: |a6| ≤ (EMp Δ) * ε :=by
      have e1: |a6| = |Ep i Δ| * |(Qp Δ c rr) - (rnd (Qp Δ c rr))| := by apply  abs_mul
      have i1: |(Qp Δ c rr) - (rnd (Qp Δ c rr))| ≤ ε := by apply hrnd
      rw[e1] ; apply mul_le_mul; assumption;  assumption; simp; assumption;
    have i7: |a7| ≤  ε :=by
      have e1: |a7| = |rnd (Qp Δ c rr)| * |(Ep i Δ) - (rnd (Ep i Δ) )| := by apply  abs_mul
      have i1: |(Ep i Δ) - (rnd (Ep i Δ) )| ≤ ε := by apply hrnd
      have i2: |rnd (Qp Δ c rr)| ≤ (1:ℝ) :=by
        apply Qp_lt_1 irr0 (by linarith)
      have e2: ε = (1:ℝ) * ε :=by simp
      rw[e1, e2] ; apply mul_le_mul; assumption;  assumption; simp; linarith;
    have i8: |a8| ≤  ε  := by apply hrnd
    have isum: EECfixp  Δ ΔP c i r ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8|:=by
      unfold EECfixp; rw[eq0]; apply sum_8_abs1
    linarith



lemma Theorem68m (hi : i ≤ -1)(hc : c ≤ -1) (hr1 : 0 < r) (hr2 : r < Δ) (hΔ:  ΔP < Δ ) (hΔP:  ΔP > 0 ):
    EECfixm Δ ΔP c i r ≤ (4+Δ)*ε + (EMm Δ) * (QRm Δ + QIm Δ ΔP + ε) := by
    set rr := (Int.floor (r / ΔP) * ΔP)
    set a1 := Φm i - rnd (Φm i)
    set a2 := rnd (r * rnd (deriv Φm i) ) - r * rnd (deriv Φm i)
    set a3 := r * (rnd (deriv Φm i) -  (deriv Φm i))
    set a4 := (Em i Δ)*((Qm Δ i r) - (Qm Δ c r))
    set a5 := (Em i Δ)*((Qm Δ c r) - (Qm Δ c rr))
    set a6 := (Em i Δ)*((Qm Δ c rr) - (rnd (Qm Δ c rr)))
    set a7 := (rnd (Qm Δ c rr)) * ((Em i Δ) - (rnd (Em i Δ) ) )
    set a8 := (rnd (Em i Δ) ) * (rnd (Qm Δ c rr)) - rnd (rnd (Em i Δ) * rnd (Qm Δ c rr))

    have irr0: rr ≥ 0:= by
      apply mul_nonneg; simp; apply Int.floor_nonneg.mpr;
      apply div_nonneg;
      any_goals linarith;

    have irr1: r - rr ≥ 0:= by
      simp only [ge_iff_le, sub_nonneg];
      have i2: Int.floor (r / ΔP) * ΔP ≤ r / ΔP * ΔP := by
        apply mul_le_mul; apply Int.floor_le; simp only [le_refl]; linarith
        apply div_nonneg;
        any_goals linarith;
      have e0: r / ΔP * ΔP = r := by field_simp
      rw[e0] at i2; exact i2

    have eq0: Φm (i - r) - EECm  Δ ΔP c i r = a1 + a2 + a3 - (a4 + a5 + a6 + a7 + a8) := by
      rw[Φm_eq_EC hi hr1 hr2]; unfold EECm; ring_nf
    have i0 : |Em i Δ| ≤ (EMm Δ) := by unfold EMm; apply Lemma52 hi ; linarith; linarith
    have i01 :  (EMm Δ) ≥ 0 :=by
      have : |Em i Δ| ≥ 0 := by simp only [ge_iff_le, abs_nonneg];
      linarith
    have i1 : |a1| ≤ ε := by apply hrnd
    have i2 : |a2| ≤ ε := by apply hrndn;
    have i3 : |a3| ≤ Δ * ε := by
      have e1 : |a3| = |r| * |rnd (deriv Φm i) -  (deriv Φm i)| :=by apply abs_mul
      have e2 : |r| = r := by apply abs_of_pos hr1;
      rw[e1,e2]; apply mul_le_mul; linarith; apply hrndn; simp only [abs_nonneg]; linarith;
    have i4 : |a4| ≤ (EMm Δ) * (QRm Δ) :=by
      have e1: |a4| = |Em i Δ| * |(Qm Δ i r) - (Qm Δ c r)| := by apply  abs_mul
      have i1: |(Qm Δ i r) - (Qm Δ c r)| ≤ (QRm Δ):= by apply Lemma66; any_goals linarith
      rw[e1] ; apply mul_le_mul; assumption;  assumption;  simp; assumption;
    have i5: |a5| ≤ (EMm Δ) * (QIm Δ ΔP) :=by
      have e1: |a5| = |Em i Δ| * |(Qm Δ c r) - (Qm Δ c rr)| := by apply  abs_mul
      have i1: |(Qm Δ c r) - (Qm Δ c rr)| ≤ QIm Δ ΔP := by apply Lemma67; any_goals linarith
      rw[e1] ; apply mul_le_mul; assumption;  assumption;  simp; assumption;
    have i6: |a6| ≤ (EMm Δ) * ε :=by
      have e1: |a6| = |Em i Δ| * |(Qm Δ c rr) - (rnd (Qm Δ c rr))| := by apply  abs_mul
      have i1: |(Qm Δ c rr) - (rnd (Qm Δ c rr))| ≤ ε := by apply hrnd
      rw[e1] ; apply mul_le_mul; assumption;  assumption; simp; assumption;
    have i7: |a7| ≤  ε :=by
      have e1: |a7| = |rnd (Qm Δ c rr)| * |(Em i Δ) - (rnd (Em i Δ) )| := by apply  abs_mul
      have i1: |(Em i Δ) - (rnd (Em i Δ) )| ≤ ε := by apply hrnd
      have i2: |rnd (Qm Δ c rr)| ≤ (1:ℝ) :=by
        apply Qm_lt_1 hc irr0 (by linarith)
      have e2: ε = (1:ℝ) * ε :=by simp
      rw[e1, e2] ; apply mul_le_mul; assumption;  assumption; simp; linarith;
    have i8: |a8| ≤  ε  := by apply hrnd
    have isum: EECfixm  Δ ΔP c i r ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8|:=by
      unfold EECfixm; rw[eq0]; apply sum_8_abs2
    linarith
