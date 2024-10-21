import LNS.Common
import LNS.Basic
import LNS.Lemma71
set_option maxHeartbeats 10000000

noncomputable section

open LNS
open Real
open Real Filter Topology



opaque Φe : ℝ → ℝ

opaque EΦ  : ℝ

axiom hΦe : ∀ x , |Φe x - Φm x| ≤ EΦ

lemma hΦen :  |Φm x - Φe x| ≤ EΦ := by
  have : |Φe x - Φm x| = |Φm x - Φe x| :=by apply abs_sub_comm
  rw[← this]
  apply hΦe

lemma hrndn :  |rnd x - x| ≤ ε := by
  have : |rnd x - x| = |x - rnd x| :=by apply abs_sub_comm
  rw[this]
  apply hrnd

/-Case 2-/

def rb2 (x:ℝ) (Δa:ℝ) := (Int.ceil (x/Δa) - 1) * Δa

def ra2 (x:ℝ) (Δa:ℝ) := (rb2 x Δa) - x

def k (x:ℝ) (Δa:ℝ):= x - Φm (rb2 x Δa)  + Φm (ra2 x Δa)

def Pest2 (x:ℝ) (Δa:ℝ) := Φm (rb2 x Δa) + Φm (k x Δa)

def krnd (x:ℝ) (Δa:ℝ) := x - rnd (Φm (rb2 x Δa) )  + rnd (Φm (ra2 x Δa) )

def Prnd2 (x:ℝ) (Δa:ℝ) := rnd (Φm (rb2 x Δa) ) + Φe (krnd x Δa)

lemma rb2_lt_x (ha:Δa >0): rb2 x Δa < x:=by
  unfold rb2
  have i11: (Int.ceil (x/Δa) -1 < x/Δa) ∧ ( x/Δa ≤ Int.ceil (x/Δa)) := by
    apply Int.ceil_eq_iff.mp; simp
  have i1: Int.ceil (x/Δa) -1 < x/Δa := i11.left
  have i2: (Int.ceil (x/Δa) -1)*Δa < (x/Δa)*Δa :=by apply (mul_lt_mul_right ha).mpr i1
  have e: (x/Δa)*Δa = x :=by field_simp;
  linarith

lemma k_neg (hx: x<0) (ha:Δa >0): k x Δa < 0 :=by
  have i1: rb2 x Δa < x := rb2_lt_x ha
  have : Φm (ra2 x Δa) < Φm (rb2 x Δa) :=by
    apply Φm_strictAnti
    any_goals simp;
    linarith; unfold ra2; linarith; unfold ra2; linarith
  unfold k; linarith


lemma cotrans2 (hx: x<0) (ha:Δa >0) : Φm x = Pest2 x Δa :=by
  unfold Pest2 Φm
  have i0: (2:ℝ) ^ x < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  have i1: (2:ℝ) ^ rb2 x Δa < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg; linarith;
    have i0: rb2 x Δa < x := rb2_lt_x ha
    linarith
  have i2: (2:ℝ) ^ k x Δa < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg; linarith;
    apply k_neg hx ha
  have i3: (2:ℝ) ^ ra2 x Δa < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg; linarith;
    have i0: rb2 x Δa < x := rb2_lt_x ha
    unfold ra2; linarith
  have e1: logb 2 (1 - 2 ^ rb2 x Δa) + logb 2 (1 - 2 ^ k x Δa) = logb 2 ((1 - 2 ^ rb2 x Δa) * (1 - 2 ^ k x Δa)) :=by
    rw [← logb_mul]; linarith; linarith
  rw[e1]; unfold logb; field_simp;
  apply Real.exp_eq_exp.mp;
  have e: rexp (log (1 - 2 ^ x)) = 1 - 2 ^ x := by apply Real.exp_log; linarith
  rw[e]
  have e: rexp (log ((1 - 2 ^ rb2 x Δa) * (1 - 2 ^ k x Δa)))= (1 - 2 ^ rb2 x Δa) * (1 - 2 ^ k x Δa):= by
    apply Real.exp_log; apply mul_pos; linarith; linarith
  rw[e]
  set a:= (2:ℝ)^ra2 x Δa
  set b:= (2:ℝ)^rb2 x Δa
  have e: 2^ k x Δa = 2^x * (1-(2:ℝ)^ra2 x Δa)/(1-(2:ℝ)^rb2 x Δa) :=by
    unfold k Φm; rw [rpow_add, rpow_sub, rpow_logb, rpow_logb]; field_simp;
    any_goals linarith;
  rw[e];
  have e: (1 - b) * (1 - 2 ^ x * (1 - a) / (1 - b)) = 1 - b - 2^x + a* 2^x  := by
    have i: 1 - b ≠ 0 := by linarith;
    field_simp; ring_nf
  rw[e];
  have e: a * (2:ℝ) ^ x = b :=by rw [← rpow_add]; unfold ra2; simp; linarith
  rw[e]; ring_nf


lemma bound_case2 (hx: x<0) (ha:Δa >0) (hk: k x Δa ≤ -1) (hkr: krnd  x Δa ≤ -1) :
      |Φm x - Prnd2 x Δa| ≤ ε +  Φm (-1-2*ε) - Φm (-1) + EΦ :=by
  have e: Φm x = Pest2 x Δa := cotrans2 hx ha
  rw[e]
  set s1:= Φm (rb2 x Δa) - rnd (Φm (rb2 x Δa) )
  set s2:= Φm (k x Δa) - Φm (krnd x Δa)
  set s3:= Φm (krnd x Δa) - Φe (krnd x Δa)
  have e: Pest2 x Δa - Prnd2 x Δa = s1 + s2 + s3  :=by unfold Pest2 Prnd2; ring_nf
  rw[e];
  have i01: |s1 + s2 + s3| ≤ |s1 + s2| + |s3|:= by apply abs_add
  have i02: |s1 + s2| ≤ |s1| + |s2|:= by apply abs_add
  have i1 : |s1| ≤ ε := by apply hrnd
  have i3 : |s3| ≤ EΦ := by apply hΦen;
  have i2 : |s2| ≤ Φm (-1-2*ε) - Φm (-1) :=by
    apply Lemma71 hk hkr
    set a1:= rnd (Φm (rb2 x Δa) ) - Φm (rb2 x Δa)
    set a2:= Φm (ra2 x Δa) - rnd (Φm (ra2 x Δa) )
    have e: k x Δa - krnd x Δa = a1 + a2:= by unfold k krnd; ring_nf;
    rw[e]
    have i0: |a1 + a2| ≤ |a1| + |a2|:= by apply abs_add
    have i1 : |a1| ≤ ε := by apply hrndn;
    have i2 : |a2| ≤ ε := by apply hrnd
    linarith
  linarith



/-Case 3-/

def rc (x:ℝ) (Δb:ℝ) := (Int.ceil (x/Δb) - 1) * Δb

def rab (x:ℝ) (Δb:ℝ) := (rc x Δb) - x

def rb (x:ℝ) (Δa:ℝ) (Δb:ℝ) := (Int.ceil ( rab x Δb  /Δa) - 1) * Δa

def ra (x:ℝ) (Δa:ℝ) (Δb:ℝ) :=  rb x Δa Δb  - rab x Δb

def k1 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := rab x Δb  - Φm (rb x Δa Δb)  + Φm (ra x Δa Δb)

def k2 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := x + Φm (rb x Δa Δb) + Φm (k1 x Δa Δb) - Φm (rc x Δb)

def Pest3 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := Φm (rc x Δb) +  Φm (k2 x Δa Δb)

def k1rnd (x:ℝ) (Δa:ℝ) (Δb:ℝ) := rab x Δb  - rnd (Φm (rb x Δa Δb))  + rnd (Φm (ra x Δa Δb))

def k2rnd (x:ℝ) (Δa:ℝ) (Δb:ℝ) := x + rnd (Φm (rb x Δa Δb)) + Φe (k1rnd x Δa Δb) - rnd (Φm (rc x Δb))

def Prnd3 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := rnd (Φm (rc x Δb)) +  Φe (k2rnd x Δa Δb)

lemma cotrans3 (hx: x<0) (ha:Δa >0) (hb:Δb >0): Φm x = Pest3 x Δa Δb :=by
  have e1: Φm x  = Pest2 x Δb := cotrans2 hx hb
  rw[e1]; unfold Pest2 Pest3
  have e0: rb2 x Δb = rc x Δb :=by unfold rb2 rc; simp;
  rw[e0]; simp;
  have e2: Φm (ra2 x Δb) = Φm (rb x Δa Δb) + Φm (k1 x Δa Δb) :=by
    apply cotrans2;
    have i0: rb2 x Δb < x := rb2_lt_x hb;
    unfold ra2; linarith; assumption
  have e: k x Δb = k2 x Δa Δb:=by
    unfold k k2; rw[e0, e2]; ring_nf;
  rw[e]


def Ek2 := 2*ε +  Φm (-1-2*ε) - Φm (-1) + EΦ

lemma bound_case3 (hx: x<0) (ha:Δa >0) (hb:Δb >0)
    (hk1: k1 x Δa Δb ≤ -1) (hk1r: k1rnd x Δa Δb ≤ -1)
    (hk2: k2 x Δa Δb ≤ -1) (hk2r: k2rnd x Δa Δb ≤ -1):
    |Φm x - Prnd3  x Δa Δb| ≤ ε +  Φm (-1- Ek2) - Φm (-1) + EΦ :=by
  have e: Φm x = Pest3 x Δa Δb := cotrans3 hx ha hb
  rw[e]
  set s1:= Φm (rc x Δb) - rnd (Φm (rc x Δb) )
  set s2:= Φm (k2 x Δa Δb) - Φm (k2rnd x Δa Δb)
  set s3:= Φm (k2rnd x Δa Δb) - Φe (k2rnd x Δa Δb)
  have e: Pest3 x Δa Δb - Prnd3 x Δa Δb = s1 + s2 + s3  :=by unfold Pest3 Prnd3; ring_nf
  rw[e];
  have i01: |s1 + s2 + s3| ≤ |s1 + s2| + |s3|:= by apply abs_add
  have i02: |s1 + s2| ≤ |s1| + |s2|:= by apply abs_add
  have i1 : |s1| ≤ ε := by apply hrnd
  have i3 : |s3| ≤ EΦ := by apply hΦen;
  have i2 : |s2| ≤  Φm (-1- Ek2) - Φm (-1) :=by
    apply Lemma71 hk2 hk2r
    set a1:=  Φm (rb x Δa Δb) - rnd ( Φm (rb x Δa Δb))
    set a2:=  rnd (Φm (rc x Δb)) - Φm (rc x Δb)
    set a3:=   Φm (k1 x Δa Δb) - Φm (k1rnd x Δa Δb)
    set a4:=  Φm (k1rnd x Δa Δb) - Φe (k1rnd x Δa Δb)
    have e: k2 x Δa Δb - k2rnd x Δa Δb = a1 + a2 + a3 + a4 := by unfold k2 k2rnd; ring_nf;
    rw[e]
    have i00: |a1 + a2 + a3 + a4| ≤ |a1 + a2 + a3| + |a4|:= by apply abs_add
    have i01: |a1 + a2 + a3| ≤ |a1 + a2| + |a3|:= by apply abs_add
    have i02: |a1 + a2| ≤ |a1| + |a2|:= by apply abs_add
    have i1 : |a1| ≤ ε := by apply hrnd
    have i2 : |a2| ≤ ε := by apply hrndn;
    have i4 : |a4| ≤ EΦ := by apply hΦen;
    have i3 : |a3| ≤  Φm (-1-2*ε) - Φm (-1) :=by
      apply Lemma71 hk1 hk1r
      set b1:= rnd (Φm (rb x Δa Δb)) - Φm (rb x Δa Δb)
      set b2:= Φm (ra x Δa Δb) - rnd (Φm (ra x Δa Δb))
      have e: k1 x Δa Δb - k1rnd x Δa Δb = b1 + b2 := by unfold k1 k1rnd; ring_nf;
      rw[e]
      have i0: |b1 + b2| ≤ |b1| + |b2|:= by apply abs_add
      have i1 : |b1| ≤ ε := by apply hrndn;
      have i2 : |b2| ≤ ε := by apply hrnd
      linarith
    unfold Ek2; linarith
  linarith
