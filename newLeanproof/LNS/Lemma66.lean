import LNS.Common
import LNS.Tactic
import LNS.Basic
import LNS.Lemma62
import LNS.Lemma61
import LNS.Lemma63
import LNS.Lemma65
set_option maxHeartbeats 10000000

noncomputable section
open LNS
open Real
open Real Filter Topology


lemma Vm_pos : X > 1 →  Vm X > 0 :=by
  have i1: ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have i2: ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  unfold Vm
  apply pos_of_deriv_pos_Ici
  fun_prop (disch:= assumption);
  simp only [log_one, mul_zero, mul_one, zero_sub, neg_eq_zero, log_eq_zero, sub_eq_neg_self,
    OfNat.ofNat_ne_zero, or_false, (by linarith: (2:ℝ) - 1 = 1)]
  intro x hx
  get_deriv (fun {X} ↦ 2 * log X - log (2 * X - 1)) at x
  simp only [List.Forall, toFun, ne_eq, id_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
  constructor <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h]
  have:  2*x - 1 > 0 := by linarith
  field_simp; linarith

lemma deriv_Cm : Y > 1 → deriv Cm Y = 2*(Y-1)/(Y^2*(2*Y-1)) :=by
  intro h; unfold Cm
  get_deriv (fun Y ↦ 2 * log Y - 2 * log (2 * Y - 1) + 2 - 2 / Y) at Y
  simp only [List.Forall, toFun, ne_eq, id_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
  split_ands <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h]
  have:  2*Y - 1 > 0 := by linarith
  field_simp; ring_nf

lemma Cm_pos: Y > 1 →  Cm Y > 0 :=by
  apply pos_of_deriv_pos_Ici
  unfold Cm
  have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  unfold Cm
  simp only [log_one, mul_zero, mul_one, (by linarith : (2 : ℝ) - 1 = 1), sub_self, zero_add, div_one]
  intro x hx; rw[deriv_Cm hx];
  have:  2*x - 1 > 0 := by linarith
  have:  x - 1 > 0 := by linarith
  positivity

lemma Am_pos: Y > 1 →  Am Y > 0 :=by
  intro h
  have e: Am Y = (Cm Y)*Y := by simp only [Am, Cm]; field_simp; ring_nf
  rw[e]; apply mul_pos (Cm_pos h) (by linarith)

lemma Bm_pos  : Y > 1 →  Bm Y > 0 :=by
  intro h; unfold Bm; apply mul_pos (by linarith) (Vm_pos h)

def Rm (Y:ℝ) := Am Y - (Bm Y)/Y

def dRm (Y:ℝ) := 2 * log Y - 2 * log (2*Y - 1) +2 - 2/Y

lemma deriv_Rm : Y > 1 → deriv Rm Y = dRm Y :=by
  intro hy ; unfold Rm Am Bm dRm Vm
  get_deriv (fun Y ↦ 2 * Y * log Y - 2 * Y * log (2 * Y - 1) + 2 * Y - 2 - Y * (2 * log Y - log (2 * Y - 1)) / Y) at Y
  simp only [List.Forall, toFun, ne_eq, id_eq];
  split_ands <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h];
  have:  2*Y - 1 > 0 := by linarith
  field_simp; ring_nf

lemma deriv_dRm  : Y > 1 → deriv dRm Y = 2*(Y-1)/(Y^2*(2*Y-1)):=by
  intro h ; unfold dRm
  get_deriv (fun Y ↦ 2 * log Y - 2 * log (2 * Y - 1) + 2 - 2 / Y) at Y
  simp only [List.Forall, toFun, ne_eq, id_eq, OfNat.ofNat_ne_zero, not_false_eq_true, true_and]
  split_ands <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h];
  have:  2*Y - 1 > 0 := by linarith
  field_simp; ring_nf

lemma dRm_pos:  Y > 1 →  dRm Y > 0 :=by
  apply pos_of_deriv_pos_Ici
  unfold dRm
  have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  simp only [dRm, log_one, mul_zero, mul_one, (by linarith : 2 - (1 : ℝ) = 1), sub_self, zero_add, div_one];
  intro x hx; rw[deriv_dRm hx];
  have: 2*x - 1 > 0 :=by linarith
  have: x - 1 > 0 :=by linarith
  positivity

lemma Rm_pos:  Y > 1 →  Rm Y > 0 :=by
  apply pos_of_deriv_pos_Ici
  unfold Rm Am Bm Vm
  have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  simp only [Rm, Am, mul_one, log_one, mul_zero, (by linarith : 2 - (1 : ℝ) = 1), sub_self,
    zero_add, Bm, Vm, div_one]
  intro x hx; rw[deriv_Rm hx]; exact dRm_pos hx

lemma Max_Xm_lt_X (h: Y > 1): Max_Xm Y < Y :=by
  unfold Max_Xm
  have i1: Am Y > 0 := Am_pos h
  have i2: Y/ Am Y > 0 :=by positivity
  have i3: Am Y - (Bm Y)/Y > 0:= Rm_pos h
  simp only [gt_iff_lt, sub_pos] at i3
  have i3: (Bm Y / Y)* (Y/ Am Y) < Am Y * (Y/ Am Y):=  (mul_lt_mul_right i2).mpr i3
  field_simp at i3
  exact i3

def Mm (Y:ℝ) := (Bm Y - Am Y)/Y

lemma deriv_Mm:  Y > 1 → deriv Mm Y = 2*(Y-1)^2/(Y^2*(2*Y-1)) :=by
  intro h
  unfold Mm Am Bm Vm
  get_deriv (fun Y ↦ (Y * (2 * log Y - log (2 * Y - 1)) - (2 * Y * log Y - 2 * Y * log (2 * Y - 1) + 2 * Y - 2)) / Y) at Y
  simp only [List.Forall, toFun, ne_eq, id_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true,
    true_and]
  split_ands <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h];
  have: 2*Y - 1 > 0 :=by linarith
  field_simp; ring_nf

lemma Mm_pos : Y > 1 → Mm Y > 0:=by
  apply pos_of_deriv_pos_Ici
  unfold Mm Am Bm Vm
  have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  simp only [Mm, Bm, Vm, log_one, mul_zero, mul_one, (by linarith : (2 : ℝ) - 1 = 1), sub_self, Am,
    zero_add, div_one]
  intro x hx; rw[deriv_Mm hx];
  have: x - 1 > 0 := by linarith
  have: 2*x - 1 > 0 := by linarith
  positivity

lemma Max_Xm_gt_one (h: Y > 1): Max_Xm Y > 1 :=by
  unfold Max_Xm
  have i1: Am Y > 0 := Am_pos h
  have i2: (Bm Y - Am Y)/Y > 0:= Mm_pos h
  field_simp at i2
  exact (one_lt_div i1).mpr i2

lemma deriv_Qm_Range_YX (hY: Y > 1) : Set.EqOn (deriv (Qm_Range_YX Y)) (dQm_Range_YX Y) (Set.Ioi 1):=by
  have i1:= Vm_pos hY
  have i4:= U_pos hY
  intro X hX; simp only [Set.mem_Ioi] at hX; unfold Qm_Range_YX Qm_hi_YX Qm_lo_YX U Vm
  get_deriv (fun X ↦ (2 * log X - log (2 * X - 1)) / (2 * log Y - log (2 * Y - 1)) - (1 / X + log X - 1) / (1 / Y + log Y - 1)) at X
  simp only [Set.mem_Ioi, List.Forall, toFun, one_div, ne_eq, id_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, and_true, true_and, and_self_left]
  rw[(by simp only [one_div]: Y⁻¹  = 1/Y )]
  split_ands <;> try linarith
  unfold Vm at i1; linarith
  unfold U at i4; linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h]
  simp only [zero_mul, mul_one, zero_sub, Nat.cast_ofNat, rpow_two, one_div, sub_zero, mul_zero,
    sub_self, zero_div, add_zero, zero_add]
  simp only [← one_div]
  rw[(by simp only [Vm] : 2 * log Y - log (2 * Y - 1) = Vm Y ), (by simp only [U] : 1 / Y + log Y - 1 = U Y)]
  have: 2*X - 1 > 0 := by linarith
  have e1: (2 * (1 / X) - 2 / (2 * X - 1)) * Vm Y / Vm Y ^ 2 - (-1 / X ^ 2 + 1 / X) * U Y / U Y ^ 2
      = (X-1)*(2*U Y * X  - Vm Y*(2*X -1))/(U Y * Vm Y * X^2 * (2*X-1)) :=by field_simp; ring_nf
  have e2: dQm_Range_YX Y X = (X-1)*((-Am Y * X + Bm Y)/Y)/ (U Y* Vm Y*X^2*(2*X-1)):=by
    unfold dQm_Range_YX; field_simp; ring_nf; simp only [true_or]
  have e3: (-Am Y * X + Bm Y)/Y = (2*U Y * X  - Vm Y*(2*X -1)) :=by
    unfold Am Bm Vm U ; field_simp; ring
  rw[e1, e2, e3]

lemma max_Qm_Range_YX (h1: X > 1) (h2: X < Y): Qm_Range_YX Y X ≤ Qm_Range_YX Y (Max_Xm Y) :=by
  have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have hY: Y > 1 :=by linarith
  have iA: Am Y > 0 := Am_pos hY
  have iV:= Vm_pos hY
  have iU:= U_pos hY
  have cont: ContinuousOn (Qm_Range_YX Y) (Set.Ici 1) :=by
    unfold Qm_Range_YX Qm_hi_YX Qm_lo_YX U Vm
    fun_prop (disch:= assumption);
  have first_half: StrictMonoOn (Qm_Range_YX Y) (Set.Icc 1 (Max_Xm Y)):=by
    apply strictMonoOn_of_deriv_pos (convex_Icc 1 (Max_Xm Y))
    apply ContinuousOn.mono cont
    rw[Set.Icc_subset_Ici_iff];
    linarith [Max_Xm_gt_one hY]
    intro x hx; simp only [interior_Icc, Set.mem_Ioo] at hx;
    rw[deriv_Qm_Range_YX hY, dQm_Range_YX ]
    have i1: Am Y * x < Am Y * Max_Xm Y := (mul_lt_mul_left iA).mpr hx.right
    unfold Max_Xm at i1; field_simp at i1
    have : -Am Y * x + Bm Y > 0 :=by linarith
    have: (x - 1) > 0 := by linarith
    have: 2*x - 1 > 0 := by linarith
    have : x > 0 := by linarith
    positivity
    simp only [Set.mem_Ioi]; linarith
  have second_half: StrictAntiOn (Qm_Range_YX Y) (Set.Icc (Max_Xm Y) Y):=by
    apply strictAntiOn_of_deriv_neg (convex_Icc (Max_Xm Y) Y)
    apply ContinuousOn.mono cont
    rw[Set.Icc_subset_Ici_iff];
    linarith [Max_Xm_gt_one hY]; linarith [Max_Xm_lt_X hY]
    intro x hx; simp only [interior_Icc, Set.mem_Ioo] at hx;
    rw[deriv_Qm_Range_YX hY, dQm_Range_YX ]
    have i1: Am Y * x > Am Y * Max_Xm Y := (mul_lt_mul_left iA).mpr hx.left
    unfold Max_Xm at i1; field_simp at i1
    have: (x - 1) > 0 := by linarith [Max_Xm_gt_one hY]
    have : x > 0 := by linarith
    apply mul_neg_of_pos_of_neg
    have: 2*x - 1 > 0 := by linarith
    positivity; linarith
    simp only [Set.mem_Ioi]; linarith[Max_Xm_gt_one hY]
  by_cases (X ≤  (Max_Xm Y))
  apply StrictMonoOn.monotoneOn first_half
  simp only [Set.mem_Icc] ; constructor <;> linarith
  simp only [Set.mem_Icc] ; constructor <;> linarith
  assumption
  apply StrictAntiOn.antitoneOn second_half
  simp only [Set.mem_Icc] ; constructor <;> linarith
  simp only [Set.mem_Icc] ; constructor <;> linarith
  linarith

lemma Qm_Range_YX_eq_Qm_range (hΔ : 0 < Δ) (hr: 0 < r) :  Qm_Range Δ r =  Qm_Range_YX (2^Δ) (2^r) :=by
  unfold Qm_Range Qm_Range_YX
  have hΔ0: Δ > 0 := by linarith
  have e1: ∀ x > (0:ℝ), (2:ℝ)^(-x) = 1/2^x :=by intro x _; rw[rpow_neg]; ring_nf; simp only [Nat.ofNat_nonneg]
  have e2: ∀ x > (0:ℝ), log ((2:ℝ)^x) = x * log 2 :=by intro x _; rw[log_rpow]; simp only [Nat.ofNat_pos]
  have eh : Qm_lo Δ r = Qm_lo_YX (2 ^ Δ) (2 ^ r) :=by
    unfold Qm_lo Qm_lo_YX U
    simp only [e1 r hr, e1 Δ hΔ0, e2 r hr, e2 Δ hΔ0]
  have el : Qm_hi Δ r = Qm_hi_YX (2 ^ Δ) (2 ^ r) :=by
    unfold Qm_hi Qm_hi_YX Vm ;
    rw[Qm_of_Fm (by simp only [Set.mem_Iio, Left.neg_neg_iff,zero_lt_one]) hr hΔ]
    have: Fm (2 ^ Δ) (2 ^ (-1:ℝ )) > 0 :=by
      apply Fm_pos;
      simp only [Set.mem_Ioo, Nat.ofNat_pos,rpow_pos_of_pos, true_and]
      ring_nf; field_simp; simp only [Set.mem_Ioi]; apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ
    have: 2 * log (2 ^ Δ) - log (2 * 2 ^ Δ - 1) > 0 :=by apply Vm_pos (one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ)
    simp only [Function.comp_apply]; field_simp
    have e1: ∀ r > (0:ℝ),  log (2 ^ r - 2 ^ (-1:ℝ )) = log (2*2^r -1) - log 2:=by
      intro r hr
      have: (2:ℝ) ^ r - 2 ^ (-1:ℝ ) = (2*2^r -1)/2 :=by field_simp; ring_nf
      rw[this, log_div]
      have: (2:ℝ)^r > 1:=by apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hr
      linarith; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    have e2: log (1 / 2) = - log 2 :=by simp only [one_div, log_inv]
    simp only [Function.comp_apply, Fm, (by field_simp; ring: ((1:ℝ) - 2 ^ (-1:ℝ)) = 1/2), e1 r hr, e1 Δ hΔ, e2]
    field_simp; ring_nf
  rw[el,eh]

lemma lemma66sub  (hΔ  : r < Δ) (hr : 0 < r) : Qm_Range Δ r ≤ Qm_Range Δ (Rm_opt Δ) := by
  have hΔ0: 0 < Δ := by linarith
  have i1: (2:ℝ)  ^ Δ > 1 :=by apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ0
  have i2: (2:ℝ)  ^ r > 1 :=by apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hr
  have hRm_opt0: 0 < Rm_opt Δ:= logb_pos (by simp only [Nat.one_lt_ofNat]) (Max_Xm_gt_one i1)
  rw [Qm_Range_YX_eq_Qm_range hΔ0 hr, Qm_Range_YX_eq_Qm_range hΔ0 hRm_opt0]
  have : 2 ^ Rm_opt Δ = Max_Xm (2 ^ Δ) :=by
    have iA := @Am_pos (2 ^ Δ) i1;
    have iB := @Bm_pos (2 ^ Δ) i1;
    unfold Rm_opt Max_Xm; simp only;
    rw[Real.rpow_logb]; simp only [Nat.ofNat_pos];
    simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    positivity
  rw[this]
  apply max_Qm_Range_YX i2
  apply rpow_lt_rpow_of_exponent_lt (by simp only [Nat.one_lt_ofNat]) hΔ


lemma qm_upper_bound (hi : i ≤ -1) (hr1 : 0 < r) (hr2 : r < Δ) : Qm Δ i r ≤ Qm_hi Δ r  :=
  StrictMonoOn.monotoneOn (Lemma65 hr1 hr2) hi Set.right_mem_Iic hi

lemma qm_lower_bound (hi : i ≤ -1) (hr : 0 < r) (hΔ : r < Δ) :  Qm_lo Δ r ≤ Qm Δ i r := by
  apply le_of_tendsto (Lemma61m hr (by linarith))
  simp only [eventually_atBot]
  use i; intro b hb;
  apply StrictMonoOn.monotoneOn (Lemma65 hr hΔ) (by simp only [Set.mem_Iic]; linarith) (by simp only [Set.mem_Iic]; linarith) hb


lemma Lemma66 (hi : i ≤ -1) (hc : c ≤ -1) (hr : 0 < r) (hΔ : r < Δ) :
    |Qm Δ i r - Qm Δ c r| ≤ Qm_hi Δ (Rm_opt Δ) - Qm_lo Δ (Rm_opt Δ) := by
  have i1:  Qm_hi Δ r - Qm_lo Δ r ≤ Qm_hi Δ (Rm_opt Δ) - Qm_lo Δ (Rm_opt Δ):=by apply lemma66sub hΔ hr
  have case1:  Qm Δ i r - Qm Δ c r ≥ 0 → |Qm Δ i r - Qm Δ c r| ≤ Qm_hi Δ (Rm_opt Δ) - Qm_lo Δ (Rm_opt Δ) :=by
    intro i0
    have i2: Qm Δ i r ≤ Qm_hi Δ r := by apply qm_upper_bound; linarith; assumption; assumption;
    have i3: Qm_lo Δ r ≤ Qm Δ c r := by apply qm_lower_bound; assumption; assumption; assumption;
    have e0:   |Qm Δ i r - Qm Δ c r| = Qm Δ i r - Qm Δ c r :=by apply abs_of_nonneg; linarith
    linarith
  apply by_cases case1; simp;
  intro i0
  have i2: Qm Δ c r ≤ Qm_hi Δ r := by apply qm_upper_bound; linarith; assumption; assumption;
  have i3: Qm_lo Δ r ≤ Qm Δ i r := by apply qm_lower_bound; assumption; assumption; assumption;
  have e0:   |Qm Δ i r - Qm Δ c r| = -(Qm Δ i r - Qm Δ c r) :=by apply abs_of_neg; linarith
  linarith
