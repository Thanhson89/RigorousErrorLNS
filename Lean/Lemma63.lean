import LNS.Common
import LNS.Tactic
import LNS.Basic
import LNS.Lemma62
import LNS.Lemma61

noncomputable section
open LNS
open Real
open Real Filter Topology



lemma V_pos : X > 1 →  V X > 0 :=by
  unfold V
  apply pos_of_deriv_pos_Ici
  have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  simp only [(by linarith : (1 : ℝ) + 1 = 2), log_one, sub_zero, sub_self]
  intro x hx
  get_deriv (fun {X} ↦ 2 * log (X + 1) - log X - 2 * log 2) at x
  simp only [List.Forall, toFun, ne_eq, id_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
  constructor <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h]
  field_simp; linarith

lemma deriv_C : Y > 1 → deriv C Y = 2/(Y*(Y+1)^2) :=by
  intro h; unfold C
  get_deriv (fun {Y} ↦ -2 * Y / (Y + 1) + 2 * log Y - 2 * log (Y + 1) + 2 * log 2 + 1) at Y
  simp only [List.Forall, toFun, ne_eq, id_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
  split_ands <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h]
  field_simp; ring_nf

lemma C_pos: Y > 1 →  C Y > 0 :=by
  apply pos_of_deriv_pos_Ici
  unfold C
  have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  unfold C
  simp only [mul_one, (by linarith : (1 : ℝ) + 1 = 2), ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, neg_div_self, log_one, mul_zero, add_zero, sub_add_cancel, neg_add_cancel]
  intro x hx; rw[deriv_C hx]; positivity

lemma deriv_A : Y > 1 → deriv A Y = C Y :=by
  intro h; unfold A C
  get_deriv (fun {Y} ↦ -2 * Y * (log (Y + 1) - log Y - log 2) - Y + 1) at Y
  simp only [List.Forall, toFun, ne_eq, id_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
  constructor <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h];
  field_simp; ring_nf

lemma A_pos: Y > 1 →  A Y > 0 :=by
  apply pos_of_deriv_pos_Ici
  unfold A
  have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  unfold A
  simp only [mul_one, (by linarith : (1 : ℝ) + 1 = 2), log_one, sub_zero, sub_self, mul_zero,
    zero_sub, neg_add_cancel]
  intro x hx; rw[deriv_A hx]; exact C_pos hx


lemma B_pos  : Y > 1 →  B Y > 0 :=by
  have : B Y = Y * V Y :=by unfold B V; ring_nf
  rw[this]; intro h; apply mul_pos (by linarith) (V_pos h)

def R (Y:ℝ) := A Y - (B Y)/Y

def dR (Y:ℝ) := 2 * log Y - 2 * log (Y + 1) - 1 + 2 * log 2 + 1/Y

lemma deriv_R : Y > 1 → deriv R Y = dR Y :=by
  intro h ; unfold R A B dR
  get_deriv (fun Y ↦ -2 * Y * (log (Y + 1) - log Y - log 2) - Y + 1 - Y * (2 * log (Y + 1) - log Y - 2 * log 2) / Y) at Y
  simp only [List.Forall, toFun, ne_eq, id_eq];
  split_ands <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h]; field_simp; ring_nf

lemma deriv_dR  : Y > 1 → deriv dR Y = (Y-1)/(Y^2*(Y+1)):=by
  intro h ; unfold dR
  get_deriv (fun Y ↦ 2 * log Y - 2 * log (Y + 1) - 1 + 2 * log 2 + 1 / Y) at Y
  simp only [List.Forall, toFun, ne_eq, id_eq, OfNat.ofNat_ne_zero, not_false_eq_true, true_and]
  split_ands <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h]; field_simp; ring_nf

lemma dR_pos:  Y > 1 →  dR Y > 0 :=by
  apply pos_of_deriv_pos_Ici
  unfold dR
  have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  simp only [dR, log_one, mul_zero, (by linarith : (1 : ℝ) + 1 = 2), zero_sub, ne_eq, one_ne_zero,
    not_false_eq_true, div_self]; ring_nf
  intro x hx; rw[deriv_dR hx];
  have: x - 1 > 0 :=by linarith
  positivity

lemma R_pos:  Y > 1 →  R Y > 0 :=by
  apply pos_of_deriv_pos_Ici
  unfold R A B
  have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  simp only [R, A, mul_one, (by linarith : (1 : ℝ) + 1 = 2), log_one, sub_zero, sub_self, mul_zero,
    zero_sub, neg_add_cancel, B, div_one]
  intro x hx; rw[deriv_R hx]; exact dR_pos hx

lemma Max_X_lt_X (h: Y > 1): Max_X Y < Y :=by
  unfold Max_X
  have i1: A Y > 0 := A_pos h
  have i2: Y/ A Y > 0 :=by positivity
  have i3: A Y - (B Y)/Y > 0:= R_pos h
  simp only [gt_iff_lt, sub_pos] at i3
  have i3: (B Y / Y)* (Y/ A Y) < A Y * (Y/ A Y):=  (mul_lt_mul_right i2).mpr i3
  field_simp at i3
  exact i3

def M (Y:ℝ) := (B Y - A Y)/Y

lemma deriv_M:  Y > 1 → deriv M Y = (Y-1)^2/(Y^2*(Y+1)) :=by
  intro h
  unfold M A B
  get_deriv (fun {Y} ↦ (Y * (2 * log (Y + 1) - log Y - 2 * log 2) - (-2 * Y * (log (Y + 1) - log Y - log 2) - Y + 1)) / Y) at Y
  simp only [List.Forall, toFun, ne_eq, id_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true,
    true_and]
  split_ands <;> linarith
  simp only [toFun] at h
  rw[HasDerivAt.deriv h]; field_simp; ring_nf

lemma M_pos : Y > 1 → M Y > 0:=by
  apply pos_of_deriv_pos_Ici
  unfold M A B
  have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  fun_prop (disch:= assumption);
  simp only [M, B, (by linarith : (1 : ℝ) + 1 = 2), log_one, sub_zero, sub_self, mul_zero, A,
    mul_one, zero_sub, neg_add_cancel, div_one]
  intro x hx; rw[deriv_M hx];
  have: x - 1 > 0 := by linarith
  positivity

lemma Max_X_gt_one (h: Y > 1): Max_X Y > 1 :=by
  unfold Max_X
  have i1: A Y > 0 := A_pos h
  have i2: (B Y - A Y)/Y > 0:= M_pos h
  field_simp at i2
  exact (one_lt_div i1).mpr i2

lemma deriv_Qp_Range_YX (hY: Y > 1) : Set.EqOn (deriv (Qp_Range_YX Y)) (dQp_Range_YX Y) (Set.Ioi 0):=by
  have i1: (2 * log (Y + 1) - log Y - 2 * log 2) > 0 := V_pos hY
  have i2: A Y > 0 := A_pos hY
  have i3: B Y > 0 := B_pos hY
  have i4: 1 / Y + log Y - 1 > 0 := U_pos hY
  intro X hX; unfold Qp_Range_YX Qp_hi_YX Qp_lo_YX U V
  get_deriv (fun X ↦ (1 / X + log X - 1) / (1 / Y + log Y - 1) -
        (2 * log (X + 1) - log X - 2 * log 2) / (2 * log (Y + 1) - log Y - 2 * log 2)) within (Set.Ioi 0)
  simp only [Set.mem_Ioi, List.Forall, toFun, one_div, ne_eq, id_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, and_true, true_and, and_self_left]
  intro x hx; rw[(by simp only [one_div]: Y⁻¹  = 1/Y )]
  split_ands <;> try linarith
  simp only [toFun] at h
  rw[h.right X hX]
  simp only [zero_mul, mul_one, zero_sub, Nat.cast_ofNat, rpow_two, one_div, sub_zero, mul_zero,
    sub_self, zero_div, add_zero, zero_add]
  simp only [Set.mem_Ioi] at hX
  simp only [← one_div]
  have : X ^ 2 * X * Y * (1 + log Y * Y - Y) ^ 2 >0 :=by
    have : X ^ 2 * X * Y * (1 + log Y * Y - Y) ^ 2 = X ^ 2 * X * Y ^ 3 * (1/Y + log Y -1) ^ 2 := by field_simp; ring
    rw[this]; positivity
  unfold dQp_Range_YX
  field_simp;
  unfold A B; ring

lemma max_Qp_Range_YX (h1: X > 1) (h2: X < Y): Qp_Range_YX Y X ≤ Qp_Range_YX Y (Max_X Y) :=by
  have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have hY: Y > 1 :=by linarith
  have iA: A Y > 0 := A_pos hY
  have iB: B Y > 0 := B_pos hY
  have cont: ContinuousOn (Qp_Range_YX Y) (Set.Ici 1) :=by
    unfold Qp_Range_YX Qp_hi_YX Qp_lo_YX U V
    fun_prop (disch:= assumption);
  have first_half: StrictMonoOn (Qp_Range_YX Y) (Set.Icc 1 (Max_X Y)):=by
    apply strictMonoOn_of_deriv_pos (convex_Icc 1 (Max_X Y))
    apply ContinuousOn.mono cont
    rw[Set.Icc_subset_Ici_iff];
    linarith [Max_X_gt_one hY]
    intro x hx; simp only [interior_Icc, Set.mem_Ioo] at hx;
    rw[deriv_Qp_Range_YX hY, dQp_Range_YX ]
    have i1: A Y * x < A Y * Max_X Y := (mul_lt_mul_left iA).mpr hx.right
    unfold Max_X at i1; field_simp at i1
    have : -A Y * x + B Y > 0 :=by linarith
    have: (x - 1) > 0 := by linarith
    have : x > 0 := by linarith
    positivity
    simp only [Set.mem_Ioi]; linarith
  have second_half: StrictAntiOn (Qp_Range_YX Y) (Set.Icc (Max_X Y) Y):=by
    apply strictAntiOn_of_deriv_neg (convex_Icc (Max_X Y) Y)
    apply ContinuousOn.mono cont
    rw[Set.Icc_subset_Ici_iff];
    linarith [Max_X_gt_one hY]; linarith [Max_X_lt_X hY]
    intro x hx; simp only [interior_Icc, Set.mem_Ioo] at hx;
    rw[deriv_Qp_Range_YX hY, dQp_Range_YX ]
    have i1: A Y * x > A Y * Max_X Y := (mul_lt_mul_left iA).mpr hx.left
    unfold Max_X at i1; field_simp at i1
    have: (x - 1) > 0 := by linarith [Max_X_gt_one hY]
    have : x > 0 := by linarith
    apply mul_neg_of_pos_of_neg
    positivity; linarith
    simp only [Set.mem_Ioi]; linarith[Max_X_gt_one hY]
  by_cases (X ≤  (Max_X Y))
  apply StrictMonoOn.monotoneOn first_half
  simp only [Set.mem_Icc] ; constructor <;> linarith
  simp only [Set.mem_Icc] ; constructor <;> linarith
  assumption
  apply StrictAntiOn.antitoneOn second_half
  simp only [Set.mem_Icc] ; constructor <;> linarith
  simp only [Set.mem_Icc] ; constructor <;> linarith
  linarith

lemma Qp_Range_YX_eq_Qp_range (hΔ : 0 < Δ) (hr: 0 < r) :  Qp_Range Δ r =  Qp_Range_YX (2^Δ) (2^r) :=by
  unfold Qp_Range Qp_Range_YX
  have hΔ0: Δ > 0 := by linarith
  have e1: ∀ x > (0:ℝ), (2:ℝ)^(-x) = 1/2^x :=by intro x _; rw[rpow_neg]; ring_nf; simp only [Nat.ofNat_nonneg]
  have e2: ∀ x > (0:ℝ), log ((2:ℝ)^x) = x * log 2 :=by intro x _; rw[log_rpow]; simp only [Nat.ofNat_pos]
  have eh : Qp_hi Δ r = Qp_hi_YX (2 ^ Δ) (2 ^ r) :=by
    unfold Qp_hi Qp_hi_YX U
    simp only [e1 r hr, e1 Δ hΔ0, e2 r hr, e2 Δ hΔ0]
  have el : Qp_lo Δ r = Qp_lo_YX (2 ^ Δ) (2 ^ r) :=by
    unfold Qp_lo Qp_lo_YX V
    simp only [Qp_of_Fp hΔ, Fp, neg_add_rev, Function.comp_apply, rpow_zero,
      (by linarith : (-1 : ℝ) + -1 = -2), (by linarith : (1 : ℝ) + 1 = 2), neg_mul]
    have e1:  (-(2 * log 2) + 2 * log (1 + 2 ^ r) - log (2 ^ r))  =  (2 * log (2 ^ r + 1) - log (2 ^ r) - 2 * log 2) :=by ring_nf
    have e2:  (-(2 * log 2) + 2 * log (1 + 2 ^ Δ) - log (2 ^ Δ))   =  (2 * log (2 ^ Δ + 1) - log (2 ^ Δ) - 2 * log 2) :=by ring_nf
    rw[e1,e2]
  rw[el,eh]

lemma lemma63sub  (hΔ  : r < Δ) (hr : 0 < r) : Qp_Range Δ r ≤ Qp_Range Δ (Rp_opt Δ) := by
  have hΔ0: 0 < Δ := by linarith
  have i1: (2:ℝ)  ^ Δ > 1 :=by apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ0
  have i2: (2:ℝ)  ^ r > 1 :=by apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hr
  have hRp_opt0: 0 < Rp_opt Δ:= logb_pos (by simp only [Nat.one_lt_ofNat]) (Max_X_gt_one i1)
  rw [Qp_Range_YX_eq_Qp_range hΔ0 hr, Qp_Range_YX_eq_Qp_range hΔ0 hRp_opt0]
  have : 2 ^ Rp_opt Δ = Max_X (2 ^ Δ) :=by
    have iA := @A_pos (2 ^ Δ) i1;
    have iB := @B_pos (2 ^ Δ) i1;
    unfold Rp_opt Max_X; simp only;
    rw[Real.rpow_logb]; simp only [Nat.ofNat_pos];
    simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    positivity
  rw[this]
  apply max_Qp_Range_YX i2
  apply rpow_lt_rpow_of_exponent_lt (by simp only [Nat.one_lt_ofNat]) hΔ


lemma q_lower_bound (hi : i ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) : Qp_lo Δ r ≤ Qp Δ i r :=
  StrictAntiOn.antitoneOn (Lemma62 hr1 hr2) hi Set.right_mem_Iic hi

lemma q_upper_bound (hi : i ≤ 0) (hr : 0 < r) (hΔ : r < Δ) : Qp Δ i r ≤ Qp_hi Δ r := by
  apply ge_of_tendsto (Lemma61 hr (by linarith))
  simp only [eventually_atBot]
  use i; intro b hb;
  apply StrictAntiOn.antitoneOn (Lemma62 hr hΔ) (by simp only [Set.mem_Iic]; linarith) (by simp only [Set.mem_Iic]; linarith) hb


lemma lemma63 (hi : i ≤ 0) (hc : c ≤ 0) (hr : 0 < r) (hΔ : r < Δ) :
    |Qp Δ i r - Qp Δ c r| ≤ Qp_hi Δ (Rp_opt Δ) - Qp_lo Δ (Rp_opt Δ) := by
  have i1:  Qp_hi Δ r - Qp_lo Δ r ≤ Qp_hi Δ (Rp_opt Δ) - Qp_lo Δ (Rp_opt Δ):=by apply lemma63sub hΔ hr
  have case1:  Qp Δ i r - Qp Δ c r ≥ 0 → |Qp Δ i r - Qp Δ c r| ≤ Qp_hi Δ (Rp_opt Δ) - Qp_lo Δ (Rp_opt Δ) :=by
    intro i0
    have i2: Qp Δ i r ≤ Qp_hi Δ r := by apply q_upper_bound; linarith; assumption; assumption;
    have i3: Qp_lo Δ r ≤ Qp Δ c r := by apply q_lower_bound; assumption; assumption; assumption;
    have e0:   |Qp Δ i r - Qp Δ c r| = Qp Δ i r - Qp Δ c r :=by apply abs_of_nonneg; linarith
    linarith
  apply by_cases case1; simp;
  intro i0
  have i2: Qp Δ c r ≤ Qp_hi Δ r := by apply q_upper_bound; linarith; assumption; assumption;
  have i3: Qp_lo Δ r ≤ Qp Δ i r := by apply q_lower_bound; assumption; assumption; assumption;
  have e0:   |Qp Δ i r - Qp Δ c r| = -(Qp Δ i r - Qp Δ c r) :=by apply abs_of_neg; linarith
  linarith
