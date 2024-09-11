import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import LNS.Common
import LNS.Tactic
set_option maxHeartbeats 10000000



/- Definitions of Φ⁺(x) and E(i, r) -/

noncomputable section


namespace LNS

open Real

attribute [fun_prop] Differentiable.div_const
attribute [fun_prop] Differentiable.rpow
attribute [fun_prop] Differentiable.log
attribute [fun_prop] Differentiable.exp
attribute [fun_prop] Differentiable.div
attribute [fun_prop] DifferentiableOn.div_const
attribute [fun_prop] DifferentiableOn.rpow
attribute [fun_prop] DifferentiableOn.log
attribute [fun_prop] DifferentiableOn.exp
attribute [fun_prop] DifferentiableOn.div
attribute [fun_prop] ContinuousOn.div_const
attribute [fun_prop] ContinuousOn.rpow
attribute [fun_prop] ContinuousOn.log
attribute [fun_prop] ContinuousOn.exp
attribute [fun_prop] ContinuousOn.div

attribute [simp] rpow_pos_of_pos
attribute [simp] log_pos
/- Φ⁺ from Introduction -/

def Φp (x : ℝ) := logb 2 (1 + (2 : ℝ) ^ x)

def Φm (x : ℝ) := logb 2 (1 - (2 : ℝ) ^ x)

/- Iₓ and Rₓ correspond to iₓ and rₓ from Eq (1) -/

def Iₓ (Δ x : ℝ) := ⌈x / Δ⌉ * Δ

def Rₓ (Δ x : ℝ) := Iₓ Δ x - x

/- Φₜ is the first order Taylor approximation of Φ⁺ from Eq (1) -/

def ΦTp (Δ x : ℝ) := Φp (Iₓ Δ x) - Rₓ Δ x * deriv Φp (Iₓ Δ x)

/- E i r is the error of the first order Taylor approximation
   defined for all real i and r -/

def Ep (i r : ℝ) := Φp (i - r) - Φp i + r * deriv Φp i

def Em (i r : ℝ) := -Φm (i - r) + Φm i - r * deriv Φm i

def Ep_i (r: ℝ):= fun i => Ep i r

def Em_i (r: ℝ):= fun i => Em i r

noncomputable def fp (a : ℝ) := a * exp (-a) + exp (-a) - 1

noncomputable def gp a := exp (-a) + a - 1

def Qp (Δ i r : ℝ) := Ep i r / Ep i Δ

def Qm (Δ i r : ℝ) := Em i r / Em i Δ

def Fp b a := - (a + 1) * log (a + 1) + (a + 1) * log (a + b) - log b



/-
  Fixed-point rounding
-/

opaque rnd : ℝ → ℝ

opaque ε  : ℝ

axiom hrnd : ∀ x , |x - rnd x| ≤ ε

noncomputable def Ep_fix (i r : ℝ) := Φp (i - r) - rnd (Φp i) + rnd (r * rnd (deriv Φp i) )

noncomputable def Em_fix (i r : ℝ) := Φm (i - r) - rnd (Φm i) + rnd (r * rnd (deriv Φm i) )

/-
  INEQUALITIES FOR FUN_PROP
-/

@[simp]
lemma one_plus_two_pow_pos (x : ℝ) : 0 < 1 + (2 : ℝ) ^ x := by
  linarith [rpow_pos_of_pos two_pos x]

@[simp]
lemma one_plus_two_pow_ne_zero (x : ℝ) : 1 + (2 : ℝ) ^ x ≠ 0 := by
  linarith [rpow_pos_of_pos two_pos x]


@[simp]
lemma one_minus_two_pow_ne_zero2 :  ∀ x < (0:ℝ),  ¬ 1 - (2:ℝ) ^ x = 0 :=by
  intro x h
  have ieq : (2:ℝ) ^ x < 1:=by refine rpow_lt_one_of_one_lt_of_neg ?hx h; linarith
  linarith

@[simp]
lemma one_monus_two_pow_ne_zero :  ∀ x ∈ Set.Iio (0:ℝ),  1 - (2:ℝ) ^ x ≠ 0 :=by
  simp only [Set.mem_Iio, ne_eq] ;  exact one_minus_two_pow_ne_zero2


@[simp]
lemma two_ne_zero :  ∀ x ∈ Set.Iio (0:ℝ),  (2:ℝ)  ≠ (0:ℝ)  :=by
  simp only [Set.mem_Iio, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, implies_true]

lemma one_minus_two_pow_ne_zero3 (hi: i < (0:ℝ)) (hr: r > 0): 1 - (2:ℝ) ^(i-r) ≠ 0 :=by
  apply one_minus_two_pow_ne_zero2; linarith

lemma one_minus_two_pow_ne_zero4 (hi: i < (0:ℝ)) (hr: r ≥  0): 1 - (2:ℝ) ^(i-r) ≠ 0 :=by
  apply one_minus_two_pow_ne_zero2; linarith

lemma aux_inq1 (hi: i ∈  (Set.Iio (0:ℝ)))
    : ∀ x ∈ Set.Ioi 0, ¬1 - (2:ℝ)  ^ (i - x) = 0 ∧ ¬1 - (2:ℝ)  ^ i = 0 :=by
  simp_all only [Set.mem_Iio, Set.mem_Ioi, one_minus_two_pow_ne_zero2, not_false_eq_true, and_true]
  intro x hx
  exact one_minus_two_pow_ne_zero3 hi hx

lemma aux_inq1' (hi: i ∈  (Set.Iio (0:ℝ)))
    : ∀ x ∈ Set.Ici 0, ¬1 - (2:ℝ)  ^ (i - x) = 0 ∧ ¬1 - (2:ℝ)  ^ i = 0 :=by
  simp_all only [Set.mem_Iio, Set.mem_Ici, one_minus_two_pow_ne_zero2, not_false_eq_true, and_true]
  intro x hx
  have: (2:ℝ) ^ (i - x) < 1 :=by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  linarith

lemma aux_inq2 (hi: i ∈  (Set.Iio (0:ℝ)))
    : ∀ x ∈ Set.Ici 0, ¬1 - (2:ℝ)  ^ (i - x) = 0  :=by
  simp_all only [Set.mem_Iio, Set.mem_Ioi, one_minus_two_pow_ne_zero2, not_false_eq_true, and_true]
  intro x hx; simp only [Set.mem_Ici] at hx
  apply one_minus_two_pow_ne_zero2; linarith


lemma aux_eq1:  rexp (-(log 2 * r) )= 1/ 2 ^ r :=by
  rw [exp_neg, exp_mul, exp_log]; field_simp; simp only [Nat.ofNat_pos]

lemma aux_eq2 :  (2:ℝ)  ^ ((x:ℝ) - r) = 2^x /2^r :=by
  simp only [Nat.ofNat_pos, rpow_sub];

lemma err_eq_zero : Ep i 0 = 0 := by simp only [Ep, sub_zero, sub_self, zero_mul, add_zero]

lemma i_sub_r_eq_x (Δ x : ℝ) : Iₓ Δ x - Rₓ Δ x = x := by
  simp only [Iₓ, Rₓ, sub_sub_cancel]

lemma Φₜ_error : Φp x - ΦTp Δ x = Ep (Iₓ Δ x) (Rₓ Δ x) := by
  simp only [ΦTp, Ep, i_sub_r_eq_x]; ring_nf

lemma x_le_ix {Δ} (hd : 0 < Δ) x : x ≤ Iₓ Δ x :=
  (div_le_iff hd).mp $ Int.le_ceil $ x / Δ

lemma x_neg_iff_ix_neg {Δ} (hd : 0 < Δ) x : x ≤ 0 ↔ Iₓ Δ x ≤ 0 := by
  constructor
  · intro hx
    apply mul_nonpos_of_nonpos_of_nonneg _ (le_of_lt hd)
    rw [← Int.cast_zero, Int.cast_le, Int.ceil_le, Int.cast_zero]
    exact div_nonpos_of_nonpos_of_nonneg hx (le_of_lt hd)
  · exact le_trans (x_le_ix hd x)

lemma rx_eq_zero_iff {Δ x : ℝ} : Rₓ Δ x = 0 ↔ Iₓ Δ x = x := by
  simp only [Rₓ, Iₓ, sub_eq_zero]

lemma rx_eq_fract {Δ x : ℝ} (hd : Δ ≠ 0) (ix : Iₓ Δ x ≠ x) :
    Rₓ Δ x = Δ * (1 - Int.fract (x / Δ)) := by
  unfold Rₓ Iₓ at *
  rcases Int.fract_eq_zero_or_add_one_sub_ceil (x / Δ) with h | h
  · exfalso; apply ix
    simp only [Int.ceil_eq_self.mpr h]; field_simp
  · rw [h]; field_simp; ring

lemma rx_nonneg {Δ} (hd : 0 < Δ) x : 0 ≤ Rₓ Δ x :=
  Int.ceil_div_mul_sub_nonneg hd


lemma rx_lt_delta {Δ} (hd : 0 < Δ) x : Rₓ Δ x < Δ :=
  Int.ceil_div_mul_sub_lt hd

@[simp]
lemma numineq : ¬ (2:ℝ) = -1 :=by linarith


lemma deriv_EqOn {f1 f2: ℝ → ℝ} (h: Set.EqOn f1 f2 (Set.Iio (a:ℝ))) (hx: x ∈ (Set.Iio (a:ℝ)))
      : deriv f1 x = deriv f2 x :=by
  apply Filter.EventuallyEq.deriv_eq
  apply Filter.eventuallyEq_of_mem _ h
  exact Iio_mem_nhds hx

lemma deriv_EqOn2 {f1 f2: ℝ → ℝ} (h: Set.EqOn f1 f2 (Set.Ioi (a:ℝ))) (hx: x ∈ (Set.Ioi (a:ℝ)))
      : deriv f1 x = deriv f2 x :=by
  apply Filter.EventuallyEq.deriv_eq
  apply Filter.eventuallyEq_of_mem _ h
  exact Ioi_mem_nhds hx

lemma deriv_EqOn3 {f1 f2: ℝ → ℝ} (h: Set.EqOn f1 f2 (Set.Ioo (a:ℝ) (b:ℝ))) (hx: x ∈ (Set.Ioo (a:ℝ) (b:ℝ)))
      : deriv f1 x = deriv f2 x :=by
  apply Filter.EventuallyEq.deriv_eq
  apply Filter.eventuallyEq_of_mem _ h
  simp only [Set.mem_Ioo] at hx
  apply Ioo_mem_nhds hx.left hx.right

/- Derivatives and differentiability of Φ -/


lemma differentiable_Φp : Differentiable ℝ Φp :=by
  unfold Φp logb;
  diff_fun fun x ↦ log (1 + 2 ^ x) / log 2

lemma deriv_Φp : deriv Φp = fun (x : ℝ) => (2 : ℝ) ^ x / (1 + (2 : ℝ) ^ x) := by
  unfold Φp logb
  deriv_EQ fun x ↦ log (1 + 2 ^ x) / log 2

lemma deriv2_Φp : deriv (deriv Φp)  = fun x=> (2 : ℝ) ^ x * log 2 / (1 + (2 : ℝ) ^ x) ^ 2 := by
  simp only [deriv_Φp]
  deriv_EQ (fun x ↦ 2 ^ x / (1 + 2 ^ x))

lemma deriv_Φp_pos : (deriv Φp) x > 0 :=by
  simp only [deriv_Φp, gt_iff_lt, Nat.ofNat_pos, rpow_pos_of_pos, div_pos_iff_of_pos_left,
    one_plus_two_pow_pos]

lemma deriv2_Φp_pos :  deriv (deriv Φp) x > 0:= by
  simp only [deriv2_Φp, gt_iff_lt, one_plus_two_pow_pos, pow_pos, div_pos_iff_of_pos_right,
    Nat.ofNat_pos, rpow_pos_of_pos, mul_pos_iff_of_pos_left, Nat.one_lt_ofNat, log_pos]

lemma differentiable_Φm : DifferentiableOn ℝ Φm (Set.Iio (0:ℝ)):=by
  unfold Φm logb;
  have i:= one_monus_two_pow_ne_zero
  have i2:= two_ne_zero
  fun_prop (disch:=assumption)

lemma deriv_Φm : Set.EqOn (deriv Φm)  (fun x=> -(2 : ℝ) ^ x / (1 - (2 : ℝ) ^ x)) (Set.Iio (0:ℝ)) := by
  unfold Φm logb
  get_deriv (fun x ↦ log (1 - 2 ^ x) / log 2) within (Set.Iio (0:ℝ))
  simp only [Set.mem_Iio, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, numineq, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and]
  exact one_minus_two_pow_ne_zero2
  simp only [toFun, Set.mem_Iio, deriv_div_const, zero_mul, one_mul, zero_add, zero_sub, zero_div,
    mul_zero, sub_zero, Nat.cast_ofNat, rpow_two] at h
  simp only [Set.EqOn, Set.mem_Iio, deriv_div_const]
  intro x hx
  simp only [h.right x hx]; field_simp; ring_nf

lemma deriv2_Φm:  Set.EqOn (deriv (deriv Φm)) (fun x => -(log 2 *(2 : ℝ) ^ x ) / (1 - (2 : ℝ) ^ x)^2) (Set.Iio (0:ℝ)) := by
  unfold Set.EqOn
  intro x hx
  rw[deriv_EqOn deriv_Φm hx]
  get_deriv (fun x ↦ -2 ^ x / (1 - 2 ^ x)) within (Set.Iio (0:ℝ))
  simp only [Set.mem_Iio, List.Forall, toFun, ne_eq, id_eq, gt_iff_lt, Nat.ofNat_pos, and_self, and_true]
  exact one_minus_two_pow_ne_zero2
  simp only [toFun, zero_mul, one_mul, zero_add, neg_mul, zero_sub, mul_neg, neg_neg,
    Nat.cast_ofNat, rpow_two] at h
  simp only [h.right x hx]; field_simp; ring_nf



/- Derivatives and differentiability of E -/




lemma deriv_Ep_r : deriv (Ep i) = fun (r : ℝ) => ((2:ℝ)^i - (2:ℝ)^(i-r)) / ((1+(2:ℝ)^i) * (1+(2:ℝ)^(i-r)) ) := by
  unfold Ep; rw[deriv_Φp]; simp only [Φp, logb]
  deriv_EQ fun r ↦ log (1 + 2 ^ (i - r)) / log 2 - log (1 + 2 ^ i) / log 2 + r * (2 ^ i / (1 + 2 ^ i))

lemma deriv_Em_r (hi: i ∈  (Set.Iio 0) )
    : Set.EqOn (deriv (Em i)) (fun (r : ℝ) => ((2:ℝ)^i - (2:ℝ)^(i-r)) / ((1-(2:ℝ)^i) * (1-(2:ℝ)^(i-r)) )) (Set.Ioi 0):=by
  unfold Em Set.EqOn
  intro r hr
  rw[deriv_Φm hi]; simp only [Φm, logb]
  get_deriv (fun r ↦ -(log (1 - 2 ^ (i - r)) / log 2) + log (1 - 2 ^ i) / log 2 - r * (-2 ^ i / (1 - 2 ^ i))) within (Set.Ioi 0)
  simp only [Set.mem_Ici, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, numineq, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and]
  exact aux_inq1 hi
  simp only [toFun, zero_mul, zero_sub, neg_mul, one_mul, zero_add, sub_neg_eq_add,
    zero_div, mul_zero, sub_zero, Nat.cast_ofNat, rpow_two, add_zero, sub_self, neg_zero] at h
  rw[h.right r hr];
  simp only [Set.mem_Iio, Set.mem_Ioi] at hi hr
  have ie:= one_minus_two_pow_ne_zero3 hi hr
  field_simp; simp only [aux_eq2]; field_simp; ring_nf

lemma differentiable_Ep_r : Differentiable ℝ (Ep i) :=by
  unfold Ep; rw[deriv_Φp]; simp only [Φp, logb]
  fun_prop  (disch:=simp)

lemma differentiable_Em_r (hi: i ∈  (Set.Iio 0) ): DifferentiableOn ℝ (Em i) (Set.Ioi 0):=by
  unfold Em
  rw[deriv_Φm hi]; simp only [Φm, logb]
  get_deriv (fun r ↦ -(log (1 - 2 ^ (i - r)) / log 2) + log (1 - 2 ^ i) / log 2 - r * (-2 ^ i / (1 - 2 ^ i))) within (Set.Ioi 0)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, numineq, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and]
  exact aux_inq1 hi
  simp only [toFun, zero_mul, zero_sub, neg_mul, one_mul, zero_add, sub_neg_eq_add,
    zero_div, mul_zero, sub_zero, Nat.cast_ofNat, rpow_two, add_zero, sub_self, neg_zero] at h
  simp only [h]

lemma continuous_Em_r (hi: i ∈  (Set.Iio 0) ): ContinuousOn (Em i) (Set.Ici 0):=by
  unfold Em; rw[deriv_Φm hi]; simp only [Φm, logb]
  have e:= aux_inq2 hi
  have u: ∀ x ∈ Set.Ici 0, (2:ℝ) ≠ 0 ∨ 0 < i - x :=by simp only [Set.mem_Ici, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, sub_pos, true_or, implies_true]
  fun_prop (disch:=assumption)


lemma deriv_Em_r_pos (hi: i ∈  (Set.Iio 0) ) (hr: r ∈  (Set.Ioi 0) ):  deriv (Em i) r > 0 := by
  simp only [deriv_Em_r hi hr, gt_iff_lt]
  simp only [Set.mem_Iio, Set.mem_Ioi] at hi hr
  have i1:  (2:ℝ) ^ i < 1 :=by apply rpow_lt_one_of_one_lt_of_neg _ hi; simp only [Nat.one_lt_ofNat]
  have _:  (2:ℝ) ^ (i-r) < 1 :=by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  have i3:  (2:ℝ) ^ i > 2 ^ (i - r) :=by apply rpow_lt_rpow_of_exponent_lt; simp only [Nat.one_lt_ofNat]; linarith
  apply div_pos; linarith; apply mul_pos; linarith; linarith

lemma Ep_r_monotone: MonotoneOn (Ep i) (Set.Ici 0) :=by
  apply monotoneOn_of_deriv_nonneg_Ici0
  apply Differentiable.differentiableOn differentiable_Ep_r
  intro r hr; simp only [deriv_Ep_r, ge_iff_le]
  have i3:  (2:ℝ) ^ i ≥  2 ^ (i - r) :=by apply rpow_le_rpow_of_exponent_le; simp only [Nat.one_le_ofNat]; linarith
  have i3: (2:ℝ) ^ i -  2 ^ (i - r) ≥ 0 :=by linarith
  positivity

lemma Ep_r_strictMonotone: StrictMonoOn (Ep i) (Set.Ici 0) :=by
  apply strictMonoOn_of_deriv_pos_Ici0
  apply DifferentiableOn.continuousOn (Differentiable.differentiableOn differentiable_Ep_r)
  intro r hr; simp only [deriv_Ep_r, ge_iff_le]
  have i3:  (2:ℝ) ^ i >  2 ^ (i - r) :=by apply rpow_lt_rpow_of_exponent_lt; simp only [Nat.one_lt_ofNat]; linarith
  have i3: (2:ℝ) ^ i -  2 ^ (i - r) > 0 :=by linarith
  positivity

lemma Em_r_strictMono (hi: i ∈  (Set.Iio 0) ): StrictMonoOn (Em i) (Set.Ici 0) :=by
  apply strictMonoOn_of_deriv_pos_Ici0 (continuous_Em_r hi)
  intro r hr; apply deriv_Em_r_pos hi; simp only [Set.mem_Ioi]; exact hr

lemma Ep_r_nonneg : r ≥ 0 → (Ep i) r ≥ 0 := by
  apply nonneg_of_deriv_nonneg_Ici0
  apply Differentiable.differentiableOn differentiable_Ep_r
  simp only [Ep, sub_zero, sub_self, zero_mul, add_zero]
  intro r hr; simp only [deriv_Ep_r, ge_iff_le]
  have i3:  (2:ℝ) ^ i ≥  2 ^ (i - r) :=by apply rpow_le_rpow_of_exponent_le; simp only [Nat.one_le_ofNat]; linarith
  have i3: (2:ℝ) ^ i -  2 ^ (i - r) ≥ 0 :=by linarith
  positivity

lemma Ep_r_pos : r > 0 → (Ep i) r > 0 := by
  apply pos_of_deriv_pos_Ici
  apply DifferentiableOn.continuousOn (Differentiable.differentiableOn differentiable_Ep_r)
  simp only [Ep, sub_zero, sub_self, zero_mul, add_zero]
  intro r hr; simp only [deriv_Ep_r, ge_iff_le]
  have i3:  (2:ℝ) ^ i >  2 ^ (i - r) :=by apply rpow_lt_rpow_of_exponent_lt; simp only [Nat.one_lt_ofNat]; linarith
  have i3: (2:ℝ) ^ i -  2 ^ (i - r) > 0 :=by linarith
  positivity

lemma Em_r_nonneg (hi: i ∈  (Set.Iio 0) ): r ≥ 0 → (Em i) r ≥ 0 := by
  intro hr
  rw[(by simp only [Em, sub_zero, neg_add_cancel, zero_mul, sub_self] :0 = Em i 0 )]
  apply StrictMonoOn.monotoneOn (Em_r_strictMono hi) (by simp only [Set.mem_Ici, le_refl])
  simp only [Set.mem_Ici]; exact hr; exact hr

lemma Em_r_pos (hi: i ∈  (Set.Iio 0) ): r > 0 → (Em i) r > 0 := by
  intro hr
  rw[(by simp only [Em, sub_zero, neg_add_cancel, zero_mul, sub_self] :0 = Em i 0 )]
  apply Em_r_strictMono hi (by simp only [Set.mem_Ici, le_refl])
  simp only [Set.mem_Ici]; linarith; assumption


lemma differentiable_Ep_i: Differentiable ℝ (Ep_i r) :=by
  unfold Ep_i Ep; rw[deriv_Φp]; simp only [Φp, logb, fp, gp]
  get_deriv fun i ↦ log (1 + 2 ^ (i - r)) / log 2 - log (1 + 2 ^ i) / log 2 + r * (2 ^ i / (1 + 2 ^ i))
  simp only [List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    numineq, or_self, not_false_eq_true, id_eq, one_plus_two_pow_ne_zero, gt_iff_lt, Nat.ofNat_pos,
    and_self, implies_true]
  simp only [toFun, zero_mul, sub_zero, one_mul, zero_add, zero_div, mul_zero, Nat.cast_ofNat,
    rpow_two] at h
  exact h.left

lemma differentiable_Em_i (hr: r ∈  (Set.Ici 0) ): DifferentiableOn ℝ (Em_i r) (Set.Iio 0):=by
  unfold Em_i Em
  have : ∀ i ∈ (Set.Iio 0), (fun i ↦ -Φm (i - r) + Φm i - r * deriv Φm i) i =
            (fun i ↦ -Φm (i - r) + Φm i - r * (-(2 : ℝ) ^ i / (1 - (2 : ℝ) ^ i))) i :=by
    intro i hi ; simp only [sub_right_inj, mul_eq_mul_left_iff]
    simp only [deriv_Φm hi, true_or]
  apply DifferentiableOn.congr _ this
  simp only [Φm, logb]
  get_deriv (fun i ↦ -(log (1 - 2 ^ (i - r)) / log 2) + log (1 - 2 ^ i) / log 2 - r * (-2 ^ i / (1 - 2 ^ i))) within (Set.Iio 0)
  simp only [List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, numineq, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and];
  intro x hx; exact aux_inq1' hx r hr
  simp only [toFun, Set.mem_Iio, zero_mul, sub_zero, one_mul, zero_add, zero_sub, zero_div,
    mul_zero, Nat.cast_ofNat, rpow_two, neg_mul, mul_neg, neg_neg] at h
  simp only [h]

lemma deriv_Ep_i:  deriv (Ep_i r) =
    fun (i : ℝ) => (2^i)/((1+(2:ℝ)^i)^2 * (1+(2:ℝ)^(i-r)))*(2^i * fp (log 2 * r) + gp (log 2 * r)) := by
  unfold Ep_i Ep; rw[deriv_Φp]; simp only [Φp, logb, fp, gp]
  get_deriv fun i ↦ log (1 + 2 ^ (i - r)) / log 2 - log (1 + 2 ^ i) / log 2 + r * (2 ^ i / (1 + 2 ^ i))
  simp only [List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    numineq, or_self, not_false_eq_true, id_eq, one_plus_two_pow_ne_zero, gt_iff_lt, Nat.ofNat_pos,
    and_self, implies_true]
  simp only [toFun, zero_mul, sub_zero, one_mul, zero_add, zero_div, mul_zero, Nat.cast_ofNat,
    rpow_two] at h
  simp only [h.right]; ext x; simp[aux_eq1, aux_eq2]; field_simp; ring_nf

lemma deriv_Em_i (hr: r ∈  (Set.Ici 0) ): Set.EqOn (deriv (Em_i r))
    (fun (i : ℝ) => (2^i)/((1-(2:ℝ)^i)^2 * (1-(2:ℝ)^(i-r)))*(- (2^i * fp (log 2 * r)) + gp (log 2 * r))) (Set.Iio 0) := by
  unfold Em_i Em Set.EqOn; intro i hi
  have  : deriv (fun i ↦ -Φm (i - r) + Φm i - r * deriv Φm i) i =
        deriv (fun i ↦ -Φm (i - r) + Φm i - r * -(2 : ℝ) ^ i / (1 - (2 : ℝ) ^ i)) i :=by
    apply deriv_EqOn _ hi; intro y hy; simp only [mul_neg, sub_right_inj]
    simp only [deriv_Φm hy]; field_simp
  rw[this]; simp only [Φm, logb, mul_neg, fp, neg_mul, gp]
  get_deriv (fun i ↦ -(log (1 - 2 ^ (i - r)) / log 2) + log (1 - 2 ^ i) / log 2 - -(r * 2 ^ i) / (1 - 2 ^ i)) within (Set.Iio 0)
  simp only [Set.mem_Iio, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, numineq, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and]
  intro x hx; exact aux_inq1' hx r hr
  simp only [toFun, zero_mul, sub_zero, one_mul, zero_add, zero_sub, zero_div,
    mul_zero, Nat.cast_ofNat, rpow_two, neg_mul, mul_neg, neg_neg] at h
  rw[h.right i hi];
  have ie:= one_minus_two_pow_ne_zero4 hi hr
  have ie2:= one_minus_two_pow_ne_zero2 i hi
  field_simp
  simp[aux_eq1, aux_eq2]; field_simp; ring_nf

lemma differentiable_fp : Differentiable ℝ fp  :=by
  unfold fp; fun_prop

lemma deriv_fp : deriv fp = fun a:ℝ  => -a * exp (-a) :=by
  unfold fp
  get_deriv fun a ↦ a * rexp (-a) + rexp (-a) - 1
  simp only [List.Forall, implies_true]
  simp_all only [toFun, differentiable_const, Differentiable.sub_iff_left, one_mul, mul_neg,
    mul_one, add_neg_cancel_comm, sub_zero, neg_mul]

lemma fp_nonpos : x ≥ 0 →  fp x ≤ 0 :=by
  apply nonpos_of_deriv_nonpos_Ici0
  apply Differentiable.differentiableOn differentiable_fp
  simp only [fp, neg_zero, exp_zero, mul_one, zero_add, sub_self]
  intro x hx
  simp only [deriv_fp, neg_mul, Left.neg_nonpos_iff];
  apply mul_nonneg hx
  apply exp_nonneg

def N a (i:ℝ)  := 2^i * fp a + gp a

def h a := N a 0

lemma differentiable_h : Differentiable ℝ h  :=by
  unfold h N gp fp
  fun_prop

lemma deriv_h : deriv h = fun x => - fp x :=by
  unfold h N fp gp
  deriv_EQ fun a ↦ 2 ^ 0 * (a * rexp (-a) + rexp (-a) - 1) + (rexp (-a) + a - 1)
  ring_nf

lemma h_nonneg : a ≥ 0 → h a ≥ 0  :=by
  apply nonneg_of_deriv_nonneg_Ici0
  apply Differentiable.differentiableOn differentiable_h
  simp only [h, N, pow_zero, fp, neg_zero, exp_zero, mul_one, zero_add, sub_self, mul_zero, gp, add_zero]
  intro x hx
  simp only [deriv_h, ge_iff_le, Left.nonneg_neg_iff]
  exact fp_nonpos hx

lemma differentiable_N : Differentiable ℝ (N a)  :=by
  unfold N fp gp; fun_prop (disch:=simp)

lemma deriv_N : deriv (N a) = fun i:ℝ => 2^i * log 2  * fp a :=by
  unfold N fp gp
  get_deriv fun i ↦ 2 ^ i * (a * rexp (-a) + rexp (-a) - 1) + (rexp (-a) + a - 1)
  simp only [List.Forall, toFun, gt_iff_lt, Nat.ofNat_pos, id_eq, implies_true]
  simp_all only [toFun, differentiable_add_const_iff, deriv_add_const', deriv_mul_const_field',
    zero_mul, one_mul, zero_add, neg_zero, mul_zero, add_zero, sub_self]

lemma N_nonneg : i ≤ 0 → a ≥ 0 → N a i ≥ 0 :=by
  intro hi ha
  apply nonneg_of_deriv_nonpos_Iic0
  apply Differentiable.differentiableOn differentiable_N
  rw[← h]; exact h_nonneg ha
  intro x _; simp only [deriv_N];
  have :  (-LNS.fp a) ≥ 0 :=by simp only [ge_iff_le, Left.nonneg_neg_iff]; exact fp_nonpos ha
  have ie : 2 ^ x * log 2 * (-LNS.fp a) ≥ 0 :=by positivity
  simp at ie; exact ie
  exact hi

lemma deriv_Ep_i_nonneg (hi: i ≤ 0) (hr: 0 ≤ r):  (deriv (Ep_i r)) i ≥ 0 :=by
  simp only [deriv_Ep_i, ge_iff_le]
  norm_num
  rw[← N]; apply N_nonneg
  assumption; positivity

lemma Ep_i_monotone (hr: 0 ≤ r) : MonotoneOn (Ep_i r) (Set.Iic 0) :=by
  apply monotoneOn_of_deriv_nonneg_Iic0
  apply Differentiable.differentiableOn differentiable_Ep_i
  intro i hi; exact deriv_Ep_i_nonneg hi hr



lemma differentiable_gp : Differentiable ℝ gp  :=by
  unfold gp
  fun_prop

lemma gp_nonneg: a ≥ 0 → gp a ≥ 0  :=by
  apply nonneg_of_deriv_nonneg_Ici0
  apply Differentiable.differentiableOn differentiable_gp
  simp only [gp, neg_zero, exp_zero, add_zero, sub_self]
  intro x hx; unfold gp
  get_deriv (fun a ↦ rexp (-a) + a - 1)
  simp only [List.Forall, implies_true]
  simp only [toFun, differentiable_const, Differentiable.sub_iff_left, differentiable_id',
    Differentiable.add_iff_left, mul_neg, mul_one, sub_zero] at h
  simp only [h.right, ge_iff_le, le_neg_add_iff_add_le, add_zero, exp_le_one_iff,
    Left.neg_nonpos_iff, hx]

lemma deriv_Em_i_nonneg (hi: i ∈  (Set.Iio 0) ) (hr: r ∈  (Set.Ici 0) ):  (deriv (Em_i r)) i ≥ 0 :=by
  simp only [deriv_Em_i hr hi, ge_iff_le]
  simp only [Set.mem_Iio, Set.mem_Ici] at hi hr
  have i1:  (2:ℝ) ^ i < 1 :=by apply rpow_lt_one_of_one_lt_of_neg _ hi; simp only [Nat.one_lt_ofNat]
  have i1:  1 - (2:ℝ) ^ i > 0 :=by linarith
  have i2:  (2:ℝ) ^ (i-r) < 1 :=by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  have i2:  1 - (2:ℝ) ^ (i-r) > 0 :=by linarith
  have i0: (2:ℝ) ^ i > 0 :=by norm_num
  have ie: (-(2 ^ i * LNS.fp (log 2 * r)) + LNS.gp (log 2 * r)) ≥  0 :=by
    have : 2 ^ i * (- LNS.fp (log 2 * r)) ≥ 0:=by
      apply mul_nonneg; linarith; simp only [Left.nonneg_neg_iff]; apply fp_nonpos; positivity
    have: LNS.gp (log 2 * r) ≥ 0 :=by apply gp_nonneg; positivity
    linarith
  positivity

lemma Em_i_monotone (hr: r ∈  (Set.Ici 0) ) : MonotoneOn (Em_i r) (Set.Iio 0) :=by
  apply monotoneOn_of_deriv_nonneg_Iio0
  exact differentiable_Em_i hr
  intro i hi; apply deriv_Em_i_nonneg hi hr;


/-
  Section 6
-/
lemma aux_eq3: log (1 + 2 ^ (i:ℝ) / 2 ^ r) = log (2^i + 2^r) - r * log 2 :=by
  have : (2:ℝ) ^ i > 0 :=by norm_num
  have : (2:ℝ) ^ r > 0 :=by norm_num
  have: 1 + (2:ℝ)  ^ (i:ℝ) / 2 ^ r =  (2^i + 2^r)  / 2 ^ r :=by field_simp; ring_nf
  rw[this, log_div, log_rpow]; simp only [Nat.ofNat_pos];
  linarith; linarith


def Qp_lo (Δ r : ℝ) := Qp Δ 0 r

def Qp_hi (Δ r : ℝ) := (2 ^ (-r) + r * log 2 - 1) / (2 ^ (-Δ) + Δ * log 2 - 1)


def Qp_Range (Δ r : ℝ) := Qp_hi Δ r  - Qp_lo Δ r

def U (X:ℝ) := 1/X + log X - 1

def V (X:ℝ) := 2 * log (X+1) - log X - 2 * log 2

def Qp_hi_YX (Y X: ℝ) := U X/U Y

def Qp_lo_YX (Y X : ℝ) := V X/V Y

def Qp_Range_YX (Y X : ℝ) := Qp_hi_YX Y X - Qp_lo_YX Y X

def A (Y:ℝ) := -2*Y*(log (Y+1) - log Y - log 2) - Y + 1

def B (Y:ℝ) := Y*(2* log (Y+1) - log Y - 2 * log 2)

def Rp_opt (Δ : ℝ) :=
  let X := 2 ^ Δ
  logb 2 (B X / A X)

def C (Y:ℝ) := -2*Y/(Y+1) +2*log Y - 2*log (Y+1) + 2*log 2 + 1

def Max_X (Y:ℝ) := B Y / A Y

def dQp_Range_YX (Y X : ℝ)  := (Y *(X-1))/ (X*X*(X+1)*(B Y + A Y)* B Y)  *(-A Y * X + B Y)















end LNS