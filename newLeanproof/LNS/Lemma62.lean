import LNS.Common
import LNS.Tactic
import LNS.Basic

open LNS

open Real




noncomputable def Gp a b := (Fp b a)/ ((deriv (Fp b)) a)

noncomputable def K a b := a * a * log (a + b) - a * a * log (a + 1) - a * b + a + b * log b + b * log (a + 1) - b * log (a + b)




lemma deriv_K (ha: a ∈ (Set.Ioo 0 1)): Set.EqOn (deriv (K a))
      (fun b=> (a*a)/(a+b) - a - b/(a+b) + log b + log (a+1) - log (a+b) + (1:ℝ)) (Set.Ici 1) :=by
  unfold K
  get_deriv (fun b ↦ a * a * log (a + b) - a * a * log (a + 1) - a * b + a + b * log b + b * log (a + 1) - b * log (a + b))
      within (Set.Ici 1)
  simp only [Set.mem_Ici, List.Forall, toFun, ne_eq, id_eq]
  simp only [Set.mem_Ioo] at ha
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  intro b hb
  rw[h.right b hb]
  simp only [Set.mem_Ioo, Set.mem_Ici] at ha hb
  have : a + 1 ≠ 0 := by  linarith
  have : a + b ≠ 0 := by  linarith
  field_simp; ring_nf

lemma deriv2_K (ha: a ∈ (Set.Ioo 0 1)):  Set.EqOn (deriv (deriv (K a)))
      (fun b=> (a*a)*(1-b)/(b*(a+b)^2)) (Set.Ioi 1) :=by
  have e: Set.EqOn (deriv (K a))
      (fun b=> (a*a)/(a+b) - a - b/(a+b) + log b + log (a+1) - log (a+b) + (1:ℝ)) (Set.Ioi 1):=by
    apply Set.EqOn.mono _ (deriv_K ha)
    simp only [Set.Ioi_subset_Ici_iff, le_refl]
  intro b hb; rw[deriv_EqOn2 e hb]
  get_deriv (fun b ↦ a * a / (a + b) - a - b / (a + b) + log b + log (a + 1) - log (a + b) + 1) within (Set.Ioi 1)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq, and_self_left]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  rw[h.right b hb]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  have : a + 1 ≠ 0 := by  linarith
  have : a + b ≠ 0 := by  linarith
  field_simp; ring_nf

lemma deriv_K_strictAnti (ha: a ∈ (Set.Ioo 0 1)): StrictAntiOn (deriv (K a)) (Set.Ici 1) :=by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  apply ContinuousOn.congr _ (deriv_K ha)
  have: ∀ x ∈ Set.Ici 1, a + x ≠ 0 :=by
    simp only [Set.mem_Ici, ne_eq]; simp only [Set.mem_Ioo] at ha
    intro x hx; linarith
  have: ∀ x ∈ Set.Ici (1:ℝ), x ≠ 0 :=by simp only [Set.mem_Ici, ne_eq]; intro x hx; linarith
  fun_prop (disch := assumption)
  intro b hb; simp only [Set.nonempty_Iio, interior_Ici'] at hb
  simp only [deriv2_K ha hb]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  have :  a * a * (1 - b) / (b * (a + b) ^ 2) =  - (a * a * (b-1) / (b * (a + b) ^ 2)):=by ring_nf
  simp only [this, Left.neg_neg_iff, gt_iff_lt]
  have : b - 1 > 0 :=by linarith
  have :  a > 0 := ha.left
  positivity

lemma deriv_K_neg (ha: a ∈ (Set.Ioo 0 1)) (hb: b ∈ (Set.Ioi 1)) : deriv (K a) b < 0 :=by
  simp only [Set.mem_Ioi] at hb
  have :  deriv (K a) 1 = 0 :=by
    rw[deriv_K ha (by simp only [Set.mem_Ici, le_refl])]
    simp only [Set.mem_Ioo] at ha;
    have : a + 1 > 0 :=by linarith
    field_simp; ring_nf
  rw[← this]
  apply (deriv_K_strictAnti ha) (by simp only [Set.mem_Ici, le_refl]) (by simp only [Set.mem_Ici]; linarith) hb


lemma K_strictAnti (ha: a ∈ (Set.Ioo 0 1)): StrictAntiOn (K a) (Set.Ici 1) :=by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  unfold K
  have: ∀ x ∈ Set.Ici 1, a + x ≠ 0 :=by
    simp only [Set.mem_Ici, ne_eq]; simp only [Set.mem_Ioo] at ha
    intro x hx; linarith
  have: ∀ x ∈ Set.Ici (1:ℝ), x ≠ 0 :=by simp only [Set.mem_Ici, ne_eq]; intro x hx; linarith
  fun_prop (disch := assumption)
  intro b hb;
  apply deriv_K_neg ha; simp only [Set.nonempty_Iio, interior_Ici'] at hb; exact hb


lemma K_neg (ha: a ∈ (Set.Ioo 0 1)) (hb: b ∈ (Set.Ioi 1)) : K a b < 0 :=by
  have : K a 1 = 0 :=by simp only [K, sub_self, mul_one, zero_sub, neg_add_cancel, log_one,
    mul_zero, add_zero, one_mul, zero_add]
  rw[← this]; simp only [Set.mem_Ioi] at hb
  apply (K_strictAnti ha) (by simp only [Set.mem_Ici, le_refl]) _ hb
  simp only [Set.mem_Ici]; linarith


lemma deriv_Gp_b_neg (ha: a ∈ (Set.Ioo 0 1)) (hb: b ∈ (Set.Ioi 1))
    : (deriv (Gp a)) b < 0 :=by
  unfold Gp;
  simp only [Set.mem_Ioc, Set.mem_Ioi] at ha hb
  rw[deriv_div];
  have : deriv (Fp b) a ^ 2 > 0 :=by apply pow_pos (deriv_Fp_a_pos ha hb)
  apply div_neg_of_neg_of_pos
  rw[deriv_Fp_a_b ha hb, deriv_Fp_b ha.left hb, deriv_Fp_a (by simp only [Set.mem_Ici]; linarith) ha]
  unfold Fp
  simp only
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  have : a + b > 0 := by  linarith
  have : a * (b - 1) / (b * (a + b)) * ((a + 1) / (a + b) - 1 - log (a + 1) + log (a + b)) -
    (-(a + 1) * log (a + 1) + (a + 1) * log (a + b) - log b) * ((b - 1) / (a + b) ^ 2)
    = (b-1)/(b*(a+b)^2)* (K a b) :=by
    unfold K; field_simp; ring_nf
  rw[this]; apply mul_neg_of_pos_of_neg;
  have : b - 1 > 0:=by linarith
  have: a + b > 0 :=by linarith
  positivity
  apply K_neg ha hb
  apply pow_pos (deriv_Fp_a_pos ha hb)
  exact differentiable_Fp_b ha hb
  exact differentiable_Fp_a_b ha hb
  apply ne_of_gt (deriv_Fp_a_pos ha hb)

lemma Anti_Gp_b (ha: a ∈ (Set.Ioo 0 1)) : StrictAntiOn (Gp a) (Set.Ioi 1):=by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  unfold Gp
  apply ContinuousOn.div
  apply ContinuousAt.continuousOn
  intro b hb
  apply DifferentiableAt.continuousAt (differentiable_Fp_b ha hb)
  apply ContinuousAt.continuousOn
  intro b hb
  apply DifferentiableAt.continuousAt (differentiable_Fp_a_b ha hb)
  intro b hb; apply ne_of_gt (deriv_Fp_a_pos ha hb)
  intro b hb; simp only [interior_Ioi, Set.mem_Ioi] at hb; exact deriv_Gp_b_neg ha hb

lemma deriv_Fp_div_pos (ha: a ∈ (Set.Ioo 0 1)) (hb: b > 1) (hc: c > b) : deriv (fun a ↦ Fp b a / Fp c a) a < 0 :=by
  have ie : Gp a b > Gp a c :=by apply Anti_Gp_b ha hb (by simp only [Set.mem_Ioi];linarith) hc
  unfold Gp at ie
  have i1: deriv (Fp b) a > 0 := by apply deriv_Fp_a_pos ha hb
  have i2: deriv (Fp c) a > 0 := by apply deriv_Fp_a_pos ha; simp only [Set.mem_Ioi]; linarith
  simp only [gt_iff_lt, div_lt_div_iff i2 i1] at ie
  rw[deriv_div]
  apply div_neg_of_neg_of_pos; linarith
  apply pow_pos (Fp_pos ha.left (by simp only [Set.mem_Ioi]; linarith))
  apply differentiable_Fp_a ha hb
  apply differentiable_Fp_a ha (by simp only [Set.mem_Ioi]; linarith)
  apply ne_of_gt (Fp_pos ha.left (by simp only [Set.mem_Ioi]; linarith))



lemma Lemma62 (hr1 : 0 < r) (hr2 : r < Δ):  StrictAntiOn (fun i => Qp Δ i r) (Set.Iic 0):= by
  have i1: ∀ x ∈ Set.Iio (0:ℝ), (2:ℝ)  ^ x ∈ Set.Ioo 0 1 :=by
    intro x hx
    simp only [Set.mem_Ioo, Nat.ofNat_pos, rpow_pos_of_pos, true_and]
    apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) hx
  have i2: ∀ x ∈ Set.Ioi (0:ℝ), (2:ℝ)  ^ x ∈ Set.Ioi 1 :=by
    intro x hx
    apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hx
  apply strictAntiOn_of_deriv_neg (convex_Iic (0:ℝ))
  have: ContinuousOn (fun i ↦ Qp Δ i r) (Set.Iic 0) :=by
    unfold Qp; apply ContinuousOn.div;
    apply DifferentiableOn.continuousOn (Differentiable.differentiableOn differentiable_Ep_i)
    apply DifferentiableOn.continuousOn (Differentiable.differentiableOn differentiable_Ep_i)
    intro x _; apply ne_of_gt (Ep_r_pos (by linarith))
  exact this
  intro x hx; simp only [Set.nonempty_Ioi, interior_Iic'] at hx
  have : Set.EqOn (fun i ↦ Qp Δ i r) ((fun a => Fp (2^r) a / Fp (2^Δ) a) ∘ (fun i=> 2^i)) (Set.Iio 0):=by
    intro i _; simp only [Qp_of_Fp (by linarith)]
  rw[deriv_EqOn this hx, deriv.comp]
  apply mul_neg_of_neg_of_pos
  apply deriv_Fp_div_pos (i1 x hx) (i2 r hr1)
  apply rpow_lt_rpow_of_exponent_lt (by simp only [Nat.one_lt_ofNat]) hr2
  get_deriv (fun i ↦ 2 ^ i)
  simp only [List.Forall, toFun, gt_iff_lt, Nat.ofNat_pos, id_eq, implies_true]
  simp only [toFun, zero_mul, one_mul, zero_add] at h
  simp only [h, Nat.ofNat_pos, rpow_pos_of_pos, mul_pos_iff_of_pos_left, Nat.one_lt_ofNat, log_pos]
  apply DifferentiableAt.div
  apply differentiable_Fp_a (i1 x hx) (i2 r hr1);
  apply differentiable_Fp_a (i1 x hx) (i2 Δ (by simp only [Set.mem_Ioi]; linarith));
  apply ne_of_gt (Fp_pos (i1 x hx).left (i2 Δ (by simp only [Set.mem_Ioi]; linarith)))
  apply DifferentiableAt.rpow <;> simp
