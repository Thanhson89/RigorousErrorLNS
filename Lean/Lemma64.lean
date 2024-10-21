import LNS.Common
import LNS.Tactic
import LNS.Basic
import LNS.Lemma63
set_option maxHeartbeats 10000000

noncomputable section
open LNS
open Real



def Wp c Δ r t := (Ep c r - Ep c (r-t)) / (Ep c Δ)

def Wtp c Δ t r := Wp c Δ r t



lemma monoWp1 (h1: r ≥ ΔP) (hr: r >  0)  (htp: t ≤ ΔP)
    (htd: r ≤ Δ) : (Wp c Δ) r t ≤  (Wp c Δ) r ΔP := by
  have ep : Ep c Δ > 0 := by apply Ep_r_pos; linarith
  unfold Wp; rw[div_le_div_right ep]; apply sub_le_sub_left;
  apply Ep_r_monotone
  simp only [Set.mem_Ici, sub_nonneg]; linarith
  simp only [Set.mem_Ici, sub_nonneg]; linarith
  linarith

lemma monoWp2 (hr: r > 0) (ht: t≥ 0) (htr: t ≤ r)
    (htd: r ≤ Δ) : (Wp c Δ) r t ≤  (Wp c Δ) Δ t := by
  have ep : Ep c Δ > 0 := by apply Ep_r_pos; linarith
  unfold Wp; rw[div_le_div_right ep];
  have ec2 : (fun y ↦ Ep c (y - t)) = (fun y=> Ep c y) ∘ (fun y=>y-t) :=by ext y; simp only [Function.comp_apply];
  have diff: DifferentiableOn ℝ (fun x => Ep c x - Ep c (x - t))  (Set.Ici t) :=by
    apply DifferentiableOn.sub
    apply Differentiable.differentiableOn differentiable_Ep_r
    have mt: Set.MapsTo (fun y ↦ y - t) (Set.Ici t) (Set.Ici 0) :=by
      unfold Set.MapsTo; intro x hx; simp only [Set.mem_Ici] at hx; simp only [Set.mem_Ici, sub_nonneg, hx]
    rw[ec2]; apply DifferentiableOn.comp (Differentiable.differentiableOn differentiable_Ep_r) _ mt
    simp only [differentiableOn_const, DifferentiableOn.sub_iff_left]
    exact differentiableOn_id
  have: MonotoneOn (fun x => Ep c x - Ep c (x - t))  (Set.Ici t):= by
    apply monotoneOn_of_deriv_nonneg (convex_Ici t)
    apply DifferentiableOn.continuousOn diff
    apply DifferentiableOn.mono diff
    simp only [Set.nonempty_Iio, interior_Ici', Set.Ioi_subset_Ici_iff, le_refl]
    intro x hx ;
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    rw[deriv_sub, ec2, deriv.comp];
    simp only [differentiableAt_id', differentiableAt_const, deriv_sub, deriv_id'', deriv_const',
      sub_zero, mul_one, sub_nonneg]
    rw[(by simp only: (fun y ↦ Ep c y) = Ep c)]
    apply (StrictMonoOn.monotoneOn deriv_Ep_r_strictmono);
    simp only [Set.mem_Ici, sub_nonneg]; linarith
    simp only [Set.mem_Ici, sub_nonneg]; linarith
    linarith
    apply Differentiable.differentiableAt differentiable_Ep_r
    simp only [differentiableAt_id', differentiableAt_const, DifferentiableAt.sub]
    apply Differentiable.differentiableAt differentiable_Ep_r
    rw[ec2]; apply DifferentiableAt.comp
    apply Differentiable.differentiableAt differentiable_Ep_r
    simp only [differentiableAt_id', differentiableAt_const, DifferentiableAt.sub]
  apply  this
  simp only [Set.mem_Ici]; linarith
  simp only [Set.mem_Ici]; linarith
  assumption


lemma mainlem64 (hr: r>0) (ht0: 0 ≤ t) (htp: t ≤ ΔP) (htr: t ≤ r)
            (htd: r ≤ Δ) (hΔ:  ΔP ≤ Δ ): (Wp c Δ) r t ≤  (Wp c Δ) Δ ΔP:= by
  have first : (Wp c Δ) r t ≤ (Wp c Δ) Δ t := monoWp2 hr ht0 htr htd
  have second : (Wp c Δ) Δ t ≤ (Wp c Δ) Δ ΔP := by
    apply  monoWp1 hΔ (by linarith) htp (by simp only [le_refl])
  linarith

lemma W_pos  (hr: r>0) (htd: r ≤ Δ) (ht0: 0 ≤ t) (htr: t ≤ r) :  Wp c Δ r t ≥ 0:= by
  have e0: 0 = Wp c Δ r 0 := by unfold Wp; field_simp
  rw[e0]; apply monoWp1 htr hr ht0 htd

lemma W_eq_Q_Δ  (hΔ : Δ >0): 1 - Qp Δ c (Δ - ΔP) = (Wp c Δ) Δ ΔP:=by
  unfold Wp Qp;
  have ep : Ep c Δ > 0 := by apply Ep_r_pos; linarith
  field_simp;

lemma W_eq_Q  (hΔ : Δ >0):  Qp Δ c r - Qp Δ c rr = Wp c Δ r (r - rr) :=by
  unfold Wp Qp; simp only [sub_sub_cancel]
  have ep : Ep c Δ > 0 := by apply Ep_r_pos; linarith
  field_simp;

lemma lemma64sub (hr: r>0) (ht0: 0 ≤ r - rr) (htp: r - rr ≤ ΔP) (hrr: rr ≥ 0)
            (htd: r ≤ Δ) (hΔ:  ΔP ≤ Δ ) :  |Qp Δ c r - Qp Δ c rr| ≤ 1 - Qp Δ c (Δ - ΔP) :=by
  have e1: |Qp Δ c r - Qp Δ c rr| = Qp Δ c r - Qp Δ c rr := by
    apply abs_of_nonneg; rw[W_eq_Q]; apply W_pos;
    any_goals linarith
  rw[e1, W_eq_Q_Δ, W_eq_Q ];
  apply mainlem64
  any_goals linarith;


lemma lemma64 (hc : c ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) (hΔ:  ΔP < Δ ) (hΔP:  ΔP > 0 ):
    |Qp Δ c r - Qp Δ c (Int.floor (r / ΔP) * ΔP)| ≤ 1 - Qp_lo Δ (Δ - ΔP) := by
  have i00: (Int.floor (r / ΔP) * ΔP) ≥ 0:= by
    apply mul_nonneg; simp; apply Int.floor_nonneg.mpr;
    apply div_nonneg;
    any_goals linarith;

  have i01: r - (Int.floor (r / ΔP) * ΔP) ≥ 0:= by
    simp;
    have i2: Int.floor (r / ΔP) * ΔP ≤ r / ΔP * ΔP := by
      apply mul_le_mul; apply Int.floor_le; simp; linarith
      apply div_nonneg;
      any_goals linarith;
    have e0: r / ΔP * ΔP = r := by field_simp
    linarith;

  have i02: r - (Int.floor (r / ΔP) * ΔP) <  ΔP:= by
    have i1: Int.floor (r / ΔP) +1 > r / ΔP:= by apply Int.lt_floor_add_one
    have i2: Int.floor (r / ΔP) * ΔP > (r/ΔP -1)* ΔP:=by
      apply mul_lt_mul; linarith; simp; linarith; simp;
      apply Int.floor_nonneg.mpr; apply div_nonneg; linarith;linarith
    have e1: r - (r/ΔP -1)* ΔP = ΔP :=by field_simp;
    linarith

  have i1: |Qp Δ c r - Qp Δ c (Int.floor (r / ΔP) * ΔP)| ≤ 1 - Qp Δ c (Δ - ΔP) :=by
    apply lemma64sub
    any_goals linarith
  have i2: Qp Δ c (Δ - ΔP) ≥  Qp_lo Δ (Δ - ΔP):= by apply q_lower_bound; assumption; linarith; linarith
  linarith
