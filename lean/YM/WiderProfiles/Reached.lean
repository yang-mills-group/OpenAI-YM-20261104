import YM.WiderProfiles.Geometry
/-!
# Check that the linear-in-height example is genuinely a widening

Not needed in the comparison proof. On *every* sufficiently late mesh, the
result for `n=2`, exponent 1 applies to actual layouts of unbounded extent,
even with unbounded pair distance (and a name right at the origin).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set Real
open Lattice XSpace XSpace.Cirrus Arrival.Schedule
open scoped Topology BigOperators Classical
lemma unbounded_window (R : ℝ) :
    ∀ᶠ p in Front, ∃ s : Sample 2, grab s=p ∧ Admits 1 1 1 s ∧
      plot (familiar s) 0 = 0 ∧ R ≤ theta p ∧
      theta p ≤ ‖plot (familiar s) (1:Fin 2)‖ := by
  have he : ∀ᶠ p : Mesh in Front, p.spacing ≤ 1 := frontier.smaller
  have ht : Tendsto theta Front atTop := by
    have hf : Tendsto (fun p : Mesh => log p.spacing) Front atBot :=
      tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨frontier.endpt,
        Eventually.of_forall fun i => i.positive⟩)
    exact (tendsto_neg_atBot_atTop.comp hf).congr' (he.mono fun i hi => (theta_value hi).symm)
  filter_upwards [he, frontier.horizon.eventually_ge_atTop 16,
    ht.eventually_ge_atTop (max 1 R)] with p hp hm hi
  let N := p.p.side.val
  change 16 ≤ (N:ℝ) at hm
  let c := ⌈(N:ℝ)/8⌉; let w := ⌈theta p / p.spacing⌉; let v := p.spacing * (w:ℝ)
  let s : Sample 2 := ⟨p, fun i _ => if i=0 then c else c+w, fun _ => p.spacing * (c:ℝ)⟩
  have hp0 := p.positive; have h1 : 1 ≤ theta p := (le_max_left ..).trans hi
  have hw0 : theta p ≤ v := (div_le_iff₀ hp0).1 (Int.le_ceil _) |>.trans_eq (mul_comm ..)
  have hw1 : v ≤ 1 + theta p := by
    have h : (w:ℝ)-1 ≤ theta p / p.spacing := by linarith [Int.ceil_lt_add_one (theta p / p.spacing)]
    rw [le_div_iff₀ hp0] at h; unfold v; nlinarith
  have hor : ‖fun (_ : Axis) => v‖ = v := by
    rw [pi_norm_const, Real.norm_of_nonneg ((by linarith : 0 ≤ theta p).trans hw0)]
  have h0 : plot (familiar s) 0=0 := by
    funext j; change p.spacing * ((if (0:Fin 2)=0 then c else c+w:ℤ):ℝ) - p.spacing*(c:ℝ)=0; simp
  have hw : plot (familiar s) 1=(fun _ => v) := by
    funext j; change p.spacing*((if (1:Fin 2)=0 then c else c+w:ℤ):ℝ) - p.spacing*(c:ℝ) = p.spacing*(w:ℝ)
    simp [mul_add]
  have huk : welcome s := by
    change (fun (_:Axis) => p.spacing * (c:ℝ)) ∈ Icc (fun _ => p.size /8) (fun _ => p.size /4)
    have h : (N:ℝ) / 8 ≤ c := Int.le_ceil _
    have hc : (c:ℝ) < (N:ℝ) / 8 + 1 := Int.ceil_lt_add_one _
    have hd : (c:ℝ) ≤ (N:ℝ) / 4 := by linarith
    constructor
    · intro i; change p.spacing*N/8 ≤ _; linarith [mul_le_mul_of_nonneg_left h hp0.le]
    intro i; change _ ≤ p.spacing*N/4; linarith [mul_le_mul_of_nonneg_left hd hp0.le]
  have hor2 (i : Fin 2) : i=0 ∨ i=1 := by omega
  refine ⟨s, rfl, ⟨⟨by change 16 ≤ N; exact_mod_cast hm,hp,huk⟩, ?_, ?_⟩, h0,
    (le_max_right ..).trans hi, ?_⟩
  · intro i; change ‖_‖ ≤ 1 * (1 + theta p)^1; rw [one_mul,pow_one]
    rcases hor2 i with hi | hi
    · rw [hi,h0,norm_zero]; linarith
    rw [hi,hw,hor]; exact hw1
  · intro i j hv; rcases hor2 i with hi|hi <;>
      rcases hor2 j with hj|hj
    · exact False.elim (hv (hi.trans hj.symm))
    · rw [hi,hj,h0,hw,zero_sub,norm_neg,hor]; exact h1.trans hw0
    · rw [hi,hj,h0,hw,sub_zero,hor]; exact h1.trans hw0
    exact False.elim (hv (hi.trans hj.symm))
  rw [hw,hor]; exact hw0
end YM.FVA2.WiderProfiles
