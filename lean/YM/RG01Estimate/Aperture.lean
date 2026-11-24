import YM.RG01Estimate.Rotors
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld
/-!
# Changing charts while retaining sufficiently many powers

Arbitrary healthy patch in Seam; all k+T+2 derivatives at normalized directions.
Keep margin +1 so `horizon_pay` aperture on Y can be matched. Only changes the
shape sigma on the consumer side. No curvature identities or coefficient germ comparison
provided by this theorem. Need actual alignment proof for using the auxiliary calculation
in a different torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Receipt
open Function Filter Set Metric Finset Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat Blaze.March
open AbsoluteSums Animals PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open Laplace Laplace.Stellar Series Boulevard Blaze.Frond Exterior
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
lemma openings (G:Gauge)(L:Side) (Y:ℝ→ℕ) (hk:Laplace.Cookie G L (fun x=> (Y x:ℝ))) :
    ∃ f:ℝ→ℝ, Cookie G L f ∧ ∀ᶠ t in atTop,
      ∀ (P:BudgetPoint), P.threshold ≤ 2*Pressure.fiery G t L →
       ∀ (c f':Side) (s:Site c) (w:ℕ)(u:2*w≤f'.val), 2*Y t < c.val → w+1≤Y t →
       ∀ (β:ℝ), betaF G t L/2≤ β→ β≤2*betaF G t L→
       ∀ V:Config G c, Healthy P.threshold (neighbors (Y t) s) V →
        ∃ (z:Site f'→G.El) (x:Positions (Uniform.Primary f' G)), actual (gStep β • x)=
             gauge z (Slide.shape (Slide.cognac u) s V) ∧ ‖x‖+1 < f t := by
  obtain ⟨A,d,hA,hd,H⟩:= Next.Fluctuations.extend_interior G
  let ℓ t:= (16:ℝ)*(2*(Y t:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)
  let K t:= A*(ℓ t * (4*Delay.fineMonitor G L t))
  let F t:=ℓ t*(2*Pressure.fiery G t L)
  have hm:=hk
  have hh: Cookie G L ℓ:= ((Cookie.const 16).pays ((((Cookie.const 2).pays hm).joins (Cookie.const 1)).pow 5)).pays (Cookie.const _)
  have hk : Cookie G L K:= (Cookie.const _).pays (hh.pays ((Cookie.const _).pays Cookie.mast))
  have hF := hh.uses.mul (Rate.flame (G:=G) (L:=L)|>.mul_left 2)
  refine ⟨fun i=> K i+2,hk.joins (Cookie.const _),?_⟩
  filter_upwards [hF.below (by norm_num) d hd, Delay.shift_pos G L] with x hv h0 P hx c g o w u h hp β hb hβ V he
  have hf :0≤ F x:= by have hh := P.threshold_pos.trans_le hx; unfold F ℓ; positivity
  have hj (y:Site c) (hy:separation o y≤Y x) (p : PlaqAxes): toll V (y,p) ≤ P.threshold:= by by_contra! hv; exact Finset.disjoint_left.mp he ((neighbors_mem ..).2 hy) ((flags_spec ..).mpr ⟨(y,p), WilsonStartup.anchor_visit _,hv⟩)
  obtain ⟨a,ha⟩:= Work.E08.axial_patch o V w (Y x) hp h (2*Pressure.fiery G x L) (P.threshold_pos.trans_le hx).le (fun y hy p=> (hj y hy p).trans hx)
  · let z (i:Site g):= a (Slide.sites (Slide.cognac u) o i); let g':=Slide.shape (Slide.cognac u) o V
    let W:= gauge z g'; have he i:G.chord (W i) ≤ F x:= by
      unfold W g'; rw [show gauge z (Slide.shape (Slide.cognac u) o V)=_ from (Slide.shape_gauge (Slide.cognac u) o a V).symm]; unfold Slide.shape; split; exact ha _ (Slide.village ..)
      split; next h'=> rw [G.chord_inv]; exact ha _ (Slide.village ..)
      simpa [Gauge.chord] using hf
    obtain ⟨b,hb',hQ⟩:= H (fun _=> (0:Site c)) 0 0 W (F x) hf ((le_abs_self _).trans hv) (fun i _=>he i)
    let t:=gStep β; have hz := Fare.gS β ((half_pos h0).trans_le hb)
    let X:=(Uniform.tint G _).symm b
    refine ⟨z,t⁻¹ • X,?_,?_⟩
    · rw [smul_inv_smul₀ hz.1.ne']; unfold Boulevard.actual; rw [show tint G _ X=_ from ContinuousLinearEquiv.apply_symm_apply ..]; exact funext fun i=> (hQ i (by simp)).symm
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hz.1).le]; suffices he : t⁻¹* ‖X‖ ≤ K x by linarith
    rw [inv_mul_le_iff₀ hz.1]
    have ht:=reverse_g x β h0 ((half_pos h0).trans_le hb) hβ
    have hp:2*Pressure.fiery G x L ≤ t*(4*Delay.fineMonitor G L x) := by
        change 2*(gStep (betaF G x L)* Delay.fineMonitor G L x) ≤ t *_
        refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (Delay.monitor_pos G L x).le) (show 0≤(2:ℝ) by norm_num)).trans_eq ?_; unfold t; ring
    apply le_trans ((Uniform.tint_inv_le _).trans hb')
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by unfold ℓ; positivity)) hA.le).trans_eq
    unfold K; ring
end YM.RG01Estimate.Receipt
