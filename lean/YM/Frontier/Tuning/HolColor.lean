import YM.Frontier.Tuning.RecoilIdentity
/-! Algebraic holomorphy in all coefficient directions chosen before integration, with actual gauge arguments held real. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Frontier.Tuning.HolColor
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Eider Flux YM.Frontier.Tuning.Held TwoMotion RecoilIdentity Shield DensityTilt PhysicalNext.Repeat.Alabaster
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {O:ChartRatio G}(Q:Coat T F) (R : Rep G f)
variable {z:ℂ}{τ : ℂ→ℂ}{e h : ℂ→Payload G f}{I:Config G f}{u:Directions G f}{n:Air f G}
variable {τ':ℂ}{l:ℕ}{k:Finset ℕ}{a W:ℝ}(ht : DifferentiableAt ℂ τ z)(hb:τ z ∈ Complex.slitPlane)
include ht hb in
lemma tint : DifferentiableAt ℂ (ComplexVertex.logMass O ∘ τ) z:=
by unfold Function.comp ComplexVertex.logMass; exact DifferentiableAt.sub (differentiableAt_const _) ((ht.clog hb).const_mul _)
  -- manually
include ht
lemma paintL (he:∀ i,DifferentiableAt ℂ (fun z=>e z i I) z) (j : LogIndex c f) : DifferentiableAt ℂ (fun z=>comboLog Q R I u n O a (τ z) (e z) j) z:=by
  rcases j with (j|j)|j
  · change DifferentiableAt ℂ (fun z=> -ComplexVertex.hiddenC _ _ (e z j) I * _) z
    refine DifferentiableAt.mul_const (DifferentiableAt.neg ?_) _
    by_cases ht:Healthy R.p.threshold (R.activities.reg j).support I
    · simp only [ComplexVertex.hiddenC,masked_eq _ _ _ _ ht]; exact he j
    simp_rw [ComplexVertex.hiddenC,masked_ne _ _ _ _ ht]; exact differentiableAt_const _
  all_goals dsimp only [comboLog]; split_ifs; try exact differentiableAt_const _
  all_goals first | simp_rw [div_eq_mul_inv]; exact (ht.mul_const _).mul_const _ | apply differentiableAt_const
include hb
lemma paintH (he:∀ i,DifferentiableAt ℂ (fun z=>e z i I) z) (hh:∀ i,DifferentiableAt ℂ (fun z=>h z i I) z)(j:Head S) : DifferentiableAt ℂ (fun z=> emberC Q R I u n O a W k (τ z) l (e z) (h z) j) z:=by
  rcases j with j|j|j|j
  · simp only [emberC,penGain,Sum.elim]; split_ifs; swap;· exact differentiableAt_const _
    apply DifferentiableAt.mul_const;apply (Complex.differentiableAt_exp).comp z
    exact ((ht.sub_const _).mul_const _).add ((DifferentiableAt.sub (differentiableAt_const _) (tint ht hb)).const_mul _)
  · exact (hh j).mul_const _
  · exact ((Complex.differentiableAt_exp.comp z (paintL Q R ht he j)).sub_const _)
  exact differentiableAt_const _
lemma mass (B:Finset (Bond f))(K:ℝ)(C:Config G c): DifferentiableAt ℂ (fun z=>phasePoly (τ z) R Q B K C n) z:=by
 unfold phasePoly; dsimp only; simp_rw [div_eq_mul_inv]; apply Complex.differentiableAt_exp.comp (f:=fun _=>_) z
 exact (((ht.clog hb).sub_const _).const_mul _).add ((DifferentiableAt.sub (differentiableAt_const _) (ht.mul_const _)).mul_const _) -- div
lemma turn (B:Finset (Bond f)) (K:ℝ)(C:Config G c)(j:Molecule S)
   (he:∀ i,DifferentiableAt ℂ (fun w=>e w i (Q.input (worldZ Q R.beta n))) z) (hh:∀ i,DifferentiableAt ℂ (fun w=>h w i (Q.input (worldZ Q R.beta n))) z) : DifferentiableAt ℂ (fun z=>floatC Q R n O a W k (τ z) l (e z) (h z) j) z:=by
 unfold floatC
 dsimp only
 let f i z:= emberC Q R (Q.input (worldZ Q R.beta n)) (worldZ Q R.beta n) n O a W k (τ z) l (e z) (h z) i
 change DifferentiableAt ℂ (fun z=>∏ i∈j, f i z) z
 rw [show (fun z=>∏ i∈j, f i z)=(∏ i∈j, f i) from funext fun _=> (Finset.prod_apply _ _ _).symm]
 exact DifferentiableAt.finset_prod (fun i hi=> paintH Q R ht hb he hh i)
lemma spin (B:Finset (Bond f)) (K:ℝ)(C:Config G c)(j:Molecule S)
   (he:∀ i y,DifferentiableAt ℂ (fun w=>e w i y) z)(hh:∀ i y,DifferentiableAt ℂ (fun w=>h w i y) z): DifferentiableAt ℂ (fun w=>rotor B K C j (e w) (h w) R Q O a W l (τ w) n) z:=
   ((mass Q R ht hb B K C).mul_const _).mul (turn (vary Q C) R ht hb B K C j (fun i=>he i _) (fun i=>hh i _))
end YM.Frontier.Tuning.HolColor
