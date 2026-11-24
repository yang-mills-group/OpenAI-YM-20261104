import YM.Frontier.Tuning.DensityTilt
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tropolis
/-! Changing variables with a real Jacobian AND two complex tilted Gaussian factors. This is on one immutable full-color marginal; no integration on a complex group chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.ComplexSweep
open Footage HeldBurst DensityTilt
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Eider Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift TwoMotion AngularReceipt Flux Shield Pond Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R A' : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {H0 a C α Z β γ d η ε σ W s b μ r q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
variable {χ:Chi}
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
section
variable {ι : Type}[Fintype ι][DecidableEq ι]
def tiltQ (A : Matrix ι ι ℝ)(b:ℝ)(τ:ℂ)(w:Poll.Body ι):= Complex.exp ((Fintype.card ι:ℂ)/2*(Complex.log τ-Complex.log b)+(1-τ/b)*(dotProduct w.ofLp (A⁻¹ *ᵥ w.ofLp)/2:ℝ))*(lens₀ A w:ℝ) -- result complex
lemma recommendsC (A:Matrix ι ι ℝ)(h:A.PosDef)(f:Poll.Body ι→ℂ): (∫ w, f w ∂ Poll.sweep A)= ∫ w,(lens₀ A w:ℝ) • f w := by
  have ht : Measurable (fun x=> lens₀ A x) := bulbB (S:=fun _ : Poll.Body ι=>A) (fun i j=> measurable_const) (z:=id) measurable_id
  rw [magnifies A h]; rw [integral_withDensity_eq_integral_toReal_smul (show Measurable (fun x=> ENNReal.ofReal (lens₀ A x)) from ENNReal.measurable_ofReal.comp ht) (ae_of_all _ (fun x=> ENNReal.ofReal_lt_top))]
  apply integral_congr_ae (ae_of_all _ fun w=>?_)
  simp_rw [ENNReal.toReal_ofReal ((fullFuel _ _).le)]
end
variable (B : Finset (Bond f)) (X : Coat T F) (V : Config G c)
local notation "J" => lensS B G
variable {A:ℝ}(perm : Canary G d A)(he:Drivable X d A V)
lemma exactPhase (z : Air f G)(τ : ℂ) : phasePoly τ R X B d V z= Complex.exp (((lensS B G).card:ℂ)/2*(Complex.log τ-Complex.log R.beta)+(1-τ/R.beta)*(dotProduct (WithLp.ofLp (swim J (course X d R.beta z V))) ((circuit J (vary X V).relating)⁻¹ *ᵥ WithLp.ofLp (swim J (course X d R.beta z V)))/2:ℝ)) := rfl
lemma phase_slab (z z': Air f G) (h:swim J z=swim J z')(τ:ℂ): scTilt X τ R B d V z=scTilt X τ R B d V z':= by
  rw [scTilt,scTilt,exactPhase,exactPhase,← pitch_alt,← pitch_alt,h,slab B X V z z' h]
lemma gather {K:Air f G→ℂ}(h: X.relating.PosDef) (he:∀ z z',swim J z=swim J z' → K z=K z') (hh:Measurable K):
    (∫ u,K u ∂X.dice)=∫ w,K (spill J w) ∂Poll.sweep (circuit J X.relating):=by
  have hP:=(Pond.orbit h.posSemidef J).map_eq
  unfold arch at hP
  rw [← hP, integral_map (swim_m J).aemeasurable (show AEStronglyMeasurable (fun y=>K (spill J y)) (Measure.map (swim J) (Poll.sweep X.relating)) from (hh.comp (spill_m J)).aestronglyMeasurable)]
  exact integral_congr_ae (ae_of_all _ fun z=> he z _ (Pond.settled ..).symm)
include perm he
lemma gyreC {R:Rep G f} (hR:0<R.beta) (g:Poll.Body (↥J) → ℂ) : (∫ w,g w)=∫ z,(jacL B X d R.beta V (spill J z)) • g (pitch B X d R.beta V z) :=by
   classical
   let f:= pitch B X d R.beta V
   have hh (z : Poll.Body (↥J)) : DifferentiableAt ℝ f z := by
      nth_rw 1 [← Pond.settled J z]; exact (blocks B X perm hR V he _).differentiableAt
   have hi:= Flux.across B X perm hR V he
   have hF:= integral_image_eq_integral_abs_det_fderiv_smul volume (s:=Set.univ) MeasurableSet.univ (fun x _=>
      (hh x).hasFDerivAt.hasFDerivWithinAt) hi.1.injOn g
   rw [Set.image_univ, Set.range_eq_univ.mpr hi.2,setIntegral_univ,setIntegral_univ] at hF
   refine hF.trans (integral_congr_ae (ae_of_all _ fun z=>?_))
   let v:=Pond.spill J z
   have hp := almanac B X perm hR V he v; unfold v at hp; rw [Pond.settled] at hp
   dsimp only
   rw [show (fderiv ℝ f z).det=_ from hp,abs_of_pos (jac_pos B X V he ..)]
lemma rotates {R:Rep G f} (hR:0<R.beta)(τ:ℂ)(g:Air f G→ℂ) (hf: ∀ z z':Air f G, swim J z=swim J z' → g z=g z') (hp : X.relating.PosDef) (hm:Measurable fun z=> scTilt X τ R B d V z * g (course X d R.beta z V)):
  (∫ w, tiltQ (circuit J (vary X V).relating) R.beta τ w * g (spill J w))=
  ∫ z, scTilt X τ R B d V z * g (course X d R.beta z V) ∂X.dice:= by
  let f(z:Air f G):=scTilt X τ R B d V z * g (course X d R.beta z V)
  have he': (∫ u,f u ∂X.dice)= ∫ w, f (spill J w) ∂Poll.sweep (circuit J X.relating) :=by
    apply gather B X hp _ hm
    intro z z' h
    rw [phase_slab B X V z z' h]; congr 1
    exact hf _ _ (by rw [← pitch_alt,←pitch_alt,h])
  rw [he', recommendsC (circuit J X.relating) (hp.submatrix Subtype.val_injective), gyreC B X V perm he hR]
  apply integral_congr_ae (ae_of_all _ fun w=>?_)
  let v:= spill J w; let w':Poll.Body (↥J):= pitch B X d R.beta V w
  have h1:swim J (course X d R.beta v V)=w' :=rfl
  have h2:g (spill J w')=g (course X d R.beta v V) := hf _ _ (by rw [h1,Pond.settled])
  change (jacL B X d R.beta V v) • (tiltQ _ _ _ w'*_) = _ • f v
  unfold f scTilt tiltQ
  rw [exactPhase, scalp,h1] -- Fintype.card_coe and let
  rw [h2, show swim J v=w from settled ..]
  rw [Complex.real_smul, Complex.real_smul]; push_cast; rw [Fintype.card_coe]
  have h3:=show (lens₀ (circuit J X.relating) w:ℂ)≠0 by exact_mod_cast (fullFuel (circuit J X.relating) w).ne'
  field_simp

end YM.Frontier.Tuning.ComplexSweep
