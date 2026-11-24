import YM.Integration.FVA1Physical.Wilson.PureForest
import YM.Integration.FVA1Physical.Wilson.HotelTest

/-! One purchased physical cell for the FVA2 Wilson readings, with an explicit
probability and signed readout cost for its rejected sector. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum
open MSbar.Bakery.Portal MSbar.Mosaic
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {Q : StepData c f} {R : Rep G f} {out : Rep G c}

def ForestCell.CutCost (T : ForestCell Q R out) (g w price : ℝ) : Prop :=
  let V := represent (tint G (Exterior.Body 1 c) T.x)
  let copy := chambers T.F T.Y T.J V T.center
  let kept := copy ⁻¹' regularInputs g w
  chance Q R V keptᶜ ≤ price ∧ ∀ F : Config G f→ℝ, Measurable F → ∀ b:ℝ, 0 ≤ b →
     (∀ U, |F U|≤b) → |expect Q R V F-expect Q R V (kept.indicator F)|≤b*price

theorem purchased_wilson_cell (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    {D : ℝ} (hD : 0 ≤ D) (exp : ℝ) :
    ∃ p : Palisade, ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G), A.S.patch=P → A.S.kernel=K →
      Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ∀ (z : Positions (Primary A.c G)) (b : Site A.f), ‖z‖ ≤ A.fClock*D →
      let v := tip G P.L x
      ∃ T : ForestCell A.S A.pre A.post, T.P=p ∧ T.J=J ∧ T.F=A.F ∧ T.source=A.v ∧
        T.X=Mosaic.boxX v b ∧ T.Y=Mosaic.boxY v b ∧ T.x=z ∧
        T.Fits A.fClock (Mosaic.vol v) ∧ T.CutCost A.fClock (Mosaic.vol v) (v^exp) := by
  obtain ⟨p,buy⟩ := purchased_chart_chance J cle simple H H' P K branch hD exp
  refine ⟨p,?_⟩
  by_cases ok : 0 < p.gap ∧ 0 < p.a ∧ 0 < p.density
  swap
  · filter_upwards [buy] with x acquire
    intro A patch kernel season z b hb
    have good := (acquire A patch kernel season z b hb).1.buys
    exact False.elim (ok ⟨good.pos_m,good.pos_a,good.pos_C⟩)
  have rise := Work.E09.betaF_growth G P.L
  filter_upwards [buy,fees p P J cle,solders P K J H H' p cle ok.1 ok.2.1 ok.2.2,
    rise.eventually (bounded_hotel_radii p J cle hD)] with x acquire sizes tinting radius
  intro A patch kernel season z b hb v
  obtain ⟨give,paid,_,rare⟩ := acquire A patch kernel season z b hb
  have price := season.case_
  rw [patch] at price
  obtain ⟨v₁,_,_,_,_,_,_,_,_,_,_,_,rad,garden⟩ := sizes
  have band := Mosaic.ever (zero_lt_one.trans v₁) price.beta price.upper
  have shield := (tinting A.pre A.post price season.hull).holm
  let X := Mosaic.boxX v b
  let Y := Mosaic.boxY v b
  let O := represent (tint G (Exterior.Body 1 A.c) z)
  let μ := vest (priced A.F A.v A.pre.clip A.pre.path) z
  let T : ForestCell A.S A.pre A.post :=
    ⟨A.F,X,Y,J,p,z,μ,pillow v,room v,base J v,rot p v,voyageB v,Pressure.radiusB v,v^(-(1:ℝ)),3,A.v,
      cle,paid.first,shield,give,rad,garden⟩
  have fit : T.Fits A.fClock (Mosaic.vol v) := radius A.fClock band ‖z‖ ‖μ‖ (norm_nonneg _) hb
    (fun hz=>terror A.F A.v p z give le_rfl hz)
  refine ⟨T,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fit,rare,?_⟩
  intro F mF cost hc bound
  have mass : 0 < A.S.push A.pre.beta A.pre.eval O := by
    rw [←season.taskEval]; unfold Rep.eval
    rw [Activities.gas_one _ _ (voids paid.first.folds shield),mul_one]
    exact Real.exp_pos _
  have adm : Admitted O A.pre A.S H'.width H'.paths (ability v) (lbt v) 1 :=
    ⟨price.lawful,fun Q=>(season.shine Q).le,mass,A.S.isKernel season.bends.1 _⟩
  exact expect_on_chart O ((informed A.F X Y J O μ cle paid.first.extendsX).1 (regular_meas _ _))
    adm F mF hc bound rare

end YM.Integration.FVA1Physical.Wilson
