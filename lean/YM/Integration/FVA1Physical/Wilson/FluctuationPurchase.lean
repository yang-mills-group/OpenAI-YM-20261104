import YM.Integration.FVA1Physical.Wilson.FluctuationChart

/-! Purchase the local marked-support forest collar for boundary data of the
same order as thermal fluctuations. The failure probability takes any fixed
power of the inverse coupling, before torus or cutoff is chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum
open MSbar.Bakery.Portal MSbar.Mosaic
open scoped Classical Topology
variable {G : Gauge}

/-- Each marked center has its own two boxes. The conditional probability is
computed with the physical Haar blocking density at this boundary. -/
theorem purchased_fluctuation_chance (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    {D : ℝ} (hD : 0 ≤ D) (exp : ℝ) :
    ∃ p : Palisade, ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G), A.S.patch=P → A.S.kernel=K →
      Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ∀ (z : Positions (Primary A.c G)) (b : Site A.f), ‖z‖ ≤ D * room (tip G P.L x) →
      let v := tip G P.L x
      let X := Mosaic.boxX v b
      let Y := Mosaic.boxY v b
      let O := represent (tint G (Exterior.Body 1 A.c) z)
      let μ := vest (priced A.F A.v A.pre.clip A.pre.path) z
      let χ := chambers A.F Y J O μ
      let U := hotel A.F X Y J O μ (pillow v) (room v)
      let width := fluctuationFee p J D*room v/A.fClock
      Grants A.v A.pre A.F p 3 ∧ A.Calibrate J p X Y z v 0 exp ∧
      (∀ V∈U,χ V∈regularInputs A.fClock width) ∧
      chance A.S A.pre O (χ ⁻¹' regularInputs A.fClock width)ᶜ ≤ v^exp := by
  obtain ⟨p,_,offer⟩ := armlet P K J H H' branch cle 3 le_rfl
  refine ⟨p,?_⟩
  by_cases ok : 0 < p.gap ∧ 0 < p.a ∧ 0 < p.density
  swap
  · exact Eventually.of_forall fun x A h₀ h₁ season z b hb => by
      have g := (offer _ _ _ h₀ h₁ season A.F A.v).buys
      exact False.elim (ok ⟨g.pos_m,g.pos_a,g.pos_C⟩)
  have rise := Work.E09.betaF_growth G P.L
  filter_upwards [earned J H H' p P K cle simple 0 exp 3,fees p P J cle,
    solders P K J H H' p cle ok.1 ok.2.1 ok.2.2,
    rise.eventually (calibrated_fluctuation_chance p J cle hD),
    rise.eventually (fluctuation_below_skies D)]
    with x covered sizes tint coverage wide
  intro A patch kernel season z b bound v X Y O μ χ U width
  have give := offer A.pre A.post x patch kernel season A.F A.v
  have price := season.case_
  rw [patch] at price
  obtain ⟨v₁,_,_,_,_,_,_,_,_,_,_,_,rad,garden⟩ := sizes
  have hg := Mosaic.ever (zero_lt_one.trans v₁) price.beta price.upper
  have hg' : Mosaic.lensT v A.fClock := hg
  have hs : ‖z‖ ≤ skies v := bound.trans wide
  have paid := Mosaic.Issue.fills A J p X Y z b P K H H' patch.symm kernel.symm season give hs cle covered rfl rfl rad garden
  have shield := (tint A.pre A.post price season.hull).holm
  have mass : 0 < A.S.push A.pre.beta A.pre.eval O := by
    rw [←season.taskEval]
    unfold Rep.eval
    rw [Activities.gas_one _ _ (voids paid.first.folds shield),mul_one]
    exact Real.exp_pos _
  have adm := (show Admitted O A.pre A.S H'.width H'.paths (ability v) (lbt v) 1 from
    ⟨price.lawful,fun Q=>(season.shine Q).le,mass,A.S.isKernel season.bends.1 _⟩)
  exact ⟨give,paid,coverage A X Y z hg' bound give paid adm⟩

end YM.Integration.FVA1Physical.Wilson
