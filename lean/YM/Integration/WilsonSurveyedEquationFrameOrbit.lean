import YM.Integration.WilsonReflectedEquationSurveyOrbit
import YM.Integration.WilsonOriginalPivotWardProduct

/-! All-order erasure of the registered Wilson equation frame on the surveyed inversion tree.
The finite section and its local support are chosen before every coefficient and spectator.
The full orbital integral is taken before extracting its Taylor series. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace YM.Integration.WilsonSurveyedEquationFrameOrbit

open Function Filter Lattice Wilson RG Source Labels Maxwell Push MeasureTheory FVA2
open XSpace PertExtension PertExtension.Orb PertExtension.Series
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard
open PhysicalNext.Repeat.Legato WilsonMaxwellThermometerWardConditional
open scoped Classical Topology BigOperators

variable {G : Gauge} {p : Period}

theorem integrated (T : p.Tree) {f : Config G p.side → ℝ} (test : PreTest f)
    (zero : ∀ t : ℝ, t ≠ 0 → preExpectation f t = 0) :
    Bare.normalized T G (BareOrb.stencil T f) = 0 := by
  have even := even_iff_two_dvd.mpr p.even
  have same : preExpectation f =ᶠ[Tested.germ] preExpectation (0 : Config G p.side → ℝ) := by
    filter_upwards [Tested.eventually_pos] with t ht
    rw [zero t ht.ne']
    exact (WilsonMaxwellThermometerWardCredit.scalar even 0 t).symm
  have gone := unique_wilson same (before_tree_formula even (traySpec G) test)
    (before_tree_formula even (traySpec G) (WilsonMaxwellThermometerWardLinear.zeroField 0))
  rw [BareOrb.diagram_eq T test]
  change replyCoeff f = 0
  rw [← reply_nil (G:=G) even]
  change TaylorWick.into (PowerSeries.mk _) = TaylorWick.into (PowerSeries.mk _)
  change diag (restrictedO f) = diag (restrictedO (0 : Config G p.side → ℝ)) at gone
  rw [gone]

variable (R : Run G) (W : Initialize G) {h : ℕ}
    (V : SectionData (R.family.labels.level h)) (A : Mark.Weave G)

theorem original (granted : Mark.Portfolio R.family.params V (A h)) :
    ∃ r M : ℕ, ∀ (p : Period), M ≤ p.side.val → ∀ x : p.Sites,
      2*r+4 < separation x (-x) →
      (∀ e : Edge p.Sites, e.1 ∈ V.footprint x → e.1+step e.2 ∈ V.footprint x →
        far r x (reflect e)) →
      ∀ (v : (R.family.labels.level h).Coeff) (L : ℂ →L[ℝ] ℝ)
        (P : Config G p.side → ℝ) (s : Set p.Sites), PreTest P → LocalOn s P →
          (∀ e : Edge p.Sites, e.1 ∈ s → e.1+step e.2 ∈ s → far r x e ∧ far r x (reflect e)) →
      Bare.normalized (W.tree p) G
        (BareOrb.stencil (W.tree p) (fun U => L (V.places
          (WilsonReflectedEquationSurveyOrbit.registered R W A v) x U)) *
          BareOrb.stencil (W.tree p) P) = 0 := by
  obtain ⟨r,M,pay⟩ := Mark.radiusH A V granted
  refine ⟨r,M,?_⟩
  intro p cut x span clear v L P s test loc room
  let c := WilsonReflectedEquationSurveyOrbit.registered R W A v
  let src := fun U => L (V.places c x U)
  have st : PreTest src := WilsonMaxwellThermometerWardLinear.placed V c L x granted.valid granted.pays
  rw [←WilsonOriginalPivotWardProduct.product (W.tree p) st test]
  apply integrated (W.tree p) (Uses.pre_mul st test)
  intro t live
  have paid := pay _ (WilsonOriginalPublicFigureWick.invisible W (R.family.labels.level h) v)
  apply WilsonMaxwellThermometerWardCredit.normalize (V.continuous_places c x) test.continuous L t
  apply WilsonMaxwellThermometerWardInversion.original (even_iff_two_dvd.mpr p.even) cut x span
    (V.continuous_evaluate c) paid (V.placed_local x c) clear
    (Complex.continuous_ofReal.comp test.continuous) _ room t live
  intro U Z eq
  exact congrArg (fun z : ℝ => (z:ℂ)) (loc U Z eq)

end YM.Integration.WilsonSurveyedEquationFrameOrbit
