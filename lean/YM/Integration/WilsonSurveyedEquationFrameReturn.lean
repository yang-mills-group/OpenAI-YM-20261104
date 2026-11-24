import YM.Integration.WilsonSurveyedEquationFrameBasis
import YM.Integration.WilsonIndependentWardNamedCancellation
import YM.Integration.WilsonIndependentRawRosterWord

/-! Actual regulated spectators of each thermal rank against the full equation
section. Support and the inverted images are checked on the integrated board. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace YM.Integration.WilsonSurveyedEquationFrameReturn
open Function Filter Lattice Wilson RG Source Labels Maxwell Push MeasureTheory FVA2
open XSpace PertExtension PertExtension.Orb PertExtension.Series
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard
open PhysicalNext.Repeat.Legato WilsonMaxwellThermometerWardConditional XSpace.Cirrus XSpace.Rose
open RegulatorIR RegulatorIR.Profiles RegulatorIR.Cluster
open WilsonSurveyedEquationFrameBasis (projection kernel)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentRawRosterWord (degree physical film)
open WilsonReflectedEquationSurveyOrbit
open scoped Classical BigOperators Topology

variable {G : Gauge} (H : Hol G) {d : ℕ} (B : Labels.Frame G d) (V : SectionData B)
    (A : Mark.Weave G)

/-- The housing is chosen before the complete raw direction and each test. -/
theorem erases (has : Mark.Portfolio H V (A d)) : ∃ r M : ℕ, ∀ (p : Period), M ≤ p.side.val →
    ∀ x : p.Sites, 2*r+4 < separation x (-x) →
    (∀ e : Edge p.Sites, e.1 ∈ V.footprint x → e.1+step e.2 ∈ V.footprint x →
      far r x (reflect e)) →
    ∀ (n : Label G d), n ∈ equationIdeal G d → ∀ (L : ℂ →L[ℝ] ℝ) (T : p.Tree)
      (Y : Config G p.side → ℝ) (s : Set p.Sites), PreTest Y → LocalOn s Y →
      (∀ e : Edge p.Sites, e.1 ∈ s → e.1+step e.2 ∈ s → far r x e ∧ far r x (reflect e)) →
    Bare.normalized T G (BareOrb.stencil T (fun U => L (V.places (B.coords (A d n)) x U)) *
      BareOrb.stencil T Y) = 0 := by
  obtain ⟨r,M,paid⟩ := Mark.radiusH A V has
  refine ⟨r,M,?_⟩
  intro p cut x span clear n hn L T Y s test loc room
  let c := B.coords (A d n)
  have st := WilsonMaxwellThermometerWardLinear.placed V c L x has.valid has.pays
  rw [←WilsonOriginalPivotWardProduct.product T st test]
  apply WilsonSurveyedEquationFrameOrbit.integrated T (Uses.pre_mul st test)
  intro t active
  apply WilsonMaxwellThermometerWardCredit.normalize (V.continuous_places c x) test.continuous L t
  apply WilsonMaxwellThermometerWardInversion.original (even_iff_two_dvd.mpr p.even) cut x span
    (V.continuous_evaluate c) (paid _ hn) (V.placed_local x c) clear
    (Complex.continuous_ofReal.comp test.continuous) _ room t active
  intro U Z eq
  exact congrArg Complex.ofReal (loc U Z eq)

variable {I : Type} (R : Run G) (W : Initialize G) (Y : Sample 2)
    (survey : I → Bool) (h : I → ℕ) (i : ∀ a, (R.family.labels.level (h a)).Index)
    (z : I → Cover)
local notation "Tr" => W.tree Y.F.p

theorem placed (s : Set Y.F.Sites)
    (inside : ∀ a, ((sectionAt R W (survey a) (h a)).footprint (wrap Y.F.p.side (z a)) : Set Y.F.Sites) ⊆ s)
    (J : Composite I) : LocalOn s (physical R W survey h i Y z J) := by
  induction J with
  | atom a =>
    intro U V same
    apply WilsonIndependentWardNamedCancellation.peer_local R W Y _ (i a) (survey a) (z a) U V
    exact fun e g k => same e (inside a g) (inside a k)
  | pair l k left right =>
    intro U V eq
    exact congrArg₂ (·*·) (left U V eq) (right U V eq)

theorem unsuspend {N Q : Bare.Series Tr G} {f : Config G Y.F.p.side → ℝ}
    (j : ℕ) (clear : PowerSeries.X^j*Q = BareOrb.stencil Tr f)
    (zero : Bare.normalized Tr G (N*BareOrb.stencil Tr f) = 0) :
    Bare.normalized Tr G (N*Q) = 0 := by
  apply (mul_eq_zero.mp (show PowerSeries.X^j * Bare.normalized Tr G (N*Q) = 0 from ?_)).resolve_left
    (pow_ne_zero _ PowerSeries.X_ne_zero)
  rw [←Bare.normalized_scalar]
  simp only [Bare.scalar,map_pow,PowerSeries.map_X]
  rwa [←mul_left_comm N,clear]

/-- All labels are fitted in a single full finite section before any roster or
geometry. The exact Ward residual is tested on the fully integrated W tree,
with each occupied spectator's actual desuspended thermal rank. -/
theorem original :
    ∃ (V : ∀ d, SectionData (R.family.labels.level d)) (A : Mark.Weave G)
      (P : ∀ d, Label G d ≃ₗ[ℂ] Label G d) (C : ℕ → ℝ), ∀ d,
    Mark.Portfolio W.hol (V d) (A d) ∧ (∀ p, P d p = projection p + A d (kernel p)) ∧
    (∀ p, ‖(R.family.labels.level d).coords ((P d).symm p)‖ ≤ C d * ‖(R.family.labels.level d).coords p‖) ∧
    ∃ r M : ℕ, ∀ (Y : Sample 2), M ≤ Y.F.p.side.val → ∀ x : Y.F.Sites,
    2*r+4 < separation x (-x) →
    (∀ e : Edge Y.F.Sites, e.1 ∈ (V d).footprint x → e.1+step e.2 ∈ (V d).footprint x →
      far r x (reflect e)) →
    ∀ (p : Label G d) (L : ℂ →L[ℝ] ℝ) (I : Type) (survey : I → Bool) (h : I → ℕ)
      (i : ∀ a, (R.family.labels.level (h a)).Index) (z : I → Cover) (J : Composite I)
      (s : Set Y.F.Sites), (∀ a, ((sectionAt R W (survey a) (h a)).footprint (wrap Y.F.p.side (z a)) : Set Y.F.Sites) ⊆ s) →
    (∀ e : Edge Y.F.Sites, e.1 ∈ s → e.1+step e.2 ∈ s → far r x e ∧ far r x (reflect e)) →
      Bare.normalized (W.tree Y.F.p) G
        (BareOrb.stencil (W.tree Y.F.p) (fun U => L ((V d).places
          ((R.family.labels.level d).coords (A d (kernel ((P d).symm p)))) x U)) *
          film R W survey h i Y z J) = 0 := by
  choose J₀ V A P C nn bank deposited matched bill using
    fun d => WilsonSurveyedEquationFrameBasis.original (R.family.labels.level d) W
  refine ⟨V,A,P,C,?_⟩
  intro d
  obtain ⟨r,M,paid⟩ := erases W.hol (R.family.labels.level d) (V d) A (bank d)
  refine ⟨bank d,matched d,bill d,r,M,?_⟩
  intro Y cut x span clear p L I survey h i z J s inHouse room
  have full := WilsonIndependentRawRosterWord.finite R W survey h i Y z J
  apply unsuspend W Y _ full.2
  exact paid Y.F.p cut x span clear _ (WilsonSurveyedEquationFrameBasis.equation ((P d).symm p)) L
    (W.tree Y.F.p) _ s full.1 (placed R W Y survey h i z s inHouse J) room

end YM.Integration.WilsonSurveyedEquationFrameReturn
