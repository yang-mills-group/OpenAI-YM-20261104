import YM.Integration.WilsonMaxwellThermometerWardConditional
import YM.Integration.WilsonOffsetEquationLaw

/-! The true incoming equation removed from the funded Wilson presentation has
zero local Haar integral at each fixed exterior and every nonzero beta on that
very torus, retaining both its fitted input and engineering factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardStation
open Function Set Filter MeasureTheory Lattice Wilson RG Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato
open WilsonOffsetEquationLaw WilsonMaxwellThermometerWardConditional
open scoped Classical Topology
variable {G:Gauge}

theorem original (R:Run G) (V:∀d,SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    (P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ] R.family.label d)) (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (issued:Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∀d,∃r:ℕ,∀ᶠ N:ℕ in atTop,∀ (p:ℕ) (x:R.family.label d) (o:Site (R.family.side N p))
        (β:ℝ), β≠0 → ∀y:Held G r o,
        (∫z:Free G r o,
          (bare β ((chamber r o).symm (y,z)):ℂ)*
          incoming R.family (V d) N p (P d (N,p)) (x-b.step d (N,p) x) o
            ((chamber r o).symm (y,z)) ∂WilsonMaxwellThermometerWardConditional.law G)=0 := by
  intro d
  obtain ⟨r,M,empty⟩:=Mark.radiusH W (V d) (portfolio d)
  refine ⟨r,?_⟩
  filter_upwards [Mark.lengths R.family.S M] with N size
  intro p x o β pos y
  obtain ⟨v,hv,actual⟩ := (issued.foundation.step d N p).id_sub x
  change bindP R.family W d N p (P d (N,p)) v = x-b.step d (N,p) x at actual
  rw [←actual,evaluated]
  let f:Mark.Pre G:=(V d).evaluate ((R.family.labels.level d).coords (W d v))
  let t:ℂ:=((R.family.S.a N:ℂ)^d)⁻¹
  have zero:=WilsonMaxwellThermometerWardConditional.original
    ((V d).continuous_evaluate _ |>.const_smul t)
    ((empty v hv).scale t) o (size p) pos y
  exact zero

end YM.Integration.WilsonMaxwellThermometerWardStation
