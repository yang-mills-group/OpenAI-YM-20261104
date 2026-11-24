import YM.Integration.WilsonMaxwellThermometerWardInversion
import YM.Integration.WilsonMaxwellThermometerWardStation

/-! The exact original step defect on its selected numerical input has a
single finite stencil. Its unregraded group function annihilates all cleared
tests of the finite inversion integral, also on larger independent periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardOrbitStation
open Function Set Filter MeasureTheory Lattice Wilson RG Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato PertExtension.Orb
open WilsonOffsetEquationLaw WilsonMaxwellThermometerWardConditional
open scoped Classical Topology
variable {G:Gauge}

def field (R:Run G) {d:ℕ} (V:SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    (N:ℕ) (v:Label G d): Mark.Pre G :=
  ((R.family.S.a N:ℂ)^d)⁻¹ • V.evaluate ((R.family.labels.level d).coords (W d v))

theorem original (R:Run G) (V:∀d,SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    (P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ] R.family.label d)) (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (issued:Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∀d,∃r M:ℕ,∀N p (x:R.family.label d),∃v∈Maxwell.equationIdeal G d,
      (∀o:Site (R.family.side N p),
        incoming R.family (V d) N p (P d (N,p)) (x-b.step d (N,p) x) o =
        field R (V d) W N v ∘ expandAt o) ∧
      ∀ {n:Side}, Even n.val → M≤n.val → ∀o:Site n, 2*r+4<separation o (-o) →
        (∀ e:Edge (Site n), e.1∈(V d).footprint o → e.1+step e.2∈(V d).footprint o →
          far r o (reflect e)) →
        ∀{T:Set (Site n)} {K:Config G n→ℂ}, Continuous K → LocalOn T K →
        (∀e:Edge (Site n),e.1∈T→e.1+step e.2∈T→far r o e ∧ far r o (reflect e)) →
        ∀s:ℝ,s≠0→
          (∫q:OEdge n→G.El,(preDensity s (liftLinks q):ℂ)*
            (field R (V d) W N v (expandAt o (liftLinks q))*K (liftLinks q))
            ∂WilsonMaxwellThermometerWardConditional.law G)=0 := by
  intro d
  obtain ⟨r,M,empty⟩:=Mark.radiusH W (V d) (portfolio d)
  refine ⟨r,M,?_⟩
  intro N p x
  obtain ⟨v,hv,source⟩:=(issued.foundation.step d N p).id_sub x
  change bindP R.family W d N p (P d (N,p)) v=x-b.step d (N,p) x at source
  refine ⟨v,hv,fun o=>?_,?_⟩
  · rw [←source,evaluated]; rfl
  · intro n even cut o span clear T K hk localK room s hs
    apply WilsonMaxwellThermometerWardInversion.original even cut o span
      ((V d).continuous_evaluate _ |>.const_smul _) ((empty v hv).scale _) _ clear hk localK room s hs
    intro U X same
    exact congrArg (fun z:ℂ=>((R.family.S.a N:ℂ)^d)⁻¹ • z) ((V d).placed_local o _ U X same)

end YM.Integration.WilsonMaxwellThermometerWardOrbitStation
