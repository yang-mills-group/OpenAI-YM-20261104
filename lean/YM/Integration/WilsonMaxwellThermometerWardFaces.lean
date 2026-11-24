import YM.Integration.WilsonMaxwellThermometerWardMasks

/-! All four faces containing the true upper equation in the (6,4,4)
thermometer. The other three faces are unrestricted. The two lower sections
are the original selected Wilson sections, on their individual translated
supports and with arbitrary measured numerical inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardFaces
open Function Filter Set MeasureTheory Lattice Wilson RG Labels Source Push Finset
open Next.Extract MergeProof PhysicalNext.Repeat.Legato PertExtension PertExtension.Orb
open WilsonOffsetEquationLaw WilsonMaxwellThermometerWardConditional WilsonMaxwellThermometerWardReflection
open WilsonMaxwellThermometerWardOrbitStation WilsonMaxwellThermometerWardPupil
open WilsonMaxwellThermometerWardOccupant WilsonMaxwellThermometerWardMasks
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem original (R:Run G) (V:∀d,SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    (P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ] R.family.label d)) (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (issued:Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) (simple:G.Simple) :
    ∃r M:ℕ,∀N p (x:R.family.label 6),∃v∈Maxwell.equationIdeal G 6,
      (∀o:Site (R.family.side N p),
        incoming R.family (V 6) N p (P 6 (N,p)) (x-b.step 6 (N,p) x) o =
          (V 6).places (currency R W N v) o) ∧
      ∀ {n:Side}, Even n.val → M≤n.val → ∀o:Site n, 2*r+4<separation o (-o) →
        (∀ e:Edge (Site n), e.1∈(V 6).footprint o → e.1+step e.2∈(V 6).footprint o →
          far r o (reflect e)) → ∀ z:Fin 2→Site n,
        (∀ e:Edge (Site n),e.1∈rooms R z→e.1+step e.2∈rooms R z→
          far r o e ∧ far r o (reflect e)) →
        ∀ (L:ℂ→L[ℝ]ℝ) (c:Fin 2→(R.family.labels.level 4).Coeff) (phase:Fin 2→(ℂ→L[ℝ]ℝ)),
        let a:=currency R W N v
        L (a 0)=0 ∧ ∀S:Finset (Fin 2),
          let K:=companion R c phase z S
          diagonalWith (tray G)
            (restrictedO (selected (V 6) a L o (next (F:=R.family.labels.level 6))*K)) (2+2*S.card)=0 ∧
          diagonalWith (tray G)
            (restrictedO (selected (V 6) a L o (later (F:=R.family.labels.level 6))*K)) (3+2*S.card)=0 := by
  obtain ⟨r,M,funded⟩:=WilsonMaxwellThermometerWardOccupant.original R V W P b portfolio issued simple 6
  refine ⟨r,M,?_⟩
  intro N p x
  obtain ⟨v,hv,literal,account⟩:=funded N p x
  refine ⟨v,hv,literal,?_⟩
  intro n even cut o away fine z clear L c β
  have receipt:=account even cut o away fine L
  refine ⟨receipt.1,?_⟩
  intro S
  dsimp only
  obtain ⟨hk,order,inside⟩:=WilsonMaxwellThermometerWardMasks.admitted R c β z S
  constructor
  · apply WilsonMaxwellThermometerWardCompanion.coefficient (V 6) (currency R W N v) L o
      (portfolio 6).valid (portfolio 6).pays even simple hk order
    exact receipt.2.2 hk.continuous inside clear
  · exact Orb.normalized_odd (traySpec G) even _ (show Odd (3+2*S.card) from ⟨1+S.card,by omega⟩)

end YM.Integration.WilsonMaxwellThermometerWardFaces
