import YM.Integration.WilsonSignedEquationProducts

/-! Exact restoration of the original signed product at the physical fine
insertion sites. The canonical primary and the mismatch of the equation
cylinder are kept on every leg. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetReportingProducts
open Function Set Filter MeasureTheory Lattice Wilson RG Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato WilsonOffsetEquationLaw
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {d : ℕ}

def residual (C : Family G) {d : ℕ} (V : SectionData (C.labels.level d))
    (N p : ℕ) (P : C.label d ≃ₗ[ℂ] C.label d) (z : C.label d) (o : Site (C.side N p)) :=
  C.O N p z o - incoming C V N p P z o

def corrected (C : Family G) {d : ℕ} (V : SectionData (C.labels.level d)) (N p : ℕ)
    (P : C.label d ≃ₗ[ℂ] C.label d) (b : Presentation C) (x : C.label d)
    (o : Site (C.side N p)) :=
  C.O N p (b.step d (N,p) x) o + residual C V N p P (x - b.step d (N,p) x) o

theorem restore (V : SectionData (C.labels.level d)) (N p : ℕ)
    (P : C.label d ≃ₗ[ℂ] C.label d) (b : Presentation C) (x : C.label d)
    (o : Site (C.side N p)) :
    corrected C V N p P b x o =
      C.O N p x o - incoming C V N p P (x-b.step d (N,p) x) o := by
  have linear := ((C.linearO N p d o).mk' _).map_sub x (b.step d (N,p) x)
  change C.O N p (x - b.step d (N,p) x) o = _ at linear
  unfold corrected residual
  rw [linear]
  change C.O N p (b.step d (N,p) x) o +
    (C.O N p x o - C.O N p (b.step d (N,p) x) o - _) = _
  abel

theorem incoming_continuous (V : SectionData (C.labels.level d)) (N p : ℕ)
    (P : C.label d ≃ₗ[ℂ] C.label d) (x : C.label d) (o : Site (C.side N p)) :
    Continuous (incoming C V N p P x o) := by
  exact continuous_const.smul (V.continuous_places _ o)

theorem incoming_local (V : SectionData (C.labels.level d)) (N p : ℕ)
    (P : C.label d ≃ₗ[ℂ] C.label d) (x : C.label d) (o : Site (C.side N p)) :
    LocalOn (V.footprint o) (incoming C V N p P x o) := by
  intro U U' ht
  exact congrArg (fun z : ℂ => ((C.S.a N:ℂ)^d)⁻¹ • z) (V.placed_local o _ U U' ht)

def Avoids (V : ∀ d, SectionData (C.labels.level d)) (radius : ℕ → ℕ)
    {I : Type} (d : I → ℕ) {N p : ℕ} (o : I → Site (C.side N p)) : Prop :=
  ∀ i j, i ≠ j →
      (↑((C.localSection (d j)).footprint (o j)) : Set (Site (C.side N p))) ⊆
        Mark.Outer (radius (d i)) (o i) ∧
      (↑((V (d j)).footprint (o j)) : Set (Site (C.side N p))) ⊆
        Mark.Outer (radius (d i)) (o i)

theorem purchased (R : Run G) (hG : G.Simple) :
    ∃ (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
      (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d))
      (b : Presentation R.family) (radius : ℕ → ℕ),
      (∀ d, Mark.Portfolio R.family.params (V d) (W d)) ∧
      Hearthside R.family V W P b (Bandage.fly R.alloy.B.a) ∧
      ∀ (I : Type) [Fintype I] (d : I → ℕ), ∀ᶠ N : ℕ in atTop,
        ∀ (p : ℕ) (x : (i : I) → R.family.label (d i)) (o : I → Site (R.family.side N p))
        (X : Config G (R.family.side N p) → ℂ), Avoids V radius d o →
        (∀ i, LocalOn (Mark.Outer (radius (d i)) (o i)) X) → Envelope X →
        moment (R.family.beta N p) (fun U => (∏ i, R.family.O N p (x i) (o i) U) * X U) =
        moment (R.family.beta N p) (fun U =>
          (∏ i, corrected R.family (V (d i)) N p (P (d i) (N,p)) b (x i) (o i) U) * X U) := by
  obtain ⟨V,W,P,b,v,record,zero⟩ := WilsonOffsetEquationLaw.selected R hG
  choose radius null using zero
  refine ⟨V,W,P,b,radius,v,record,fun I _ d => ?_⟩
  filter_upwards [eventually_all.mpr (fun i:I => null (d i))] with N star
  intro p x o X separated localX bounded
  let A i := R.family.O N p (x i) (o i)
  let D i := incoming R.family (V (d i)) N p (P (d i) (N,p)) (x i-b.step (d i) (N,p) (x i)) (o i)
  have result := WilsonSignedEquationProducts.erase (R.family.beta N p)
    (fun i => Mark.Outer (radius (d i)) (o i)) A D
    (fun i => R.family.continuousO N p (d i) (x i) (o i))
    (fun i => incoming_continuous ..)
    (fun i j h => ⟨fun U Z agreed => R.family.localO N p (d j) (x j) (o j) U Z
        (agrees_mono agreed (separated i j h).1),
      fun U Z agreed => incoming_local _ _ _ _ _ _ U Z (agrees_mono agreed (separated i j h).2)⟩)
    (fun i X => star i p (x i) (o i) X) Finset.univ X bounded (fun i _ => localX i)
  simp_rw [restore]
  exact result

end YM.Integration.WilsonOffsetReportingProducts
