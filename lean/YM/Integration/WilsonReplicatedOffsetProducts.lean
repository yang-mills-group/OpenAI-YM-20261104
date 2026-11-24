import YM.Integration.WilsonReplicatedEquationLaw
import YM.Push.GRID_APPROXIMATION.Joint

/-! The two replicated signed Wilson products have equal expectations on the
same torus and hence equal chessboard root tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReplicatedOffsetProducts
open Function Set Filter MeasureTheory Lattice Cells Wilson RG Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato WilsonOffsetEquationLaw
open WilsonOffsetReportingProducts
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side}

private theorem continuous_copy (T : Tiling n) (i : T.Cell) {Y : Config G n → ℂ}
    (h : Continuous Y) : Continuous (T.copy i Y) := by
  have hp := h.comp (continuous_pull (T.omega i) (T.translateBy i))
  change Continuous (fun U => if T.hand i then star (Y (pull (T.omega i) (T.translateBy i) U))
    else Y (pull (T.omega i) (T.translateBy i) U))
  by_cases rev : T.hand i
  · simpa only [if_pos rev,Function.comp_def] using hp.star
  · simpa only [if_neg rev,Function.comp_def] using hp

private theorem local_copy (T : Tiling n) (i : T.Cell) {Y : Config G n → ℂ}
    {K L : Set (Site n)} (h : LocalOn K Y) (maps : MapsTo (T.copyMap i) K L) :
    LocalOn L (T.copy i Y) := by
  have hp := Mark.MicroAt.turn_local h (T.omega i) (T.translateBy i) maps
  intro U U' same
  unfold Tiling.copy
  split <;> first | exact congrArg star (hp U U' same) | exact hp U U' same

private theorem copies {I : Type} [Fintype I] (T : Tiling n) (A : I → Config G n → ℂ)
    (U : Config G n) :
    (∏ t:T.Cell, T.copy t (fun Z => ∏ i, A i Z) U) =
      ∏ t:T.Cell×I, T.copy t.1 (A t.2) U := by
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro t _
  unfold Tiling.copy
  split_ifs <;> simp only [star_prod]

def AvoidsCopies {C : Family G} (V : ∀ d, SectionData (C.labels.level d)) (radius : ℕ → ℕ)
    {I : Type} (d : I → ℕ) {N p : ℕ} (T : Tiling (C.side N p))
    (o : I → Site (C.side N p)) : Prop :=
  ∀ a b : T.Cell×I, a ≠ b →
      MapsTo (T.copyMap b.1) ((C.localSection (d b.2)).footprint (o b.2))
        (Mark.Outer (radius (d a.2)) (T.copyMap a.1 (o a.2))) ∧
      MapsTo (T.copyMap b.1) ((V (d b.2)).footprint (o b.2))
        (Mark.Outer (radius (d a.2)) (T.copyMap a.1 (o a.2)))

theorem on_issued (R : Run G) (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
    (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d))
    (b : Presentation R.family) (funded : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (data : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∃ radius : ℕ → ℕ, ∀ (I : Type) [Fintype I] (d : I → ℕ), ∀ᶠ N : ℕ in atTop,
      ∀ (p : ℕ) (x : (i : I) → R.family.label (d i))
        (o : I → Site (R.family.side N p)) (T : Tiling (R.family.side N p)),
        AvoidsCopies V radius d T o →
        T.rootTest (R.family.beta N p) (fun U => ∏ i, R.family.O N p (x i) (o i) U) =
        T.rootTest (R.family.beta N p) (fun U => ∏ i,
          corrected R.family (V (d i)) N p (P (d i) (N,p)) b (x i) (o i) U) := by
  choose r quiet using WilsonReplicatedEquationLaw.on_issued R V W P b funded data
  refine ⟨r,fun I _ d => ?_⟩
  filter_upwards [eventually_all.mpr (fun i:I => quiet (d i))] with N null
  intro p x o T away
  let A i := R.family.O N p (x i) (o i)
  let D i := incoming R.family (V (d i)) N p (P (d i) (N,p))
    (x i-b.step (d i) (N,p) (x i)) (o i)
  let K (i:T.Cell×I) := Mark.Outer (r (d i.2)) (T.copyMap i.1 (o i.2))
  have tested := WilsonSignedEquationProducts.erase (R.family.beta N p) K
    (fun i => T.copy i.1 (A i.2)) (fun i => T.copy i.1 (D i.2))
    (fun i => continuous_copy T i.1 (R.family.continuousO ..))
    (fun i => continuous_copy T i.1 (incoming_continuous ..))
    (fun i j diff => ⟨local_copy T j.1 (R.family.localO N p (d j.2) (x j.2) (o j.2))
        (away i j diff).1,
      local_copy T j.1 (incoming_local (V (d j.2)) N p (P (d j.2) (N,p)) _ (o j.2))
        (away i j diff).2⟩)
    (fun i => null i.2 p (x i.2) (o i.2) T i.1)
    Finset.univ (fun _ => (1:ℂ)) (Mark.cont_envelope continuous_const) (fun _ _ _ _ _ => rfl)
  simp only [mul_one] at tested
  unfold Tiling.rootTest
  simp_rw [copies,restore,GridApprox.Joint.copy_sub]
  exact congrArg (fun z:ℂ => ‖z‖^(Fintype.card T.Cell:ℝ)⁻¹) tested

end YM.Integration.WilsonReplicatedOffsetProducts
