import YM.Integration.WilsonOffsetReportingProducts

/-! Every signed chessboard copy of the selected Wilson equation cylinder is
silent at its actual reflected fine site, with the same microscopic radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReplicatedEquationLaw
open Function Set Filter MeasureTheory Lattice Cells Wilson RG Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato WilsonOffsetEquationLaw
open scoped Classical Topology BigOperators
variable {G : Gauge}

theorem copy_null {f : Mark.Pre G} {r M : ℕ} (null : Mark.MicroAt f r M)
    (cont : Continuous f) {n : Side} (hn : M ≤ n.val) (β : ℝ) (nonzero : β ≠ 0)
    (T : Tiling n) (i : T.Cell) (o : Site n) (X : Config G n → ℂ)
    (far : LocalOn (Mark.Outer r (T.copyMap i o)) X) (entry : Envelope X) :
    moment β (fun U => T.copy i (f ∘ expandAt o) U * X U) = 0 := by
  have turned := null.signed cont (T.omega i)
  by_cases rev : T.hand i
  · have hit := turned.conj n hn (T.copyMap i o) β nonzero X far entry
    simpa only [Tiling.copy,if_pos rev,Function.comp_apply,expandAt_pull,Tiling.copyMap,Pi.star_apply]
      using hit
  · have hit := turned n hn (T.copyMap i o) β nonzero X far entry
    simpa only [Tiling.copy,if_neg rev,Function.comp_apply,expandAt_pull,Tiling.copyMap] using hit

theorem on_issued (R : Run G) (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
    (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d))
    (b : Presentation R.family) (funded : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (data : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) (d : ℕ) :
    ∃ radius : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ) (x : R.family.label d)
      (o : Site (R.family.side N p)) (T : Tiling (R.family.side N p)) (i : T.Cell)
      (X : Config G (R.family.side N p) → ℂ), LocalOn (Mark.Outer radius (T.copyMap i o)) X →
      Envelope X → moment (R.family.beta N p) (fun U =>
        T.copy i (incoming R.family (V d) N p (P d (N,p)) (x - b.step d (N,p) x) o) U * X U) = 0 := by
  obtain ⟨r,M,erase⟩ := Mark.radiusH W (V d) (funded d)
  refine ⟨r,?_⟩
  filter_upwards [Mark.lengths R.family.S M] with N sizes
  intro p x o T i X far env
  obtain ⟨y,hy,raw⟩ := (data.foundation.step d N p).id_sub x
  change bindP R.family W d N p (P d (N,p)) y = x - b.step d (N,p) x at raw
  rw [← raw,evaluated]
  have positive : 0 < R.family.beta N p :=
    (half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed _))).trans_le
      ((R.makes.wilson.represents N p N le_rfl).band.1)
  exact copy_null ((erase y hy).scale (((R.family.S.a N:ℂ)^d)⁻¹))
    (continuous_const.smul ((V d).continuous_evaluate _)) (sizes p) _ positive.ne' T i o X far env

end YM.Integration.WilsonReplicatedEquationLaw
