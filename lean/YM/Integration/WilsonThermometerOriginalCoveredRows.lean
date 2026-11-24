import YM.Integration.WilsonThermometerOriginalCoveredSlope

/-! The signed zeroth and first lower coefficients of the original deposited source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalCoveredRows
open Function MeasureTheory Lattice RG Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Assembly Comparison.RG02.Order YM.Next.SectorChange YM.Primitives.GCC.Anchor
open WilsonThermometerVertexVariation
open scoped Classical BigOperators

variable {G:Gauge} {c f:Side} {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
  {S:StepData c f} {clip:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S clip P O) (F:Forest S.ratio) (t:S.Choices) (X:Bulk.Colors R G f)
  (angle:fieldDir G c 1)

local notation "u" z:max => Bulk.translated K F angle z
local notation "heads" j:max z:max => vertex X.power (Bulk.markFn S F X) (u z) j
local notation "μ" => Gaussian.cloud (K.covariance F t)

/-- The genuine conditional zero face is integrated on the same shifted lower marginal. -/
def base : Poly R := Poly.inject fun s=>∫ z,(Poly.pass (heads 0 z)).part s ∂μ

/-- The first source derivative and minus the entire classical cubic action score before normalization. -/
def first : Poly R := Poly.inject fun s=>∫ z,
  ((variation (heads 0 z) (heads 1 z)) + Poly.bead R (-(↑(jet (Bulk.geometric K F t X) 3 (u z):ℝ):ℂ))
    *Poly.pass (heads 0 z)).part s ∂μ

private theorem view (p:ℕ) (s:R.Mode) (j:ℕ) (hp:j≤p) :
    (observe R p (Bulk.Fk K F t X angle p) j).part s=
     ∫ z, rows (expansions X.power (Bulk.markFn S F X) (Bulk.geometric K F t X)) s j (u z) ∂μ := by
  have h:=observed (x:=Bulk.Fk K F t X angle p) s hp
  rw [Bulk.table,picked p hp] at h
  exact mul_left_cancel₀ (by exact_mod_cast (Nat.factorial_pos j).ne' : (j.factorial:ℂ)≠0) h

theorem joint (p:ℕ) (live:0<p) :
    First.buc (Bulk.Fk K F t X angle p)=base K F t X angle ∧
    First.ind (Bulk.Fk K F t X angle p)=first K F t X angle := by
  constructor
  · ext1 s
    rw [First.buc,view K F t X angle p s 0 (Nat.zero_le p)]
    unfold base
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    exact congrArg (fun a:Poly R=>a.part s) (WilsonThermometerVertexVariation.leading X.power
      (Bulk.markFn S F X) (Bulk.geometric K F t X) (u z))
  · ext1 s
    rw [First.ind,view K F t X angle p s 1 live]
    unfold first
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    exact congrArg (fun a:Poly R=>a.part s) (WilsonThermometerVertexVariation.first X.power
      (Bulk.markFn S F X) (Bulk.geometric K F t X) (u z))

/-- Entries include the quiet derivative, proper marked subsets and previously deposited mixed modes. -/
theorem signed (p:ℕ) (live:0<p) :
    First.buc (logMarked (Bulk.Fk K F t X angle p))=Extra.Trajectories.connected (base K F t X angle) ∧
    First.ind (logMarked (Bulk.Fk K F t X angle p))=
      first K F t X angle * inverseMass (base K F t X angle) -
        Poly.bead R ((first K F t X angle).part R.quiet) := by
  obtain ⟨b,d⟩:=joint K F t X angle p live
  rw [Cumulants.orphan (Bulk.fk_sym ..) (Bulk.fk_unit ..),
    First.first_log live (Bulk.fk_sym ..) (Bulk.fk_unit ..),b,d]
  exact ⟨rfl,rfl⟩

end YM.Integration.WilsonThermometerOriginalCoveredRows
