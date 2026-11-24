import YM.Integration.WilsonMaxwellThermometerFirstDetector
import YM.Integration.WilsonPositionGradedThermometerGround
import YM.Integration.WilsonSeparatedOriginalThermometerDetectorMesh

/-! The first position coefficient on the same corrected reporting station as the
original Wilson three-field hearing. The physical pair of regulator indices is
removed before the reporting radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerFirstPosition
open Function Set Filter Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace
open XSpace.Normalize XSpace.Photo XSpace.Cirrus
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open WilsonSeparatedOriginalThermometerDetectorMesh
open scoped Topology Classical BigOperators

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) {V : Store G}
    {Y : Ultrafilter (ℕ × ℕ)} {H : (Bel R.family.book).Hierarchy}
    (A : ℝ → Group R.family 6)
local notation "A'" => WilsonPositionCorrectedCap.adjusted F J V A
local notation "P" => WilsonPositionPrescribedFrame.positioned F J V
local notation "tags" => WilsonPositionGradedThermometerGround.tags

/-- The filed upper vector has the original orientation, and the two lower
vectors are fitted on their own cap before raising them into the test. -/
theorem fitted (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J) (i : Fin 3) :
    Reads 6 (F:=trail) (fun r => tags (A' r) i) (Rose.tag G i) := by
  have paid := WilsonPositionCorrectedCap.original F J V A book lead
  have identity : localCost trail P P := fun d x => by simp
  have near (j : Fin 7) (v : (Bel R.family.book).Field j) :
      Tendsto (fun r => (A' r).change j v) trail (𝓝 v) := by
    simpa only [WilsonPositionCapTransport.through, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
      (WilsonPositionCapTransport.near P P A' paid identity j v)
  have rotated (j : Fin 7) (D : Sec G j →ₗ[ℂ] Sec G 6) (v : Sec G j) :
      Reads 6 (F:=trail) (fun r => D (WilsonPositionGradedThermometerGround.transform (A' r) j v)) (D v) := by
    let b := Maxwell.Free.fields R.family.labels j
    let L := (tableD G 6).toLinearMap ∘ₗ (D ∘ₗ b.toLinearMap).restrictScalars ℝ
    have endpoint : L (b.symm v) = tableD G 6 (D v) := by simp [L]
    change Tendsto (fun r => L ((A' r).change j (b.symm v))) trail (𝓝 (tableD G 6 (D v)))
    rw [← endpoint]
    exact L.continuous_of_finiteDimensional.continuousAt.tendsto.comp (near j (b.symm v))
  fin_cases i
  · exact rotated 6 LinearMap.id (Rose.toll G)
  · exact rotated 4 (up (by decide)) (lower G)
  · exact rotated 4 (up (by decide)) (lower G)

variable (K : Rose.Pick V) (W : Initialize G) (simple : G.Simple) (B : ℕ)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels simple B

def coefficient (r : ℝ) (z : ℕ × ℕ) : ℂ :=
  WilsonMaxwellThermometerFirstDetector.finite W K
    (chart R (m r) z.2 (spacing R simple B r) (positive R simple B r)) (tags (A' r))

theorem original (hB : 0<B) (prior : (Y : Filter _) ≤ f.fuse)
    (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J) :
    Tendsto (fun z : ℝ × (ℕ × ℕ) => coefficient F J A K W simple B z.1 z.2)
      (trail.curry (Y : Filter _)) (𝓝 ((Rose.c_T K : ℝ) : ℂ)) := by
  have geo := reporting R trail f (Y : Filter _) prior m _ (positive R simple B) (shrinking R simple B hB)
  have radius : Tendsto (Prod.fst : ℝ × (ℕ × ℕ) → ℝ) (trail.curry (Y : Filter _)) trail :=
    tendsto_fst.mono_left Filter.curry_le_prod
  exact WilsonMaxwellThermometerFirstDetector.moving W K _ geo _
    (fun i => (fitted F J A book lead i).comp radius) simple

end YM.Integration.WilsonMaxwellThermometerFirstPosition
end
