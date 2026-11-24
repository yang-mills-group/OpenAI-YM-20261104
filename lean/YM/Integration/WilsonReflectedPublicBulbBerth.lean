import YM.Integration.WilsonReflectedPublicFlatBerth
import YM.Integration.WilsonReflectedPublicStationFare
import YM.Integration.WilsonPositionProgramPublicWideHearing

/-! The same reflected shape serves all finite physical Gram columns. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicBulbBerth
open Function Filter Set RG Wilson Source Spec Table Extraction PhysMS Lattice Labels Maxwell MS MS.Menus
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus Table.Pairing Local.Physical
open MeasureTheory Next.Rank Climb Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionProgramPublicReflectedRead
open WilsonThermometerUnitFilingFourSquare WilsonMeasuredPublicBank WilsonPositionProgramPublicStations
open WilsonInvariantActionPosition WilsonInvariantActionSeparatedCells
open scoped Classical Topology

variable {G:Gauge} (R:Run G) (axis:Axis)

def shape (b:Bulb (center axis) axis) : Test 2 :=
  let u:=b.tests (L:=R.family.book) (fun _=>⟨0,0⟩)
  withOther u u

variable {h:Extraction.Order} {S:Table R.family.book} (F:Final R.family h S)
    {l:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}

theorem fixedShape {I:Type} {d:ℕ} {x:I→S.Field d}
    (arm:(i:I)→Bool→Arm R.family S (l:Filter _) d (x i))
    (b:Bulb (center axis) axis)(i j:I):
    WilsonPositionProgramPublicWideHearing.profile arm axis b i j=shape R axis b:=rfl

theorem mesh {k:ℕ}(W:Vane R.family k)(ok:W.checked h H k):
    R.family.S.a W.k ≤ W.wheel.r:=by
  have mag:1 ≤ Next.Rank.Station.mag R.family.path.levels W.b W.k:=
    Real.one_le_rpow (RG12.Alidade.monitor_big R.family.path.levels W.k) (by linarith only [ok.high.1])
  exact le_mul_of_one_le_right (R.family.S.a_pos W.k).le mag

/-- The geometry comes from the single original W and the actual occupied
compact test. Neither array of microscopic positions needs to be captured on
the zero-residue subgrid. -/
theorem original (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    (b:Bulb (center axis) axis)(c:ℝ)(cp:0 ≤ c):
    ∃ floor:ℕ, ∀ᶠ t in trail, ∀(ht:0<t){D d k:ℕ}{s r B:ℝ}(stock:Bank F l D s B)
    (cap:d ≤ D) (W:Vane R.family k)(fits:D ≤ k)(T:Spin.change S d)
    (P:Pair F stock cap W fits T r), W.checked h H k → W.wheel.r=r → r ≤ t →
    let m:=max floor (max stock.j W.k)
    let f:=berth R 5 m
    m<f ∧ (R.family.path.levels.clock.hatBeta m)^5  ≤  R.family.S.a m / R.family.S.a f ∧
    R.family.S.a m / R.family.S.a f  ≤  (R.family.path.levels.clock.hatBeta m)^5*
      (R.family.path.levels.clock.hatBeta m)^(1:ℝ) ∧
    ∀N per (live:f ≤ N) (y:Fin 2→Site (R.family.side N per)) (I:Type)
      (v:I→S.Field d)(i j:I),
    WilsonExternalMeshMass.charge R.family (dilate ht (WilsonPositionProgramPublicWideHearing.profile
      (fun a w=>P.arm w (v a)) axis b i j)) y≠0 →
    c*(1+((R.family.path.levels.budget f).B:ℝ))^2  ≤  (gap R.family live y:ℝ):=by
  let φ:=shape R axis b
  obtain ⟨floor,pay⟩:=WilsonReflectedPublicFlatBerth.original R simple slow φ φ.hasCompactSupport φ.tsupport_subset (Subset.rfl) c cp
  refine ⟨floor,?_⟩
  filter_upwards [pay] with t earned
  intro ht D d k s r B stock cap W fits T P issued actual window m f
  have late:W.k ≤ m:=(le_max_right ..).trans (le_max_right ..)
  have begun:R.family.S.a m ≤ t:=(R.family.S.strictAnti.antitone late).trans ((mesh R W issued).trans (actual.le.trans window))
  obtain ⟨a,c₁,c₂,sites⟩:=earned ht m (le_max_left ..) begun
  exact ⟨a,c₁,c₂,fun N per live y I v i j => sites N per live y⟩

end YM.Integration.WilsonReflectedPublicBulbBerth
end
