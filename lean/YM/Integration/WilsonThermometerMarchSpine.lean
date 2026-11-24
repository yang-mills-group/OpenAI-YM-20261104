import YM.Integration.WilsonThermometerMarchReference
import YM.Integration.WilsonThermometerOwnOffsetColumn
import YM.Next.RANK.StationMeter

/-! Transport of the surviving, independently displaced arms on the actual normalized child history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchSpine
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open Labels Source Bid Cells Push FullVolume MergeProof Next.Extract Extra.Histories XSpace.Rose MergeProof.East
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open scoped Topology Classical BigOperators
open private exp_bills from YM.Next.RANK.StationMeter
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {H : (Bel C.book).Hierarchy}

theorem span (simple : G.Simple) : ∀ᶠ k : ℕ in atTop,
    ∀ {d} (V : Vane C d), V.k=k → V.checked f H d → C.S.scale k ≤ 2*(-Real.log V.wheel.r) := by
  let L:=C.path.levels
  filter_upwards [exp_bills L 1,WilsonPositionOriginalDiagnosticCorridor.upper L simple
    (show 0<(1/2:ℝ) by norm_num)] with k currency high d V seat checked
  subst k
  have βpos : 0<L.clock.hatBeta V.k := zero_lt_one.trans (L.fits.delayed V.k)
  have cap : L.clock.hatBeta V.k ≤ Real.exp (C.S.scale V.k) := by simpa only [one_mul] using currency
  have βlog : Real.log (L.clock.hatBeta V.k) ≤ C.S.scale V.k := by
    simpa only [Real.log_exp] using Real.log_le_log βpos cap
  have magpos : 0<Next.Rank.Station.mag L V.b V.k := Next.Rank.Station.mag_pos ..
  have ml:=Real.log_le_log magpos (high V.b checked.high.2)
  rw [Real.log_rpow βpos] at ml
  change C.S.scale V.k ≤ 2*(-Real.log (C.S.a V.k*Next.Rank.Station.mag L V.b V.k))
  rw [Real.log_mul (C.S.a_pos V.k).ne' magpos.ne']
  have hs : C.S.scale V.k = -Real.log (C.S.a V.k) := Real.log_inv _
  linarith only [hs,ml,βlog]

variable {R : Run G} {T : Table R.family.book}
variable (F : Final R.family f T) (J : ℝ → tower T) (V : Store G) {H : (Bel R.family.book).Hierarchy}
    {l : Ultrafilter (ℕ × ℕ)} (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)

theorem original (simple : G.Simple) (paid : Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J)
    (η : ℝ) (positive : 0<η) : ∀ᶠ k₀ : ℕ in atTop, ∀ᶠ r in trail,
    let Z:=adjusted F J V A r
    ∀ N p, Z.station.k<N → ∀ (s : Badge) (i : Fin 3) (z : Site (R.family.side N p))
      (B : ℕ → ℕ → ℝ) (X : Sight R.family (grade i) p) (Q : Emblems R.family (grade i)),
      Enrolled R.makes R.doors B k₀ N p (grade i) (digits R N p z) X Q →
      ∀ {k : ℕ} (start : k₀ ≤ k) (_close : k ≤ Z.station.k) (y : Palette R.family (grade i))
        (M : ℝ), 0≤M → size y ≤ M * (R.family.labels.level (grade i)).coeffSize
          (Z.station.wheel.atCut (N,p) (index Z (grade i)) (vector Z s i)) →
        (∀ h : k≤N, finer Q h (finer Q start y)=finer Q (start.trans h) y) ∧
        size (finer Q start y) ≤ M * WilsonThermometerMarchReference.fee R.family s i *
          Real.exp (η*(-Real.log r)) := by
  have quarter : 0<η/4 := by positivity
  have go : Tendsto (fun r=>(adjusted F J V A r).station.k) trail atTop :=
    tendsto_atTop.mpr fun m=>(paid m).mono fun _ c=>c.1
  filter_upwards [string_paid (C:=R.family) quarter] with k₀ strings
  filter_upwards [paid k₀,go.eventually (span (f:=f) (H:=H) simple),
    WilsonThermometerMarchReference.original F J V A simple paid lead (η/2) (half_pos positive)]
    with r booked clock quoted
  dsimp only
  let Z:=adjusted F J V A r
  intro N p top s i z B X Q record k start close y M M0 small
  have cap:=clock Z.station rfl booked.2.1
  have radius : Z.station.wheel.r=r := booked.2.2.1
  rw [radius] at cap
  have mono : Monotone R.family.S.scale := monotone_nat_of_le_succ fun n=>by
    rw [R.family.S.scale_succ]
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (R.family.S.block n).property))
  have room : R.family.S.scale k-R.family.S.scale k₀ ≤ 2*(-Real.log r) :=
    (sub_le_self _ (RG.Shoot.scale_nn R.family.path.levels k₀)).trans ((mono close).trans cap)
  have bounded:= (record.inverse le_rfl start (close.trans top.le) y).trans
    (mul_le_mul_of_nonneg_right (strings k start) (size_ge y))
  have stamp := quoted N p top s i
  have one := small.trans (mul_le_mul_of_nonneg_left stamp M0)
  refine ⟨fun h=>by rw [Many.sumwalk Q start h]; rfl, bounded.trans ?_⟩
  have half : Real.exp ((η/4)*(R.family.S.scale k-R.family.S.scale k₀)) ≤
      Real.exp ((η/2)*(-Real.log r)) := by
    rw [Real.exp_le_exp]
    nlinarith only [mul_le_mul_of_nonneg_left room quarter.le]
  calc
    _ ≤ Real.exp ((η/2)*(-Real.log r)) * (M *
        (Real.exp ((η/2)*(-Real.log r))*WilsonThermometerMarchReference.fee R.family s i)) :=
      mul_le_mul half one (size_ge y) (Real.exp_pos _).le
    _ = M * WilsonThermometerMarchReference.fee R.family s i *
        (Real.exp ((η/2)*(-Real.log r))*Real.exp ((η/2)*(-Real.log r))) := by ring
    _ = _ := by rw [←Real.exp_add]; congr 2; ring

end YM.Integration.WilsonThermometerMarchSpine
