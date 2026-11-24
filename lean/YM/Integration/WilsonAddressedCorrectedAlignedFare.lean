import YM.Integration.WilsonAddressedAlignedStation
import YM.Integration.WilsonThermometerMarchReference

set_option autoImplicit false
/-! The actual three corrected physical coordinates and their common earlier reporting cost. -/

noncomputable section
namespace YM.Integration.WilsonAddressedCorrectedAlignedFare
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerReading
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {T : Table R.family.book}
variable (F : Final R.family f T) (P : ℝ → tower T) (V : Store G) {H : (Bel R.family.book).Hierarchy}
    {l : Ultrafilter (ℕ × ℕ)} (A : ℝ → Group R.family 6)


theorem original (simple:G.Simple) (paid:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P)
    (ε:ℝ) (positive:0<ε) :
    ∀ᶠ r in trail, let Z:=adjusted F P V A r
    ∀ (N p:ℕ), Z.station.k < N → ∀ (s:Badge) (i:Fin 3) (k:ℕ),
    R.family.ref (grade i) ≤ k → k ≤ Z.station.k →
    let x:=Z.station.wheel.atCut (N,p) (index Z (grade i)) (vector Z s i)
    (R.family.labels.level (grade i)).coeffSize (Next.Rank.Price.awake R.family (grade i) k N p x) ≤
       (R.family.S.a k / R.family.S.a Z.station.k) *
       ((R.family.path.levels.clock.hatBeta Z.station.k)^ε * WilsonThermometerMarchReference.fee R.family s i) := by
  let d : Badge × Fin 3 → Fin 7 := fun v=>grade v.2
  let v : ∀ j : Badge × Fin 3, (Bel R.family.book).Field (d j) := fun j=>source R.family j.1 j.2
  have book (n:ℕ):=WilsonPositionCorrectedCap.mixed F P V A paid lead d v n
  have go:Tendsto (fun r=>(adjusted F P V A r).station.k) trail atTop:=
    tendsto_atTop.mpr fun n=>(book n).mono fun _ h=>h.1
  have each(i:Fin 3):=WilsonAddressedAlignedStation.original (f:=f) (H:=H) R simple (grade i) ε positive
  filter_upwards [book 0,go.eventually (eventually_all.mpr each),
    go.eventually ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 0)]
    with r filed ready beta
  let Z:=adjusted F P V A r
  dsimp only
  intro N p upper s i k entered before
  have price:=ready i Z.station (index Z (grade i)) rfl rfl filed.2.1 (vector Z s i) k N p entered before upper
  have close:‖vector Z s i - source R.family s i‖ ≤ costHint 0:=filed.2.2.2.2.2 (s,i)
  have normBound:‖vector Z s i‖ ≤ ‖source R.family s i‖+costHint 0:=calc
    _ = ‖(vector Z s i-source R.family s i)+source R.family s i‖:=by rw [sub_add_cancel]
    _ ≤ ‖vector Z s i-source R.family s i‖+‖source R.family s i‖:=norm_add_le _ _
    _ ≤ _:=by linarith only [close]
  have localBound:WilsonPositionThermometerStationNorm.cost R.family (grade i) * ‖vector Z s i‖ ≤
      WilsonThermometerMarchReference.fee R.family s i:=by
    unfold WilsonThermometerMarchReference.fee
    apply mul_le_mul_of_nonneg_left normBound
    unfold WilsonPositionThermometerStationNorm.cost; positivity
  exact price.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left localBound (Real.rpow_nonneg beta _))
    (div_nonneg (R.family.S.a_pos k).le (R.family.S.a_pos Z.station.k).le))

end YM.Integration.WilsonAddressedCorrectedAlignedFare
end
