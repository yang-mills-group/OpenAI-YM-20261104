import YM.Integration.WilsonThermometerMarchNomination

/-! All displaced proper and full Vane faces in the same numerical moving
marked aperture, chosen before the upper cutoff and the reporting period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchEnrollment
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open RG.Shoot Marker PhysicalNext.Repeat.Legato RG05Readout Native Address Many RG05Readout.Records
open RG17 Trace.Pilot Climb Table Spec WilsonPositionThermometerCapStation
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource
open WilsonThermometerMarchNomination WilsonThermometerMarchSource WilsonThermometerOffsetTrajectory
open WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetNectar MergeProof FVA1 OriginalForcedAddresses
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "d" => (fun i : Fin 3 => (grade i).val)
local notation "J" => Stock.census (Fin 3)
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "β" => R.family.path.levels.clock.hatBeta

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) :
    ∃ t ≥ 9, ∀ᶠ m : ℕ in atTop, ∀ p N (hm : m ≤ N) (o : Positions (Fin 3) (R.family.side N p)),
      (∀ i i' : Fin 3, i ≠ i' → (R.family.path.levels.budget m).B^2 <
        separation (WilsonThermometerOwnOffsetJoint.origins R o.origin m i)
          (WilsonThermometerOwnOffsetJoint.origins R o.origin m i')) →
      ∃ (V : (i : Fin 3) → Sight R.family (d i) p) (r : (i : Fin 3) → Emblems R.family (d i)),
        (∀ i, Enrolled R.makes R.doors B m N p (d i) (digits R N p (o.origin i)) (V i) (r i)) ∧
        (∀ b ≥ m, ∀ s : (Stock.census (Fin 3)).Mode, WilsonThermometerMarchFaces.inverse R t m b s ≤
          β b ^ (3*(t+1)*(b-m+1))) ∧
        ∀ A : Group R.family 6,
          WilsonThermometerIntrinsicRoster.filed R d o.origin (prepared R A (p:=p) r hm) V r J hm t ∧
          ∀ b (hb : b ≤ N) (s : (Stock.census (Fin 3)).Mode),
          (fun U => (WilsonThermometerIntrinsicRoster.density R d o.origin (prepared R A (p:=p) r hm)
            r J hm hb U).part s) = (∏ i ∈ s.val,weight R A (p:=p) r hm i) •
            (fun U => (WilsonThermometerCourseIntake.incoming R A simple hb o U).part s) := by
  obtain ⟨t, ht, gates⟩ := WilsonThermometerMarchRoster.original R simple shop
  refine ⟨t, ht, ?_⟩
  have ages : ∀ᶠ m : ℕ in atTop, ∀ i : Fin 3, R.family.ref (d i) ≤ m :=
    Filter.eventually_all.mpr (fun i => eventually_ge_atTop (R.family.ref (d i)))
  filter_upwards [gates,ages] with m issue start
  intro p N hm o cleared
  obtain ⟨V,r,good,book,prices⟩ := issue p N hm o.origin cleared
  refine ⟨V,r,good,prices,?_⟩
  intro A
  have posted := book (prepared R A (p:=p) r hm) (fun i => small _)
  refine ⟨posted,?_⟩
  intro b hb s
  exact reads R A simple r hm o (fun i => (start i).trans hm) (posted N hm le_rfl).1 s hb

end YM.Integration.WilsonThermometerMarchEnrollment
