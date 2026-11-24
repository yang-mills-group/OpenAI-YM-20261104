import YM.Integration.WilsonAddressedWeakSeparation
import YM.Integration.WilsonAddressedWeakNormalization
import YM.Integration.WilsonThermometerReflectedRoster

/-! One finite-cutoff preparation for the displacement-dependent two-probe
Gram. Every reflected cell uses the same two preselected trajectories. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakDetectorCourse
open Function Filter Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Next.Rank Edition Baler Value Glyph Thirst Alarm
open Trace.Physical Table Spec Extraction XSpace
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetNectar
open WilsonThermometerReflectedTrajectory WilsonAddressedWeakPointCells
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {k N p : ℕ}
local notation "C" => R.family
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "L" => R.family.path.levels

theorem translated (live : k ≤ N) (z : Fin 2 → Site ((C).side N p)) (s : Motion) (c : Site ((C).side k p))
    (i j : Fin 2) :
    separation (WilsonThermometerReflectedTrajectory.point R (z i) s c k) (WilsonThermometerReflectedTrajectory.point R (z j) s c k) =
    separation (((C).S.toDepth live p).parent (z i)) (((C).S.toDepth live p).parent (z j)) := by
  simp only [WilsonThermometerReflectedTrajectory.point,WilsonThermometerOwnOffsetNectar.location,dif_pos live,WilsonThermometerOwnOffsetTale.site,Lattice.affine,
    separation_translate,separation_signed]

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) (D : ℕ) :
    ∃ (t u : ℕ), D+3 ≤ t ∧ D+3 ≤ u ∧ ∀ᶠ k : ℕ in atTop, ∀ p N (live : k ≤ N)
      (d : Fin 2 → ℕ) (_ : ∀ i,d i ≤ D) (ρ : ℝ) (_ : 0 < ρ) (x : Points 2),
      (32+4*(((L).budget k).B^2:ℕ))*((C).S.a k/ρ) < dist (x 0) (x 1) →
      2*(dist (x 0) (x 1)+32*((C).S.a k/ρ)) < ((C).side k p : ℝ)*((C).S.a k/ρ) →
      let z := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
      ∃ (V : (i:Fin 2) → Sight C (d i) p) (r : (i:Fin 2) → Emblems C (d i)),
        (∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i)) ∧
        ∀ (Y : (i:Fin 2) → Palette C (d i)),
          let v := fun i => WilsonAddressedWeakNormalization.unit R (Y i)
          WilsonThermometerIntrinsicRoster.filed R d z v V r (Stock.census (Fin 2)) live t ∧
          (∀ (s:Motion) (c:Site ((C).side k p)),
            WilsonThermometerReflectedRoster.filed R d z (fun _=>s) (fun _=>c) v V r
              (Stock.census (Fin 2)) live u) ∧
          ∀ face : (Stock.census (Fin 2)).Mode,reading R d z Y r live face =
              (∏ i ∈ face.val,(WilsonAddressedWeakNormalization.weight R (Y i):ℂ)) *
              reading R d z v r live face := by
  obtain ⟨t,dt,base⟩ := WilsonThermometerIntrinsicRoster.original R simple shop D
  obtain ⟨u,du,copies⟩ := WilsonThermometerReflectedRoster.original R simple shop D
  refine ⟨t,u,dt,du,?_⟩
  filter_upwards [base,copies] with k straight other
  intro p N live d hd ρ hr x apart within
  let z := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
  have distance := WilsonAddressedWeakSeparation.original R (p:=p) live ρ hr x (((L).budget k).B^2) apart within
  have room (i j : Fin 2) (diff : i ≠ j) : ((L).budget k).B^2 <
      separation (((C).S.toDepth live p).parent (z i)) (((C).S.toDepth live p).parent (z j)) := by
    fin_cases i <;> fin_cases j
    · exact (diff rfl).elim
    · exact distance
    · rw [separation_comm];exact distance
    · exact (diff rfl).elim
  have native (i j : Fin 2) (diff : i ≠ j) : ((L).budget k).B^2 <
      separation (WilsonThermometerOwnOffsetJoint.origins R z k i)
        (WilsonThermometerOwnOffsetJoint.origins R z k j) := by
    simpa only [WilsonThermometerOwnOffsetJoint.origins,WilsonThermometerOwnOffsetNectar.location,dif_pos live,WilsonThermometerOwnOffsetTale.site] using room i j diff
  obtain ⟨V,r,H,well⟩ := straight p N live (Fin 2) d hd z native
  refine ⟨V,r,H,?_⟩
  intro Y
  let v := fun i => WilsonAddressedWeakNormalization.unit R (Y i)
  have cap (i : Fin 2) := WilsonAddressedWeakNormalization.allowed R (Y i)
  refine ⟨well _ v cap,?_,WilsonAddressedWeakNormalization.charged R d z Y r live⟩
  intro s c
  apply other p N live (Fin 2) d hd z V r H (fun _=>s) (fun _=>c) _ (Stock.census _) v cap
  intro i j diff
  rw [translated R live]
  exact room i j diff

end YM.Integration.WilsonAddressedWeakDetectorCourse
