import YM.Integration.WilsonAddressedWeakTiling

/-! The actual offset fields on the original centered reflection array. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakTilingCourse
open Function Filter Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Table Spec Extraction XSpace
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open WilsonThermometerReflectedTrajectory WilsonAddressedWeakPointCells
open WilsonAddressedWeakCalibration
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {k N p : ℕ}
local notation "L" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

/-- These are the actual reflected bare fields used at every occupied cell, including conjugation. -/
theorem copied {χ:ℕ} (gr:χ≤k) (live:k≤N) (d:Fin 2→ℕ) (z:Fin 2→Site (R.family.side N p))
    (Y:(i:Fin 2)→Palette R.family (d i)) (r:(i:Fin 2)→Emblems R.family (d i))
    (j:Site (R.family.side χ p)) (i:Fin 2) (W:Config G (R.family.side N p)) :
    let T := Cells.center R.family.S p (gr.trans live) 0
    let g := R.family.S.toDepth gr p
    T.copy j (WilsonThermometerIntrinsicRoster.source R d z Y r live i) W =
      WilsonThermometerReflectedRoster.source R (fun a:T.Cell × Fin 2=>d a.2) (fun a=>z a.2)
        (fun a=>(T.omega a.1,decide (T.hand a.1))) (fun a=>g.embed a.1)
        (fun a:T.Cell × Fin 2=>Y a.2) (fun a=>r a.2) live (j,i) W :=
  WilsonAddressedWeakTiling.physical R gr live j _ W

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) (D : ℕ) :
    ∃ (t u : ℕ), D+3 ≤ t ∧ D+3 ≤ u ∧ ∀ᶠ k : ℕ in atTop, ∀ p N (live : k ≤ N)
      (d : Fin 2 → ℕ) (_ : ∀ i,d i ≤ D) (ρ : ℝ) (_ : 0 < ρ) (x : Points 2) (Q : ℕ),
      (32+4*(((L).budget k).B^2:ℕ))*(R.family.S.a k/ρ) < dist (x 0) (x 1) →
      2*(dist (x 0) (x 1)+32*(R.family.S.a k/ρ)) < (R.family.side k p : ℝ)*(R.family.S.a k/ρ) →
      (∀ i, ‖x i‖+16*(R.family.S.a k/ρ) ≤ (R.family.S.a k/ρ)*Q) →
      let z := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
      ∃ (V : (i:Fin 2) → Sight R.family (d i) p) (r : (i:Fin 2) → Emblems R.family (d i)),
        (∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i)) ∧
        ∀ (Y : (i:Fin 2) → Palette R.family (d i)),
          let v := fun i => WilsonAddressedWeakNormalization.unit R (Y i)
          WilsonThermometerIntrinsicRoster.filed R d z v V r (Stock.census (Fin 2)) live t ∧
          ∀ (χ:ℕ) (gr:χ≤k),
            let T := Cells.center R.family.S p (gr.trans live) 0
            let g := R.family.S.toDepth gr p
            ((L).budget k).B^2+2*Q<g.count.val →
            ∀ names : Census (Site (R.family.side χ p) × Fin 2),
            WilsonThermometerReflectedRoster.filed R (fun i : Site (R.family.side χ p) × Fin 2=>d i.2) (fun i=>z i.2)
              (fun i=>(T.omega i.1,decide (T.hand i.1))) (fun i=>g.embed i.1)
              (fun i : Site (R.family.side χ p) × Fin 2=>v i.2) (fun i=>V i.2) (fun i=>r i.2) names live u := by
  obtain ⟨t,u,dt,du,X⟩ := WilsonAddressedWeakReflectedArray.original R simple shop D
  refine ⟨t,u,dt,du,?_⟩
  filter_upwards [X] with k choices
  intro p N live d hd ρ hr x Q apart side fits
  obtain ⟨V,r,enrolled,replicas⟩ := choices p N live d hd ρ hr x Q apart side fits
  refine ⟨V,r,enrolled,?_⟩
  intro Y
  refine ⟨(replicas Y).1,?_⟩
  intro χ gr
  dsimp only
  intro spacing names
  let T := Cells.center R.family.S p (gr.trans live) 0
  let s : Site (R.family.side χ p) → Motion := fun j => (T.omega j,decide (T.hand j))
  let c : Site (R.family.side χ p) → Site (R.family.side k p) := (R.family.S.toDepth gr p).embed
  have sh (j l:Site (R.family.side χ p)) (h:j≠l) :
      ((L).budget k).B^2+2*Q < separation (anchorAt R (c j) k) (anchorAt R (c l) k) :=
    spacing.trans_le (WilsonAddressedWeakTiling.spacing R gr j l h)
  exact (replicas Y).2 (Site (R.family.side χ p)) s c sh names

end YM.Integration.WilsonAddressedWeakTilingCourse
