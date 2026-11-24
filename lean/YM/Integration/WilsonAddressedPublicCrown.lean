import YM.Integration.WilsonAddressedAlignedColumn
import YM.Integration.WilsonAddressedPublicFineward
import YM.Integration.WilsonThermometerReflectedRoster
import YM.Integration.WilsonThermometerMarchSource

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedPublicCrown
open Function Filter Finset Set Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonOriginalMicroscopicGuardedNomination WilsonPositionProgramBlockedPublicExperiment
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {d k N p : ℕ} {f : Extraction.Order} {S : Table R.family.book}
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "T₀" => (C₀).factory d N p

theorem salary (payer : Final C₀ f S) (r B : ℝ) (v : S.Field d) (x : (C₀).label d)
    (opened : Opened C₀ d k p) (hk : k ≤ N)
    (V : Sight C₀ d p) (u : Emblems C₀ d)
    (raw : Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p d (digits R N p 0) V u)
    (ref : ∀e≤d, (C₀).ref e ≤ N)
    (paid : (F₀).coeffSize (deposited R d N p k x).x ≤ budget R payer d r k B v) :
    charge (offer R x opened hk) ≤ max 1 (2*(B*GapsContact.Ascent.cost payer d r v)) := by
  have recorded := (WilsonAddressedAlignedColumn.original R raw hk le_rfl ref opened x).2
  have ap := pow_pos ((C₀).S.a_pos k) d
  change (F₀).coeffSize (deposited R d N p k x).x ≤ ((C₀).S.a k)^d*B*_ at paid
  have exactCost : (F₀).coeffSize (Price.awake C₀ d k N p x) =
      (((C₀).S.a k)^d)⁻¹ * (F₀).coeffSize (deposited R d N p k x).x := by
    rw [Price.awake,Extra.Histories.Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg ((C₀).S.a_pos _).le]
    rfl
  rw [exactCost] at recorded
  have cancel := mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr ap.le)
  rw [mul_assoc (((C₀).S.a k)^d),←mul_assoc,inv_mul_cancel₀ ap.ne',one_mul] at cancel
  exact max_le_max_left _ (recorded.trans (mul_le_mul_of_nonneg_left cancel zero_le_two))

theorem arm {I : Type} (d : I → ℕ) (x : (i : I) → (C₀).label (d i))
    (V : (i : I) → Sight C₀ (d i) p) (u : (i : I) → Emblems C₀ (d i))
    (est : ∀i, Opened C₀ (d i) k p) (hk : k ≤ N)
    (raw : ∀ i, Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p (d i)
      (digits R N p 0) (V i) (u i)) (ref : ∀i e, e ≤ d i → (C₀).ref e ≤ N)
    (c : I → Site ((C₀).side k p)) (i : I) :
    let y := fun a => offer R (x a) (est a) hk
    let b := WilsonThermometerReflectedTrajectory.anchorAt R (c i) N
    WilsonThermometerReflectedRoster.source R d (fun _ => 0) (fun _ => (1,false)) c
      (fun a => reduce (y a)) u hk i =
      ((charge (y i):ℝ):ℂ)⁻¹ • (C₀).O N p (x i) b := by
  intro y b
  let α : ℂ := ((C₀).S.a k:ℂ)^(d i)
  let χ : ℂ := ((charge (y i):ℝ):ℂ)⁻¹
  let T := (C₀).factory (d i) N p
  let w := T.terminal (finer (u i) hk (y i) (primaryLetter (d i)))
  have point : α • w = x i := (WilsonAddressedAlignedColumn.original R (raw i) hk le_rfl
    (ref i) (est i) (x i)).1
  have head : T.terminal (finer (u i) hk (reduce (y i)) (primaryLetter (d i))) = χ • w := by
    rw [reduce,map_smul,Pi.smul_apply];exact T.terminal.map_smul _ _
  have birth : WilsonThermometerIntrinsicRoster.source R d (fun _ => 0) (fun a => reduce (y a)) u hk i =
      χ • (C₀).O N p (x i) 0 := by
    unfold WilsonThermometerIntrinsicRoster.source WilsonThermometerOwnOffsetNectar.birth
    rw [head,←point,((C₀).linearO N p (d i) 0).map_smul,((C₀).linearO N p (d i) 0).map_smul,smul_comm]
  rw [WilsonThermometerReflectedRoster.source,birth]
  funext W
  unfold stepUp
  dsimp only
  rw [pull_one]
  change χ*((C₀).O N p (x i) 0 (translate b W)) = χ*((C₀).O N p (x i) b W)
  rw [(C₀).translation,zero_add]

end YM.Integration.WilsonAddressedPublicCrown
end
