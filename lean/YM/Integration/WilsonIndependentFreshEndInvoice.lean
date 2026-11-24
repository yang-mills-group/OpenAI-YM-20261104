import YM.Integration.WilsonIndependentFreshQuietEnding
import YM.Integration.WilsonIndependentFreshFoldedHaar
import YM.Integration.WilsonIndependentFreshAppointment

/-! The authentic bounded inversion terminal, after a compound source is
inserted on the previously evolved independent vacuum. The original
finite determinant, Gaussian, Haar, and winding expenditures share one election. -/
noncomputable section
namespace YM.Integration.WilsonIndependentFreshEndInvoice
open Lattice RG RegulatorIR RegulatorIR.Budget RegulatorIR.Spatial RegulatorIR.Uniform
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Calibration RegulatorIR.Profiles RegulatorIR.Taping
open RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Halo RegulatorIR.FVAAlt2
open scoped ENNReal Classical
variable {G : Gauge} {W : Type} {j : W → ℕ} {n : Page j → Side}
variable (S : Circuit j n) {K : KernelChoices} (Y : Oracle.Program K)
variable (branch : ∀ patch : Patch, patch.Branches K G) {color : G.ColorIndex}
variable {L : Meter W} {base capture stop : Choice j} {budget : Marked j}
variable {p m offset e moments : ℕ} {F : Tent j} {γ : ℝ}
local notation "world" => S.dialect Y G branch (sheet F)
local notation "quiet" => S.payroll Y G branch (sheet F)


theorem original (simple : G.Simple) (grade : quantum 1 0 ≤ moments)
    (book : SatisfiesQ G Y S branch budget p moments γ)
    (notebook : Notebook S Y G branch color base F p)
    (atBase : ∀ w, budget.peak (base.choose w) = 0)
    (mesh : ∀ w, S.l (base.choose w) = 1) (age : OfAge budget L)
    (endSide : ℕ) (bounded : ∀ w, (n (Page.finallyW j w)).val ≤ endSide) :
    ∃ seed : (world).Primitive L p (quantum 1 0),
    ∀ (m offset : ℕ) (capture stop : Choice j)
      (Z : (capture.after.part (world) (quiet) seed).Report m)
      (portrait : W → Portrait G),
      (∀ w, BasisT m offset (portrait w) (Z.main (Page.opening capture.after.spans w))) →
      ∀ (root : W → Room), (world).cushion (1/8) root →
      ∀ (gross : W → ℝ≥0∞), (∀ w, gross w ≠ ⊤) →
      (∀ i, i ≤ p → ∀ r, 0 < r → Claim L
        (fun w => (world).coverQ root 2 (capture.choose w)) gross
        (fun w => Z.main (Page.opening capture.after.spans w) i r)) →
      base.age ≤ capture.age → capture.age ≤ stop.age → ∀ e, e ≤ p →
      Carry L (fun w => gross w * ENNReal.ofReal ((S.l (capture.choose w) / S.l (stop.choose w))^γ))
        (fun w => ‖(capture.after.expanse (world)).vista (capture.after.part (world) (quiet) seed) Z
          (WilsonIndependentFreshReel.margins (S.lane Y G branch (sheet F)) capture.after) w e -
          note (Z.main (Page.finallyW capture.after.spans w) e 0)‖ₑ) := by
  obtain ⟨enrolled,lamp⟩ := Atlas.reservations S G Y branch atBase age book color notebook simple mesh
  let paid := enrolled.emits (b := 1) (u := 0) (by norm_num) grade
  let light := paid.leads lamp
  let R := S.lane Y G branch (sheet F)
  let old : (quiet).Report 0 := declaring (quiet) (fun _ => 0) (fun _ _ _ h => (h rfl).elim)
  have native := paid.splines old (fun _ => 0) (fun _ => WilsonIndependentFreshQuietReel.priorZero G) lamp
  have endAt := Atlas.closures S G Y branch age book endSide bounded F
  refine ⟨paid.creators,?_⟩
  intro m offset capture stop Z portrait genuine root interior gross finite earning begun older e he
  let E := capture.after
  let C := E.expanse (world)
  let T := E.part (world) (quiet) paid.creators
  let v := WilsonIndependentFreshScalar.remaining capture stop
  let res := WilsonIndependentResidentWinding.inherited (world) (quiet) E native
    ((world).soften light (by norm_num)).lead
  have B := E.sector (world) paid.creators
  have fund := E.getN (world) paid.bulk paid.creators
  have soft := E.credit (world) ((world).warmer light)
  have lead := E.restrict (world) ((world).soften light (show 1 ≤ 2 by norm_num)).lead
  have ward := WilsonIndependentFreshCoverWard.original R (quiet) paid.port E paid.creators Z
    paid.bulk paid.price portrait genuine (by norm_num [quantum]) paid.rates paid.inspiration
  have windingWard := WilsonIndependentFreshDeviationWard.original R (quiet) paid.port E paid.creators Z
    paid.bulk paid.price portrait genuine (by norm_num [quantum]) paid.rates paid.inspiration
  have big (z : Flap E.spans) : 1 ≤ C.l z.next := by
    have hz : base.age (E.wing z).volW ≤ (E.wing z).offset :=
      (begun z.volW).trans (Nat.le_add_right _ _)
    obtain ⟨t, ht⟩ := Radiants.rearward (k := base) (E.wing z) hz
    change 1 ≤ (world).l (E.wing z).next
    rw [←ht]
    exact light.crested t.next
  have cp (i : ℕ) (hi : i ≤ p) (r : ℕ) (hr : 0 < r) := WilsonIndependentFreshFiniteWage.cover C T Z B fund soft (by norm_num [quantum])
    gross finite earning ward hi hr
  have wp (i : ℕ) (hi : i ≤ p) (r : ℕ) := WilsonIndependentFreshFiniteWage.winding C T Z res lead soft interior (by norm_num)
    lamp.gleams.le lamp.small big (lamp.scale.us E.wing) gross finite earning ward windingWard (r := r) hi
  let F' := WilsonIndependentFreshReel.margins R E
  have year := WilsonIndependentFreshQuietEnding.actual R (L := L) (p := p) (u := 0) capture endAt
  have earth (w : W) : C.l (v.choose w) ≤ C.P w := by
    let z := E.page (v.choose w)
    have h := R.phase z
    change (world).l z ≤ (world).P z.bindW
    rw [←h]
    apply le_mul_of_one_le_right ((world).hl _).le
    exact_mod_cast (n z).pos
  have h := WilsonIndependentFreshFoldedHaar.original C T Z F' year
    (fun _ => T.cap_o B.grade _) (fun _ hi _ => WilsonIndependentFreshQuietEnding.salary C T F' year res hi)
    cp wp v earth lamp.gleams.le he
  convert h using 1
  funext w
  change gross w * ENNReal.ofReal ((S.l (capture.choose w) / S.l (stop.choose w))^γ) =
    gross w * ENNReal.ofReal ((S.l (capture.choose w) / S.l (E.page (v.choose w)))^γ)
  rw [show E.page (v.choose w) = stop.choose w from WilsonIndependentFreshScalar.page capture stop older w]

end YM.Integration.WilsonIndependentFreshEndInvoice
