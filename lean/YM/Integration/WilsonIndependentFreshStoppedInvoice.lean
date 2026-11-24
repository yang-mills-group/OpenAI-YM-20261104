import YM.Integration.WilsonIndependentFreshQuietEnding
import YM.Integration.WilsonIndependentFreshFoldedHaar
import YM.Integration.WilsonIndependentFreshAppointment

/-! Compare the actual stopped torus scalar with its stopped cover scalar
for the very same occupied input. This permits finite-board source limits. -/
noncomputable section
namespace YM.Integration.WilsonIndependentFreshStoppedInvoice
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


private theorem scalarFold {P : ℝ} {I J : Type} (D : Budget.Deck P I J) (T : Budget.Packet I 0) :
    note (D.scroll T) = note T := by
  unfold note Budget.Deck.scroll Budget.Stalk.collect
  let t : Budget.Stalk D.project Fin.elim0 := ⟨Fin.elim0, Subsingleton.elim ..⟩
  rw [tsum_eq_single t]
  · change D.dyed T Fin.elim0 = T Fin.elim0
    simp [Budget.Deck.dyed, Budget.Deck.polish]
  · exact fun b hb => (hb (Subsingleton.elim ..)).elim

theorem original (simple : G.Simple) (grade : quantum 1 0 ≤ moments)
    (book : SatisfiesQ G Y S branch budget p moments γ)
    (notebook : Notebook S Y G branch color base F p)
    (atBase : ∀ w, budget.peak (base.choose w) = 0)
    (mesh : ∀ w, S.l (base.choose w) = 1) (age : OfAge budget L) :
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
        (fun w => ‖note (Z.point ((WilsonIndependentFreshScalar.remaining capture stop).choose w) e 0) -
          note (Z.main ((WilsonIndependentFreshScalar.remaining capture stop).choose w) e 0)‖ₑ) := by
  obtain ⟨enrolled,lamp⟩ := Atlas.reservations S G Y branch atBase age book color notebook simple mesh
  let paid := enrolled.emits (b := 1) (u := 0) (by norm_num) grade
  let light := paid.leads lamp
  let R := S.lane Y G branch (sheet F)
  let old : (quiet).Report 0 := declaring (quiet) (fun _ => 0) (fun _ _ _ h => (h rfl).elim)
  have native := paid.splines old (fun _ => 0) (fun _ => WilsonIndependentFreshQuietReel.priorZero G) lamp
  refine ⟨paid.creators,?_⟩
  intro m offset capture stop Z portrait genuine root interior gross finite earning begun older e he
  let E := capture.after
  let C := E.expanse (world)
  let T := E.part (world) (quiet) paid.creators
  let v := WilsonIndependentFreshScalar.remaining capture stop
  let res := WilsonIndependentResidentWinding.inherited (world) (quiet) E native
    ((world).soften light (by norm_num)).lead
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
  have wp (i : ℕ) (hi : i ≤ p) (r : ℕ) := WilsonIndependentFreshFiniteWage.winding C T Z res lead soft interior (by norm_num)
    lamp.gleams.le lamp.small big (lamp.scale.us E.wing) gross finite earning ward windingWard (r := r) hi
  have earth (w : W) : C.l (v.choose w) ≤ C.P w := by
    let z := E.page (v.choose w)
    have h := R.phase z
    change (world).l z ≤ (world).P z.bindW
    rw [←h]
    apply le_mul_of_one_le_right ((world).hl _).le
    exact_mod_cast (n z).pos
  have wind := (wp e he 0).us (fun w => v.choose w)
  have local_ : Carry L (fun w => gross w * ENNReal.ofReal
      ((C.l (Page.opening E.spans w) / C.P w)^γ))
      (fun w => ‖note (Z.point (v.choose w) e 0) - note (Z.main (v.choose w) e 0)‖ₑ) := by
    apply Carry.mono wind
    intro w
    dsimp only
    rw [quotaNote, ← scalarFold (C.maps (v.choose w))]
    exact le_rfl
  apply Carry.charge local_
  apply Carry.mono (Carry.unit ..)
  intro w
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow (div_nonneg (C.hl _).le (C.hp _).le) _ lamp.gleams.le
  change S.l (capture.choose w) / S.P w ≤ S.l (capture.choose w) / S.l (stop.choose w)
  have pos := (world).hl (stop.choose w)
  apply div_le_div_of_nonneg_left ((world).hl _).le pos
  have lower := earth w
  change S.l (E.page (v.choose w)) ≤ S.P w at lower
  rwa [show E.page (v.choose w) = stop.choose w from WilsonIndependentFreshScalar.page capture stop older w] at lower

end YM.Integration.WilsonIndependentFreshStoppedInvoice
