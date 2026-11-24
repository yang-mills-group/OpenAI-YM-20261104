import YM.Integration.WilsonIndependentCapturedContrastSalary
import YM.Integration.WilsonIndependentFreshAppointment

/-! Assess the signed occupied tensors at capture once. Their later scalar
uses the actual incoming history, genuine unmarked program and all older
feeds. The independent source can have a different arity ceiling. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option warningAsError true
namespace YM.Integration.WilsonIndependentCapturedContrastAppointment
open Lattice RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Spatial RegulatorIR.Uniform
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Cluster
open RegulatorIR.Epoch RegulatorIR.Calibration RegulatorIR.Profiles RegulatorIR.Taping
open RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Halo RegulatorIR.FVAAlt2
open scoped ENNReal Classical
variable {G : Gauge} {W : Type} {j : W → ℕ} {n : Page j → Side}
variable (S : Circuit j n) {K : KernelChoices} (Y : Oracle.Program K)
variable (branch : ∀ patch : Patch, patch.Branches K G) {color : G.ColorIndex}
variable {L : Meter W} {base : Choice j} {budget : Marked j}
variable {p moments : ℕ} {F : Tent j} {γ : ℝ}
local notation "world" => S.dialect Y G branch (sheet F)
local notation "quiet" => S.payroll Y G branch (sheet F)

theorem original (simple : G.Simple) (grade : quantum 1 0 ≤ moments)
    (book : SatisfiesQ G Y S branch budget p moments γ)
    (notebook : Notebook S Y G branch color base F p)
    (atBase : ∀ w, budget.peak (base.choose w) = 0)
    (mesh : ∀ w, S.l (base.choose w) = 1) (age : OfAge budget L) :
    ∃ seed : (world).Primitive L p (quantum 1 0),
    ∀ (m h a off : ℕ) (capture stop : Choice j), capture.age ≤ stop.age →
      let T := capture.after.part (world) (quiet) seed
      ∀ (incoming : (quiet).Report m) (issued : T.Report h) (remaining : T.Report a)
        (portrait : W → Portrait G),
        (∀ w i r, Prim.Bounded (incoming.main (Page.opening j w) i r)) →
        (∀ w, BasisT a off (portrait w) (remaining.main (Page.opening capture.after.spans w))) →
        (∀ w i, i ≤ p → incoming.main (capture.choose w) i - issued.main (Page.opening capture.after.spans w) i =
          remaining.main (Page.opening capture.after.spans w) i) →
        ∀ (root : W → Room) (fee : W → ℝ), (∀ w, 0 ≤ fee w) →
        (∀ i, i ≤ p → ∀ r, Claim L (fun w => (world).coverQ root 2 (capture.choose w))
          (fun w => ENNReal.ofReal (fee w)) (fun w => remaining.main (Page.opening capture.after.spans w) i r)) →
        ∀ e, e ≤ p → ∃ K : ℝ, ∃ d : ℕ, 0 ≤ K ∧ ∀ w,
        ‖note (incoming.main (stop.choose w) e 0) -
          note (issued.main ((WilsonIndependentFreshScalar.remaining capture stop).choose w) e 0)‖ ≤
          K*(L.val w).toReal^d*fee w := by
  obtain ⟨enrolled,lamp⟩ := Atlas.reservations S G Y branch atBase age book color notebook simple mesh
  let paid := enrolled.emits (b:=1) (u:=0) (by norm_num) grade
  refine ⟨paid.creators,?_⟩
  intro m h a off capture stop older T incoming issued remaining portrait top actual joined root fee nonneg wage e he
  let E := capture.after
  let C := E.expanse (world)
  let R := WilsonIndependentCapturedRocket.arrived (world) (quiet) paid.creators capture incoming
  let native : Milieu C T (quantum 1 0) p L :=
    ⟨E.sector (world) paid.creators, E.getN (world) paid.bulk paid.creators,
      fun f => enrolled.milieu.align (E.wing f), fun f => enrolled.milieu.mirror (E.wing f)⟩
  have quietWard := WilsonIndependentFreshCoverWard.original _ (quiet) paid.port E paid.creators remaining
    paid.bulk paid.price portrait actual (by norm_num [quantum]) paid.rates paid.inspiration
  have inStock (w : W) : Bill (R.main (Page.opening E.spans w)) p :=
    WilsonIndependentCapturedContrast.inventory (world) (quiet) enrolled.milieu incoming
      (fun x i _ r => Prim.bound_cost (top x i r)) (capture.choose w)
  have outStock (w : W) : Bill (issued.main (Page.opening E.spans w)) p := by
    intro i hi r
    have sub := congrFun (joined w i hi) r
    change incoming.main (capture.choose w) i r - issued.main (Page.opening E.spans w) i r =
      remaining.main (Page.opening E.spans w) i r at sub
    rw [show issued.main (Page.opening E.spans w) i r =
        incoming.main (capture.choose w) i r - remaining.main (Page.opening E.spans w) i r by
      rw [←sub];abel]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨inStock w i hi r,
      Prim.bound_cost ((actual w).canopy i r)⟩) (quota_sub ..)
  let v := WilsonIndependentFreshScalar.remaining capture stop
  have coverSoft := E.credit (world) ((world).warmer (paid.leads lamp))
  obtain ⟨K,d,kp,rate⟩ := WilsonIndependentCapturedContrastSalary.original C T native R issued remaining
    coverSoft (by norm_num [quantum]) inStock outStock joined quietWard fee nonneg wage v he
  refine ⟨K,d,kp,fun w => ?_⟩
  have same := WilsonIndependentCapturedRocket.chronological (world) (quiet) paid.creators capture incoming stop older w e he
  change R.main (v.choose w) e = incoming.main (stop.choose w) e at same
  exact same ▸ rate w

end YM.Integration.WilsonIndependentCapturedContrastAppointment
