import YM.Integration.WilsonOriginalOpticalTariffs
import YM.Integration.WilsonOriginalAllOrderAcceptance

/-! Enroll the true marked Schur constant and the optical post-block charges
inside the original full public election. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOpticalSchedule
open WilsonLimitConstruction PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Filter Function Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonOriginalAllOrderCourse WilsonOriginalAllOrderCalendar
open scoped Classical
universe u
variable {G : Gauge}

/-- Change only finite numerical pre-block quotes. -/
def prior (s : WilsonOriginalAllOrderCourse.Schedule G) : WilsonOriginalAllOrderCourse.Schedule G :=
  { s with
    neutral := fun q =>
      { s.neutral q with
        entrance := fun K j stage =>
          max ((s.neutral q).entrance K j stage) (WilsonOriginalOpticalTariffs.before G K j) } }

/-- Both the independent event and its whole-interval tariff enter the same
post-length quote. No field, period or regulator enters the preselection. -/
def prepared (s : WilsonOriginalAllOrderCourse.Schedule G) : WilsonOriginalAllOrderCourse.Schedule G :=
  let c := prior s
  { c with
    gearBill := fun q j I =>
      max (s.gearBill q j I)
        (max (combined (rows c) (events c) j I) (WilsonOriginalOpticalTariffs.after j I)) }

abbrev total (s : WilsonOriginalAllOrderCourse.Schedule G) := WilsonOriginalSeparatedElection.amount (bills (prepared s))

theorem pay (s : WilsonOriginalAllOrderCourse.Schedule G) (j : ℕ) (I : Gear G) :
    max (combined (rows (prepared s)) (events (prepared s)) j I) (WilsonOriginalOpticalTariffs.after j I)
      ≤ total s j I :=
  (le_max_right ..).trans
    (WilsonOriginalSeparatedElection.funded_bill (bills (prepared s)) j 0 (Nat.zero_le _) I)

theorem prior_bill (s : WilsonOriginalAllOrderCourse.Schedule G) (q : Key) (j : ℕ) (I : Gear G)
    (ready : Encodable.encode q ≤ j) : s.gearBill q j I ≤ total s j I := by
  have visit := WilsonOriginalSeparatedElection.funded_bill (bills (prepared s)) j _ ready I
  apply le_trans _ visit
  change s.gearBill q j I ≤ max (s.gearBill (index (Encodable.encode q)) j I) _
  rw [indexed]
  exact le_max_left ..

theorem opening (s : WilsonOriginalAllOrderCourse.Schedule G) (R : Run G)
    (neutral : WilsonOriginalCollarElection.Neutral (teacher (prepared s)) R.kit) (m : ℕ) :
    let A := R.family.path.levels
    WilsonOriginalOpticalTariffs.before G A.clock.kernel (A.clock.J (m+1)) ≤ (A.S.block m).val := by
  let A := R.family.path.levels
  let j := A.clock.J (m+1)
  obtain ⟨_,_,floors,_⟩ :=
    WilsonOriginalAllOrderFiledRealm.entrance (rows (prepared s)) R neutral (m+1) 0 (Nat.zero_le _)
  have h := (floors 0 (Nat.zero_le _)).1
  have t : WilsonOriginalOpticalTariffs.before G R.metals.p.kernel j ≤ (A.clock.factor j).val :=
    (le_max_right ..).trans h
  change WilsonOriginalOpticalTariffs.before G A.clock.kernel j ≤ (A.S.block m).val
  rw [show A.clock.kernel=R.metals.p.kernel from R.alloy.B.valid.kernel,←A.fits.sameFactor]
  exact t

/-- The very original Wilson fields, full physical master, and its ordinary
independent price source are common to every later finite optical query. -/
theorem published (a : Axis) (simple : G.Simple) {ε : ℝ} (pos : 0 < ε) (s : WilsonOriginalAllOrderCourse.Schedule G) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W ∧
      WilsonOriginalAllOrderPublicFields.Master.{u} R simple (fun _ => True) Extraction.Order.full :=
  WilsonOriginalAllOrderAcceptance.published a simple pos (prepared s)

end YM.Integration.WilsonOriginalOpticalSchedule
end
