import YM.Integration.WilsonIndependentCapturedHistory
import YM.FVAAlt2.Rocket.Code

/-! Capture the whole chronological occupied array. At the cut its folded
array differs from the inherited finite one by the original winding tensor.
The stopped cover read retains every earlier covariance and scalar feed. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedRocket
open RegulatorIR RegulatorIR.Budget RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform
open RegulatorIR.Diagram RegulatorIR.Taping RegulatorIR.Profiles RegulatorIR.Halo
open RegulatorIR.Oracle RegulatorIR.Calibration RegulatorIR.FVAAlt2 RegulatorIR.Cluster
open Lattice RG YM.FVAAlt2 Source Labels
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side}
variable (S : Heir n G) (T : S.Accounts) {p u : ℕ} {L : Meter W}
variable (B : S.Primitive L p u) (b : Choice M) {h : ℕ} (H : T.Report h)

def arrived : (b.after.part S T B).Report h :=
  declaring (b.after.part S T B) (fun w => H.main (b.choose w)) (fun w => H.cap_b B.grade (b.choose w))

theorem opening (w : W) : (arrived S T B b H).main (Page.opening b.after.spans w) = H.main (b.choose w) := rfl

theorem winding (w : W) (i r : ℕ) :
    H.point (b.after.page (Page.opening b.after.spans w)) i r - (arrived S T B b H).point (Page.opening b.after.spans w) i r =
      H.deviation (b.choose w) i r := rfl

theorem chronological (v : Choice M) (older : b.age ≤ v.age) (w : W) (e : ℕ) (he : e ≤ p) :
    (arrived S T B b H).main ((WilsonIndependentFreshScalar.remaining b v).choose w) e =
      H.main (v.choose w) e := by
  have induced := WilsonIndependentCapturedHistory.cover S T B b H (arrived S T B b H)
    (fun _ _ _ => rfl) ((WilsonIndependentFreshScalar.remaining b v).choose w) e he
  rw [WilsonIndependentFreshScalar.page b v older] at induced
  exact induced.symm

variable (R : Circuit M n) {K : KernelChoices} (Y : Program K)
  (branch : ∀ P : Patch, P.Branches K G) (F : Tent M)
  {L' : Frames G} {H' : Hol G} (basis : Lobby.Registry L' H') {I : Type} [LinearOrder I]
  (roster : Finset I) (grade : I → ℕ) (axis : (i : I) → (L'.level (grade i)).Index) (z : W → I → Cover)
local notation "sky" => R.dialect Y G branch (sheet F)
local notation "quiet" => R.payroll Y G branch (sheet F)

theorem stopped (paid : (sky).Primitive L p u) (v : Choice M) (older : b.age ≤ v.age)
    (w : W) (e : ℕ) (he : e ≤ p) :
    note ((arrived (sky) (quiet) paid b (Rocket.Ignite R Y branch F basis roster grade axis z)).main
      ((WilsonIndependentFreshScalar.remaining b v).choose w) e 0) =
      Rocket.stopped R Y branch F basis roster grade axis v z w e := by
  rw [chronological _ _ paid b _ v older w e he]
  rfl

end YM.Integration.WilsonIndependentCapturedRocket
