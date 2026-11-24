import YM.GradedFar.Growth.Tare

/-!
# W,N and H relation under a dilation

Scale.Homogeneous, Touched etc used exactly. Work for operator *quotients*.
No different θ or frame for when testing.
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
local notation "ψ"=> GroupS.ψ N.criterion M ν
local notation "K"=> Kseries N M
local notation "α"=> Measure.adjust N.scheme N.criterion
local notation "B"=> GroupS.gaugeN N.scheme N.criterion M ν
open Reg.Point (stepV)

/-- Equivalent trial in W (1472), includes all its lower terms. -/
def train (d : ℕ) (s : ℝ) : Guard G d := Measure.adjust N.scheme N.criterion d * Kseries N M d (-s) * stepV
    (GroupS.ψ N.criterion M (Teller.logNu 1) (-s)) (Scale.mirror (Measure.adjust N.scheme N.criterion d))
lemma transferred (t : ℝ) (S : Guard G d) :
    S * C (Level.Dial d t)= C (Level.Dial d t) * convertT t S := by
    ext1 k; rw [coeff_mul_C,coeff_C_mul,Level.transfer,convertT,coeff_mk]
lemma train_spread (s : ℝ) : train N M d s= PowerSeries.C (Level.Dial d (-s)) *
    (convertT (-s) (α d) * B (-s) d * stepV (ψ (-s)) (mirror (α d))) := by unfold train Kseries; rw [← mul_assoc (α d) _ _,transferred]; simp [mul_assoc]

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H
lemma recruited_j : Base (α d) := ((H.details.toServed.toPosted.toQuoted.toContract.joint ν d).2.2).scale
lemma train_started (d : ℕ) (s : ℝ) : Base (convertT (-s) (α d) * B (-s) d * stepV (ψ (-s)) (mirror (α d))) :=
    ((converts (-s) _ (recruited_j N M H)).mul ((H.dilation ν).check.paid (-s) d)).mul
      ((recruited_j N M H).rewind.switch (tendsK N M H s).real)
lemma train_dial (s : ℝ) : coeff 0 (train N M d s) = Level.Dial d (-s) := by rw [train_spread,coeff_C_mul,(train_started N M H d s).zero,mul_one]
lemma train_walk (d e : ℕ) (h : d ≤ e) (s : ℝ) : Scale.Walk h (train N M d s) (train N M e s) := by
    let data:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born
    have he := Scale.Measure.grades N.scheme N.criterion ν M A simple data.Taylor data.still data.base h
    exact (he.mul (column_cap_compatible H h (-s))).mul ((he.rewind (recruited_j N M H) (recruited_j N M H)).steps _)
lemma un_train (s : ℝ) : train N M d s * stepV (ψ (-s)) (α d)= α d * K d (-s) := by rw [train, mul_assoc, ← Frame.step_mul _ _ _ (tendsK N M H s).start, (recruited_j N M H).turn, Frame.step_one, mul_one]

lemma unadj_match (d : ℕ)(s : ℝ) :
    actMark (convertT (-s) (α d) * B (-s) d * stepV (ψ (-s)) (mirror (α d)))
        (scaling (-s) (Pose.Bbook N d)) = couple (ψ (-s)) (Pose.Bbook N d) := by
    have he := (H.dilation ν).check.reads (-s) d
    change actMark (B (-s) d) (scaling (-s) (actMark (α d) (Pose.Bbook N d)))=
      couple (ψ (-s)) (actMark (α d) (Pose.Bbook N d)) at he
    rw [← Facets.acts,← Facets.acts,← Facets.pose_act, he, Facets.team _ _ _ (tendsK N M H s).start,
      Facets.acts, (recruited_j N M H).turn',Facets.acts_h]
lemma train_exact (x : Stage n) (d : ℕ) (s : ℝ) :
    status (train N M d s) (Pose.Bbook N d n (posing (-s) x)) = substitute (ψ (-s)) (Pose.Bbook N d n x) := by
    change _ = couple _ (Pose.Bbook N d) n x
    rw [← unadj_match N M H d s, actMark, train_spread]; ext1 i; ext1 p
    simp_rw [seen, scale_at]
    refine Finset.sum_congr rfl fun j _=> ?_
    unfold pulseU; simp_rw [coeff_C_mul]
    rfl
end
end YM.FVA2.GradedFar.Moving
