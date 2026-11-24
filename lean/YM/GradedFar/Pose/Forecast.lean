import YM.GradedFar.FormalSecond

/-!
# Prepare RingCalibration (F.2) inputs of the pose-fit interface

In this file, and this subdirectory (`Pose`), **before homogeneous
adjustment**. Use the real RingCalibration meter with all of its
fixed witnesses. Note Scene, Screen, Rose etc are the original ones.
-/
namespace YM.FVA2.GradedFar.Pose
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m d : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1

abbrev Bbook := Measure.start N.scheme N.criterion
abbrev reports (d : ℕ) := Reg.Faith.reports ν N.criterion M d
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H
lemma birth (d : ℕ) : Orders (Bbook N d) (reports N M d) := by
  let h := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact Jury.enrolled ν M _ _ A simple h.Taylor h.still h.base

lemma nickel (x : Points n) (h : x ∈ conf n) (d : ℕ) : Jury.fxt (Bbook N d) x 0 = scene x d := by
  let q := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  rw [show x=(⟨x,h⟩:Stage n).val from rfl, Jury.exactC]
  exact (Measure.dawn N.scheme N.criterion ν M A simple q.Taylor q.still q.base) n ⟨x,h⟩

lemma ground (d : ℕ) : reports N M d 0=reference G d := by
  ext1 n; ext1 t; ext1 v
  rw [(birth N M H d).exact n 0,reflects]
  exact Test.apply_eq _ fun x hx=> by rw [nickel N M H x hx]

open MS.Book.Program
/-- First of (F.2). Pose is on the unadjusted but already **recruited** position
system, `reports` the true-integrated software prediction. -/
lemma geared (d i : ℕ) : (N.store.measure d).D (reports N M d i) = if i=0 then (N.store.measure d).D (reference G d) else 0 := by
  let h := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  let he := birth N M H d
  have hX := he.glance PowerSeries.X
  rw [Facets.team_one] at hX
  have hx := Jury.solved ν M N.scheme N.criterion A simple h.Taylor h.still h.base (d:=d)
    (p:=PowerSeries.X) (by simp [Rooted]) (by simp [Reg.Unique.CoreR]) i
  rw [← Jury.peer _ _ he.exact hX.exact,deck0, Normalize.author] at hx
  exact hx

open XSpace.Rose Finset
/-- No dialing by another array; execute the signed full Rose thermometer as in A.
Proof follows `WilsonPositionScaleLawThermometerGround.zero` (own declaration),
without coupling(dilation). -/
lemma zero_single (x : Points 3) (hx : x∈conf 3) : coeff 0 (Select.Single (Bbook N 6) x)=0 := by
  let P:=Jury.fxt (Bbook N 6) x
  have no (a:Badge)(ha:a.Nonempty):constantCoeff (batchT P a)=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply,batchT,coeff_mk,show P 0=scene x 6 from nickel N M H x hx 6]
    exact silent N.scheme simple hx a ha
  change coeff 0 (b3 (batchT P))=0
  rw [coeff_zero_eq_constantCoeff_apply]
  unfold b3
  simp only [two_smul,map_add,map_sub,map_mul]
  rw [no univ (by decide),no {0,1} (by decide),no {0,2} (by decide),no {1,2} (by decide),
    no {0} (by decide),no {1} (by decide),no {2} (by decide)]
  ring

/-- Second (F.2), adaptation of `WilsonPositionScaleLawThermometerChart.coefficient`. -/
theorem registered (j:ℕ) : (Rose.test N.criterion).applyTo (fun x=> coeff j (Select.Single (Bbook N 6) x))=
    (Rose.cT N.criterion.cut G N.criterion.image:ℂ)*coeff j PowerSeries.X := by
  cases j with
  | zero =>
    rw [Test.apply_eq _ (show EqOn _ _ _ from (show EqOn (fun x=> coeff 0 (Select.Single (Bbook N 6) x)) (fun _=>0) (conf 3) from fun x h=>zero_single N M H x h))]; simp [Test.applyTo]
  | succ k=>
    let c:ℂ:=Rose.cT N.criterion.cut G N.criterion.image
    have live:c≠0:=Complex.ofReal_ne_zero.mpr N.criterion.fresh.ne
    have h:=congrArg (coeff (k+1)) H.details.toServed.toPosted.toQuoted.toContract.meant
    change coeff (k+1) (c⁻¹ • (Select.output N.criterion (Bbook N 6)-PowerSeries.C (coeff 0 (Select.output N.criterion (Bbook N 6)))))=_ at h
    simp only [map_smul,map_sub,coeff_C_of_ne_zero (Nat.succ_ne_zero k),sub_zero,smul_eq_mul,Select.output,coeff_mk] at h
    change _=c*_
    rw [←h,←mul_assoc,mul_inv_cancel₀ live,one_mul]
end
end YM.FVA2.GradedFar.Pose
