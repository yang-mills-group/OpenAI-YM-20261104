import YM.GradedFar.Moving.Train
/-!
# Admissible changes (point maps) at the actual caps. Trial orientation.
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
open private change_left stand_unit_inverse from YM.XSpace.Deck
variable {G : Gauge} {n d e : ℕ} {I : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
local notation "ψ"=> GroupS.ψ N.criterion M ν
local notation "K"=> Kseries N M
local notation "α"=> Measure.adjust N.scheme N.criterion
local notation "B"=> GroupS.gaugeN N.scheme N.criterion M ν
open Reg.Point (stepV)
open Continuation (atColumn)

/-- Affine version. -/
def permissible (A : FieldEnd G d) := A-1 ∈ Normalize.Change G d
namespace permissible
lemma stood_as {A : FieldEnd G d} (h : permissible A) : stand (⟨_,h⟩ : Normalize.Change G d)=A :=
    (show 1+(A-1)=A from by abel)
lemma of_stand (T : Normalize.Change G d) : permissible (stand T) := by
    unfold permissible stand
    rw [show 1+T.val-1=T.val by abel]; exact T.property
lemma times {A R : FieldEnd G d} (ha : permissible A) (hb : permissible R) : permissible (A*R) := by
    obtain ⟨T,he⟩:= stand_times (⟨_,ha⟩:Normalize.Change G d) (⟨_,hb⟩:Normalize.Change G d)
    rw [ha.stood_as,hb.stood_as] at he
    rw [he]; exact of_stand T
lemma inverse {A R : FieldEnd G d} (ha : permissible A) (hc : R*A=1) (hd : A*R=1) : permissible R := by
    obtain ⟨T,hT⟩:= stand_unit_inverse ⟨A,R,hd,hc⟩ _ ha.stood_as; rw [show R=stand T from hT]; exact of_stand T
lemma of_features {A : FieldEnd G d} (hA : A (leaf G d)=leaf G d)
    (h : Level.Band A) (he : ∀ p, A (reel d p)=reel d (A p)) (ht : ∀ (s:Signed) p, A (ori s.ortho d p)=ori s.ortho d (A p)) :
    permissible A := by
    unfold permissible; rw [may_change]
    simp only [LinearMap.sub_apply,Module.End.one_apply,hA,sub_self,map_sub,he,ht]
    exact ⟨trivial,fun i hi p hp=> Submodule.sub_mem _ (h i hi p hp) hp, fun _=>trivial,fun _ _=>trivial⟩
lemma dial (d : ℕ) (s : ℝ) : permissible (Level.Dial (G:=G) d s) := of_features (Level.Dial_leaf _) (Level.Dial_band _) (Level.Dial_real s) (fun j=> Level.Dial_ori s j.ortho)
lemma columns (j : ℕ) (t : ℝ) (x : Guard G d) (h : Base x) : permissible (atColumn x j t) := by
    have he (x : FieldEnd G d) : 1 + x - 1=x := by abel
    unfold permissible atColumn; rw [← Finset.add_sum_erase (Finset.range (j+1)) (f:=fun i=> (t:ℂ)^i • coeff i x) (a:=0) (by simp),pow_zero,one_smul,h.zero, he]
    refine Submodule.sum_mem _ fun b hb=> ?_
    rw [← Complex.ofReal_pow, show ((t^b:ℝ):ℂ) • (coeff b x) = t^b • (coeff b x) from IsScalarTower.algebraMap_smul ℂ (t^b) _]; exact Submodule.smul_mem _ _ (h.high b (Finset.mem_erase.mp hb).1)
end permissible

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H
lemma trial_permitted (j : ℕ) (t s : ℝ) : permissible (atColumn (train N M d s) j t) := by
    let x:= convertT (-s) (α d) * B (-s) d * stepV (ψ (-s)) (mirror (α d)); let A : FieldEnd G d:= Level.Dial d (-s)
    have he : atColumn (train N M d s) j t=A * atColumn x j t:= by
      rw [train_spread]; unfold atColumn; rw [Finset.mul_sum]; simp_rw [coeff_C_mul]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [mul_smul_comm]
    rw [he]; exact (permissible.dial ..).times (permissible.columns j t x (train_started N M H d s))
end
end YM.FVA2.GradedFar.Moving
