import YM.Integration.WilsonMovingForkReporterSuppliedBatch

/-! A pair of apertures on one physical date uses one original table for both marks. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterSharedCutoffs
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open YM.Integration.WilsonLimitConstruction PhysicalNext.Repeat.Legato
open WilsonMovingForkReporterNamedInk
variable {G:Gauge} (R:Run G) (B:Binding R.family) (H:R.family.Makes) (O:HaarBudget G) (J:ChartRatio G)
  {f:Extraction.Order} (a:(Cells.standard R.family).Hierarchy)
  (b:ℕ→Fin 3→ℝ) (z c:ℕ→ℝ) (P:∀d,ℝ→Fin 3→Tapes.Panel d) (grade:ℕ→ℕ)
  {start:ℕ} (k₁ k₂:ℕ→{k:ℕ // start<k}) (s₁ s₂:ℕ→ℝ)

def geometry (i:ℕ) (k:{k:ℕ // start<k}) (j:Fin (grade k+1)) : ℝ :=
  if j.val=0 ∧ k=k₁ i then s₁ i else if k=k₂ i then s₂ i else 0

local notation "width" => WilsonPhysicalPositionWeakRoofSchedule.width b
local notation "VaneAt" => WilsonMovingForkReporterOriginalCouncil.reporters R
local notation "pupil" => geometry grade k₁ k₂ s₁ s₂

theorem original
    (opened:∀k:{k:ℕ // start<k},WilsonPhysicalPositionWeakRoofCourse.earned (F:=f) R B H O J a b z c P (grade k) k)
    (aligned:∀d,∀x∈Icc 0 (width d),(P d x 0).arc=b d 0+x)
    (first:∀i,s₁ i∈Icc 0 (width (grade (k₁ i)))) (second:∀i,s₂ i∈Icc 0 (width (grade (k₂ i))))
    (room:∀i,1≤grade (k₂ i)) :
    ∃Y:∀ (_:ℕ) (k:{k:ℕ // start<k}),ℕ→ℕ→TableL R.family (grade k),
      (∀ (i:ℕ) (k:{k:ℕ // start<k}),PoisedSky (fun j:Fin (grade k+1)×Fin 3=>P (grade k) (pupil i k j.1) j.2)
        B H O J (MergeProof.East.trays (grade k)) (z (grade k)) k (Y i k)) ∧
      ∀i, let u:=k₁ i; let v:=k₂ i
          let A:=VaneAt (grade u) u (b (grade u) 0) (c (grade u)) (Y i u) (s₁ i)
          let A':=VaneAt (grade v) v (b (grade v) 0) (c (grade v)) (Y i v) (s₂ i)
          (A.checked f a (grade u) ∧ Filed B H O J (P (grade u) (s₁ i) 0) A (MergeProof.East.trays (grade u)) (z (grade u))) ∧
          (A'.checked f a (grade v) ∧ Filed B H O J (P (grade v) (s₂ i) 0) A' (MergeProof.East.trays (grade v)) (z (grade v))) :=by
  have range (i:ℕ) (k:{k:ℕ // start<k}) (j:Fin (grade k+1)):pupil i k j∈Icc 0 (width (grade k)):=by
    unfold geometry
    split_ifs with h e
    · rw [h.2]
      exact first i
    · subst k
      exact second i
    · refine ⟨le_rfl,?_⟩
      unfold WilsonPhysicalPositionWeakRoofSchedule.width
      linarith only [le_max_left 0 (b (grade k+1) 0-b (grade k) 0)]
  choose Y school cash using fun (i:ℕ) (k:{k:ℕ // start<k})=>WilsonMovingForkReporterSuppliedBatch.original (f:=f)
    R B H O J a b z c P (grade k) k (pupil i k) (range i k) (fun j=>aligned _ _ (range i k j)) (opened k)
  refine ⟨Y,school,fun i=>?_⟩
  have l:=cash i (k₁ i) (0:Fin (grade (k₁ i)+1))
  have r:=cash i (k₂ i) (⟨1,by have h:=room i;omega⟩:Fin (grade (k₂ i)+1))
  exact ⟨by simpa only [geometry,Fin.val_zero,and_self,if_true] using l,
    by simpa only [geometry,Nat.one_ne_zero,false_and,if_false,if_true] using r⟩

end YM.Integration.WilsonMovingForkReporterSharedCutoffs
end
