import YM.Integration.WilsonMovingForkReporterPostedRanks
import YM.Integration.WilsonMovingForkReporterSharedCutoffs

/-! Both observed Vane arms retain the independently earned Wick comparison on the same full original cutoff table at coincident dates. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterRankTables
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

open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankCourse (surplus reached)
open WilsonMovingForkReporterPostedRanks (paid)
variable {G:Gauge} (R:Run G) (B:Binding R.family) (O:HaarBudget G) (J:ChartRatio G)
  {f:Extraction.Order} (a:(Cells.standard R.family).Hierarchy)
  (b:ℕ→Fin 3→ℝ) (z c:ℕ→ℝ) (P:∀d,ℝ→Fin 3→Tapes.Panel d) (grade:ℕ→ℕ)
  {start:ℕ} (k₁ k₂:ℕ→{k:ℕ // start<k}) (s₁ s₂:ℕ→ℝ)
  (count:ℕ→ℕ) (tests:∀d,Fin (count d)→Axes R.family)
local notation "width" => WilsonPhysicalPositionWeakRoofSchedule.width b
local notation "VaneAt" => WilsonMovingForkReporterOriginalCouncil.reporters R
local notation "pupil" => WilsonMovingForkReporterSharedCutoffs.geometry grade k₁ k₂ s₁ s₂

def Named {d:ℕ} (pan:Tapes.Panel d) (V:Vane R.family d) : Prop :=
  ∃ hc:V.checked f a d,Filed B R.makes O J pan V (MergeProof.East.trays d) (z d) ∧
    ∀s:Fin (count d),∀active:100*((tests d s).weight+1)≤d,
      paid R V (tests d s) (by omega) hc d

theorem original
    (opened:∀k:{k:ℕ // start<k},WilsonPhysicalPositionWeakRoofCourse.earned (F:=f) R B R.makes O J a b z c P (grade k) k)
    (ripe:∀k:{k:ℕ // start<k},(grade k:ℝ)+1≤R.family.path.levels.clock.monitor k^(surplus (grade k)))
    (assets:∀k:{k:ℕ // start<k},∀x∈Icc 0 (width (grade k)),∀s:Fin (count (grade k)),
       100*((tests (grade k) s).weight+1)≤grade k →
         reached R B R.makes O J (tests (grade k) s) (P (grade k) x 0) k (z (grade k)))
    (aligned:∀d,∀x∈Icc 0 (width d),(P d x 0).arc=b d 0+x)
    (first:∀i,s₁ i∈Icc 0 (width (grade (k₁ i)))) (second:∀i,s₂ i∈Icc 0 (width (grade (k₂ i))))
    (room:∀i,1≤grade (k₂ i)) :
    ∃Y:∀ (_:ℕ) (k:{k:ℕ // start<k}),ℕ→ℕ→TableL R.family (grade k),
      (∀ (i:ℕ) (k:{k:ℕ // start<k}),PoisedSky (fun j:Fin (grade k+1)×Fin 3=>P (grade k) (pupil i k j.1) j.2)
        B R.makes O J (MergeProof.East.trays (grade k)) (z (grade k)) k (Y i k)) ∧
      ∀i, let u:=k₁ i; let v:=k₂ i
          let A:=VaneAt (grade u) u (b (grade u) 0) (c (grade u)) (Y i u) (s₁ i)
          let A':=VaneAt (grade v) v (b (grade v) 0) (c (grade v)) (Y i v) (s₂ i)
          Named (f:=f) R B O J a z count tests (P (grade u) (s₁ i) 0) A ∧
            Named (f:=f) R B O J a z count tests (P (grade v) (s₂ i) 0) A' :=by
  obtain ⟨Y,issued,panels⟩:=WilsonMovingForkReporterSharedCutoffs.original (f:=f)
    R B R.makes O J a b z c P grade k₁ k₂ s₁ s₂ opened aligned first second room
  refine ⟨Y,issued,fun i=>?_⟩
  have one (k:{k:ℕ // start<k}) (x:ℝ) (hx:x∈Icc 0 (width (grade k)))
      (ready:let A:=VaneAt (grade k) k (b (grade k) 0) (c (grade k)) (Y i k) x
        A.checked f a (grade k) ∧ Filed B R.makes O J (P (grade k) x 0) A (MergeProof.East.trays (grade k)) (z (grade k))) :
      Named (f:=f) R B O J a z count tests (P (grade k) x 0)
        (VaneAt (grade k) k (b (grade k) 0) (c (grade k)) (Y i k) x) := by
    obtain ⟨check,ink⟩:=ready
    exact ⟨check,ink,fun s hs=>WilsonMovingForkReporterPostedRanks.original R B O J _ _ (by omega)
      check _ ink (assets k x hx s hs) (ripe k)⟩
  exact ⟨one _ _ (first i) (panels i).1,one _ _ (second i) (panels i).2⟩

end YM.Integration.WilsonMovingForkReporterRankTables
end
