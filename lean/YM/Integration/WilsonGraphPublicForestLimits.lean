import YM.Integration.WilsonGraphStandaloneCorrelation
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonGraphPublicForestLimits
open YangMills Filter
open YM.Integration.WilsonGraphStandaloneCorrelation
open YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest (film released)
open scoped Topology BigOperators Classical

variable {g : YangMills.GaugeGroup} {n : ℕ}

/-- The dimensional film at a positive infrared length on the submitted mixed-grade word. -/
def dimensional (a : Fin n → Label g) (x : YangMills.Points n) (k : ℕ) (ρ : ℝ) (z : ℂ) : ℂ :=
  film ({x} : Set (YM.Points n)) (marks a (within a)) k (Real.log ρ) z ⟨x, Set.mem_singleton x⟩

/-- The same finite marked array after the dimensional limit, before the infrared limit. -/
def releasedAt (a : Fin n → Label g) (x : YangMills.Points n) (k : ℕ) (ρ : ℝ) : ℂ :=
  released ({x} : Set (YM.Points n)) (marks a (within a)) k (Real.log ρ) ⟨x, Set.mem_singleton x⟩

theorem physical (a : Fin n → Label g) (x : YangMills.Points n) (hx : x ∈ YangMills.separated n)
    (k : ℕ) :
    (∀ ρ : ℝ, 0 < ρ → Tendsto (dimensional a x k ρ) YM.MS.Shine.dotty (𝓝 (releasedAt a x k ρ))) ∧
    Tendsto (releasedAt a x k) atTop (𝓝 (bare g n k a x)) :=
  YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.physical x ((publicSeparatedIff x).mp hx) (marks a (within a)) k

/-- Only the externally appointed finite conversion acts on the already fixed graph readings. -/
def weighted (S : YangMills.Matching.Conversion (maxwellReference g)) (k : ℕ)
    (a : Fin n → Label g) (value : (Fin n → Label g) → ℕ → ℂ) : ℂ :=
  ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
    let used := ∑ i, (ν i).val
    if used + j.val ≤ k then
      (YangMills.Matching.couplingPower S.f j.val (k-used) : ℂ) * value (S.inputs a ν) j.val
    else 0

theorem weightedTendsto {α : Type*} {l : Filter α}
    (S : YangMills.Matching.Conversion (maxwellReference g)) (k : ℕ) (a : Fin n → Label g)
    (values : α → (Fin n → Label g) → ℕ → ℂ) (limit : (Fin n → Label g) → ℕ → ℂ)
    (each : ∀ b j, Tendsto (fun z => values z b j) l (𝓝 (limit b j))) :
    Tendsto (fun z => weighted S k a (values z)) l (𝓝 (weighted S k a limit)) := by
  unfold weighted
  apply tendsto_finsetSum
  intro ν _
  apply tendsto_finsetSum
  intro j _
  dsimp only
  split_ifs
  · exact tendsto_const_nhds.mul (each _ _)
  · exact tendsto_const_nhds

theorem convertedLimits (S : YangMills.Matching.Conversion (maxwellReference g)) (k : ℕ)
    (a : Fin n → Label g) (x : YangMills.Points n) (hx : x ∈ YangMills.separated n) :
    (∀ ρ : ℝ, 0 < ρ → Tendsto (fun z => weighted S k a (fun b j => dimensional b x j ρ z))
      YM.MS.Shine.dotty (𝓝 (weighted S k a (fun b j => releasedAt b x j ρ)))) ∧
    Tendsto (fun ρ => weighted S k a (fun b j => releasedAt b x j ρ))
      atTop (𝓝 (converted S k a x)) := by
  constructor
  · intro ρ hρ
    exact weightedTendsto S k a (fun z b j => dimensional b x j ρ z)
      (fun b j => releasedAt b x j ρ) (fun b j => (physical b x hx j).1 ρ hρ)
  · change Tendsto (fun ρ => weighted S k a (fun b j => releasedAt b x j ρ))
      atTop (𝓝 (weighted S k a (fun b j => bare g n j b x)))
    exact weightedTendsto S k a (fun ρ b j => releasedAt b x j ρ)
      (fun b j => bare g n j b x) (fun b j => (physical b x hx j).2)

end YM.Integration.WilsonGraphPublicForestLimits
end

