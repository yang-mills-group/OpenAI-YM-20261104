import YM.FVAAlt2.Boot.Labels
import YM.FVAAlt2.Boot.Revenue
import YM.Integration.ActualOriginalQStartupAction

/-! The genuine all-configuration Wilson measure with arbitrary admitted frozen marked columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeWilsonColoredMeasure
open Function Filter Set Finset Lattice Wilson Precision RG Labels PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2
open PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2
open Integral Exterior Marker Multi
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {H : Census V} (R : Run G) (m p : ℕ)
local notation "σ" => R.family.side (m+1) p
local notation "X" => R.family.path.rep (m+1) p (m+1)
local notation "K" => RunFormalChain.fromRun R

/-- Retain every calibrated source price and install the original microscopic vacuum. -/
def colors (W : Bulk.Colors H G σ) : Bulk.Colors H G σ :=
  { W with vac := fun _ U => Wilson.energy U - mainTerm (X).clip (X).path U }

private def unitScout (R : Run G) := Boot.scout R (∅ : Finset (Fin 0)) (fun i => Fin.elim0 i)
  (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

omit [Fintype V] in
/-- Full Wilson vacuum and signed original colors have their original regularity receipts. -/
theorem well (W : Bulk.Colors H G σ) (hW : Bulk.Well W) : Bulk.Well (colors R m p W) := by
  have hB := (Boot.authentic (Stock.census (Fin 1)) 0 R.family.path K (m+1) p (unitScout R)).1
  exact ⟨hB.suppose_vac,hW.suppose_mark,hB.natural,hW.gauges,hB.envelope,hW.prices⟩

omit [Fintype V] in
theorem frozen {n : Side} (W : Bulk.Colors H G n) (hw : Bulk.Well W)
    (h : ∀ i t, 0<t → ∀ U, W.mark i t U = (t^W.power i) • W.mark i 1 U) : Bare.Starts W := by
  intro i
  obtain ⟨M,hM⟩ := (hw.prices i 1).cost
  refine ⟨0,max 0 M,le_max_left _ _,?_⟩
  have hlt : ∀ᶠ t : ℝ in Laplace.along, t < 1 := (gt_mem_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in Laplace.along, 0 < t := Tested.eventually_pos
  filter_upwards [hpos,hlt] with t ht hu
  intro U
  rw [h i t ht, norm_smul,Real.norm_of_nonneg (pow_nonneg ht.le _),pow_zero,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.le hu.le)).trans ((hM U).trans (le_max_right _ _))

theorem witnessed (W : Bulk.Colors H G σ) (hW : Bulk.Well W) (hstart : Bare.Starts W) :
    Bare.Witnessed (colors R m p W) ((K).step (m+1) m p (Nat.lt_succ_self m)) := by
  refine ⟨well R m p W hW,hstart,?_⟩
  intro t
  ext1 U
  unfold Integral.model Bare.top Bare.Passes Integral.weight Integral.localClassic
  rw [Boot.kept0 R.family.path K (m+1) p]
  unfold Wilson.bare colors
  congr 2
  dsimp only
  ring_nf

theorem frozen_witnessed (W : Bulk.Colors H G σ) (hW : Bulk.Well W)
    (h : ∀ i t, 0<t → ∀ U, W.mark i t U = (t^W.power i) • W.mark i 1 U) :
    Bare.Witnessed (colors R m p W) ((K).step (m+1) m p (Nat.lt_succ_self m)) :=
  witnessed R m p W hW (frozen W hW h)

end YM.Integration.NativeWilsonColoredMeasure
end
