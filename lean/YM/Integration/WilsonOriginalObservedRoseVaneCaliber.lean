import YM.Integration.WilsonReportingAbsoluteInletCoordinates
import YM.Integration.WilsonReflectedOpticalStock
import YM.Integration.WilsonOriginalObservedRoseVanePurse

/-! The finite non-mesh expense of the three original slots in units of the moving true coupling. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOriginalObservedRoseVaneCaliber
open Function Filter Lattice Wilson RG Real
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonThermometerDeclaredSeeds
open WilsonOriginalObservedRoseVanePurse (ages)
open WilsonOriginalObservedRoseMeshHeight (height)
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale
local notation "g" => regulatorRun R.family

theorem height_le (s:Finset (Fin 3)):height ages s≤14:=by
  calc height ages s≤height ages Finset.univ:=by
        unfold height
        simpa only [Finset.sum_coe_sort] using Finset.sum_le_sum_of_subset_of_nonneg (f:=ages) (Finset.subset_univ s) (by intros;exact Nat.zero_le _)
       _=14:=by decide

theorem original (simple:G.Simple)(L:ℕ):∀ᶠv:ℕ in atTop,∀N per K:ℕ,v≤K → K≤N →
    σ K-σ v ≤ L*Real.log (H v) → ∀s:Finset (Fin 3),
    (H K^2)^Fintype.card s≤(4:ℝ)^6*((g N per v)⁻¹)^12:=by
  filter_upwards [WilsonReportingAbsoluteInletCoordinates.clocks R simple L] with v prior N per K vk kn span s
  have hv:0<H v:=zero_lt_one.trans (R.family.path.levels.fits.delayed v)
  have hk:1≤H K:=(R.family.path.levels.fits.delayed K).le
  have scale:=WilsonReflectedOpticalStock.monotone R simple vk
  have corridor:=prior vk (span.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hv scale) (Nat.cast_nonneg _)))
  have band: H v/2≤R.family.path.β N per v:=(R.makes.wilson.represents N per v (vk.trans kn)).band.1
  have bp:0≤R.family.path.β N per v:=by linarith
  have identity:((g N per v)⁻¹)^2=R.family.path.β N per v:=by
    change (((Real.sqrt _)⁻¹)⁻¹)^2=_
    rw [inv_inv,Real.sq_sqrt bp]
  have paid:H K≤4*((g N per v)⁻¹)^2:=by rw [identity];linarith
  have card:Fintype.card s≤3:=by simpa only [Fintype.card_coe,Fintype.card_fin] using Finset.card_le_univ s
  calc (H K^2)^Fintype.card s≤(H K^2)^3:=pow_le_pow_right₀ (one_le_pow₀ hk) card
       _≤(4*((g N per v)⁻¹)^2)^6:=by rw [←pow_mul];exact pow_le_pow_left₀ (by linarith) paid 6
       _=(4:ℝ)^6*((g N per v)⁻¹)^12:=by ring

end YM.Integration.WilsonOriginalObservedRoseVaneCaliber
end
