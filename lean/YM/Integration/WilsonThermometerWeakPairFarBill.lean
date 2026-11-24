import YM.Integration.WilsonThermometerWeakRunningCoordinates
import YM.GapsContact.Power.Grade

/-! Uniform moving-radius cost of the physical field left by finite-sheet detection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairFarBill
open Function Filter Set Extraction Spec Table GapsContact GapsContact.Ascent GapsContact.Power
open EveryPhase
open scoped Classical Topology
universe u
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}(F:Final C f S)
theorem original {simple:G.Simple}{L:Almanac F}(H:Roll.{u} F simple L)(d:ℕ){ε:ℝ}(ep:0<ε):
    ∃B:ℝ,0<B ∧ ∀ᶠ t in 𝓝[>] (0:ℝ),∀x:S.Field d, cost F d t x ≤ B/t^((d:ℝ)+ε)*‖x‖:=by
  obtain ⟨H₀,Z,𝓛,_,_,_,_,_,_,bliss,_⟩:=H.commonFrame
  obtain ⟨R,A,market⟩:=marketplace0 F simple bliss d ε ep
  letI : FiniteDimensional ℝ (S.Field d):=Module.Finite.trans ℂ _
  obtain ⟨K,kp,wallet⟩:=metric_paid (chip F.room.kernel d R) (fun x:S.Field d=>‖x‖)
    (chip_cont F.room.kernel d R market.road) continuous_norm (fun c x=>chip_real F.room.kernel R x c)
    (fun c x=>norm_smul c x) (fun _ h=>norm_pos_iff.mpr h)
  refine ⟨A*R^((d:ℝ)+ε)*K,mul_pos (mul_pos (zero_lt_one.trans_le market.budget)
    (Real.rpow_pos_of_pos market.road _)) (zero_lt_one.trans_le kp),?_⟩
  filter_upwards [(ge_mem_nhds market.road).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t mt tp
  intro x
  have pay:=market.left (show R∈Ioc (0:ℝ) R from ⟨market.road,le_rfl⟩) (show t∈Ioc (0:ℝ) R from ⟨tp,mt⟩) x
  apply pay.trans
  calc _ ≤ A*(R/t)^((d:ℝ)+ε)*(K*‖x‖):=mul_le_mul_of_nonneg_left (wallet x)
              (mul_nonneg (zero_le_one.trans market.budget) (Real.rpow_nonneg (div_nonneg market.road.le tp.le) _))
       _ = _ := by rw [Real.div_rpow market.road.le tp.le];ring
end YM.Integration.WilsonThermometerWeakPairFarBill
end
