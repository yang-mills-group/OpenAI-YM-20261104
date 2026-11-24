import YM.Integration.WilsonPhysicalHistoryKioskFirst
import YM.FormalOPE.RG10.MarkerLog

/-! The complete marked forced gas in a measured Wilson read, normalized by
the same true vacuum as every remaining occupied component. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskGas
open Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums QuadraticLocal
open Extra.Trajectories
open QuadraticLocal.Fusion.Attached
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V T I : Type} [DecidableEq V] [Fintype V]
  {o : V → Site n} {R : Census V} {p : BudgetPoint} {X : Activities G n}
  (K : Hard T p X.forced X.K o R) (L : Lamps T I G p o R)

def gas (t : T) (U : Config G n) : Poly R := ∑' a, packet X p (K.hard t) U a

def logged (t : T) (U : Config G n) : Poly R :=
  connected (((X.gas p U : ℂ)⁻¹) • gas K t U)

theorem physical {F : T → Config G n → Poly R} (held : ReadZone T p X K F L.log)
    (t : T) (U : Config G n) (positive : (F t U).part R.quiet ≠ 0) :
    connected ((((F t U).part R.quiet)⁻¹) • F t U) = L.log t U + logged K t U := by
  classical
  obtain ⟨summed, c, field⟩ := held t U
  have whole : F t U = c • (Poly.pass (L.log t U) * gas K t U) := field
  have absent : (L.log t U).part R.quiet = 0 := by
    by_cases hs : Summable (fun b => L.frame b t U)
    · exact Lamps.quiet_of_hasSum t U hs
    rw [Lamps.log, tsum_eq_zero_of_not_summable hs]
    rfl
  have neutral : (gas K t U).part R.quiet = (X.gas p U : ℂ) :=
    Hard.packet_of_quiet K t U summed
  have head : (F t U).part R.quiet = c * (X.gas p U : ℂ) := by
    rw [whole, Poly.part_smul, Poly.quiet_mul, Poly.pass_part _ absent, neutral, one_mul]
  have nonzero := mul_ne_zero_iff.mp (head ▸ positive)
  have factor : ((F t U).part R.quiet)⁻¹ * c = (X.gas p U : ℂ)⁻¹ := by
    rw [head, mul_inv_rev, mul_assoc, inv_mul_cancel₀ nonzero.1, mul_one]
  have identity : (((F t U).part R.quiet)⁻¹) • F t U =
      Poly.pass (L.log t U) * (((X.gas p U : ℂ)⁻¹) • gas K t U) := calc
    _ = (((F t U).part R.quiet)⁻¹) • (c • (Poly.pass (L.log t U) * gas K t U)) :=
      congrArg (fun z : Poly R => (((F t U).part R.quiet)⁻¹) • z) whole
    _ = _ := by rw [smul_smul, factor, mul_smul_comm]
  have unit : ((((X.gas p U : ℂ)⁻¹) • gas K t U).part R.quiet) = 1 := by
    rw [Poly.part_smul, neutral, inv_mul_cancel₀ nonzero.2]
  rw [identity, FormalOPE.RG10.PolyUtil.conn_mul (Poly.pass_part _ absent) unit,
    FormalOPE.RG10.PolyUtil.conn_pass _ absent, logged]

end YM.Integration.WilsonPhysicalHistoryKioskGas
end
