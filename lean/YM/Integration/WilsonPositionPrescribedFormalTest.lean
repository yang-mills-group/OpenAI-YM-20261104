import YM.Integration.WilsonPositionPrescribedAllocations

/-! The numerical test of the actual independent MS kernel with the actual
formal near-identity change, truncated in both arguments. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedFormalTest
open Function PowerSeries Filter Set Finset Metric MeasureTheory Extraction Table Spec OPE Climb PhysMS Maxwell
open Trace.Pilot XSpace XSpace.Normalize FVA2 FVA2.Arrival MS MS.Land
open scoped Topology BigOperators Classical
variable {G : Gauge} (V : Store G) (ν : ℝ)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (d q : ℕ)

def raw (t : ℝ) : Prediction G d :=
  ∑ k : Fin (q+1), (t:ℂ)^k.val • Reg.State.kernel ν T d k.val

def turn (t : ℝ) : Change G d :=
  ∑ i∈range q, t^(i+1) • Reg.State.root ν V T d (i+1)

private theorem splitSum {E : Type*} [AddCommMonoid E] (u : ℕ→E) :
    (∑ i : Fin (q+1),u i.val)=u 0 + ∑ j∈range q,u (j+1) := by
  rw [Fin.sum_univ_eq_sum_range,Finset.sum_range_succ',add_comm]

theorem raw_read (t : ℝ) {n : ℕ} (φ : Test n) (v : Fin n→Sec G d) :
    raw ν T d q t n φ v =
      ∑ k : Fin (q+1),(t:ℂ)^k.val * Reg.State.kernel ν T d k.val n φ v := by
  simp only [raw,Finset.sum_apply,Pi.smul_apply,LinearMap.sum_apply,_root_.sum_apply,
    LinearMap.smul_apply,_root_.smul_apply,smul_eq_mul]

theorem menu (t : ℝ) : (V.survey d).purse (raw ν T d q t) =
    WilsonPositionPrescribedTariff.target V ν T d q t := by
  funext i a
  let aScope := (V.survey d).scope i
  rw [Fray.purse,raw_read,splitSum q (fun k=>(t:ℂ)^k * Reg.State.kernel ν T d k aScope.n aScope.t (fun j=>Module.finBasis ℝ (Sec G d) (a j)))]
  simp only [pow_zero,one_mul,Reg.State.freeT,WilsonPositionPrescribedTariff.target,
    Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rfl

private def evalChange (p : Sec G d) : Change G d→ₗ[ℝ] Sec G d where
  toFun u := u.val p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fields (t : ℝ) (p : Sec G d) :
    stand (turn V ν T d q t) p =
    ∑ k : Fin (q+1),(t:ℂ)^k.val • coeff k.val (Reg.State.chooseL ν V T d) p := by
  classical
  rw [splitSum q (fun k=>(t:ℂ)^k • coeff k (Reg.State.chooseL ν V T d) p),coeff_zero_eq_constantCoeff_apply,Reg.State.baseL,pow_zero,one_smul,stood]
  change p + evalChange d p (∑ i∈range q,t^(i+1) • Reg.State.root ν V T d (i+1)) = p + _
  rw [map_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [map_smul,Reg.State.chooseL,pos_decked _ (Nat.succ_ne_zero i),←Complex.ofReal_pow]
  rfl

/-- Uniform numerical price on any of the actual held signed test menus for
the independently filed transformed prediction. No presumed analytic Taylor
series of the implicit variable is used. -/
theorem tested {n : ℕ} (φ : Test n) (v : Fin n→Sec G d) :
    ∃ C : ℝ,0≤C ∧ ∀ t : ℝ, |t|≤1 →
      ‖recruit (stand (turn V ν T d q t)) (raw ν T d q t) n φ v -
        ∑ e∈range (q+1),(t:ℂ)^e * Reg.State.author ν V T d e n φ v‖ ≤ C * |t|^(q+1) := by
  obtain ⟨C,non,bound⟩ := WilsonPositionPrescribedAllocations.miss q (Reg.State.chooseL ν V T d)
    (Reg.State.kernel ν T d) φ v
  refine ⟨C,non,fun t ht=>?_⟩
  change ‖raw ν T d q t n φ (fun i=>stand (turn V ν T d q t) (v i)) - _‖ ≤ _
  simp_rw [fields]
  rw [raw_read]
  exact bound t ht

end YM.Integration.WilsonPositionPrescribedFormalTest

