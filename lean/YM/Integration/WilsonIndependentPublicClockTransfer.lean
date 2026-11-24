import YM.Integration.WilsonIndependentPublicReportBias
import YM.WilsonCoeffUV.Vacuum.UV.Relation

/-! At finite order the change of reporting coupling is a finite signed
matrix on the original bare coefficients. Its price depends only on the
preselected unmarked bias jets. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentPublicClockTransfer
open RegulatorIR RegulatorIR.Binding RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Profiles
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries
open WilsonIndependentPublicReportClock WilsonIndependentPublicReportBias
open scoped Classical BigOperators

theorem coefficients (K:Feeds)(D q:ℕ)(A:Writing):
    let B:=back (beta K)
    coeff q (cleared K D A)=∑ j∈Finset.range (q+1),
      coeff j A*coeff (q-j) (B^j*(B⁻¹)^D):=by
  dsimp only
  let B:=back (beta K)
  rw [cleared,WilsonIndependentPublicReportBias.backward,restoring,mul_comm,←reel_apply]
  change coeff q (reel B A*(B⁻¹)^D)=_
  rw [(Equal.mul (filtered (show constantCoeff (reel B X)=0 by rw [reel_X];simp)
    (shave A (q+1))) (Equal.refl ((B⁻¹)^D) _)) q q.lt_succ_self,
    map_sum,Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul (reel B),map_pow (reel B),reel_X,reel_C,mul_pow]
  rw [show C (coeff j A)*(B^j*X^j)*(B⁻¹)^D=(C (coeff j A)*(B^j*(B⁻¹)^D))*X^j by ring,
    coeff_mul_X_pow',if_pos (by have hj':=Finset.mem_range.mp hj;omega),coeff_C_mul]

theorem income (q D:ℕ):∃ C:ℝ,0≤C ∧ ∃ k:ℕ,∀ (K:Feeds)(x:ℝ),1≤x →
    (∀ j,j ≤ q → ‖coeff j (beta K)‖≤x) → ∀ (A:Writing)(e:ℝ),
    (∀ j,j ≤ q → ‖coeff j A‖≤e) → ‖coeff q (cleared K D A)‖≤C*x^k*e:=by
  choose k c hc pay using fun j:ℕ=>scalar_receipt (q-j) j D
  let menu:=Finset.range (q+1)
  let d:=∑ j∈menu,k j
  refine ⟨∑ j∈menu,c j,Finset.sum_nonneg (fun j _=>hc j),d,?_⟩
  intro K x hx bound A e hA
  have ex:0≤e:=(norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hcost (j:ℕ)(hj:j∈menu):
      ‖coeff (q-j) ((back (beta K))^j*((back (beta K))⁻¹)^D)‖≤c j*x^d:=by
    let gate:ScalarGate (q-j):=⟨x,0,hx,le_rfl,beta K,beta K,origin K,origin K,fun i hi=>
      ⟨bound i (by omega),bound i (by omega),by simp⟩⟩
    have h:= (pay j gate).main
    have leD:k j≤d:=Finset.single_le_sum (fun a _=>Nat.zero_le (k a)) hj
    exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx leD) (hc j))
  rw [coefficients]
  calc
    _ ≤ ∑ j∈menu,‖coeff j A*coeff (q-j) ((back (beta K))^j*((back (beta K))⁻¹)^D)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j∈menu,e*(c j*x^d) :=by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hA j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
        (hcost j hj) (norm_nonneg _) ex
    _ = _ :=by rw [←Finset.mul_sum,←Finset.sum_mul];ring

end YM.Integration.WilsonIndependentPublicClockTransfer
