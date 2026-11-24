import YM.Integration.WilsonOriginalOpticalCouplingBand
import YM.Integration.WilsonAddressedPublicFirstRoseElection

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseEnrolledCash
open Function Filter Finset Lattice Wilson RG Pert.Asymptotics
open PhysicalNext PhysicalNext.Repeat Legato
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G)
local notation "g" N:max per:max i:max => regulatorRun R.family N per i
local notation "H" i:max => R.family.path.levels.clock.hatBeta i

def roof {n:ℕ}(B:ℝ)(caps:Fin n→ℝ):ℝ:=max (max 1 (B^n)) (∑i,|caps i|)

/-- The actual semester with allowance one pays the same order-one Laurent power
at the genuine capture and infrared dates. Its multiplicative constant can depend
on the semester and on the finite set of tests. -/
theorem original (simple:G.Simple){n:ℕ}(B:ℝ)(bp:1≤B)(caps:Fin n→ℝ)(A:ℕ):
    let C:=roof B caps
    1≤C ∧ ∀ᶠ v:ℕ in atTop,∀{c K N per:ℕ},v≤c → c≤K → K≤N →
    R.family.S.a v/R.family.S.a K≤(H v)^A →
    let rate:=(Real.sqrt (R.family.path.β N per v))^(1:ℝ)*B^n
    0≤rate ∧ 0<g N per v ∧ g N per v≤1 ∧ g N per K≤1 ∧
      rate≤C*(3*(g N per c)⁻¹)^1 ∧ (∀i,caps i≤C*(3*(g N per c)⁻¹)^1) ∧
      rate≤C*(3*(g N per v)⁻¹)^1 ∧ ∀i,caps i≤C*(3*(g N per v)⁻¹)^1 :=by
  intro C
  have one:1≤C:=(le_max_left ..).trans (le_max_left ..)
  have school:B^n≤C:=(le_max_right ..).trans (le_max_left ..)
  have covered(i:Fin n):caps i≤C:=(le_abs_self _).trans ((single_le_sum (f:=fun k:Fin n=>|caps k|) (fun k _=>abs_nonneg _) (mem_univ i)).trans (le_max_right ..))
  obtain ⟨head,thermal⟩:=eventually_atTop.mp (WilsonOriginalOpticalCouplingBand.cold R simple 1)
  refine ⟨one,?_⟩
  filter_upwards [eventually_ge_atTop head,WilsonOriginalOpticalCouplingBand.scale R simple A] with v late comparative
  intro c K N per vc ck kn mesh rate
  have cold {i:ℕ}(vi:v ≤ i)(live:i≤N):1≤(g N per i)⁻¹:=thermal i (late.trans vi) N per live
  have warm {i:ℕ}(vi:v ≤ i)(live:i≤N):g N per i≤1:=by
    have pos:=ActualRunKernelPackets.regulator_pos R N per i live
    have hit:=cold vi live
    rw [le_inv_comm₀ (by norm_num : (0:ℝ)<1) pos,inv_one] at hit
    exact hit
  have vn:=vc.trans (ck.trans kn)
  have zero:0≤C:=by linarith
  have gp:=ActualRunKernelPackets.regulator_pos R N per v vn
  have coupon:rate=(g N per v)⁻¹*B^n:=by
    change (Real.sqrt _)^(1:ℝ)*_=((Real.sqrt _)⁻¹)⁻¹*_
    rw [Real.rpow_one,inv_inv]
  have transit: (g N per v)⁻¹≤2*(g N per c)⁻¹:=(comparative vc ck kn mesh).2.2.2.1
  have cp:=ActualRunKernelPackets.regulator_pos R N per c (ck.trans kn)
  have first:1≤3*(g N per c)⁻¹:=by linarith only [cold vc (ck.trans kn)]
  have last:1≤3*(g N per v)⁻¹:=by linarith only [cold le_rfl vn]
  have charge {X:ℝ}(replace:(g N per v)⁻¹≤X):rate≤C*X:=by
    rw [coupon,mul_comm C]
    exact mul_le_mul replace school (pow_nonneg (by linarith : 0≤B) _) ((inv_nonneg.mpr gp.le).trans replace)
  simp only [pow_one]
  refine ⟨?_,gp,warm le_rfl vn,warm (vc.trans ck) kn,charge ?_,
    fun i=>(covered i).trans (le_mul_of_one_le_right zero first),charge ?_,
    fun i=>(covered i).trans (le_mul_of_one_le_right zero last)⟩
  · rw [coupon]
    exact mul_nonneg (inv_nonneg.mpr gp.le) (pow_nonneg (by linarith) _)
  · linarith only [transit,inv_pos.mpr cp]
  · linarith only [inv_pos.mpr gp]

end YM.Integration.WilsonReceivedChronologicalFixedRoseEnrolledCash
end
