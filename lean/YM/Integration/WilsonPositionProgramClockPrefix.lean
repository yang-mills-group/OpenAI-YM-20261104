import YM.Integration.WilsonPositionProgramRealInverseClock
import YM.Integration.MSFixedRatioClockCharges
import YM.WilsonCoeffUV.Vacuum.Step.Ratio
import YM.WilsonCoeffUV.Winding.Mark

/-! A finite real Wilson reset uses only its declared grades of the inverse-temperature series. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramClockPrefix
open Function Filter Set Finset PowerSeries Comparison.RG02 Comparison.RG02.Adjacent
open Comparison.RG02.Moving Comparison.RG02.Moving.Path RegulatorIR RegulatorIR.Prim
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Winding FormalBulk08
open scoped Topology BigOperators Classical ContDiff

theorem tariff (A:Caliber)(r d:ℕ)(hd:d≤r):coeff d (tale (A.tariff r))=A.measure d:=by
  have represented (S:Finset ℕ):Script (∑ i∈S,C (A.measure i)*X^i)
      (fun t:ℝ=>∑i∈S,t^i*A.measure i):=by
    induction S using Finset.induction_on with
    | empty=>simpa using Script.oneC 0
    | @insert a S h ih=>
      simp only [sum_insert h]
      rw [mul_comm (C (A.measure a))]
      exact Script.add (Script.mul (Script.predicts_pow a) (Script.oneC (A.measure a))) ih
  have reading:=Script.dictates ((A.smooth r).contDiffAt.of_le le_top) (represented (range (r+1)))
  rw [reading,map_sum]
  simp [hd]


theorem reserve {p q:Cost}(h₁:constantCoeff p=1)(h₂:constantCoeff q=1)
    {k:ℕ}(same:∀j≤k,coeff j p=coeff j q)(a b:ℕ):
    coeff k ((back p)^a*((back p)⁻¹)^b)=coeff k ((back q)^a*((back q)⁻¹)^b):=by
  let x:Unit→ℝ:=fun _=>1
  let θ:Unit→ℝ:=fun _=>0
  have h:Brite x θ:=⟨fun _=>le_rfl,fun _=>le_rfl⟩
  have hq(j:ℕ)(le:j≤k):Weft x θ (fun _:Unit=>p) (fun _=>q) j:=by
    refine ⟨0,‖coeff j p‖,norm_nonneg _,fun _=>?_⟩
    change twain (‖coeff j p‖ * 1^0) 0 (coeff j p) (coeff j q)
    rw [←same j le]
    exact ⟨by simp,by simp,by simp⟩
  obtain ⟨D,A,_,bill⟩:=winter_μ h a b (fun _:Unit=>h₁) (fun _=>h₂) hq
  have gap:‖coeff k ((back p)^a*((back p)⁻¹)^b)-coeff k ((back q)^a*((back q)⁻¹)^b)‖≤0:=by
    simpa only [θ,mul_zero] using (bill ()).gap
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm gap (norm_nonneg _)))

theorem reciprocal (K:UnitCost):tale (fun t=>(K.rating t)⁻¹)=(tale K.rating)⁻¹:=by
  have one:constantCoeff (tale K.rating)=1:=by rw [←coeff_zero_eq_constantCoeff_apply,tale_base,K.origin]
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [one])).mpr
  have u:ContDiffAt ℝ ∞ (fun t=>(K.rating t)⁻¹) 0:=(K.smooth.inv (by rw [K.origin]; norm_num)).of_le le_top
  rw [←tale_mul u (K.smooth.of_le le_top)]
  have unit:(fun t=>(K.rating t)⁻¹)*K.rating=ᶠ[𝓝 0] fun _=>1:=by
    filter_upwards [K.bright] with t ht
    exact inv_mul_cancel₀ ht.ne'
  rw [tale_eq contDiffAt_const unit,tale_const,map_one]

theorem original (A:Caliber)(r k j l:ℕ)(hk:k≤r)(P:Cost)(one:constantCoeff P=1)
    (same:∀d≤k,A.measure d=coeff d P):
    ‖motion (money (A.back r) 0 j l) k‖≤rimJ (back P) k l:=by
  rw [MSFixedRatioClockCharges.charged,reciprocal,WilsonPositionProgramRealInverseClock.original]
  by_cases le:j≤k
  · rw [if_pos le,Complex.norm_real]
    have hf:constantCoeff (tale (A.tariff r))=1:=by
      rw [←coeff_zero_eq_constantCoeff_apply,tale_base,A.zero_tariff]
    have matched d (h:d≤k-j):coeff d (tale (A.tariff r))=coeff d P:=by
      have bd:=h.trans (Nat.sub_le k j)
      exact (tariff A r d (bd.trans hk)).trans (same d bd)
    rw [Wine.bill,reserve hf one matched j l]
    exact Finset.single_le_sum (s:=Finset.range (k+1))
      (f:=fun b=>‖coeff (k-b) ((back P)^b*((back P)⁻¹)^l)‖) (fun _ _=>norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le le))
  · rw [if_neg le,norm_zero]
    exact Finset.sum_nonneg (fun _ _=>norm_nonneg _)

end YM.Integration.WilsonPositionProgramClockPrefix
end
