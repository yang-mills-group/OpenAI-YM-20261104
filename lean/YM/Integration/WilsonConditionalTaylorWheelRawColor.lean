import YM.Integration.WilsonConditionalTaylorWheelKineticRead

/-! Rank-two colour isotropy survives undoing the actual unit triangular
coupling change. Thus any preselected axis of the physical course, including
the arbitrary axis fixed before its Run, computes the old kinetic clock. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelRawColor
open Function PowerSeries FormalBulk08 Lattice RG Wilson Precision Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {G:Gauge}

private theorem observed {V:Type} (A:Cost) (unit:constantCoeff A=1) (T:Pal ℝ V) (r:ℕ)
    (f:Ten ℝ V r→ₗ[ℝ]ℝ) (post:∀i,f (Blue.mix A T i r)=0):∀i,f (T i r)=0:=by
  intro i
  induction i using Nat.strong_induction_on with
  | h i earlier=>
    have fromPost:=post i
    rw [Blue.mix,Finset.sum_range_succ,map_add,map_sum] at fromPost
    have gone:∑ j∈Finset.range i, f (coeff (i-j) (A^j*(A⁻¹)^r) • T j r)=0:=by
      apply Finset.sum_eq_zero;intro j mem
      rw [map_smul,earlier j (Finset.mem_range.mp mem),smul_zero]
    simpa only [gone,zero_add,Nat.sub_self,coeff_zero_eq_constantCoeff_apply,map_mul,map_pow,constantCoeff_inv,unit,
      inv_one,one_pow,one_mul,one_smul] using fromPost

private def discrepancy (x y:Edge Cover) (u v w:G.ColorIndex):Ten ℝ (YForest G) 2→ₗ[ℝ]ℝ where
  toFun K:=K ![stone x v,stone y w]-(if v=w then K ![stone x u,stone y u] else 0)
  map_add' A B:=by by_cases h:v=w <;> simp [h]; ring
  map_smul' a A:=by by_cases h:v=w <;> simp [h]; ring

private theorem zero {K:Ten ℝ (YForest G) 2} (med:Medium K) (x y:Edge Cover) (u v w:G.ColorIndex):
    discrepancy x y u v w K=0:=by
  obtain ⟨a,h⟩:=med x y
  change K ![stone x v,stone y w]-(if v=w then K ![stone x u,stone y u] else 0)=0
  rw [h,h,if_pos rfl]
  simp

theorem original {b:ℕ} (Q:Realm G (b+1) Credit.leanC) (N t:ℕ) (live:t<N) (e:ℕ) (u:G.ColorIndex):
    coeff e (pitch Q.draws Q.paid N t)= -Cork.value u (freshet Q.draws Q.paid N t e 2):=by
  let P:=freshet Q.draws Q.paid N t
  let A:=ratioHigh Q.draws Q.paid N t
  have change:actionW Q.draws Q.paid N t=Blue.mix A (lop P):=conduct Q.draws Q.paid live
  have unit:constantCoeff A=1:=back_cc (angle_tilt Q.hG Q.green live)
  have dyed:= (catchment Q.draws Q.paid Q.hG Q.green live.le).paintU
  have actual:Medium (P e 2):=by
    intro x y
    refine ⟨P e 2 ![stone x u,stone y u],?_⟩
    intro v w
    let f:=discrepancy x y u v w
    have read (j:ℕ):f (Blue.mix A (lop P) j 2)=0:=by
      rw [←change];exact zero (loyal_medium dyed) x y u v w
    have checked:=observed A unit (lop P) 2 f read e
    have uncut:lop P e 2=P e 2:=by simp [lop]
    rw [uncut] at checked
    exact sub_eq_zero.mp checked
  rw [pitch,stellar_read]
  exact WilsonConditionalTaylorWheelKineticRead.original (P e 2) actual u

end YM.Integration.WilsonConditionalTaylorWheelRawColor
end

