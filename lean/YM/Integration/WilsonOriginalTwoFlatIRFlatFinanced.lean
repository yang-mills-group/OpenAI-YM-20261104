import YM.Integration.WilsonOriginalTwoFlatIRFlatMarked

/-! Restoring the physical complex dose at each occupied slot preserves
the original connected/ordinary recursion over the real covered coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatFinanced
open Finset Marker WilsonCoeffUV.Wheel.Mark
open WilsonOriginalTwoFlatIRFlatMarked (field roster)
open WilsonOriginalTwoFlatIRFlatSeries (unitSeries)
open scoped Classical BigOperators
variable {V:Type}[DecidableEq V]

def wallet (x:V→ℂ)(s:Finset V):PowerSeries ℝ→+PowerSeries ℂ where
  toFun a:=PowerSeries.C (∏v∈s,x v)* PowerSeries.map Complex.ofRealHom a
  map_zero':=by simp
  map_add' a b:=by simp [mul_add]

omit [DecidableEq V] in
theorem coeff (x:V→ℂ)(s:Finset V)(a:PowerSeries ℝ)(e:ℕ):
    PowerSeries.coeff e (wallet x s a)=(∏v∈s,x v)*Complex.ofReal (PowerSeries.coeff e a):=by
  change PowerSeries.coeff e (PowerSeries.C _ * (PowerSeries.map Complex.ofRealHom) a)=_
  rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_map]; rfl

private theorem product (x:V→ℂ){s t:Finset V}(sub:t⊆s)(a b:PowerSeries ℝ):
    wallet x s (a*b)=wallet x t a*wallet x (s\t) b:=by
  have dis:Disjoint t (s\t):=Finset.disjoint_left.mpr (fun v hv h=>(mem_sdiff.mp h).2 hv)
  have split:(∏v∈s,x v)=(∏v∈t,x v)*∏v∈s\t,x v:=by rw [←prod_union dis,union_sdiff_of_subset sub]
  simp only [wallet,AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_mul]
  rw [split,map_mul]; ring

theorem funded (x:V→ℂ)(M L:Sac V (PowerSeries ℝ))(law:Equation M L):
    Equation (fun s=>wallet x s (M s)) (fun s=>wallet x s (L s)):=by
  refine ⟨?_,?_,?_⟩
  · change wallet x ∅ (M ∅)=1; rw [law.1]; simp [wallet]
  · change wallet x ∅ (L ∅)=0; rw [law.2.1,map_zero]
  · funext s
    have recurrence:=congrFun law.2.2 s
    change s.card • M s=∑t∈s.powerset,(t.card • L t)*M (s\t) at recurrence
    change s.card • wallet x s (M s)=∑t∈s.powerset,(t.card • wallet x t (L t))*wallet x (s\t) (M (s\t))
    rw [←map_nsmul,recurrence,map_sum]
    apply sum_congr rfl
    intro t ht; rw [product x (mem_powerset.mp ht),map_nsmul]

open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel
variable [Fintype V] {G:Gauge}{D:V→ℕ}
theorem original (x:V→ℂ)(t:Case D)(Y:∀S:Finset V,Era G (Pen D S))(empty:Y ∅=0):
    (fun S=>wallet x S (unitSeries t S (levelsO Y S)))=
      field (roster univ (fun S=>wallet x S (unitSeries t S (Y S)))):=by
  letI : IsAddTorsionFree (PowerSeries ℂ):=⟨by
    intro n hn a b h; ext1 e
    apply (smul_right_inj (M:=ℂ) hn).mp
    exact (map_nsmul (PowerSeries.coeff e) n a).symm.trans
      ((congrArg (PowerSeries.coeff e) h).trans (map_nsmul (PowerSeries.coeff e) n b))⟩
  apply WilsonOriginalTwoFlatIRFlatMarked.original
  apply funded
  exact WilsonOriginalTwoFlatIRFlatSeries.original Y empty t

end YM.Integration.WilsonOriginalTwoFlatIRFlatFinanced
end
