import YM.Comparison.RG02.Order.Pay

/-! The nilpotence length of a normalized finite thermal polynomial is set by the number
of physical marks, at every thermal order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogDegree
open Function Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}

omit [Fintype V] in
private theorem detectable (p:Truncated Γ) (vanish:∀t:ℂ,formula t p=0):p=0:=by
  classical
  ext j s
  let a:Polynomial ℂ:=∑i∈p.support,Polynomial.monomial i ((p.coeff i).part s)
  have h:∀t:ℂ,a.eval t=0:=by
    intro t
    have ht:=congrArg (fun y:Poly Γ=>y.part s) (vanish t)
    rw [formula_sum,Poly.part_sum] at ht
    simpa [a,Polynomial.eval_finsetSum,mul_comm] using ht
  have z:a=0:=Polynomial.funext (fun t=>by simp [h t])
  by_cases hj:j∈p.support
  · have coeff:=congrArg (fun q:Polynomial ℂ=>q.coeff j) z
    simpa [a,Polynomial.coeff_sum,Polynomial.coeff_monomial,hj] using coeff
  · simp [Polynomial.notMem_support_iff.mp hj]

theorem ends {n:ℕ} (p:Truncated Γ) (quiet:∀t:ℂ,(formula t p).part Γ.quiet=1)
    (later:Fintype.card V<n):(1-p)^n=0:=by
  apply detectable
  intro t
  rw [map_pow,map_sub,map_one]
  have neutral:(1-formula t p).part Γ.quiet=0:=by
    rw [Extra.Trajectories.part_sub,Poly.one_part,if_pos rfl,quiet t,sub_self]
  exact Order.ends neutral (fun s=>s.val.card_le_univ) later

theorem reduced {r:ℕ} {x:Grade Γ r} (lead:UnitLeading x):
    logSeries (Fintype.card V+r) (render (ratio x))=
      logSeries (Fintype.card V) (render (ratio x)):=by
  classical
  unfold logSeries
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.le_add_right _ _))
  intro k _ missing
  have later:Fintype.card V<k+1:=by
    simp only [Finset.mem_range,not_lt] at missing
    omega
  have quiet (t:ℂ):(formula t (render (ratio x))).part Γ.quiet=1:=by
    rw [←value_render];exact leading_trunc_value (ratio_pure lead) _
  rw [ends _ quiet later,mul_zero]

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogDegree
