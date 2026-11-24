import YM.Integration.WilsonIndependentConditionalCoverLine

/-! Absolute convergence at each held set of slots on an authentic period
family. The two moving contraction ends are summed together. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoverFare
open Filter Function WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Bank
open Lattice Laurent Bloch Matrix
open scoped Classical BigOperators Topology
variable {α β:Type}{p:Cover}{r k:ℕ}

private theorem extents (x:dock Cover β r)(y:dock Cover α k):
    ∀ᶠ n:Side in atTop,brims (tor n) (wrap n p) (slideC n x) (slideC n y)=brims terrain p x y:=by
  let v:=Sum.elim (stud p x) (Prod.fst ∘ y)
  let z:=fun i=>(v i,())
  filter_upwards [touched z] with n hn
  refine (?_:league (tor n) _=league (tor n) _).trans hn
  apply congrArg (league (tor n))
  funext i
  cases i with
  | inl j=>exact congrFun (comps_head p (wrap n)) j
  | inr j=>rfl

theorem offer {V:Type}[NormedAddCommGroup V]{J:berth α β V k r}{F:canal Cover α β V k r}
    (h:Paves p J F):∃ s C,0<s ∧ Peb terrain p s C F:=by
  obtain ⟨s,C,hs,H⟩:=h.price
  refine ⟨s,C,hs,H.exists.choose_spec.1,fun x y=>le_of_tendsto (h.point x y).norm ?_⟩
  filter_upwards [H,extents (p:=p) x y] with n hn hn'
  rw [←hn'];exact hn.2 _ _

theorem original [Fintype α] {J:berth α β ℝ k r}{F:canal Cover α β ℝ k r}
    (h:Paves p J F)(x:dock Cover β r):Summable (F x):=by
  obtain ⟨s,C,hs,hC⟩:=offer h
  exact (hC.cache hs le_rfl x).2.1.of_norm

end YM.Integration.WilsonIndependentConditionalCoverFare
