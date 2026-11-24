import YM.Integration.WilsonMacroscopicRichFiniteSwitch

/-! The unchanged partners that accompany one substituted filed slot, in an
ordering fixed on the input type before any cutoff or observation. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichOrderedPartners
open scoped BigOperators
variable {V:Type}[Fintype V](p q:V → ℂ)

def partners (i:V):ℂ:=
  let e:=Fintype.equivFin V
  WilsonMacroscopicRichFiniteSwitch.rest (p ∘ e.symm) (q ∘ e.symm) (e i)

theorem original:(∏i,p i)-(∏i,q i)=∑i,(p i-q i)*partners p q i:=by
  let e:=Fintype.equivFin V
  have h:=WilsonMacroscopicRichFiniteSwitch.original (p ∘ e.symm) (q ∘ e.symm)
  calc
    _=(∏i,p (e.symm i))-(∏i,q (e.symm i)):=by rw [e.symm.prod_comp p,e.symm.prod_comp q]
    _=∑i:Fin (Fintype.card V),(p (e.symm i)-q (e.symm i))*partners p q (e.symm i):=by
      simpa only [partners,←show Fintype.equivFin V=e from rfl,Function.comp_apply,Equiv.apply_symm_apply] using h
    _=_:=e.symm.sum_comp (fun i=>(p i-q i)*partners p q i)

theorem continuousPartners {X:Type*}[TopologicalSpace X]
    (P Q:V → X → ℂ)(cP:∀i,Continuous (P i))(cQ:∀i,Continuous (Q i))(i:V):
    Continuous (fun x=>partners (fun j=>P j x) (fun j=>Q j x) i):=by
  unfold partners WilsonMacroscopicRichFiniteSwitch.rest
  apply continuous_finsetProd;intro j _
  split
  · apply cQ
  · apply cP

end YM.Integration.WilsonMacroscopicRichOrderedPartners
