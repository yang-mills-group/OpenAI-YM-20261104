import YM.Integration.WilsonIndependentSpoutPrimitiveWindow
import YM.Integration.WilsonIndependentSpoutThermalMark

/-! An actual centered parent whose local predictor hits a fixed tested child
has the same covering representative on all sufficiently large ordinary tori. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOrdinaryUnfold
open Filter Function Lattice RG Laurent Bloch Metric WilsonCoeffUV WilsonCoeffUV.Bank FreeResolvent Work.F08
open RegulatorIR RegulatorIR.Prim RegulatorIR.Geometry WilsonCoeffUV.Mer
open scoped Classical BigOperators Topology

theorem blocked (L:Side)(z d:Cover):
    ∀ᶠ n:Side in atTop,∀b:Site n,
      wrap (n*L) (L.val • lift b+d)=wrap (n*L) z→L.val • lift b+d=z:=by
  obtain ⟨⟨q,u⟩,hq⟩:=
    (tile_design L).2 (z-d)
  change L.val • q+lift u=z-d at hq
  filter_upwards [lift_ready q] with n hn
  intro b equal
  have v:wrap (n*L) (L.val • lift b)=wrap (n*L) (L.val • q+lift u):=by
    rw [hq,map_sub,←equal,map_add,add_sub_cancel_right]
  let g:=ratioN L n
  let a:Cloth (Co L Unit):=(lift b,(0,()))
  let b':Cloth (Co L Unit):=(q,(u,()))
  have pact:foldUnder (n*L) (panel L Unit a)=foldUnder (n*L) (panel L Unit b'):=by
    refine Prod.ext ?_ ?_
    · change wrap (n*L) (L.val • lift b+lift (0:Site L))=_
      rw [coat0,add_zero]
      exact v
    · rfl
  have folded:foldUnder n a=foldUnder n b':=by
    apply (splitCo g Unit).symm.injective
    exact (panel_wrap g a).symm.trans (pact.trans (panel_wrap g b'))
  have node:b=wrap n q:=by simpa only [a,b',foldUnder,wrap_lift] using congr_arg Prod.fst folded
  have zero:(0:Site L)=u:=congr_arg (fun j=>j.2.1) folded
  rw [node,hn]
  rw [←zero,coat0,add_zero] at hq
  rw [hq,sub_add_cancel]

end YM.Integration.WilsonIndependentSpoutOrdinaryUnfold
