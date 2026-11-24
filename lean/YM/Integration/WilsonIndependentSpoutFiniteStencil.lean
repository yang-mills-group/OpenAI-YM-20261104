import YM.Integration.WilsonIndependentSpoutOrdinaryUnfold
import YM.Integration.WilsonIndependentSpoutPrimitiveFronts

/-! Uniform unwrapping of all of the finite circuit's Haar and spring
stencils at each fixed angular link. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutFiniteStencil
open Filter Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Geometry.Field RegulatorIR.Prim
open WilsonIndependentSpoutOrdinarySpring WilsonIndependentSpoutPrimitiveWindow
open scoped Classical Topology

abbrev Raw (G:Gauge)(n:Side):=Edge (Site n)×G.ColorIndex
abbrev Keys (P:Patch)(n:Side):=Edge (Site (n*P.L))⊕Edge (Site n)

def coordinates {G:Gauge}(n:Side)(x:Foot G):Raw G n:=(around n x.1,x.2)
def fold {G:Gauge}(P:Patch)(n:Side):KFoot G→Raw G (n*P.L)⊕Raw G n:=
  Sum.map (coordinates (n*P.L)) (coordinates n)
def original {P:Patch}{n:Side}:Keys P n→Branchix:=Sum.map peg peg

private theorem equality {G:Gauge}{n:Side}{x y:Foot G}
    (same:coordinates n x=coordinates n y)(node:x.1.1=y.1.1):x=y:=
  Prod.ext (Prod.ext node (congr_arg (fun q=>q.1.2) same)) (congr_arg (fun z:Raw G n=>z.2) same)

private theorem center {G:Gauge}{n:Side}{b:Edge (Site n)}{y x:Foot G}
    (same:coordinates n x=coordinates n y)(aperture:lift (wrap n y.1.1)=y.1.1)(point:x.1=peg b):
    x=y:=by
  apply equality same
  calc x.1.1=lift (wrap n x.1.1):=by rw [point];simp [WilsonIndependentSpoutOrdinarySpring.peg]
       _=lift (wrap n y.1.1):=congr_arg lift (congr_arg (fun z=>z.1.1) same)
       _=y.1.1:=aperture

theorem genuine {G:Gauge}(P:Patch)(y:KFoot G):
    ∀ᶠ n:Side in atTop,∀(b:Keys P n)(x:KFoot G),x∈sites G P (original b)→
      fold P n x=fold P n y→x=y:=by
  classical
  cases y with
  | inl y=>
    have edges:∀ᶠ n:Side in atTop,∀v:Axis,∀d∈lantern P (0,v),∀q:Site n,
        wrap (n*P.L) (P.L.val • lift q+d.1)=wrap (n*P.L) y.1.1→P.L.val • lift q+d.1=y.1.1:=
      eventually_all.mpr fun v=>(eventually_all_finset _).mpr fun d _=>
        WilsonIndependentSpoutOrdinaryUnfold.blocked P.L y.1.1 d.1
    filter_upwards [edges,(multi_end P.L).eventually (lift_ready y.1.1)] with n localFixed centerFixed
    rintro (b|b) (x|x) inside equal
    · apply congr_arg Sum.inl
      obtain ⟨j,_,w⟩:=Finset.mem_image.mp (show Sum.inl x∈sites G P (.inl (peg b)) from inside)
      exact center (Sum.inl.inj equal) centerFixed (congr_arg Prod.fst (Sum.inl.inj w)).symm
    · simp [fold] at equal
    · apply congr_arg Sum.inl
      have ge:coordinates (n*P.L) x=coordinates _ y:=Sum.inl.inj equal
      apply equality ge
      rcases Finset.mem_union.mp (show Sum.inl x∈sites G P (.inr (peg b)) from inside) with hi|hi
      · obtain ⟨w,hw,wu⟩:=Finset.mem_image.mp hi
        have eq:w=x:=Sum.inl.inj wu
        have edge:x.1∈lantern P (lift b.1,b.2):=eq ▸ (Finset.mem_product.mp hw).1
        rw [WilsonIndependentSpoutPrimitiveFronts.shifted,rangeE] at edge
        obtain ⟨d,hd,hit⟩:=Finset.mem_image.mp edge
        have at_x:P.L.val • lift b.1+d.1=x.1.1:=congr_arg Prod.fst hit
        rw [←at_x]
        apply localFixed b.2 d hd b.1
        rw [at_x]
        exact congr_arg (fun a=>a.1.1) ge
      · obtain ⟨j,_,bad⟩:=Finset.mem_image.mp hi
        contradiction
    · simp [fold] at equal
  | inr y=>
    filter_upwards [lift_ready y.1.1] with n centerFixed
    rintro (b|b) (x|x) inside equal
    · simp [fold] at equal
    · obtain ⟨j,_,bad⟩:=Finset.mem_image.mp (show Sum.inr x∈sites G P (.inl (peg b)) from inside)
      contradiction
    · simp [fold] at equal
    · apply congr_arg Sum.inr
      rcases Finset.mem_union.mp (show Sum.inr x∈sites G P (.inr (peg b)) from inside) with hf|hc
      · obtain ⟨j,_,bad⟩:=Finset.mem_image.mp hf
        contradiction
      · obtain ⟨j,_,eq⟩:=Finset.mem_image.mp hc
        exact center (Sum.inr.inj equal) centerFixed (congr_arg Prod.fst (Sum.inr.inj eq)).symm

end YM.Integration.WilsonIndependentSpoutFiniteStencil
