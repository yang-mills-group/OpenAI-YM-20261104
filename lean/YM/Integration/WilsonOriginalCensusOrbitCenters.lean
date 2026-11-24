import YM.Integration.WilsonOriginalCensusPageOrbits
import YM.Integration.WilsonPointChildRelativeLift

/-! The same common translation acts on all real old source centers. In the
anchored cover, its lift is a single period of the physical held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusOrbitCenters
open Function Finset Lattice RG Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalConnectedPeriodPage (Deck)
open WilsonOriginalLocatedDeckAction (steps step value)
open WilsonOriginalRelativePageTail (locate retained chosen)
open WilsonPointChildRelativeLift (centers)
open scoped Classical BigOperators
variable {n X:Side} (h:n.val∣X.val) {ι:Type}

def escort (site:ι→Site X)(d:Deck h):(ι→Fin (Pages n X))≃(ι→Fin (Pages n X)):=
  Equiv.piCongrRight fun i=>steps h (splitter h (site i)) d

def shifted (site:ι→Site X)(d:Deck h)(i:ι):Site X:=d.val+site i

theorem located (site:ι→Site X)(d:Deck h)(p:ι→Fin (Pages n X))(i:ι):
    locate h (shifted h site d) (escort h site d p) i=d.val+locate h site p i:=by
  change (page h (splitter h (d.val+site i)) (step h (splitter h (site i)) d (p i))).val=_
  rw [map_add,show splitter h d.val=0 from d.property,zero_add,value]
  rfl

theorem home (site:ι→Site X)(d:Deck h):
    escort h site d (retained h site)=retained h (shifted h site d):=by
  funext i
  apply (page h (splitter h (shifted h site d i))).injective
  apply Subtype.ext
  change locate h (shifted h site d) (escort h site d (retained h site)) i=locate h _ (retained h _) i
  rw [located,chosen,chosen]
  rfl

def motion (root:Site X)(d:Deck h):Cover:=lift (d.val+root)-lift root

theorem period (root:Site X)(d:Deck h):wrap n (motion h root d)=0:=by
  rw [←Macrame.branch h,motion,map_sub,wrap_lift,wrap_lift,add_sub_cancel_right]
  exact d.property

variable [DecidableEq ι] (J:Finset ι)(a:ι)(root:Site X)(site:(J.erase a)→Site X)

def layout (p:(J.erase a)→Fin (Pages n X)):ι → Cover:=
  toe J a (lift root) (centers h J a root site p)

theorem all (d:Deck h)(p:(J.erase a)→Fin (Pages n X))(v:ι):
    layout h J a (d.val+root) (shifted h site d) (escort h site d p) v=
      motion h root d+layout h J a root site p v:=by
  classical
  unfold layout toe
  by_cases front:v=a
  · simp [front,motion]
  · by_cases inside:v∈J.erase a
    · simp only [front,if_false,inside,dif_pos,centers,located,add_sub_add_left_eq_sub]
      unfold motion
      abel
    · simp [front,inside,motion]

theorem center (d:Deck h)(v:ι):
    layout h J a (d.val+root) (shifted h site d) (retained h (shifted h site d)) v=
      motion h root d+layout h J a root site (retained h site) v:=by
  rw [←home h site d]
  exact all h J a root site d _ v

end YM.Integration.WilsonOriginalCensusOrbitCenters
end
