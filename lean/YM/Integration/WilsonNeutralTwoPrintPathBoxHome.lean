import YM.Integration.WilsonNeutralTwoPrintPathBoxMean

/-! On the original named lifted sites, the retained torus layout is
literally the specified covered layout as soon as its coordinates fit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoxHome
open Function Finset Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Address
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonNeutralTwoPrintPathBoxPlacement (homes selected box entry)
open WilsonNeutralTwoPrintPathBoxInk (ink)
open WilsonOriginalRelativePageTail (retained)
open WilsonOriginalCensusOrbitCenters (layout)
open scoped Classical BigOperators
variable {I:Type}[DecidableEq I]{n X:Side}

def radius (x:Cover):ℕ:=Finset.univ.sup (fun j:Axis=>(x j).natAbs)
def breadth (S:Finset I)(o:I)(origin:Cover)(base:(S.erase o) → Cover):ℕ:=
  max (radius origin) (Finset.univ.sup (fun i=>radius (base i)))

theorem original (h:n.val∣X.val)(S:Finset I)(o:I)(origin:Cover)(base:(S.erase o) → Cover)
    (room:2*breadth S o origin base<X.val):
    layout h S o (wrap X origin) (homes X origin base) (retained h (homes X origin base))=ink S o origin base ∧
    ∀i,separation (wrap X origin) (homes X origin base i)≤breadth S o origin base:=by
  let D:=breadth S o origin base
  have bounded (i:S.erase o)(j:Axis):(base i j).natAbs≤D:=
    (Finset.le_sup (s:=Finset.univ) (f:=fun j:Axis=>(base i j).natAbs) (Finset.mem_univ j)).trans
      ((Finset.le_sup (s:=Finset.univ) (f:=fun i=>radius (base i)) (Finset.mem_univ i)).trans (le_max_right _ _))
  have home:lift (wrap X origin)=origin:=by
    apply lift_eq_iff.mpr
    refine ⟨rfl,fun j=>?_⟩
    have pos:(origin j).natAbs≤D:=
      (Finset.le_sup (s:=Finset.univ) (f:=fun j:Axis=>(origin j).natAbs) (Finset.mem_univ j)).trans (le_max_left _ _)
    change 2*D<X.val at room
    omega
  have belongs:base∈box n base D:=(entry _ _ _ _).mpr ⟨bounded,fun _=>rfl⟩
  let w:box n base D:=⟨base,belongs⟩
  have same:selected h origin base base ((entry _ _ _ _).mp belongs).2=retained h (homes X origin base):=by
    funext i
    apply (page h (splitter h (homes X origin base i))).injective
    apply Subtype.ext
    exact (WilsonNeutralTwoPrintPathBoxPlacement.effective h origin base base _ i).trans
      (WilsonOriginalRelativePageTail.chosen h (homes X origin base) i).symm
  constructor
  · simpa only [w,same,layout,ink] using WilsonNeutralTwoPrintPathBoxRecount.placed h S o origin base D room home w
  · intro i
    rw [separation_comm]
    change pdist (wrap X (origin+base i)-wrap X origin)≤D
    rw [map_add,add_sub_cancel_left]
    have arrived:lift (wrap X (base i))=base i:=by
      apply lift_eq_iff.mpr
      refine ⟨rfl,fun j=>?_⟩
      have q:=bounded i j
      change 2*D<X.val at room
      omega
    simp only [pdist,arrived,Finset.sup_le_iff]
    exact fun j _=>bounded i j

end YM.Integration.WilsonNeutralTwoPrintPathBoxHome
end
