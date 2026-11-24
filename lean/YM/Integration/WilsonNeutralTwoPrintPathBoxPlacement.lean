import YM.Integration.WilsonNeutralTwoPrintPathPageTruncation
import YM.Integration.WilsonNeutralTwoPrintPathPageRead
import YM.Integration.WilsonPointChildRelativeLift

/-! The same finite set of original relative displacements is available on
every sufficiently large auxiliary copy. Each page is still read at its own
true physical-period residue. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoxPlacement
open Function Filter Finset Lattice RG Wilson Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (locate)
open scoped Classical BigOperators Topology
variable {ι:Type}{n X:Side}

def homes (X:Side)(root:Cover)(base:ι → Cover)(i:ι):Site X:=wrap X (root+base i)

def offsets (h:n.val∣X.val)(root:Cover)(base:ι → Cover)(p:ι→Fin (Pages n X))(i:ι):Cover:=
  lift (locate h (homes X root base) p i-wrap X root)

theorem residue (h:n.val∣X.val)(root:Cover)(base:ι → Cover)(p:ι→Fin (Pages n X))(i:ι):
    wrap n (offsets h root base p i)=wrap n (base i):=by
  have registered:splitter h (locate h (homes X root base) p i)=splitter h (homes X root base i):=
    (posted _ _ _).mp (page h (splitter h (homes X root base i)) (p i)).prop
  rw [←Macrame.branch h,offsets,wrap_lift,map_sub,registered,homes,Macrame.branch,Macrame.branch,map_add,add_sub_cancel_left]

def selected (h:n.val∣X.val)(root:Cover)(base w:ι → Cover)
    (okay:∀i,wrap n (w i)=wrap n (base i))(i:ι):Fin (Pages n X):=
  (page h (splitter h (homes X root base i))).symm ⟨wrap X (root+w i),by
    apply (posted _ _ _).mpr
    rw [homes,Macrame.branch,Macrame.branch,map_add,map_add,okay]⟩

theorem effective (h:n.val∣X.val)(root:Cover)(base w:ι → Cover)
    (okay:∀i,wrap n (w i)=wrap n (base i))(i:ι):
    locate h (homes X root base) (selected h root base w okay) i=wrap X (root+w i):=by
  unfold locate selected
  simp only [Equiv.apply_symm_apply]

theorem exactly (h:n.val∣X.val)(root:Cover)(base w:ι → Cover)
    (okay:∀i,wrap n (w i)=wrap n (base i))(i:ι):
    offsets h root base (selected h root base w okay) i=lift (wrap X (w i)):=by
  rw [offsets,effective,map_add,add_sub_cancel_left]

theorem recovers (h:n.val∣X.val)(root:Cover)(base:ι → Cover)(p:ι→Fin (Pages n X)):
    selected h root base (offsets h root base p) (residue h root base p)=p:=by
  funext i
  apply (page h (splitter h (homes X root base i))).injective
  apply Subtype.ext
  change locate h (homes X root base) (selected h root base (offsets h root base p) (residue h root base p)) i=
    locate h (homes X root base) p i
  rw [effective,map_add,offsets,wrap_lift,add_sub_cancel]

variable [Fintype ι]

def box (n:Side)(base:ι → Cover)(D:ℕ):Finset (ι → Cover):=
  (Fintype.piFinset (fun _:ι=>Fintype.piFinset (fun _:Axis=>Finset.Icc (-(D:ℤ)) D))).filter
    (fun w=>∀i,wrap n (w i)=wrap n (base i))

theorem entry (n:Side)(base w:ι → Cover)(D:ℕ):
    w∈box n base D ↔ (∀i j,(w i j).natAbs≤D) ∧ ∀i,wrap n (w i)=wrap n (base i):=by
  simp only [box,Finset.mem_filter,Fintype.mem_piFinset,Finset.mem_Icc]
  constructor
  · rintro ⟨window,atSite⟩
    exact ⟨fun i j=>by have z:=window i j; omega,atSite⟩
  · rintro ⟨window,atSite⟩
    exact ⟨fun i j=>by have z:=window i j; omega,atSite⟩

theorem honest (h:n.val∣X.val)(root:Cover)(base:ι → Cover)(D:ℕ)(room:2*D<X.val)
    (w:ι → Cover)(hw:w∈box n base D):
    offsets h root base (selected h root base w ((entry n base w D).mp hw).2)=w:=by
  funext i
  rw [exactly]
  apply lift_eq_iff.mpr
  refine ⟨rfl,fun j=>?_⟩
  have bounded:=((entry n base w D).mp hw).1 i j
  omega

theorem included (h:n.val∣X.val)(root:Cover)(base:ι → Cover)(D:ℕ)(p:ι→Fin (Pages n X))
    (near:∀i,separation (wrap X root) (locate h (homes X root base) p i)≤D):
    offsets h root base p∈box n base D:=by
  refine (entry _ _ _ _).mpr ⟨?_,residue h root base p⟩
  intro i j
  change (lift (locate h (homes X root base) p i-wrap X root) j).natAbs≤D
  apply (component_le _ _).trans
  change separation (locate h (homes X root base) p i) (wrap X root)≤D
  rw [separation_comm]
  exact near i

end YM.Integration.WilsonNeutralTwoPrintPathBoxPlacement
end
