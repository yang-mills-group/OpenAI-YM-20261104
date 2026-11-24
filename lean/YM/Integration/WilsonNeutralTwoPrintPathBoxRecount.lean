import YM.Integration.WilsonNeutralTwoPrintPathBoxPlacement

/-! The bounded original relative configurations and their authentic pages on
the enhanced physical torus are in bijection before the Gaussian reading. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoxRecount
open Function Filter Finset Lattice RG Wilson Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (locate)
open WilsonNeutralTwoPrintPathBoxPlacement
open scoped Classical BigOperators Topology
variable {ι:Type}[Fintype ι]{n X:Side}

def roster (h:n.val∣X.val)(root:Cover)(base:ι → Cover)(D:ℕ):Finset (ι→Fin (Pages n X)):=
  Finset.univ.filter (fun p=>offsets h root base p∈box n base D)

def pairing (h:n.val∣X.val)(root:Cover)(base:ι → Cover)(D:ℕ)(room:2*D<X.val):
    ↥(box n base D) ≃ ↥(roster h root base D) where
  toFun w:=⟨selected h root base w.val ((entry _ _ _ _).mp w.prop).2,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [honest h root base D room w.val w.prop];exact w.prop⟩⟩
  invFun p:=⟨offsets h root base p.val,(Finset.mem_filter.mp p.prop).2⟩
  left_inv w:=Subtype.ext (honest h root base D room w.val w.prop)
  right_inv p:=Subtype.ext (recovers h root base p.val)

theorem recount {M:Type}[AddCommMonoid M](h:n.val∣X.val)(root:Cover)(base:ι → Cover)(D:ℕ)
    (room:2*D<X.val)(f:(ι→Fin (Pages n X))→M):
    ∑p∈roster h root base D,f p=∑w:box n base D,f (selected h root base w.val ((entry _ _ _ _).mp w.prop).2):=by
  calc
    _ = ∑p:roster h root base D,f p.val:=(Finset.sum_coe_sort _ f).symm
    _ = _ :=(Equiv.sum_comp (pairing h root base D room) (fun p=>f p.val)).symm

theorem absent (h:n.val∣X.val)(root:Cover)(base:ι → Cover)(D:ℕ)(p:ι→Fin (Pages n X))
    (outside:p∉roster h root base D):∃i,D≤ separation (wrap X root) (locate h (homes X root base) p i):=by
  by_contra! below
  apply outside (Finset.mem_filter.mpr ⟨Finset.mem_univ _,included h root base D p
    (fun i=>(below i).le)⟩)

variable {I:Type}[DecidableEq I]
omit [Fintype ι] in
theorem placed (h:n.val∣X.val)(S:Finset I)(o:I)(root:Cover)(base:(S.erase o) → Cover)
    (D:ℕ)(room:2*D<X.val)(home:lift (wrap X root)=root)(w:box n base D):
    toe S o (lift (wrap X root)) (WilsonPointChildRelativeLift.centers h S o (wrap X root)
      (homes X root base) (selected h root base w.val ((entry _ _ _ _).mp w.prop).2))=
      toe S o root (fun i=>root+w.val i):=by
  have sam:=honest h root base D room w.val w.prop
  have coordinates:WilsonPointChildRelativeLift.centers h S o (wrap X root)
      (homes X root base) (selected h root base w.val ((entry _ _ _ _).mp w.prop).2)=
      (fun i=>root+w.val i):=by
    funext i
    change lift (wrap X root)+offsets h root base _ i=_
    rw [home,congrFun sam i]
  rw [coordinates,home]

end YM.Integration.WilsonNeutralTwoPrintPathBoxRecount
end
