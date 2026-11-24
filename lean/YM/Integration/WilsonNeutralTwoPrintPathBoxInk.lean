import YM.Integration.WilsonNeutralTwoPrintPathBoxRecount

/-! Angular positions of retained genuine pages at any chosen common
deck-translate of the original root. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoxInk
open Function Filter Finset Lattice RG Wilson Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.PathCost
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (locate)
open WilsonPointChildRelativeLift (centers)
open WilsonNeutralTwoPrintPathBoxPlacement
open scoped Classical BigOperators Topology
variable {I:Type}[DecidableEq I]{n X:Side}

def ink (S:Finset I)(o:I)(root:Cover)(w:(S.erase o) → Cover):I → Cover:=
  toe S o root (fun i=>root+w i)

theorem translated (S:Finset I)(o:I)(root shift:Cover)(w:(S.erase o) → Cover)(v:I):
    ink S o (shift+root) w v=shift+ink S o root w v:=by
  by_cases same:v=o
  · subst v
    simp [ink,toe]
  · by_cases hit:v∈S.erase o
    · simp [ink,toe,same,hit,add_assoc]
    · simp [ink,toe,same,hit]

theorem small (S:Finset I)(o:I)(root:Cover)(base:(S.erase o) → Cover)(D:ℕ)(w:box n base D):
    crestCard (ink S o root w.val) S≤8*D:=by
  let y:=ink S o root w.val
  have reach (v:S):Bank.terrain.gap root (y v.val)≤4*D:=by
    by_cases eqn:v.val=o
    · simp [y,ink,toe,eqn,Bank.terrain.self]
    · have hit:v.val∈S.erase o:=Finset.mem_erase.mpr ⟨eqn,v.prop⟩
      let i:S.erase o:=⟨v.val,hit⟩
      have loc:y v.val=root+w.val i:=by simp [y,ink,toe,eqn,i,hit]
      rw [loc]
      change size (root+w.val i-root)≤4*D
      rw [add_sub_cancel_left]
      calc
        _ ≤ ∑_:Axis,D:=Finset.sum_le_sum (fun j _=>((entry n base w.val D).mp w.prop).1 i j)
        _ = 4*D:=by simp
  apply league_le
  intro i j
  have b:Bank.terrain.gap (y i.val) (y j.val)≤4*D+4*D:=
    (Bank.terrain.tri (y i.val) root (y j.val)).trans
      (add_le_add (by rw [Bank.terrain.swap];exact reach i) (reach j))
  exact b.trans_eq (by omega)

def config (h:n.val∣X.val)(S:Finset I)(o:I)(root:Site X)(site:(S.erase o)→Site X)
    (p:(S.erase o)→Fin (Pages n X)):I → Cover:=toe S o (lift root) (centers h S o root site p)

theorem same (h:n.val∣X.val)(S:Finset I)(o:I)(root:Site X)(site homes':(S.erase o)→Site X)
    (receipt:∀i,splitter h (site i)=splitter h (homes' i))(p:(S.erase o)→Fin (Pages n X)):
    config h S o root site p=config h S o root homes' p:=by
  have loc (i:S.erase o):locate h site p i=locate h homes' p i:=by
    unfold locate
    rw [receipt]
  apply congrArg (toe S o (lift root))
  funext i
  simp only [centers,loc]

end YM.Integration.WilsonNeutralTwoPrintPathBoxInk
end
