import YM.Integration.WilsonOriginalRelativePageTail
import YM.Integration.WilsonPointChildFoldedPageIncome
import YM.Integration.WilsonPointChildNamedRootSum
import YM.WilsonCoeffUV.Marked.Capture.Draw
import YM.Integration.WilsonPointChildPlacedFold
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildRelativeLift
open YM Lattice WilsonCoeffUV RG FormalBulk08 Laurent
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open Work.F08 Function Finset Filter
open scoped Classical BigOperators Topology
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail
variable {ι α:Type} [DecidableEq ι] {n X:Side}

def centers (h:n.val∣X.val)(I:Finset ι)(o:ι)(root:Site X)(sites:(I.erase o) → Site X)
    (p:(I.erase o) → Fin (Pages n X)) (j:I.erase o):Cover:=lift root + lift (locate h sites p j-root)

theorem injective (h:n.val∣X.val)(I:Finset ι)(o:ι)(root:Site X)(sites:(I.erase o) → Site X):
    Injective (centers h I o root sites):=by
  intro p q he
  funext j
  have eq:=congrArg (wrap X) (congrFun he j)
  have take:locate h sites p j=locate h sites q j:=by simpa [centers] using eq
  exact (page h (splitter h (sites j))).injective (Subtype.ext take)

omit [DecidableEq ι] in
theorem metric (a b:Site X):separation a b ≤ (tor X).gap a b:=by
  rw [separation_comm]
  unfold separation pdist
  apply Finset.sup_le
  intro j _
  change (lift (b-a) j).natAbs ≤ ∑ i:Axis,(lift (b-a) i).natAbs
  exact Finset.single_le_sum (fun (i:Axis) _=>Nat.zero_le (lift (b-a) i).natAbs) (Finset.mem_univ j)

theorem connected (h:n.val∣X.val)(I:Finset ι)(o:ι)(live:o∈I)(root:Site X)
    (sites:(I.erase o) → Site X)(r:ℕ)(p:(I.erase o) → Fin (Pages n X))(x:dock (Site X) α r)(j:I.erase o):
    let G:=toe I o (lift root) (centers h I o root sites p)
    separation root (locate h sites p j) ≤ Syn (tor X) (wrap X ∘ G) I x:=by
  intro G
  have hit:=leg_le (tor X) (foyer (wrap X ∘ G) I x) (Sum.inl (⟨o,live⟩:I))
    (Sum.inl (⟨j.val,(Finset.mem_erase.mp j.property).2⟩:I))
  have home:wrap X (G o)=root:=by simp [G,toe]
  have away:wrap X (G j.val)=locate h sites p j:=by
    simp [G,toe,centers,(Finset.mem_erase.mp j.property).1,j.property]
  change (tor X).gap (wrap X (G o)) (wrap X (G j.val)) ≤ Syn (tor X) (wrap X ∘ G) I x at hit
  rw [home,away] at hit
  exact (metric root _).trans hit

/-- The retained full-period pages give the original displacements from the
same root, also when a short physical source crosses the centered cell boundary. -/
theorem radius (h:n.val ∣ X.val)(I:Finset ι)(o:ι)(root:Site X)(site:(I.erase o) → Site X)
    (D:ℕ)(near:∀j,separation root (site j)≤D):
    let R:=toe I o (lift root) (centers h I o root site (retained h site))
    crestCard R I ≤ 8*D:=by
  intro R
  have reach:∀i:I,terrain.gap (lift root) (R i.val) ≤ 4*D:=by
    intro i
    by_cases same:i.val=o
    · simp [R,toe,same,terrain.self]
    · have inrow:i.val∈I.erase o:=mem_erase.mpr ⟨same,i.property⟩
      let j:I.erase o:=⟨i.val,inrow⟩
      have value:R i.val=lift root + lift (site j-root):=by
        simp [R,toe,same,inrow,centers,WilsonOriginalRelativePageTail.chosen,j]
      rw [value]
      change size (lift root+lift (site j-root)-lift root) ≤ 4*D
      rw [add_sub_cancel_left]
      calc
        size (lift (site j-root)) ≤ ∑_:Axis,D :=Finset.sum_le_sum fun t _=>
          (component_le (site j-root) t).trans (by change separation (site j) root ≤ D; rw [separation_comm]; exact near j)
        _=4*D:=by simp
  apply league_le
  intro i j
  have budget:terrain.gap (R i.val) (R j.val) ≤ 4*D+4*D:=
    (terrain.tri (R i.val) (lift root) (R j.val)).trans
      (add_le_add (by rw [terrain.swap (R i.val) (lift root)]; exact reach i) (reach j))
  exact budget.trans_eq (by omega)

end YM.Integration.WilsonPointChildRelativeLift
