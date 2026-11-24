import YM.Integration.WilsonOriginalRelativePageTail
import YM.Integration.WilsonPointChildFoldedPageIncome
import YM.Integration.WilsonPointChildNamedRootSum
import YM.WilsonCoeffUV.Marked.Capture.Draw
import YM.Integration.WilsonPointChildPlacedFold
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildDeckLift
open YM Lattice WilsonCoeffUV RG FormalBulk08 Laurent
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open Work.F08 Function Finset Filter
open scoped Classical BigOperators Topology
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail
variable {ι α:Type} [DecidableEq ι] {n X:Side}

def centers (h:n.val∣X.val)(I:Finset ι)(o:ι)(sites:(I.erase o) → Site X)
    (p:(I.erase o) → Fin (Pages n X)) (j:I.erase o):Cover:=lift (locate h sites p j)

theorem injective (h:n.val∣X.val)(I:Finset ι)(o:ι)(sites:(I.erase o) → Site X):
    Injective (centers h I o sites):=by
  intro p q he
  funext j
  have eq:=congrArg (wrap X) (congrFun he j)
  have take:locate h sites p j=locate h sites q j:=by simpa only [centers,wrap_lift] using eq
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
    let G:=toe I o (lift root) (centers h I o sites p)
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

end YM.Integration.WilsonPointChildDeckLift
