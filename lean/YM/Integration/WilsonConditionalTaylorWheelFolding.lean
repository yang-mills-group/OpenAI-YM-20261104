import YM.Integration.WilsonConditionalTaylorWheelBirth
import YM.Integration.WilsonConditionalTaylorBulkLimit

/-! Ordered positive-rank torus folding is literally the same full
lattice fibre on the upper cover and on the independent finite history. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelFolding
open Function Lattice Laurent RG Wilson FormalBulk08 FormalBulk08.Lotus FormalBulk08.Lava
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open scoped Classical BigOperators Topology
variable {G:Gauge} {n:Side} {r:ℕ} (X:stars G r n)

def placed (w:Shift ((Fin r×Axis))) : Fin (r+1)→Biglot (Hooks G):=
  fun i => (lift (X 0).1+feetP w i,(X i).2)

def offsets (v:Fin (r+1)→Biglot (Hooks G)) : Shift ((Fin r×Axis)):=
  fun k=>((v k.1.succ).1-lift (X 0).1) k.2

theorem dates (v:Picks 0 n (boil n (X 0)) X) (j:Fin (r+1)):
    feetP (offsets X v.val) j=(v.val j).1-lift (X 0).1:=by
  refine Fin.cases ?_ (fun i=>?_) j
  · rw [v.property.1]; simp [feetP,boil]
  · rfl

def lifts : {w:Shift ((Fin r×Axis)) // trope X w} ≃ Picks 0 n (boil n (X 0)) X where
  toFun w:=⟨placed X w.val,by simp [placed,feetP,boil],by
    funext j;apply Prod.ext
    · change wrap n (lift (X 0).1+feetP w.val j)=(X j).1
      rw [map_add,←w.property j];simp
    · rfl⟩
  invFun v:=⟨offsets X v.val,by
    intro j;rw [dates X v j,map_sub]
    have hj:=congrArg Prod.fst (congrFun v.property.2 j)
    change wrap n (v.val j).1=(X j).1 at hj
    rw [hj];simp⟩
  left_inv w:=by
    apply Subtype.ext
    funext k
    rcases k with ⟨k,a⟩
    change (lift (X 0).1+feetP w.val k.succ-lift (X 0).1) a=w.val (k,a)
    rw [add_sub_cancel_left];rfl
  right_inv v:=by
    apply Subtype.ext
    funext j;apply Prod.ext
    · change lift (X 0).1+feetP (offsets X v.val) j=(v.val j).1
      rw [dates X v j];abel
    · exact (congrArg Prod.snd (congrFun v.property.2 j)).symm

theorem periodized (P:post G r) (moves:stroll P):
    lagoon P n X=cum 0 n P X:=by
  let S: Set (Shift ((Fin r×Axis))) := {w|trope X w}
  have inside:Function.support (flair X P)⊆S:=by
    intro w h;by_contra no
    exact h (flair_miss (show ¬trope X w from no))
  change (∑' w,flair X P w)= ∑' v:Picks 0 n (boil n (X 0)) X,P v.val
  rw [←tsum_subtype_eq_of_support_subset inside,←(lifts X).tsum_eq]
  apply tsum_congr
  intro w
  rw [flair_hit w.property]
  change P (goose w.val (stH X) (stR X))=P (placed X w.val)
  exact (moves (lift (X 0).1) (goose w.val (stH X) (stR X))).symm

end YM.Integration.WilsonConditionalTaylorWheelFolding
end

