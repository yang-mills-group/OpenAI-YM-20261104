import YM.OPE.Compatible.Cum.Braid
/-!
# Abstract gadget for de-imaging along one volume leg in forced cumulant.
Support either ordinary closed cover or folded. Includes Lap epsilon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Matrix
variable {I J E R:Type}{e d t u j:ℕ}{N:Side}
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [Fintype I]
local notation "Q"=>deck I N
local notation "TK"=> Flume.Script.Tab I N
variable (L:Law E)(Z:E→L[ℝ] deck I N)
-- condition for EXTRA: cross convolution in one weighted volume insertion
def Rookie (U:Row I I)(X: Q)(p:Script I j)(c:ℝ):Prop:= ∀ i:Fin j,∀ x:E, ∀ q: Fin j→Q,(∀ h,h≠i→ q h=X+Z x∨q h=X) → ∀ k: Flume.Script.Tab I N,
         ∑ a:TK, Oriel L Z k a * (c * library N p (Function.update q i (deltaH a)))=∑ a:TK,U.acts N k a * library N p (Function.update q i (deltaH a))
lemma frontier (y: Tensor.T Q ℝ (u+t)) (X: Q)(a:E)(i:Fin t)(k:TK):
      φx X X Z y (L.inverse (Ferry Z k)) i a= ∑ j:TK, Oriel L Z k j * y (Function.update (cue (X+Z a) X u t) (pinT i) (deltaH j)):=by
       unfold φx; rw [sage]; let T:=y.toContinuousLinearMap (cue (X+Z a) X u t) (pinT i); rw [show y _ =_ from (show y _=T (∑ j:TK,Oriel L Z k j • deltaH j) from rfl),map_sum]; exact sum_congr rfl fun i _=> map_smul T _ _
lemma under (Ω: Row I I)(x:Q)(i:Site N)(w:ℝ)(h:Script I (u+(t+1)))(p:Script I (e+d+1))(z:E)(g: Fin (t+1))(hp:Summable p)(hQ:Summable h)(hΩ: Whole Ω)(hh:Rookie L Z Ω x h w):
      let V:=(w • listV h N : Tensor.T Q ℝ (u+(t+1)))
      (∑ j:TK, FTl e d (orchestra p i) x x (deltaH j) Z z* φx x x Z V (L.inverse (Ferry Z j)) g z)=scribe i (mitt e d u t p h g Ω) (cue (x+ Z z) x (e+u) (d+t)):=by
        intro V; let P:=cue (x+Z z) x e d; let y:= pinT (e:=u) g; let q:=cue (x+Z z) x u (t+1); let D(k:TK):= library N h (Function.update q y (deltaH k)); let v(k:TK):= scribe i p (Fin.cons (deltaH k) P); rw [mittGo i p h Ω hp hQ hΩ g (x+Z z) x] -- replace
        refine sum_congr rfl fun j _=>?_
        rw [show FTl _ _ _ _ _ _ _ _= v j from scriptV i p _ hp,frontier]; have he(k:TK): V (Function.update q y (deltaH k))=w* D k:=by rw [show V= _ from rfl,_root_.smul_apply,muses _ hQ];rfl
        rw [show (∑ k:TK, Oriel L Z j k * V (Function.update q y (deltaH k)))=∑ k:TK, Oriel L Z j k*(w*D k) from Finset.sum_congr rfl (fun k _=> congr_arg (Oriel L Z j k* · ) (he k))]; have hv:= hh y z q (by
              intro i hj; unfold q cue; split; exact Or.inl rfl;exact Or.inr rfl) j
        rw [show (∑ k:TK,Oriel L Z j k* (w*D k))=_ from hv, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _=> by change v j* (Ω.acts N j k*D k)= _*v j* D k;ring
end YM.OPE.Libra.Shell
