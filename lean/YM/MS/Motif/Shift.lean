import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import YM.MS.Book.Pairs

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif.Literal
open Finset Book.Convolve
variable {I E F:Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [ Module ℂ F] [AddCommGroup I] [Module ℂ I]
abbrev Box (E:Type)[Zero E]:= ℕ →₀ E
def value (E:Type)[AddCommGroup E][Module ℂ E] (z:ℂ) : Box E →ₗ[ℂ] E := Finsupp.lsum ℂ fun i:ℕ=> (z^i) • (LinearMap.id: E→ₗ[ℂ] E)
lemma valued (U:Box E)(z:ℂ) : value E z U= ∑ i∈ U.support,z^i • U i:= rfl
lemma value_sl (i:ℕ)(x:E)(z:ℂ): value E z ( Finsupp.single i x )= z^i • x:= Finsupp.lsum_single ..
lemma low_row (U:Box E): value E 0 U=U 0:= by
    rw [ valued ]; by_cases ht:0∈ U.support
    · rw [ Finset.sum_eq_single 0]; simp; · intro i hi he; simp [zero_pow he]
      exact fun h=>(h ht).elim
    rw [Finsupp.notMem_support_iff.mp ht]; apply Finset.sum_eq_zero; intro i hi; simp [ show i≠0 from fun h=> ht (h ▸ hi)]
def Boom (n:ℕ)(L:E→ₗ[ℂ] F) : Box E→ₗ[ℂ] Box F:= Finsupp.lsum ℂ fun i:ℕ=> ( Finsupp.lsingle (n+i) ).comp L
def root (L: E→ₗ[ℂ] F→ₗ[ℂ] I): Box E →ₗ[ℂ] Box F→ₗ[ℂ] Box I:= Finsupp.lsum ℂ fun i:ℕ=> {
    toFun x:= Boom i (L x)
    map_smul' c x:= LinearMap.ext (fun i'=>by simp [Boom,map_smul, Finsupp.lsum_apply,Finsupp.sum,Finset.smul_sum,Finsupp.smul_single])
    map_add' x y:= LinearMap.ext (fun i'=>by simp [ Boom,Finsupp.lsum_apply,Finsupp.sum,Finsupp.single_add,Finset.sum_add_distrib]) }
lemma Boom_sl (n i:ℕ)(L:E→ₗ[ℂ] F)(x:E): Boom n L (Finsupp.single i x)= Finsupp.single (n+i) (L x):= Finsupp.lsum_single ..
lemma root_sl (L:E→ₗ[ℂ] F→ₗ[ℂ] I)(i:ℕ)(x:E): root L (Finsupp.single i x)= Boom i (L x):= Finsupp.lsum_single ..
def linear (E:Type)[AddCommGroup E][Module ℂ E] : Box E→ₗ[ℂ] T E where
    toFun f:= fun i=> f i
    map_smul' _ _:= funext fun _=>Finsupp.smul_apply ..
    map_add' _ _:= funext fun _=>Finsupp.add_apply ..
lemma hiss (E:Type)[AddCommGroup E][Module ℂ E](i:Box E)(n:ℕ): linear E i n=i n:= rfl
variable {X:Box E} {L:E→ₗ[ℂ] F→ₗ[ℂ] I}
lemma linear_v (X:Box E)(L:E→ₗ[ℂ] F)(z:ℂ): value F z (Boom 0 L X)=L (value E z X):= by rw [← Finsupp.sum_single X,Finsupp.sum]; simp only [map_sum,Boom_sl,value_sl,Nat.zero_add,map_smul] -- simp_lint
lemma pair_v (X:Box E)(Y:Box F)(L:E→ₗ[ℂ] F→ₗ[ℂ] I)(z:ℂ): L (value E z X) ( value F z Y ) = value I z (root L X Y):= by
    rw [← Finsupp.sum_single X,← Finsupp.sum_single Y]; simp only [ Finsupp.sum,map_sum,LinearMap.sum_apply]; -- order check
    simp only [ root_sl,Boom_sl,value_sl,map_smul,LinearMap.smul_apply,pow_add,mul_smul]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl fun j _=> smul_comm ..)
end YM.MS.Motif.Literal
