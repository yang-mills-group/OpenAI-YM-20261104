import YM.GradedFar.Crop
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.Ring.GeomSum
/-! # Divided differences for exact finite poll variations -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries
open FVA2.GradedFar
open scoped Topology BigOperators Classical
variable {E:Type*} [AddCommGroup E][Module ℂ E] {n p:ℕ}
def splice (u v:Fin n→E)(k:ℕ)(j:Fin n) := if j.val<k then u j else v j
lemma splice_row (M:MultilinearMap ℂ (fun _:Fin n=>E) ℂ) (u v: Fin n→E): M u - M v =
    ∑ i:Fin n,M (update (splice u v i.val) i (u i - v i)):=by
 let f j:= splice u v j; let y(i:ℕ):= M (f i)
 have hx(i:Fin n):f (i.val+1)=update (f i.val) i (u i):=by
   funext j; unfold f splice; by_cases h:j=i; · simp [h]
   rw [update_of_ne h]; have he:j.val ≠ i.val:= fun H=> h (Fin.ext H); split <;> split <;> (first| rfl| omega)
 have h(i:Fin n): f i.val i=v i:= if_neg (lt_irrefl _)
 have hi(i:Fin n): M (update (splice u v i.val) i (u i-v i))=y (i.val+1)-y i.val:= by
   unfold y; rw [hx,M.map_update_sub,← show f i.val i= v i from h i,update_eq_self]; -- u i-v i rewrite if occ fine
 have h0:f 0=v:= funext fun i=> if_neg (Nat.not_lt_zero _)
 have hn:f n=u:= funext fun i=> if_pos i.isLt
 rw [← show y n=M u from by unfold y; rw [hn],← show y 0=M v from by unfold y; rw [h0]]
 simp_rw [hi]; rw [← Finset.sum_range_sub y n]; rw [Finset.sum_fin_eq_sum_range]; exact Finset.sum_congr rfl fun i hi=> by rw [dif_pos (Finset.mem_range.mp hi)]

def geometric (x y:ℂ)(k:ℕ):=∑ i∈ Finset.range k,x^i*y^(k-1-i)
def traverse (p:ℕ)(A:PowerSeries ℂ)(x y:ℝ) :ℂ:= ∑ k∈Finset.range (p+1), geometric x y k * coeff k A
lemma walking (p:ℕ)(A:PowerSeries ℂ)(x y:ℝ): ((x-y:ℝ):ℂ)* traverse p A x y = appointedH140Crop p x A-appointedH140Crop p y A:=by
    unfold traverse; rw [Finset.mul_sum,crop_eq,crop_eq,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
    rw [← mul_assoc,mul_comm _ (geometric ..), ← sub_mul,geometric,Complex.ofReal_sub,geom_sum₂_mul]
lemma fixed (p:ℕ)(hp:1≤p)(A:PowerSeries ℂ): traverse p A 0 0= coeff 1 A:=by
    unfold traverse; simp only [Complex.ofReal_zero]; rw [Finset.sum_eq_single 1]
    · simp [geometric]
    · intro b _ hv; unfold geometric; by_cases h:b=0; · simp [h]
      rw [ Finset.sum_eq_zero ?_, zero_mul ]; intro i hi; by_cases h0:i=0; · subst i; rw [pow_zero,zero_pow (by omega),mul_zero]
      rw [zero_pow h0,zero_mul]
    simp
    omega
set_option maxHeartbeats 300000 in
lemma coherent (p:ℕ)(A:PowerSeries ℂ): Continuous (fun i:ℝ×ℝ=> traverse p A i.1 i.2) := by
 unfold traverse geometric; exact continuous_finsetSum _ fun i _=> (continuous_finsetSum _ fun j _=> ((Complex.continuous_ofReal.comp continuous_fst).pow _).mul ((Complex.continuous_ofReal.comp continuous_snd).pow _)).mul continuous_const
attribute [local irreducible] traverse
lemma traverse_limit {I:Type*}{v:Filter I}{p:ℕ}(hp:1≤p){f g:I→ℝ}(h:Tendsto f v (𝓝 0))(he:Tendsto g v (𝓝 0))(A:PowerSeries ℂ):
    Tendsto (fun i=>traverse p A (f i) (g i)) v (𝓝 (coeff 1 A)):=by
    have hu:Tendsto (fun i:ℝ×ℝ=> traverse p A i.1 i.2) (𝓝 (0,0)) (𝓝 (traverse p A 0 0)):= (Continuous.tendsto (coherent p A) ((0,0):ℝ×ℝ))
    rw [fixed _ hp] at hu; exact hu.comp (h.prodMk_nhds he)
end YM.Integration.GradedFar.Tariff.Billboard
