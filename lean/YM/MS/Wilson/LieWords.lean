import YM.MS.Bare.Spark
import YM.MS.Color.Only
import YM.MS.Wilson.Space

set_option autoImplicit false
noncomputable section
namespace YM.MS.Native
open Function Filter Finset Set Koszul Plane Complex
open scoped Topology ContDiff InnerProductSpace
variable {G: Gauge} {P: Type} [DecidableEq P] [Fintype P]
def letterLie (i j k:Conn G): ℝ:= (G.ad (baseC i) (baseC j)) k
omit [DecidableEq P][Fintype P] in
lemma scaled_tensor (a b c:Conn G): letterLie a b c= ⟪G.ad (baseC a) (baseC b),baseC c⟫_ℝ := by
    rw [real_inner_comm,← OrthonormalBasis.repr_apply_apply]; simp [letterLie,baseC]
omit [DecidableEq P][Fintype P] in
lemma notrace (a b:Conn G): letterLie a b a=0:= by
    rw [scaled_tensor,Only.ad_anti,inner_neg_left]; have ht:= Gauge.ad_skew (baseC b) (baseC a) (baseC a); rw [real_inner_comm (G.ad _ _)] at ht; nlinarith [real_inner_comm (baseC a) (G.ad (baseC b) (baseC a))]
def braid (f:Lot G P) : Lot G P→ₗ[ℝ] Lot G P:= LinearMap.pi fun i:P=> (G.ad (f i)).comp (LinearMap.proj i)
omit [DecidableEq P][Fintype P] in
lemma braidal (f g:Lot G P): braid f g= -braid g f:= funext fun _=> Only.ad_anti ..
omit [DecidableEq P][Fintype P] in
lemma bouquet (f g:Lot G P): braid (braid f g)=braid f * braid g-braid g * braid f:= by
    apply LinearMap.ext; intro v; funext i; exact DFunLike.congr_fun (Gauge.ad_jacobi (f i) (g i)) (v i)
def colorTerm (G:Gauge)(P:Type)[DecidableEq P][Fintype P] : Eyes G P→ Eyes G P→ Eyes G P→ℝ:= fun i j k=> projector k (braid (priv i) (priv j))
local notation "κ" => colorTerm G P
lemma story (u v w:P) (i j k:Conn G): κ (u,i) (v,j) (w,k)= if w=u ∧ w=v then letterLie i j k else 0:= by
    unfold colorTerm; rw [projector_k]
    by_cases hu:w=u <;> by_cases hv:w=v <;> simp +zetaDelta [braid,priv,Pi.single_apply,letterLie,hu,hv,apply_ite] <;> split_ifs <;> simp
lemma crowd (k l:Eyes G P): ∑ i:Eyes G P, κ k l i • priv i= braid (priv k) (priv l):= frame _
lemma reel (i j k l:Eyes G P): ∑ w,κ i j w*κ w k l= -projector l (braid (priv k) (braid (priv i) (priv j))):= by
   rw [← crowd, map_sum,map_sum]; simp only [map_smul] -- orientation
   unfold colorTerm; simp_rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun v _=> ?_; rw [braidal (priv v) (priv k),map_neg]; simp
lemma cartan (G:Gauge) (P:Type) [DecidableEq P][Fintype P]: Bare.Focus.Metric (Eyes G P) (colorTerm G P) := by
    constructor
    · intro i j k; unfold colorTerm; rw [braidal (priv i),map_neg]
    · intro i j k l; rw [Finset.sum_add_distrib,Finset.sum_add_distrib,reel,reel,reel]
      have he := bouquet (priv i) (priv j); have hh : braid (priv i) (braid (priv j) (priv k))+ braid (priv j) (braid (priv k) (priv i))+braid (priv k) (braid (priv i) (priv j))=0:=by
          rw [braidal (priv k) (priv i), map_neg, ← sub_eq_add_neg, ← show braid (braid (priv i) (priv j)) (priv k)= braid (priv i) (braid (priv j) (priv k))-braid (priv j) (braid (priv i) (priv k)) from DFunLike.congr_fun he (priv k), braidal (f:=braid _ _)]; abel
      have hv:= congr_arg (projector l) hh; simp only [map_add,map_zero] at hv; linarith
    intro i; apply Finset.sum_eq_zero; intro j _; rw [show colorTerm G P j i j=_ from story j.1 i.1 j.1 j.2 i.2 j.2]; simp [notrace]
end YM.MS.Native
