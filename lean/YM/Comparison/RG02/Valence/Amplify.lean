import YM.Comparison.RG02.Valence.Marginal
import YM.Comparison.RG02.Assembly.Core
/-!
# Rewrite Fk kernel monomials by accounting for every external leg in Wick's recursion.
 Report weight before symmetrized tensor readout; vertex groups include all MarkLog subsets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Valence
open Function Filter Finset YM.Analysis YM.Marker YM.Multi Cumulants Cumulants.Wick Order
open YM.Extra.Trajectories (connected)
open YM.Next.Rank
open scoped Topology BigOperators Classical ContDiff

variable {I E V J : Type} {n r : ℕ} [DecidableEq I] [Fintype I] [Fintype J]
  [DecidableEq V] [Fintype V] {R : Census V}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : (I→ℝ) →ₗ[ℝ] E) (b : Module.Basis J ℝ E)
  (y : E) (l : Hot R→ℕ) (f : E→ℝ) (W : Hot R→E→ℂ)

namespace Enlist
open Normal MvPolynomial

def volt : I⊕J→E := Sum.elim (fun i=>L (Pi.single i 1)) b

def shape (z : I→ℝ) : I⊕J→ℝ:= Sum.elim z (fun i=>b.repr y i)

def gauge : J→ℂ := fun i=> ↑(b.repr y i)

lemma minted (z : I→ℝ) : Assembly.translate y L z=∑ i,shape b y z i • volt L b i:= by
   unfold Assembly.translate; rw [Fintype.sum_sum_type]; simp_rw [volt,shape, Sum.elim_inl,Sum.elim_inr,b.sum_repr]
   simp_rw [← map_smul L,← map_sum L]; rw [add_comm (_:E) (L z)]
   have hv : (∑ i,z i • Pi.single i 1)=z:=by ext i; rw [Finset.sum_apply]; simp [Pi.single_apply]
   rw [hv]

def stamina (T : Tensor.T E ℂ n) := ∑ i: Fin n→ I⊕J,MvPolynomial.C (T (volt L b ∘ i)) * glyphs i univ

lemma equipped (T : Tensor.T E ℂ n) : stamina L b T∈ Area (I⊕J) n:= by
   unfold stamina; apply (Area ..).sum_mem
   intro c _; rw [C_mul']; exact (Area ..).smul_mem _ (fits n c)

omit [DecidableEq I] [Fintype I] in
lemma paint_inj {p q : Normal.poly I} (h : ∀ x, Cloud.paint x p=Cloud.paint x q) : p=q := by
   refine MvPolynomial.funext_set (fun _=> Set.range ((↑) : ℝ→ℂ)) (fun _=> Set.infinite_range_of_injective Complex.ofReal_injective) (fun x he=>?_)
   choose f hf using (show ∀ i, ∃ t : ℝ, ↑t=x i from fun i=> he i (Set.mem_univ _)); rw [← _root_.funext hf]; exact h f

omit [DecidableEq I] [Fintype I] [Fintype J] in
lemma downward (z:I→ℝ) : (Cloud.paint z).comp (Stamp.descend (I:=I) (gauge b y)) = Cloud.paint (shape b y z) := by
    ext1 i; rw [AlgHom.comp_apply]; rcases i with i|j
    · rw [Stamp.inl]; simp only [Cloud.paint,aeval_X,shape,Sum.elim_inl]
    rw [Stamp.inr]; simp only [Cloud.paint,aeval_X,shape,aeval_C,Sum.elim_inr]; rfl

lemma stamina_pay (z:I→ℝ) (T : Tensor.T E ℂ n) : Cloud.paint z (Stamp.descend (I:=I) (gauge b y) (stamina L b T)) = T (fun _=> Assembly.translate y L z):= by
   rw [← AlgHom.comp_apply,downward b y z]
   simp_rw [stamina,_root_.map_sum,map_mul (Cloud.paint _), glyphs,_root_.map_prod]; unfold Cloud.paint; simp only [aeval_C, aeval_X, Algebra.algebraMap_self]
   simp_rw [minted L b y z]
   rw [T.map_sum_finset (fun _ i=>_) (fun _=> Finset.univ), Fintype.piFinset_univ]
   apply Finset.sum_congr rfl; intro i _; rw [T.map_smul_univ, Complex.real_smul, Complex.ofReal_prod,mul_comm]; rfl

lemma stamina_word (T : Tensor.T E ℂ n) : Stamp.descend (I:=I) (gauge b y) (stamina L b T)=Assembly.wordL y L T := paint_inj (fun z=> (stamina_pay L b y z T).trans (Assembly.reading_word y L z T).symm)

end Enlist

abbrev hairs (s : Hot (Board R r)) :=
   if he : (Join.left s.val).val.Nonempty then l ⟨Join.left s.val,he⟩ else 2
def zephyr (s : Hot (Board R r)) : ℕ:= hairs l s+(Join.right s.val).val.card

def driver (s : Hot (Board R r)) : Normal.poly (I⊕J) :=
   let k:= (Join.right s.val).val.card
   let t:= Join.left s.val
   (k.factorial:ℂ) • if he : t.val.Nonempty then Enlist.stamina L b (Tensor.coeff (W ⟨t,he⟩) (l ⟨t,he⟩ + k) 0) else
     if k=0 then 0 else -Enlist.stamina L b (Complex.ofRealCLM.compContinuousMultilinearMap (Tensor.coeff f (k+2) 0))
lemma descends (s : Hot (Board R r)) : Assembly.generator y L l W f r s=Stamp.descend (I:=I) (Enlist.gauge b y) (driver L b l f W s):= by
   unfold Assembly.generator driver; rw [map_smul]; dsimp only
   split_ifs
   next h=> rw [Enlist.stamina_word]; rfl
   next h hs=> rw [Assembly.naked,if_pos hs,map_zero]
   next h hs=> rw [Assembly.naked,if_neg hs,map_neg,Enlist.stamina_word]; rfl
lemma budget (s : Hot (Board R r)) : driver L b l f W s∈Area (I⊕J) (zephyr l s):= by
   apply (Area ..).smul_mem; dsimp only [zephyr,hairs]; split_ifs
   · exact Enlist.equipped L b _
   · exact (Area ..).zero_mem
   rw [Nat.add_comm 2]; exact (Area (I⊕J) ((Join.right s.val).val.card+2)).neg_mem (Enlist.equipped L b _)

variable (Q : Matrix I I ℝ) (H : Q.IsSymm) (t : (Board R r).Mode)
local notation "q₀" => PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q H
local notation "q" => Stamp.pad q₀
local notation "α" y => (Sum.elim (0 : I→ℂ) (Enlist.gauge b y))
private lemma weighted : (connected (Assembly.prescription y L l W f Q H r)).part t=∑ s∈shards (Board R r) t,(connected (moments (parts (Board R r)) (Normal.blend q (α y)) (driver L b l f W))).part s := by
   unfold Assembly.prescription; rw [Cloud.prescribed_log]; rw [_root_.funext (descends (r:=r) L b y l f W),Cloud.wick, Stamp.with_legs (p:=0) q₀ ]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ E]
    (u : X→L[ℝ] E)
lemma weather (p : ℤ)
    (hp : ∀ s∈shards (Board R r) t,(∑ i∈s.val,(zephyr l i:ℤ))+2-2*s.val.card≤p) :
      Level p (fun x=> (connected (Assembly.prescription (y + u x) L l W f Q H r)).part t) := by
   classical
   let b := Module.Free.chooseBasis ℝ E
   simp_rw [weighted L b _ l f W Q H t]; apply Level.total; intro i hi
   refine full q (fun x:X=> Sum.elim (0:I→ℂ) (Enlist.gauge b (y+u x))) ?_ i (zephyr l) (driver L b l f W) p (fun j _=> budget L b l f W j) (hp i hi)
   intro j; rcases j with i|j
   · exact Level.zero _
   let c : E→L[ℝ]ℂ:= Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap (b.coord j)
   change Level _ (fun x=> c (y+u x)); simp_rw [map_add]; exact ((Level.constant (c y)).promote zero_le_one).add (Level.linear (c.comp u))
end YM.Comparison.RG02.Valence
