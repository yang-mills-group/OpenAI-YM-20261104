import YM.MSbar.Whisk.Muse
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side} (l : σ→ Site n) (W: Finset (Site n)) {Y Z:Finset (Site n)} {x y z:Site n} (ξ : View σ)
variable {m p q d:ℕ} {r a b t u v:ℝ}{f g:Pot σ}{T R:List σ}
lemma splitN (p q:Pot σ)(x:List σ): read ξ x (p*q)= Yarn x.length (fun l:List Bool => (read ξ (takeout true l x) p)*(read ξ (takeout false l x) q)):=by
   induction x generalizing p q with
   | nil=> rw [show List.length ([]:List σ)=0 from rfl,twillz]; exact MvPolynomial.eval_mul .. -- name
   | cons i L ih=>
       rw [read_next,pderiv_mul,map_add,ih,ih, List.length_cons,twilled,Fintype.sum_bool]
       simp_rw [takeout, reduceCtorEq] -- maybe
       simp only [↓reduceIte,read_next]
-- one bound with arbitrary Y,Z union.
lemma wired (ha:0≤a)(h:W ⊆ Y∪Z)(he:x∈Y)(hf:y∈Z) : lump l W a p m ξ (f*g) ≤ liftW a p (separation x y) * Yarn (ι:=Bool) m (fun A=> lump l Y a p (parts true A) ξ f*lump l Z a p (parts false A) ξ g):=by
   let e:=liftW a p (separation x y); let C (T:List σ)(L:List Bool):=rate l Y a p ξ f (takeout true L T)*rate l Z a p ξ g (takeout false L T)
 -- delete
   have hi(T : List σ)(hx:T.length=m): rate l W a p ξ (f*g) T ≤ e*Yarn m (fun A=> C T A):=by
       let v:= spread l W a p T; unfold rate; rw [splitN, hx]
       refine (mul_le_mul_of_nonneg_left (polished ..) (effect l a p W T |>.le)).trans ?_
       rw [←sheen,←sheen]; refine shiny m ?_; intro L hL; rw [abs_mul]
       let P₀ := takeout true L T; let Q:= takeout false L T; have hx' : zone l W T⊆ zone l Y P₀ ∪ zone l Z Q:=by
           intro i hi; rcases mem_union.mp hi with ha|hb
           · rcases mem_union.mp (h ha) with he|he; exact mem_union_left _ (mem_union_left _ he); exact mem_union_right _ (mem_union_left _ he)
           obtain ⟨j,hj,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hb); rcases spark T hj L (hL.trans hx.symm) with he|he; exact mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨j,he,rfl⟩))); exact mem_union_right _ (mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨j,he,rfl⟩)))
       apply (mul_le_mul_of_nonneg_right (w_cast hx' (Finset.mem_union_left _ he) (Finset.mem_union_left _ hf) ha p) (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq; unfold e C rate spread P₀ Q; ring
   unfold lump; calc
    _ ≤ Yarn m (fun L=> e*Yarn m (C L)):= shiny m hi
    _ = _ := by rw [sheen, pool]; refine congr_arg (_*·) (stitch _ ?_); exact fun L he=> knot m L he ..
-- Ledger absolute sum.Wells. Neatly.Any evaluation ξ.Send.Output not yet. Bound messages pinned.All-proof.
structure LoopNet (l:σ→ Site n)(a:ℝ)(p:ℕ)(k:σ→σ→ℝ)(c : ℝ) : Prop where
   hope : 0≤c
   glow i: ∑ j:σ,|k i j| * liftW a p (separation (l i) (l j))≤c
   forward i : ∑ j:σ,|k j i| * liftW a p (separation (l j) (l i)) ≤ c
namespace LoopNet
variable {l}
lemma loom {k:σ→σ→ℝ}(hp:LoopNet l a p k b): LoopNet l a p (fun i j=> k j i) b:=by
    refine ⟨hp.hope,fun i=> ?_,fun i=>?_⟩
    · simp_rw [separation_comm (l i)]; exact hp.forward i
    simp_rw [show ∀ j:σ,separation (l j) (l i)=separation (l i) (l j) from fun j=> separation_comm ..]; exact hp.glow i
lemma single {k:σ→σ→ℝ}(ha:0≤ a)(hp:LoopNet l a p k b)(i j:σ): |k i j| ≤ b:= (le_mul_of_one_le_right (abs_nonneg _) (w_start ha p _)).trans ((single_le_sum (f:=fun j=> |k i j| * liftW a p (separation (l i) (l j))) (s:=univ) (fun i _=>mul_nonneg (abs_nonneg _) (wpos ..|>.le)) (mem_univ j)).trans (hp.glow i)) -- inference direction
end LoopNet
end YM.MSbar.Whisk
