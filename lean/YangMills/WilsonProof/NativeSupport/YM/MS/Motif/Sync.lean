import YM.MS.Motif.Sync
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.K2
/-!
# synchronise Hessian with plane-wave charge. Sym computed for canonical letters
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Native
open Complex (I)
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{n:ℕ} {U V:Mield G n}{F H:Rack G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 " ⋄ "=> product S
lemma p_sym (p:Chan G n): Symm S ( applyS 0 G n p ) := by
    rcases p with ⟨_|p,i⟩; · simp only [applyS,Sc,neg_zero,zero_div,zero_smul, Pi.zero_apply]; exact Symm.zero
    unfold applyS convoke; simp [zero_smul]; exact m_sp ( F:= cwave n G i ) (note_sym ( onX false (none,i) ) (fun _=>1)) _ -- maybe simp
lemma ploy_sym : Symm S ( ploy G 0 n ):= by
   unfold ploy core; simp only [cur,zero_smul,add_zero]; refine (Symm.smul (p:=S) _ (Symm.sum _ (fun a _=> Symm.sum _ (fun b _=>Symm.sum _ (fun i _=>?_)))) ).add ?_; exact (mono_sym a b i).times (mono_sym a b i); exact Symm.sum _ (fun i _=> Symm.smul _ (Symm.times ( note_sym ( onX true i) (fun _:SectorP n=> (1:ℂ))) (p_sym i))) -- metavariables
lemma ploy_p (z:ℂ): Pure S false (ploy G z n):= (core_g z|>.1).add (cape0 (application z))
lemma kernel (i j:G.ColorIndex)(a b:Arts.L n)(p:SectorP n) : core G n 0 [(at_g a i,-p),(at_g b j,p)]=if i=j then -(precision a b p:ℂ) else 0:= by
   have hh(a b k:Arts.L n)(p:SectorP n): polar0 a b k (-p) = -polar0 a b k p := by unfold polar0 Landau.delta; split_ifs <;> simp [neg_sub] ; ring
   let X(k l:Arts.L n)(c:G.ColorIndex):= (F₀ k l c ⋄ F₀ k l c) [(at_g a i,-p),(at_g b j,p)]
   have he (k l:Arts.L n): ∑ c:G.ColorIndex,X k l c= X k l i:= by rw [Finset.sum_eq_single i]; intro b' hb ht; unfold X; rw [pairv (rank_α _ _ _) ( rank_α _ _ _), f_ref _ _ a, if_neg (Ne.symm ht)]; ring; simp
   rw [core_α]; change (-(1/4):ℂ) • ( ∑ k:Arts.L n,∑ l:Arts.L n,∑ c:G.ColorIndex,X k l c)=_; simp_rw [he]; by_cases hu:i=j; swap;
   · unfold X; simp_rw [pairv ( rank_α _ _ _) (rank_α _ _ _), f_ref, if_neg (Ne.symm hu), if_neg hu]; simp
   subst j; rw [if_pos rfl]; have hm (k l): X k l i=2*((polar0 k l a p*polar0 k l b p:ℝ):ℂ):= by
       unfold X; rw [pairv ( rank_α _ _ _) (rank_α _ _ _), f_ref _ _ a, f_ref _ _ b]; simp only [↓reduceIte,cross_false,show S (at_g a i,-p)=false from rfl]; rw [show delta l a ((-p) k) - delta k a ((-p) l)=_ from hh k l a p]; have hl: delta l b (p k)-delta k b (p l)=polar0 k l b p:= rfl; rw [hl]; linear_combination (norm:=(push_cast; ring)) - (↑(polar0 k l a p):ℂ)*(polar0 k l b p) * 2 * Complex.I_sq
   simp_rw [hm,← Finset.mul_sum, ← Complex.ofReal_sum]; rw [pol_net]; simp only [smul_eq_mul]; push_cast; ring
end YM.MS.Motif
