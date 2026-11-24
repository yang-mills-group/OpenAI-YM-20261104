import YM.MSbar.CrossH.Stout
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.CrossH
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice Tensor
open scoped Topology BigOperators ContDiff Classical
variable {σ ι β X:Type}[Fintype σ][DecidableEq σ][Fintype ι][DecidableEq ι]
open Polynomial MvPolynomial Matrix Rolling
local notation "Θ"=> Cacao.Pot σ
local notation "Q"=>Positions σ
local notation "∆"=>PowerSeries.coeff
variable (F:ι→Positions σ→ℝ)
variable {a b t u:ℝ}{k p q v:ℕ}{n:Side}{l:σ→ Site n}{L:ι→ Site n}
lemma piano (i:σ): ‖(bolt i:Q)‖ ≤ 1:=pi_norm_le_iff_of_nonneg (by norm_num)|>.mpr fun x=>by by_cases h:x=i <;> simp [bolt,h]
noncomputable def haul (σ:Type)[Fintype σ][DecidableEq σ] (F:Finset σ):Positions σ→ Positions σ:=fun x v=>if v∈F then x v else 0 -- shadow remove
lemma native(i:ι)(q:ℕ) {S:Side}(L:σ→ Site S)(x:Site S)(n:ℕ) (E:ℝ)(hp:ContDiffAt ℝ (↑(q+1:ℕ)) (F i) 0)(hc: ‖iteratedFDeriv ℝ (q+1) (F i) 0‖ ≤ E)(he:F i ∘ haul σ (curbL L x n) =ᶠ[𝓝 0] F i): Lumber L x n (F i) q E:=by
    let W := curbL L x n; let P : Q →L[ℝ] Q:= LinearMap.toContinuousLinearMap ({
       toFun:=haul σ W
       map_add':= by intro i j; funext x; unfold haul; split <;> simp_all
       map_smul':= by intro i j; funext x; unfold haul; split <;> simp_all } : Q→ₗ[ℝ]Q)
    refine ⟨(norm_nonneg _).trans hc,hp,fun t h=>?_,fun t hi H j hj=>?_⟩
    · rw [CrossH.chain _ _ _ _ hp h.le,←Real.norm_eq_abs]; apply le_trans (ContinuousMultilinearMap.le_opNorm ..); calc
          _ ≤ ‖iteratedFDeriv ℝ t.length (F i) 0‖*∏ i:Fin t.length,(1:ℝ):=by gcongr;exact piano ..
          _ ≤ E:=by simp only [Finset.prod_const_one,mul_one]; exact h.symm ▸ hc
    by_contra hj'; apply H; unfold buoy; let X':=t.map Uniform.bolt; have hX:X'.length=q+1:=by simp only [X',List.length_map,hi];
    have hP:0∈ X'.map P:=by
       refine List.mem_map.mpr ⟨bolt j,List.mem_map.mpr ⟨j,hj,rfl⟩,?_⟩; funext x; change (if x ∈ W then bolt j x else 0)=0; split; next h=> have hx:x≠j:=fun he=>hj' (he▸h); simp [bolt,hx]
       next ht=> rfl
    rw [← show roc (F i ∘ P) X' 0= _ from ((Lis.follows _ he).eq_of_nhds), toe P (q+1) _ (show ContDiffAt ℝ (↑(q+1:ℕ)) _ (P 0) from (map_zero P).symm ▸ hp) hX.le, map_zero]; exact Lis.emptyF _ _ _ hP hp (by simp only [List.length_map,hX,le_refl])
variable (h:∀ i,Lumber l (L i) v (F i) q t)(hk:0 ≤ t)(hp:0≤a)(G:Positions σ→ℝ)(he: G=ᶠ[𝓝 0] fun y=> ∑ i,F i y)
local notation "g!"=>potter G (q+1)
include h hp hk he
lemma scaleBook(M N:ℕ)(hf:Multiplicity l M)(hx:Multiplicity L N)(u:ℕ) : Tokew l a p u 0 (potter G (q+1)) (cities N v * rugL a t p v q (cities M v)):=by
    let g:= fun x=>∑ i,F i x; have hi:ContDiffAt ℝ (↑(q+1:ℕ)) g 0:= ContDiffAt.sum fun i _=> (h i).smooth; have hG:ContDiffAt ℝ (↑(q+1:ℕ)) G 0:= hi.congr_of_eventuallyEq he
    have hv: 0 ≤ ((cities N v:ℕ):ℝ) * rugL a t p v q (cities M v):=mul_nonneg (by positivity) (mul_nonneg (by positivity : 0 ≤ ((cities M v:ℕ):ℝ)^q) (mul_nonneg hk (wpos ..|>.le)))
    refine (token _).mpr ⟨hv,fun j hj i=>?_⟩
    rw [← scored]; by_cases hs:j=q
    swap
    · refine le_trans ?_ hv; rw [← spool (ι:=σ) (A:=ℝ) j]; refine shiny _ fun T ht=>?_ ; rw [ports G _ hG (by omega) (i::T) (by simp)]; split; next h=> rw [List.length_cons,ht] at h; omega
      next h=> rw [abs_zero,zero_mul]
    subst j
    let B(j:ι):=potter (F j) (q+1)
    have hB(i:ι): Lumber l (L i) v (clue (B i)) q t:=by
       have hb(T:List σ)(hh:T.length=q+1) : buoy (clue (B i)) 0 T= buoy (F i) 0 T:=by unfold B; rw [ports (F i) _ (h i).smooth (by omega) T (by omega),if_pos hh]
       exact ⟨hk,(helm _ _).contDiffAt,fun i' hi=> hb i' hi|>.symm ▸ (h i).cash i' hi,fun k hi hm=>(h i).pace k hi (hb k hi ▸ hm)⟩
    refine le_trans ?_ (logHome l hp L B hB (fun x=>dressP _ hf x v) (fun x=>dressP L hx x v) hk i)
    rw [←scored]; apply shiny; intro T ht
    have hS : (i::T).length=q+1:=by simp only [List.length_cons,ht]
    have hx : ((i::T).map Uniform.bolt).length≤ q+1:=by simp only [List.length_map,hS,le_refl]
    have H : buoy (clue g!) 0 (i::T)= ∑ j:ι,buoy (F j) 0 (i::T):=by
        rw [ports _ _ hG (by omega) _ (by simp),if_pos hS]; unfold buoy; rw [(Lis.follows _ he).eq_of_nhds]; exact Lis.tot (q+1) _ _ F (fun i _=> (h i).smooth) hx -- notation
    rw [H]; have hi: clue (∑ i,B i) =fun x=>∑ i,clue (B i) x:=by unfold clue; simp
    rw [hi]; refine le_of_eq (congr_arg (fun v:ℝ=>|v| *_) ?_ ); symm; unfold buoy; rw [Lis.tot (q+1) _ _ _ (fun i _=> (hB i).smooth) hx]; apply Finset.sum_congr rfl; intro j _; exact (ports (F j) (q+1) (h j).smooth (by omega) _ (by simp : (i::T).length≠0)).trans (if_pos hS)
end YM.MSbar.CrossH
