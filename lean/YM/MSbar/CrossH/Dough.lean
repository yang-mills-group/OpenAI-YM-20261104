import YM.MSbar.CrossH.Slate
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.CrossH
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice
open scoped Topology BigOperators ContDiff Classical
variable {σ ι:Type}[Fintype σ][Fintype ι][DecidableEq σ][DecidableEq ι]
open Polynomial MvPolynomial Matrix Rolling
local notation "P"=> Cacao.Pot σ
local notation "∆"=>PowerSeries.coeff
variable {n:Side}{l:σ→Site n}{L : ι→Site n}{a b w t u B:ℝ}{f g:Cacao.Pot σ}{m s k r v p:ℕ}
noncomputable def skim (l:σ→Site n)(L:ι→Site n)(a:ℝ)(s:ℕ)(i:σ)(j:ι):= factor a s (2*separation (l i) (L j))
structure Syrup (l:σ→Site n)(L:ι→Site n)(a:ℝ)(s:ℕ)(z:Matrix σ ι ℝ)(b:ℝ) :Prop where
   cash : 1≤ b
   leftP (i:σ) : (∑ j:ι,skim l L a s i j *|z i j|) ≤ b
   rightP (j:ι): (∑ i:σ, skim l L a s i j *|z i j|) ≤ b
-- preGold same site.L.S count construct Identity Ratio n n. Option prove directly Whisk.S.Common
lemma ratioId (n:Side) : ∃g:Ratio n n,g.count.val=1 ∧ g.embed=id:=by
    let g:Ratio n n:=⟨1,by simp⟩; refine ⟨g,rfl,?_⟩; funext i; unfold Ratio.embed; simp [g] -- inspect
namespace Tin
variable {z: Matrix σ ι ℝ}(h:Syrup l L a s z b)(hp:0≤a)
variable (hw:0<w) (he:Tin l a s m w f t)
include h hp hw he
lemma scaleT : Tin L a s m w (Rolling.rail z f) (b^(m+1)*t):=by
    let S:= LinearMap.toContinuousLinearMap (Matrix.toLin' z); have hh:h.cash=h.cash:=rfl; have hB:1≤b:=h.cash; have hx:= he.dec
    refine ⟨by positivity,fun j hj i=> ?_⟩; let k:= j+1
    have hv: clue (Rolling.rail z f)=clue f ∘ S:=funext fun i=>congr_fun (Rolling.clearL z i) f
    let F:= buoy (clue f) 0; obtain ⟨g,hc,hE⟩:= ratioId n
    have hL(i j) : bonus g l L a s i j= skim l L a s i j:=by unfold bonus skim; rw [hc,hE,Nat.cast_one,div_one]; rfl
    let Y:= t/w^k
    have hy:0≤Y:=by unfold Y; positivity
    have h0(i:σ)(j:ι): S (bolt j) i=z i j:=by change (∑ x:ι,z i x * bolt j x)=_; simp [bolt,Pi.single_apply]
    have hH : Yarn j (fun t:List ι=> swipe L a s (i::t)*ter (j+1) z (fun i=>|F i|) (i::t)) ≤ Y*b*b^j := preGold g l L z hp (by simp only [hc,Nat.cast_one,div_one, le_refl]) (zero_le_one.trans hB) (show ∀ i, _ from fun i=> by simp_rw [hL]; exact h.leftP i) (show ∀ i,_ from fun i=> by simp_rw [hL]; exact h.rightP i) (fun i=>|F i|) Y (fun _ _=> abs_nonneg _) (fun i=> (scored f i).le.trans (he.fan _ hj i)) hy i
    rw [← scored]; calc
        _ ≤ Yarn j (fun t:List ι=> swipe L a s (i::t)*ter (j+1) z (fun i=>|F i|) (i::t)):=by
            apply shiny; intro T ht
            rw [hv,paint (clue f) S _ _ k ((helm f k).contDiffAt) (by simp [ht,k]),map_zero,show (fun i j=> S (bolt j) i) = z from funext fun i=> funext fun j=> h0 i j,mul_comm]; apply mul_le_mul_of_nonneg_left _ (effect ..|>.le); unfold shaft ter; rw [List.length_cons,ht]; exact (polished ..).trans (shiny _ fun v h=> (abs_mul ..).le)
        _ ≤ _:= hH.trans (le_trans (b:=b^(m+1)*Y) ?_ (le_of_eq (by unfold Y; ring)))
    rw [show Y*b*b^j=b^(j+1)*Y from (by ring)]; apply mul_le_mul_of_nonneg_right _ hy; gcongr
end Tin
end YM.MSbar.CrossH
