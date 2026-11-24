import YM.MSbar.Wave.Reedy
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Function Filter Rolling Price Tensor
open scoped Topology Classical BigOperators ContDiff
variable {n:ℕ}{f:ℝ→ℝ}
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "µ"=>Tensor.coeff
local notation "X"=> ℝ×ℝ
local notation "v₀"=> ((1:ℝ),(0:ℝ))
local notation "v₁"=>((0:ℝ),(1:ℝ))
local notation "H"=> WithTop ℕ∞
variable (F:ℝ×ℝ→ℝ)
lemma lyric (j:ℕ)(f:X→ℝ)(t:X)(u:X) (h:ContDiffAt ℝ ω f t):ContDiffAt ℝ ω (fun x => pine f j x u) t:=by
    let L : Tensor.T X ℝ j→L[ℝ] ℝ := ((j.factorial:ℝ))⁻¹ • ContinuousMultilinearMap.apply ℝ _ ℝ (fun _=>u)
    have he:ContDiffAt ℝ ω (iteratedFDeriv ℝ j f) t:=h.iteratedFDeriv_right (by simp)
    exact L.contDiff.contDiffAt.comp t he
lemma pineOne (F:X→ℝ)(x y:X) : pine F 1 x y=fderiv ℝ F x y:=by unfold pine Tensor.diagonal Tensor.coeff; rw [_root_.smul_apply,iteratedFDeriv_one_apply]; simp
include n in
lemma bench (F:ℝ×ℝ→ℝ)(h:ContDiffAt ℝ ω F 0)(hx:∀ᶠ x:ℝ in 𝓝 0,Grade (fun t=>F (t,x)) (n+1)) : ∀ i,i≤n→ bill (fun t:ℝ=> pine F 1 (t,0) (0,1)) i=0:=by
    obtain ⟨U,hU,hu,h0⟩:= mem_nhds_iff.mp (h.eventually (by simp)); intro i hi
    let p(x:X):= pine F 1 x v₁; let q(x:X):= pine F i x v₀;
    have he: bill (fun t:ℝ=> pine F 1 (t,0) (0,1)) i= pine p i 0 v₀:=by
        rw [← lion p (0:X) v₀ i (lyric _ _ _ _ h)]; congr 1; ext t; simp [p]
    rw [he]; change pine _ _ _ _ = 0; rw [show pine p i 0 v₀=pine q 1 0 v₁ from Tensor.exchangeJet hu (fun i hi=> (show ContDiffAt ℝ ω F i from hU hi).of_le le_top) h0 _ _]
    have hp : q ∘ (fun t:ℝ=> (0:X)+t•v₁)=ᶠ[𝓝 0] (fun _=> 0) := by
        have hb: Tendsto (fun t:ℝ=>((0:ℝ),t)) (𝓝 0) (𝓝 (0:X)):= (continuous_const.prodMk continuous_id).continuousAt
        filter_upwards [hx,hb.eventually (hu.mem_nhds h0)] with t hx ht
        have ht': ContDiffAt ℝ ω F (0,t):=hU ht; have he': (fun x:ℝ=>F ((0,t)+x • v₀))=(fun x:ℝ=> F (x,t)):=by ext x;simp
        simp only [Function.comp_apply,zero_add]; rw [show t•v₁=(0,t) from (by simp), show q (0,t)=_ from (lion F (0,t) v₀ i ht').symm,he']; exact rebuilt hx (ht'.comp (f:=fun x:ℝ=>(x,t)) (0:ℝ) (contDiffAt_id.prodMk contDiffAt_const)) _ hi
    rw [← lion q 0 v₁ 1 (lyric _ _ _ _ h)]; unfold bill Tensor.diagonal; rw [show Tensor.coeff (fun t:ℝ=> q ((0:X)+t•v₁)) 1 0 = µ (fun _ :ℝ=>(0:ℝ)) 1 0 from Tensor.GermCoeff _ hp]; simp [Tensor.coeff]
end YM.MSbar.Wave
