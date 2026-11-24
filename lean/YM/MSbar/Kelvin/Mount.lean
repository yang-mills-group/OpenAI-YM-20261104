import YM.MSbar.Kelvin.Coke
import YM.Push.STATIONARY_UNIFORM.ImplicitRadius
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical
open Lattice Matrix Push.Uniform
variable {ι σ τ: Type}[Fintype σ][Fintype ι][Fintype τ][DecidableEq σ] [DecidableEq ι]
    {n:Side}{l:σ→Site n}{X:ι→Site n}{L:ι⊕σ→Site n}{g:Positions (ι⊕σ)→ℝ}{k s A C : Matrix σ σ ℝ} {B' : Matrix ι ι ℝ}
    (u:ι→σ) (h:Injective u)
local notation "ι!"=> imbed u
local notation "p!"=> pinch u k
local notation "e!"=> extendM u
local notation "w!"=> vanish u k
local notation "dp"=> (pinch u k)⁻¹
variable {a b c t B W D r M:ℝ} {K p m N z :ℕ} {v:Site n}
-- membership growth requests calibrate matrix-logic.F.Season.B.Prior.Fee.L.Post.

structure Solver (i:ι→σ) (l:σ→ Site n)(a r c W:ℝ)(p:ℕ)(k : Matrix σ σ ℝ):Prop where
   bids : k.PosDef
   bsize : 0 ≤ c
   hsize : 0 ≤ W
   growth : LoopNet l (a+r) p (show Matrix σ σ ℝ from k⁻¹) c
   sealed : LoopNet l (a+r) p (extendM i ((pinch i k)⁻¹)) c
   travels : LoopNet l (a+r) p (vanish i k) W
local notation "X!"=>pinch u k
variable (S: Receipt L a N K c t M g)
def frond(k:ℕ)(C M a:ℝ):= tiltWidth k M a C/4
def funds(k p:ℕ)(a r t:ℝ):= r*(t*(k*countCost a))
-- param demand purchase.L.Multi stage
lemma chill (k p N :ℕ) (C M a:ℝ)(hc:0<C)(hm:0<M)(ha:0<a):
    let v:=frond k C M a
    0<v∧ ∃ W U :ℝ, ∀ (ι σ τ :Type)[Fintype ι][Fintype σ][Fintype τ][DecidableEq σ][DecidableEq τ] {n:Side} (L : ι⊕σ → Site n)(t:ℝ)(F:Positions (ι⊕σ)→ℝ), Receipt L a N k C t M F → ∀ (u:τ→σ),Injective u → ∀ (r b:ℝ),0≤b→0≤r→ b+r≤v→ Solver u (L ∘ Sum.inr) b r W U p (block F 0):=by
    intro v; let d:=tiltWidth k M a C; have hv:0<d:=tiltWidth_pos k hm ha hc.le; have hV:0<v:=div_pos hv (by norm_num); obtain ⟨r,he,hP⟩:= ropes _ (half_pos hv) p
    let y:=d-(v+d/2); have hy:0<y:= by dsimp only [y,d,v,frond]; unfold d at hv; linarith -- adjust
    let J:=funds k p y r ((M/2)⁻¹); let W':= funds k p (a-(v+d/2)) r C
    refine ⟨hV,J,1+J*W',?_⟩; intro ι σ τ i1 i2 i3 i4 i5 T l t F h u hx r' b hr hq hY
    let k':=block F 0; let L:=l∘ (Sum.inr:σ→ ι⊕σ)
    have hp:= h.born 0 (Metric.mem_ball_self h.pos_r); have he := block_rows hp.2 (show 2 ≤N from Nat.le_trans (by omega : 2 ≤ 3) h.order); have ht:= h.mult.comp (f:=(Sum.inr:σ→ι⊕σ)) Sum.inr_injective -- parameter
    have hD : k'.PosDef:= Charge.positive h.gap (block_hermitian hp.1) hm
    have hh := inverse_sealed he hm ha h.gap hc.le ht (isUnit_iff_ne_zero.mpr hD.det_pos.ne'); have hν := fence u hx hD ha hm h.gap he ht hc.le -- should d inv constants
    have hk : v+d/2<d:=by unfold y at hy; linarith only [hy];
    have hg : d ≤ a:=by have he : d≤ a/4:=min_le_left ..;linarith
    have hx':0 ≤ (M/2)⁻¹:=inv_nonneg.mpr (half_pos hm).le
    have hI : LoopNet L (b+r') p (show Matrix σ σ ℝ from k'⁻¹) J:= LoopNet.low hY (weave hx' hh ht hk hP); have hT := LoopNet.low hY (weave hx' hν ht hk hP); let U:=extendM u ((pinch u k')⁻¹)
    have hW:LoopNet L (b+r') p k' W':= LoopNet.low hY (weave hc.le he ht (hk.trans_le hg) hP)
    have hA:=factor_Q u hx hD (add_nonneg hr hq) hW hT; exact ⟨hD,hI.hope,hA.hope,hI,hT,hA⟩
include h
-- Pad from spatial τ to arbitrary xi. This means.Symbol.Ocean
lemma reaching (J:LoopNet (l ∘ u) a p B' M) :LoopNet l a p (extendM u B') M:=by
    let F:= extendM u B'
    have hu (m:σ→ℝ)(he:∀ j,j ∉ Set.range u→m j=0): ∑ i,m i=∑ i,m (u i) := by
       let X:=Finset.univ.image u; calc
         _ = ∑ i∈X,m i:= (sum_subset (subset_univ _) (fun i _ hx=> he i (by simpa [X,Set.range] using hx))).symm
         _ = _ := by unfold X; exact sum_image (fun _ _ _ _ hv=> h hv)
    have hF(i j) : extendM u B' (u i) (u j)=B' i j:= congr_fun (congr_fun (embeds u h B') i) j
    have hZ(i j)(hi : i∉ Set.range u ∨ j∉ Set.range u): extendM u B' i j=0:= squeezed u hi
    refine ⟨J.hope,fun i=>?_,fun i=>?_⟩
    · by_cases hi:i ∈ Set.range u
      · obtain ⟨i,rfl⟩:=hi; rw [hu]; swap;· intro j hj; rw [hZ _ _ (Or.inr hj),abs_zero,zero_mul]
        simp_rw [hF]; exact J.glow i
      simp_rw [fun j=> hZ _ j (Or.inl hi)]; simpa using J.hope
    by_cases hi:i∈ Set.range u
    · obtain ⟨i,rfl⟩:=hi; rw [hu]; swap;· intro j hj; rw [hZ _ _ (Or.inl hj),abs_zero,zero_mul]
      simp_rw [hF]; exact J.forward i
    simp_rw [fun j=> hZ j _ (Or.inr hi)]; simpa using J.hope
end YM.MSbar.Kelvin
