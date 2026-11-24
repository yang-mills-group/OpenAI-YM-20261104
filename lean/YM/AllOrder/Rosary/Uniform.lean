import YM.AllOrder.Rosary.Track
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
namespace Guard
open Lapis Herb Weaving Morning
variable (h: R.Bounds c σ C Λ) (he: Decent c p)(hv: Width (pearl p) c σ)(hn: 20<n.val)(g:G.Simple) (u k:ℝ) (M: Burn.Locale G) {Y₀:ℝ}
    (hm:∀ i:Site n,Till.Fairness p i (court i p.B) (M n i) Y₀) (hW:PhysicalNext.Repeat.Trio.Mirrors (M n))
variable (hX: Collection.Local X p v H w)
local notation "Rξ"=> Devotion.basil (n:=n) p M
local notation "Y₁"=> ruby n G u
local notation "Y₂"=> blue (-u) R c p n
local notation "Y₃"=> pink (-k) R p n
local notation "τ"=> keys n
local notation "δ"=> Averaging.delta
include hm hW
abbrev costM (p:BudgetPoint)(y:ℝ):ℝ:= y*Real.exp ((preExponent p)*(↑(1:ℕ):ℝ))
lemma basil_fit : (Rξ).Proto p (costM p Y₀) ∧ (Rξ).mu=0:=by -- syntax
 refine ⟨tiny_rows _ (κ':=1) (fun i=>rfl) (fun i=>Burn.shell p i) (Devotion.lives hm hW |>.1) (fun i=> ⟨(hm i).ready,(hm i).cap⟩), Herb.still (fun i=> (hm i).he)⟩
abbrev totalFee (p:BudgetPoint)(G:Gauge)(c:Clip)(σ C k u Y H:ℝ):=costM p Y+(costP G p σ C (-k)+(costB G p c σ C (-u)+(costR G p u+H)))
include h he hv hn g hX
local notation "X₁"=> Herb.deck τ Y₁ X
local notation "v₁"=> Herb.ink τ Y₁ v
local notation "ψ"=> numbering (FFace n⊕ℕ)
local notation "Ψ"=> numbering (FPeak n⊕ℕ)
local notation "X₂"=> Herb.deck ψ Y₂ X₁
local notation "v₂"=> Herb.ink ψ Y₂ v₁
local notation "X₃"=> Herb.deck Ψ Y₃ X₂
local notation "v₃"=> Herb.ink Ψ Y₃ v₂
local notation "X₄"=> Herb.deck τ (Rξ) X₃
local notation "v₄"=> Herb.ink τ (Rξ) v₃
def portal (p:BudgetPoint)(k:ℝ)(R: PathData G)(c:Clip)(M:Burn.Locale G)(X:Listing G n)(v:Collection.Source G n)(β y:ℝ)(U: Config G n):= (frozen X R c p v β y).eval U * Real.exp (- k*(receipt R c p U+highH R p U)- Morning.news M p U)
lemma future : Collection.Local (X₄) p (v₄) (totalFee p G c σ C k u Y₀ H) w ∧
    (∀ β y U, flags p.threshold U=∅→ earlyValue X₄ R c p v₄ β y (k-u) U= portal p k R c M X v β y U) ∧ δ (Listing.read X₄ v₄)= δ (X.read v)+ u:=by
 obtain ⟨hA,hδ₁⟩:=marveled u g he.radius hn; obtain ⟨hB,hδ₂⟩:= wages (-u) h hv hn he g; obtain ⟨hC,hδ₃⟩:= crowns (-k) h hv hn he g; obtain ⟨hD,hδ₄⟩:= basil_fit M hm hW
 let hx:=Herb.why τ hX hA; let hy:= Herb.why ψ hx hB; let hz:=Herb.why Ψ hy hC; let hu:=Herb.why τ hz hD; refine ⟨hu, ?_, by rw [(pull_δ τ hz g hD).1,(pull_δ Ψ hy g hC).1,(pull_δ ψ hx g hB).1,(pull_δ τ hX g hA).1,hδ₁,hδ₂,hδ₃,hδ₄]; ring⟩
 intro β ℓ U hU; unfold portal earlyValue Rep.eval Rep.exponent; dsimp only [frozen]; rw [Activities.gas_one _ _ hU,mul_one, Activities.gas_one _ _ hU,mul_one,←Real.exp_add, ←Real.exp_add]; apply congr_arg Real.exp;
 rw [(showS τ hz hD U).1,(showS Ψ hy hC U).1,(showS ψ hx hB U).1,(showS τ hX hA U).1,(salary (-k) h hv hn he g U).2,(salary (-u) h hv hn he g U).1,gems u g he.radius hn U hU, flareB (-u) h hv hn he g U hU, teller,tsum_fintype,← show Morning.news M p U=∑ i,(Rξ).occG p i U from rfl]; ring
variable {Ξ:Cane G n ι} {X':Listing G n} {v':Collection.Source G n} {W H' σ' ℓ' β:ℝ}
    (hs:Collection.Local X' p v' H' W)(ℓ:ℝ)
    (hq:∀ U:Config G n, flags p.threshold U=∅→ portal p k R c M X v β ℓ U=earlyValue X' R c p v' β ℓ' (k-u) U)
open Gyro
include hs hq
lemma gauge_cost : |(δ (X.read v)+u)- δ (X'.read v')| ≤ reward n p.threshold * vault n p (totalFee p G c σ C k u Y₀ H+H'):= by
 obtain ⟨hz,hℓ,hΔ⟩:= future h he hv hn g u k M hm hW hX;
 rw [← hΔ]; refine Gyro.schiz g hz hs hn ?_; refine ⟨(ℓ-ℓ')*Fintype.card (Site n),fun U hU=>?_⟩; have he := (hℓ β ℓ U hU).trans (hq U hU); unfold earlyValue at he; have he:=mul_right_cancel₀ (Real.exp_pos _).ne' he; unfold Rep.eval Rep.exponent at he; simp only [frozen,Activities.gas_one _ _ hU,mul_one] at he; linarith only [Real.exp_injective he]
omit h hv he hm hW hn hX hq g hs
lemma port_star (U:Config G n)(ℓ:ℝ)(h:Cane.Ready Ξ p H)(hU:flags p.threshold U=∅): portal p k R c M X v β ℓ U=truth (c:=c) (p:=p) R X v Ξ k M (fun f o=>(0:Pot G f)) U β ℓ:= by
 unfold portal truth; have he(i:ι):Ξ.values i U=0:= by_contra fun hz=> (h.2.1 i).2.2.2 U hz (by simp only [Healthy,hU]; simp)
 rw [show news (fun f o=>(0:Pot G f)) p U=0 from Finset.sum_eq_zero (fun i _=>masked_eq _ _ _ _ (show Healthy p.threshold _ U from by unfold Healthy; rw [hU]; simp))]; simp_rw [he,tsum_zero,zero_sub,add_zero, sub_eq_add_neg]
end Guard
end YM.AllOrder.Rosary
