import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
import YM.AllOrder.Gyro.Nu
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n}
namespace Weaving
/- Retarget early residual but take logarithms with a different prescription.
 Debits differ.F.Read. -/
variable (p X v R c)
local notation "Ω"=>fill X R c p v
def dawnK (α Δ : ℝ) : Tap G n:={ Ω 0 Δ with logarithm:= loses X R c p v α Δ ∘ numbering _ }
variable {p X v R c}
local notation "Q" => shelves X R p
variable (g:G.Simple)(h: Collection.Local X p v H w) (A:R.Bounds c σ C Λ)(hc:Decent c p)(hW:Width p c σ)(hn:20 < n.val)(α Δ:ℝ)
local notation "D"=> dawnK R c p X v α Δ
include g h hn A hc
lemma ok : Payments.Fittings (D) (Q) p:= by
 let hv:= h.fittings g A hc hn 0 Δ; let he:= h.fittings g A hc hn α Δ; exact ⟨hv.regular,hv.support,hv.moves,he.visits,he.steady,he.looks,he.reads,he.carries⟩
-- no assumption projection EXACT on this v.Apply closure ledger after accrual. Want proof energy sign. Define income.Masked.Low restore.Early.Spec.
include hW
lemma members (he:p.threshold^2 * |Δ|≤ H): ((Q).pours (D)).EBound p (regularNeed G p c σ C 0 H)∧
    ∃ u v':ℕ→ℝ,Payments.rooted (D) u v'∧ Payments.hardCost p (Q) u w ∧ Payments.softCost p (Q) v' (softNeed G p c σ C α H) := by
 obtain ⟨u,hu,hb⟩:= h.cheap; obtain ⟨k,hk,hK⟩:= h.expensive; let hE:= Local.quote_family A hc hW (α:=0) (Δ:=Δ) hu hb he -- name scope
 let hL:= Collection.Local.quote_family A hc hW α _ hu hb he; let hQ(i:ℕ):= Collection.Local.quote_soft (R:=R) (c:=c) g α Δ hu h.smooth (numbering _ i)
 refine ⟨⟨_,fun i=>Collection.Local.quote_regular g A hc 0 Δ hu h.smooth (numbering _ i),fun x=>Cost.equiv (numbering _) (hE.1 x)⟩,k,_,fun i U=> ⟨(hk i).2 U,hQ i U⟩, ⟨fun i=>(hk i).1,hK⟩,fun i=>(norm_nonneg _).trans (hQ i 1),fun i=> Cost.equiv (numbering _) (hL.2 i)⟩
-- expenditure sign: target actual β= input β + A+ δ`. Here A = old α + ∆f. subtract α+∆f on true kinetic, add loan. EarlySmall.Representation.Care. doc.
abbrev highH (R:PathData G) (p:BudgetPoint) : Config G n→ℝ:= layer (fun i=> summit R p i 0)
lemma thread (U:Config G n): layer (upperFade R p 0 Δ) U= layer (upperFade R p α Δ) U + α* highH R p U:= by
 have he(a:ℝ):layer (upperFade R p a Δ) U= -(a+Δ) * highH R p U:= by rw [show upperFade (n:=n) R p a Δ=_ from funext (fun i=>funext fun u=> Collection.high_fade_eq a Δ u i),layer_scale ..] -- simp
 rw [he,he]; ring
lemma symbolizes (U:Config G n)(β τ:ℝ): let t:= trunk R c p Q D (β+α+Δ) (vac v τ); let S:ℝ:=∑' i:ℕ,(D).logarithm i U; let V:=frozen X R c p v β τ; let Δ':=delta (X.read v); t.exponent U + S= V.exponent U -α*receipt R c p U - α * highH R p U + (Δ'-Δ)*(∑ o, heads p o U):= by
 intro t S V Δ'; have hY:= h.additive g A 0 Δ U; have hz:= h.throw_sum g A hc hW α Δ U; have ht:= h.first_split g hn U; have hv: S= _ := hz; let f := layer (fade R c p Δ) U; let G₀:=∑' i,untagged X p v i U; have hm: t.activities.additive p U=G₀+ (f+layer (upperFade R p 0 Δ) U):= hY
 change vac v τ * _ - R.inChannels c p (β+α+Δ) U - t.activities.additive p U+S= (τ*_ -R.inChannels c p β U -(X.read v).additive p U)-α*receipt _ _ _ U -_+ _;  rw [show (Fintype.card (Site n):ℝ)=UVNext.CouplingReset.sites n from rfl, hm, hv,vac,sub_mul,div_mul_cancel₀ _ (UVNext.CouplingReset.sites_pos n).ne', channels_split U (β+α+Δ),channels_split U β,thread g h A hc hW hn α Δ U]; have he:= path_split A hW hc α Δ U; unfold Collection.receipt; unfold Δ' G₀ f; linarith only [he,ht] -- sign ok?
end Weaving
end YM.AllOrder.Rosary
