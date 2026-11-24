import YM.Contacts.Poetry.Yard
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Downstream
/-!
 # Hybrid loan. Prepay ALL tilted regular channels; residual Γ_
   at SAME points; hard still meets the full mask repayment. Distinct from Resetter (topology & curve not asked).
 -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Revest
open AnalyticBridge VerifiedReset Collection
open Function Filter Set Lattice Wilson RG Ovens Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration
open AnalyticBridge VerifiedReset Collection Geo Averaging
open Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{n : Side}{R:PathData G}{c:Clip}{p:BudgetPoint}{σ C Λ H w δ γ : ℝ}{X:Listing G n}{v:Source G n}
namespace Hybrid
-- βtilt = already PAID for high path; at new βtilt+delta need only apply regular unsigned remainder finisher; fund full loan into same witness before fusion.
def pliant (X:Listing G n) (R:PathData G) (c:Clip) (p:BudgetPoint) (v:Source G n) (a:ℝ) : Tap G n :=
    { Collection.branch X R c p v a with regular := (Collection.branch X R c p v 0).regular }
variable (g:G.Simple)(hn:20<n.val)(h:Local X p v H w)(hx:R.Bounds c σ C Λ)(hc:Decent c p)(hw:Width p c σ)(a:ℝ)
include h
local notation "Z₀" => shelves X R p
local notation "P" => pliant X R c p v a
include g hn hx hc
lemma fittings : Payments.Fittings (P) (Z₀) p:= by
   let Δ:= delta (X.read v); have h1:=h.fittings g hx hc hn 0 Δ; have h2:=h.fittings g hx hc hn a Δ; refine ⟨h1.regular,h1.support,h1.moves,h2.visits,h2.steady,h2.looks,h2.reads,h2.carries⟩
include hw
lemma fund (hs:∃ m κ, softNeed G p c σ C a H ≤ m∧Payments.Rates p.B γ w m κ) : Ingredients (Z₀) (P) p (regularNeed G p c σ C 0 H) γ:= by
   let Δ:=delta (X.read v); have hΔ:=delta_bound g h.projects; obtain ⟨u,hu,hb⟩:=h.cheap; obtain ⟨k,hk,hK⟩:=h.expensive; obtain ⟨m,κ,hm,hR⟩:=hs; have he:= Local.quote_family hx hc hw 0 _ hu hb hΔ|>.1; have hL:= Local.quote_family hx hc hw a _ hu hb hΔ|>.2; have hQ (i:ℕ):=Local.quote_soft (R:=R) (c:=c) g a Δ hu h.smooth (numbering _ i); exact Payments.tender (fittings g hn h hx hc a) (show (Z₀|>.pours P).EBound p (regularNeed G p c σ C 0 H) from ⟨_,fun i=> Local.quote_regular g hx hc 0 Δ hu h.smooth (numbering _ i),fun x=>Cost.equiv (numbering _) (he x)⟩) (show Payments.hardCost p (Z₀) k w from ⟨fun i => (hk i).1,hK⟩) ⟨fun i => (norm_nonneg _).trans (hQ i 1),fun x=>Cost.equiv (numbering _) (Cost.enlarge (hL x) hm)⟩ (fun i U=>⟨(hk i).2 U,hQ i U⟩) hR
lemma engine (V:Config G n)(β τ:ℝ): let D:=delta (X.read v); (trunk R c p (Z₀) P (β+D) (vac v τ)).eval V *Real.exp (∑' i, (P).logarithm i V) = earlyValue X R c p v β τ 0 V * Real.exp (layer (fun d : Low => d.loan R c 0 p a 0) V) := by
   let Δ:=delta (X.read v); let g0:=Collection.branch X R c p v; let t:=τ; have hA:= h.raw_evaluator g hx hc hw 0 hn β τ V; let L (x y:ℝ):= layer (fun d : Low => d.loan R c 0 p x y) V
   have hQ : L a Δ = L 0 Δ+ L a 0 := by
       let f (x y:ℝ) (d:Low):= d.loan (n:=n) R c 0 p x y; have he:f a Δ=fun d U=>f 0 Δ d U+f a 0 d U:= by funext d U; unfold f Low.loan; split_ifs<;> ring
       change layer (f a Δ) V= _; rw [he, layer_combine (loan_sum hx hw hc 0 Δ) (loan_sum hx hw hc a 0)]
   have hk: ∑' i,(P).logarithm i V =(∑' i,(g0 0).logarithm i V)+L a 0:= (h.throw_sum g hx hc hw a Δ V).trans (by unfold L at *; erw [h.throw_sum g hx hc hw 0 Δ V,hQ, ← add_assoc])
   rw [add_zero β] at hA; intro D; rw [hk, Real.exp_add, ← mul_assoc, ← hA]
   rfl
end Hybrid
end YM.Contacts.Revest
