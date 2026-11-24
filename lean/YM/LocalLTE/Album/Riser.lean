import YM.LocalLTE.Pond.Tactic
import YM.MergeProof.Ginger
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
local notation "η"=>p.supportExponent
open Mallow Marlin

include hR hv
lemma torqued : Ac.Hit (n:=n) (fun i:Spikes n=>(Price.ridge R p i).support) p.B (Price.unitH p R α Δ) ((raiser p).supportExponent+1) (Real.exp (ballCost 2:ℝ) * Price.lofty p G σ C' α Δ):=by
    let Z:= (raiser p).supportExponent; let u:= unitH (n:=n) p R α Δ
    have hk i: 0≤ u i:= Price.atop ..
    intro i; have he:= budget_scale (Real.exp_pos (ballCost 2:ℝ)).le (Price.torrid (n:=n) Δ α p R hR hv i); refine budget_mono he (fun i=> ?_) ?_
    · split; exact mul_nonneg (hk _) (Real.exp_pos _).le;exact le_rfl
    intro x; split
    next h =>
       rw [mul_left_comm]; by_cases hp: Price.changed p R x
       · apply mul_le_mul_of_nonneg_left _ (hk x); rw [← Real.exp_add]; apply Real.exp_monotone
         let v :ℝ:=coverNumber p.B (Price.ridge R p x).support; have ht: v≤ ballCost 2:=by unfold v; rw [Price.stationH p R x hp]; exact_mod_cast Scarf.standing (2*p.B) p 2 x.1.2 le_rfl
         have hy : (raiser p).supportExponent=p.supportExponent+1:=rfl; rw [hy]; linarith only [ht]
       -- need if unchanged cost =0; move before apply
       unfold unitH; rw [if_neg hp,zero_mul,zero_mul]
    next h=> rw [mul_zero]

include hG hn hd
open Progress.DirectedRecipe Payments Ovens.Pipes
variable {T:ℕ→ EKey n→ Pot G n}
lemma paladin (h:Collection.Local X p g a w) : let Δ:=Averaging.delta (X.read g)
    Vapor (Price.bells p R X N) (Price.azures c p R X g N Δ α T) (raiser p) (Merge.Spicy.opens G p c σ C' α a + Real.exp (ballCost 2:ℝ) * Price.lofty p G σ C' α Δ):=by
     intro Δ'; let D:=shelves X R p; let O:=(fill X R c p g α Δ'); have ht:= Merge.Spicy.june (α:=α) hG hn h hR hv hd
     let f':=Sum.elim (O).logarithm (Price.remises Δ' α p R); let g':=Sum.elim D.softer (fun i:Spikes n=>(Price.ridge R p i).support)
     let l:= numbering (Fol n); obtain ⟨v,hf₀,hf⟩:= ht.funds; let p':= Sum.elim v (unitH p R α Δ' (n:=n)); let s:=raiser p
     have he (i: Fol n) : UsesFinal (raiser p).threshold (g' i) (f' i)∧ (∀ U,Healthy p.threshold (g' i) U→ f' i U=0)∧ GaugeInvariant (f' i)∧Measurable (f' i)∧∀ U,‖f' i U‖≤p' i:=by
        rcases i with i|i; exact ⟨ht.texts _,ht.visits _,ht.travels _,ht.tails _,hf _⟩
        obtain ⟨h,hX,hP⟩:= Price.tending Δ' α p R hR i; exact ⟨h.uses,fun U hu=> not_not.mp (fun hv=>hX U hv hu),h.invariant,h.borel,hP⟩
     refine ⟨fun i=>(he (l i)).1,fun i=>(he (l i)).2.1,fun i=>(he (l i)).2.2.1,fun i=>(he (l i)).2.2.2.1,?_⟩
     refine ⟨fun i=> p' (l i),⟨fun i=>(norm_nonneg _).trans ((he (l i)).2.2.2.2 1),fun i=>?_⟩,fun i=>(he (l i)).2.2.2.2⟩
     exact Cost.equiv l (Cost.sum (f:=fun j: Fol n=> if i∈g' j then p' j* Real.exp ((s.supportExponent+1)*coverNumber s.B (g' j)) else 0) (hf₀.2 i) (Price.torqued (α:=α) (Δ:=Δ') hR hv i)) -- edit
end YM.AnalyticBridge.VerifiedReset.Collection.Price
