import YM.LocalLTE.Pond.Epoch
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
-- consumers.Try No unused warning.
open East Averaging Song Refrain Ovens Payments Rack Ovens.Pipes
variable {M:ℕ}(α Δ:ℝ)(F:ℕ→ EKey n→ Pot G n)
local notation "t₀"=> bells p R X M
local notation "t₁"=> azures c p R X g M Δ α F
local notation "g₁"=> Collection.fill X R c p g α Δ
local notation "E" => Price.tubeX R p X
variable {β C₀:ℝ}(hxβ:1 ≤ β)
include hxβ
lemma amplify (h':0≤C₀) (hs: Stocked p (Price.tubeX R p X) (archive X R c g α Δ) (C₀ * β^(chip 0)))(hv:∀ j :ℕ,j≤ M → Stocked p (Price.tubeX R p X) (archive X R c g α Δ-F j) (C₀ * β^(chip (j+1)))) (i: Fin (M+2)) : Stocked p (Price.tubeX R p X) (fun k=> Price.silt c R X g M Δ α F (i,k)) ((2*C₀)*β^(chip i.val)) :=by
   let Y:=archive X R c g α Δ; change Stocked _ _ (fun k=> Price.stairs M Y F i k) _; unfold stairs; by_cases h:i.val=M+1
   · simp only [if_pos h]; rw [h]; exact (hv _ (le_refl _)).cheaper (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (zero_le_one.trans hxβ) _))
   ·   simp only [if_neg h]
       have hk:i.val ≤ M:=by omega
       split
       next hi=>
           rw [hi]; change Stocked _ _ (F 0) _; rw [show F 0=Y-(Y-F 0) from by abel]; apply (Stocked.minus hs (hv 0 (by omega))).cheaper; have hz: Pastel.chip (0+1) ≤ Pastel.chip 0:= by norm_num [chip]
           linarith only [mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hxβ hz) h']
       next hi=>
           let v:=i.val-1; change Stocked _ _ (F i.val-F v) _
           rw [show (F i.val-F v)=(Y-F v) - (Y-F i.val) from by abel]; apply (Stocked.minus (hv v (by unfold v; omega)) (hv _ hk)).cheaper; rw [show v+1=i.val by unfold v; omega] -- edit
           have hz: Pastel.chip (i.val+1) ≤ Pastel.chip i.val:=by unfold chip; push_cast; linarith
           linarith only [mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hxβ hz) h']
variable {δ k w' : ℝ} (hr : Price.bars p M C₀ β ≤ δ) (h:Local X p g a w) (hΔ:p.threshold^2* |Δ| ≤ a) (H :∀ j:ℕ,j≤M →∀ i:EKey n, Comic G (Price.tubeX R p X i) p (F j i))
include hr h H hΔ hR hv hG hn hd hxβ
lemma full (hs:∀ i:Fin (M+2),Stocked p (Price.tubeX R p X) (fun k=> Price.silt c R X g M Δ α F (i,k)) (C₀ *β^(chip i.val))) (hQ:∃ m κ:ℝ, softNeed G p c σ C' α a + Price.lofty p G σ C' α Δ ≤ m ∧ Payments.Rates p.B w' w m κ) : Ingredients t₀ t₁ p δ w':=by
    let Z:= t₀; let T:= t₁
    have hu:(Z.pours T).EBound p δ:= Price.rank X g α Δ F hxβ hs hr; obtain ⟨m,k,hm,hP⟩:=hQ; 
    obtain ⟨s',hs',ht'⟩:= h.cheap
    let U i:= Collection.quoteL R p c α Δ s' (numbering (LKey n) i); let N':=numbering (Fol n); let K i:= Sum.elim U (Price.unitH p R α Δ) (N' i)
    have hu₁ i (x:Config G n): ‖(g₁).logarithm i x‖ ≤ U i:=Local.quote_soft hG α Δ hs' h.smooth _ x
    have hK : Ac.Hit (shelves X R p).softer p.B U (p.supportExponent+1) (softNeed G p c σ C' α a):= fun i=> Cost.equiv (numbering _) (Local.quote_family hR hd hv α Δ hs' ht' hΔ |>.2 i)
    obtain ⟨p',hz,hΓ⟩:=h.expensive
    have he i x: ‖T.logarithm i x‖ ≤ K i:=by
       change ‖Sum.elim (g₁|>.logarithm) (Price.remises Δ α p R) (N' i) x‖≤_; unfold K; cases hx:N' i; next=> exact hu₁ _ _
       next j=> exact (Price.tending Δ α p R hR j).2.2 x
    refine Payments.tender (Price.deck hR hG hn hd X g α Δ F h H) hu (p:=p') ⟨fun i=>(hz i).1,hΓ⟩ ⟨fun i=>(norm_nonneg _).trans (he i (1:Config G n)), fun x=>?_⟩ (fun i U=>⟨hz i|>.2 U, he i U⟩) hP
    let f i:= Sum.elim ((shelves X R p).softer) (fun i:Spikes n=> (Price.ridge R p i).support) i; let k i:=Sum.elim U (Price.unitH p R α Δ (n:=n)) i
    exact budget_loosen (Cost.equiv N' (Cost.sum (f:=fun i=> if x∈f i then k i*Real.exp ((p.supportExponent+1)* coverNumber p.B (f i)) else 0) (hK x) ((Price.torrid Δ α p R hR hv (n:=n)) x))) hm
end YM.AnalyticBridge.VerifiedReset.Collection.Price
