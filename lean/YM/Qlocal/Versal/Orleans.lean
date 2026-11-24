import YM.Qlocal.Versal.MintLeaf
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Versal.Freshet
open Function Filter Metric Lattice Laurent RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Repeat.Deck Repeat.Deck.Mint Greenbelt 
open Poll Pond MeasureTheory ProbabilityTheory Stellar Progress.DirectedRecipe RGComparison01 AllOrder AllOrder.Burn AllOrder.Till
open Quipu Quipu.Lasso Quipu.Sonnet Marker Marines
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge}{c f C F c' f': Side}{i j k z n m r M D D':ℕ}{g t a a' u v d:ℝ}
  {σ V:Type}[DecidableEq V]{R:Marker.Census V}
variable {W:Burn.Locale G}{L:RG.Rep G f}{L': RG.Rep G F}{E: Burn.Seed L W}{E': Burn.Seed L' W}
variable (S:Tale R G)(X:S.Decision)(s:Senses R)(o: V→Site f) (t:ℕ) (j:ℕ)(P:BudgetPoint)
set_option quotPrecheck false
open PhysicalNext.Repeat.Lotus Team Merge.Palette Merge Ovens
variable {Δ:Patch}(hc:C.val=c.val*D)(h:f.val = c.val*Δ.L.val)(H:F.val=C.val*Δ.L.val)
   (x:Site C) (O:V→Site F) (F0: Marines.Flank hc o O h H s x M)
variable (τ:σ→ Senses R)(κ:σ↪ Fin k)(Z:Pad E k)(Z':Pad E' k) (p:σ→ℝ)
  (hv:Scores S X t τ o g L.p p) (hw: Scores S X t τ O g L'.p p)
  (b:ℕ)(hb:L.p.B ≤ b) (hb': L'.p.B ≤ b) (hE:L'.p=L.p) (hm:border Δ M+t<f.val)
open RGComparison01.Pledge
local notation "Φ"=>sprout S X t τ κ Z o g p hv
local notation "Φ'"=>sprout S X t τ κ Z' O g p hw
local notation "p₀"=> Z.thread hb
local notation "p₀'"=> Z'.thread hb'
local notation "ρ"=> Pad.lower Z hb Z' hb' (Deck.fineP h H hc)
local notation "λ'"=> (fun i=> Z'.node hb' (.inr (marsh τ κ O i)))
include F0 hm hE
lemma Len (he:2≤c.val) (hh:∀ i,essence (τ i)⊆ essence s)(hz:4<f.val) : Relay.Lens (P:=Δ) (h:=h) (H:=H) (hC:=hc) (he:=he) (Φ) (Φ') p₀ p₀' (ρ) (λ') x M:= Pad.lens _ _ _ _ _ _ _ _ _ _ hE (fun i=> salute S X s hc o O h H x F0 t g hm (τ i) (hh i)) (fun i=> F0.sailing _ (hh _ (ownership (τ i)))) (fun _=> rfl) x (fun i=> F0.fits _ (hh _ (ownership (τ i)))) hz -- args check
omit hm hE
lemma portion (i:σ)(hx:Tale.Live O (τ i) t)(hL:t≤ L'.p.B) :∀ v∈ essence (τ i),(decreed H).parent (O v)∈(Φ' i).crest.image (decreed H).parent:= by
 intro v hv; rw [rank]; exact Finset.mem_image_of_mem _ (halo_spec.mpr ⟨_,mem_singleton_self _, (hx v hv).trans hL⟩)
lemma manuscript (i:σ)(hx:Tale.Live O (τ i) t)(hL:t≤ L'.p.B) (ht: Sonnet.root s∈ essence (τ i)): x∈(Φ' i).crest.image (decreed H).parent:= F0.ties ▸ (portion S X s o t hc h H x O F0 τ κ Z' p hw i hx hL _ ht)
end YM.Qlocal.Versal.Freshet
