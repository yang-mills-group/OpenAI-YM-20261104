import YM.Integration.PricedWholeProduct
import YM.Integration.WilsonOriginalTwoFlatReflection

/-! Fixed flat comparison for the original admissible product on its licensed reflection chamber. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatCapture
open OriginalProductCellMatch
open RG16 RG16.Literal Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Ribbons MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid
variable {I: Type}[Fintype I][DecidableEq I]{G:Gauge}(R₀:Run G)(simple:G.Simple)
variable (N m p:ℕ){W:Bid.Worth}{u ψ φ δ χ x :ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}
    {D:∀ N p m:ℕ,m<N→GaugeDoor (R₀.family.path.rep N p (m+1)) (R₀.family.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> R₀.family.path
local notation "P'"=> R₀.family.path.levels.budget
variable (J k:ℕ){j:ℕ}{α A e:ℝ}(i₀:I)
    (b : ℝ) (a:I→ℝ) (o:I→Site (R₀.family.side j p)) (hf:J≤k) (hk:k ≤ m) (hN:j < N) (hm:m+1 ≤ j)
local notation "T"=> center R₀.family.S p (le_trans hf (le_trans hk (le_trans (m.le_succ) (le_trans hm hN.le)))) 0
variable (t:I→ℕ) (s:(i:I)→ R₀.family.label (t i))(hh:Scrim R₀.family W u ψ φ δ ζ r D)(hR:Created R₀.family)
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm hN.le)
variable (hr:SwornClusterCuts R₀.family (δ:=δ) (μ:=D) (r:=r) (R₀.family.ref 0) 0 χ δ x)
include simple hh hR hr hm hN i₀
/-- The same captured source gives its physical expectation and its fixed flat Wilson comparison. -/
theorem original (L:Stock.Tabs R₀.family.path.levels)(hx: Stock.Tabs.opens R₀.family.path.levels 1 J k) (stop : ℕ) (hstart : R₀.family.ref 0 ≤ stop) (hstop : stop ≤ k) (hOpened : Trace.Physical.GermGraph.Opened R₀.family 0 stop p) (ht:∀ i,R₀.family.ref (t i) ≤ j)(hM:∀ i,a i*Spindle.paid R₀.family (t i) j N p (s i) ≤ ζ (t i) j)(hw:∀ i,0<a i)(htq:GridApprox.room R₀.family.path.levels J m (lensScope R₀.family 0))
    (hΩ:∀ i,loops R₀.family j p (o i) (m+1)=0)(hg:(P' (m+1)).B^2+1≤(R₀.family.S.toDepth (le_trans hf (le_trans hk (m.le_succ))) p).count.val)(hy:Edition.Spaced (P' j).B o)
    (ha:0<α)(hφ:α≤1)(hwindow :
      (∃ uL : ℕ → ℕ, m+1<j ∧
        (∀ k : ℕ, m+1 ≤ k → k<j → α ≤ license H δ (Fintype.card I) (uL k+2) k * δ k ∧
          8 ≤ uL k ∧ uL k ≤ (P' k).B ∧ 1 ≤ δ k*mintK (uL k)) ∧
        (∀ k : ℕ, m+1≤k → k ≤ j → Fintype.card I ≤ r k)) ∨
      (∀ k : ℕ, m ≤ k → k < j → α ≤ license R₀.family.path δ (Fintype.card I) (carpet R₀.family.path k) (k+1)))
    (f:I→ Config G (R₀.family.side N p)→ℂ)(hF:∀ i,f i=R₀.family.O N p (s i) ((R₀.family.S.toDepth hN.le p).embed (o i)))(hi:∀ i,Interior ((T).chamber 0) (f i))(hc₀:∀ z:R₀.family.label 0, Interior ((T).chamber 0) (R₀.family.O N p z 0))
    (hz:0<A)(hY:A≤ ManyCopies.initial R₀.family.path δ φ m j α (∏ i,a i) (Fintype.card I))
    (hb:0<b)(hL:march (fun _:Unit=>b) φ k m ()≤ δ m * (A/(16*x m)))
    (hA:4*(1+(R₀.family.path.levels.params m).columns)*(2*(R₀.family.S.a (m+1)^0*(x m*(4*(1/A)))))≤ e)
    (hp:32*(1+(R₀.family.path.levels.params m).columns)*b * ‖alto R₀.family.path k 0‖*(e/gainChart R₀.family.path m k) ≤ ζ 0 k/2)

    :
    let Y : Cut R₀.family N p := fun U => ∏ i, f i U
    ‖R₀.family.omega N p Y-WilsonThermometerUnitFilingCoarse.reading R₀ (N:=N)
      (credit R₀.family N p 0 Y m (h!).le) stop (hstop.trans hk)‖ ≤
      2*(stakes R₀.family J k/b)+e/gainChart R₀.family.path m stop := by
  intro Y
  obtain ⟨z,_,held,_,inside,root⟩:=PricedWholeProduct.capture_product_receipt
    R₀.family N m p 0 J k i₀ b a o hf hk hN hm t s R₀.makes hh hR hr L hx stop hstart hstop hOpened
    ht hM hw htq hΩ hg hy ha hφ hwindow f hF hi hc₀ hz hY hb hL hA hp
  have hfine:Continuous Y:=continuous_finsetProd _ fun i _=>hF i ▸ R₀.family.continuousO N p (t i) (s i) _
  exact WilsonOriginalTwoFlatReflection.original R₀ simple (hstop.trans hk) (h!)
    (hf.trans (hk.trans (m.le_succ.trans (hm.trans hN.le)))) hOpened Y hfine z held inside root

end
end YM.Integration.WilsonOriginalTwoFlatCapture
end
