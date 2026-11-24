import YM.OPE.Compatible.Hatch.Arc
/-! # Cost transport into orthogonal cube. Projection preserves Hardy plateau. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
set_option maxHeartbeats 200000
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
open Aloof
namespace Sleeve
variable {I:Type}{A:I→ Side}{φ:Filter I}{Z:I→ℝ}{W:I→ℕ}{a c b':ℝ}(U:Scaffold φ Z A W r)
variable (q p: GlyphQ G A)
open Scaffold
variable (h:Shor U q p)(V:(i:I)→Board (A i) (r+1))
-- Application to arbitrary enactments. Costs independent of input size using Roster.G.
open Cinders
variable {D:I→ Type} [∀ i, MeasurableSpace (D i)] {μ:(i:I)→Measure (D i)}[∀ i,IsProbabilityMeasure (μ i)]
structure SkinQ (A:I→Side)(Z:I→ℝ)(μ:(i:I)→Measure (D i))(φ:Filter I)(X:(i:I)→D i→ Bid.Dir G (A i)):Prop where
       meat:∀ᶠ i in φ, Measurable (X i)
       Φ: Grain μ φ Z (fun i x=> Roster (X i x)) 0
structure SkyQ (r:ℕ)(Z:I→ℝ)(μ:(i:I)→Measure (D i))(φ:Filter I)(c:ℝ)(Y:(i:I)→D i→ Chamber G r):Prop where
       aug:∀ᶠ i in φ,Measurable (Y i)
       leg:Grain μ φ Z (fun i x=> ‖Y i x‖) c
noncomputable abbrev HopPI (A:I→Side)(W:I→ℕ)(X:(i:I)→D i→Bid.Dir G (A i))(i:I)(x:D i):= Cpit G A W i (X i x)
variable (X:(i:I)→D i→ Bid.Dir G (A i))(Y:(i:I)→D i→ Chamber G r)
section
omit [∀ i,IsProbabilityMeasure (μ i)]
lemma SkyQ.live (p:SkyQ r Z μ φ a Y)(h:a≤c):SkyQ r Z μ φ c Y:=⟨p.aug,p.leg.mint h⟩
-- Roter at chart.X Φ inv. measure
lemma skinV (n':Side): Measurable (fun x:Bid.Dir G n' => Roster x):=((tellerT G n').symm.continuous.norm|>.measurable) -- k unused
lemma SkinQ.roos {Y:(i:I)→D i→ Bid.Dir G (A i)}(p:SkinQ A Z μ φ X)(hv:SkinQ A Z μ φ Y)(ht:Tendsto Z φ atTop): SkinQ A Z μ φ (X+Y):=by
       have he:∀ᶠ i in φ, Measurable (X i + Y i):= (p.meat.and hv.meat).mono fun i hi=> hi.1.add hi.2; refine ⟨he,(p.Φ.add hv.Φ ht).of_le ?_ ?_⟩
       · exact he.mono fun i hi=> ((skinV (G:=G) _).comp hi).aestronglyMeasurable
       filter_upwards with i; filter_upwards with y; rw [Real.norm_of_nonneg (ros _)]; exact (rAdd ..).trans (Real.le_norm_self _)
lemma SkinQ.Rise (p:SkinQ A Z μ φ X) : SkinQ A Z μ φ (HopPI A W X):=by
        have he:∀ᶠ i in φ,Measurable (HopPI A W X i):= p.meat.mono fun i hi=>(Cpit G A W i).measurable.comp hi; exact ⟨he,p.Φ.of_le (he.mono fun i hi=> ((skinV (G:=G) _).comp hi).aestronglyMeasurable) (Eventually.of_forall fun i=>Eventually.of_forall fun x=> (by rw [Real.norm_of_nonneg (ros _),Real.norm_of_nonneg (ros _)]; exact saltP ..))⟩
noncomputable def fallS (i:I)(x:D i):= sailT G (V i) (Y i x)
lemma SkyQ.turns (p:SkyQ r Z μ φ 0 Y): SkinQ A Z μ φ (fallS V Y):=by
       have he:∀ᶠ i in φ, Measurable (fallS V Y i):= p.aug.mono (fun i hi=>?_); swap
       · change Measurable ((sailT G (V i)) ∘ Y i); with_reducible_and_instances exact (sailT G (V i)).measurable.comp hi
       refine ⟨he,p.leg.of_le (he.mono fun i hi=>((skinV (G:=G) _).comp hi).aestronglyMeasurable) (Eventually.of_forall fun i=>Eventually.of_forall fun y=>?_)⟩
       rw [Real.norm_of_nonneg (ros _),norm_norm]; apply (spice _).trans; unfold fallS; with_reducible_and_instances exact sailX G _ _
end
section -- [∀ i,IsProbabilityMeasure (μ i)]
include U in lemma bodyS (p:SkinQ A Z μ φ X): Grain μ φ Z (fun i x=> ‖HopPI A W X i x‖) 0:=by
        let t:=U.top.cash; let X':=RateLE.const (1:ℝ) U.top.fair; exact (((Grain.const (X'.add t U.top.fair)|>.mul p.Φ)).mint (by norm_num)).of_le ((p.Rise X (W:=W)).meat.mono fun i hi=> hi.norm.aestronglyMeasurable) (Eventually.of_forall fun i=> Eventually.of_forall fun x=> (norm_norm _).trans_le ((Sill_price (X i x) (W i+1)).trans (Real.le_norm_self _)))
end
end Sleeve
end YM.OPE.Merchant
