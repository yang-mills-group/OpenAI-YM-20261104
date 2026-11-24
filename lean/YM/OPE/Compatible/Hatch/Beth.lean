import YM.OPE.Compatible.Hatch.Opine
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
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
variable (f:E→ℝ)(X Y :(i:I) → D i → E)
variable (he: Tendsto Z φ atTop) (hx:∀ᶠ i in φ,Measurable (X i))(hy:Grain μ φ Z (fun i x=> ‖X i x‖) a)
include he hx
lemma LinearB (q:E→ₗ[ℝ]ℝ)(hy:Grain μ φ Z (fun i x=> ‖X i x‖) a): Grain μ φ Z (fun i x=>q (X i x)) a:=by
       let Q:= LinearMap.toContinuousLinearMap q; apply Grain.of_le (((Grain.const (RateLE.const ‖Q‖ he)).mul hy).mint (by simp)) (hx.mono fun i hi=>(Q.measurable.comp hi).aestronglyMeasurable); filter_upwards with i; filter_upwards with x; exact (Q.le_opNorm _).trans (Real.le_norm_self _)
lemma InkD (h:Bond f)(hy:Grain μ φ Z (fun i x=>‖X i x‖) 0): Grain μ φ Z (fun i x=> f (X i x)) 0:=by
       induction h with|keep=> exact Grain.const (RateLE.const _ he)|glyph q=>exact LinearB X he hx q hy|add _ _ ih ih'=> exact ih.add ih' he| mul _ _ ih ih'=> exact (ih.mul ih').mint (by simp)
lemma DiffIK (h:Bond f)(hp:Grain μ φ Z (fun i x=>‖X i x‖) 0)(hY:∀ᶠ i in φ,Measurable (Y i))(hy:Grain μ φ Z (fun i x=> ‖Y i x‖) 0)(hS:Grain μ φ Z (fun i x=>‖X i x-Y i x‖) a): Grain μ φ Z (fun i x=> f (X i x)-f (Y i x)) a:=by
       induction h with
       | keep c=> apply (Grain.const (μ:=μ) (s:=a) (RateLE.zero _ _ _)).shift; filter_upwards with i; funext x; exact (sub_self c).symm
       | glyph L=> let F:= LinearB (X-Y) he ((hx.and hY).mono fun i hi=> hi.1.sub hi.2) L hS; apply F.shift; filter_upwards with i; ext1 x; exact map_sub ..
       | @add p q h h' ih ih'=>apply (ih.add ih' he).shift; filter_upwards with i; ext1 x; simp only [Pi.add_apply]; ring
       | @mul p q h h' ih ih'=> apply (((ih.mul (InkD q X he hx h' hp)).mint (le_of_eq (add_zero _))).add (((InkD p Y he hY h hy).mul ih').mint (le_of_eq (zero_add _))) he).shift; filter_upwards with i; ext1 x; simp only [Pi.mul_apply];ring
end
-- also need PinCue on XT
variable {X:(i:I)→D i→ Bid.Dir G (A i)} {Y Y':(i:I)→ D i→ Chamber G r} {L:I→Law (Chamber G r)}
include U in lemma αPin (h:SkinQ A Z μ φ X): SkyQ r Z μ φ 0 (fun i x=> PinT G (X i x)):=by
        have he:=bodyS U X h; have hh:∀ᶠ i in φ,Measurable (PinT (r:=r) G ∘ X i):=h.meat.mono fun i hi=> (PinT (r:=r) G).measurable.comp hi; refine ⟨hh,he.of_le (hh.mono fun i hi=> hi.norm.aestronglyMeasurable) ?_⟩; filter_upwards with i; filter_upwards with x; rw[norm_norm,norm_norm,← Sill_pin (U.top.room i).money _ (U.top.room i).wide]; exact money_pin G _
omit [∀ i,IsProbabilityMeasure (μ i)] in
lemma SkyQ.spend (p:SkyQ r Z μ φ a Y)(hv:SkyQ r Z μ φ a Y')(hT:Tendsto Z φ atTop): SkyQ r Z μ φ a (Y+Y'):=by
         have he:∀ᶠ i in φ, Measurable (Y i+Y' i):= (p.aug.and hv.aug).mono fun i hi=>hi.1.add hi.2; refine ⟨he,(p.leg.add hv.leg hT).of_le (he.mono fun i hi=> hi.norm.aestronglyMeasurable) ?_⟩; filter_upwards with i; filter_upwards with y; rw[norm_norm]; exact (norm_add_le ..).trans (Real.le_norm_self _)
end Sleeve
end YM.OPE.Merchant
