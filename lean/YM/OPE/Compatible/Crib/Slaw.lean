import YM.OPE.Compatible.Crib.Vent
/-! # Mark receipts in period-clock.Local views -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:I→ Host K T}{Y:∀ i, Studio (L i)}{l:Filter I}{V ε B A D:I→ℝ}{N:ChartRatio G}
variable (h:Craft Y l V A s c e u C)(H:StackP N r R t) -- namespace?
variable (hx:Bevel Y l V ε B r a) (S:∀ i, Seats (L i).ForestQ)(p:∀ i,Sender (L i))(hp:∀ᶠ i in l,Funded (L i) (S i) (p i) (D i) k)(hf:RateLE l V D 0)
noncomputable abbrev sendV (Y:∀ i,Studio (L i))(p:∀ i,Sender (L i)): Hang (fun i=>(Y i).St):= fun i x=> p i ((Y i).V ((Y i).boat x)).2
include h hf hp
set_option quotPrecheck false
local notation "O!"=>fun i=>(Y i).omS (ε i) (B i) r
local notation "μ"=>fun i=>(Y i).μφ
lemma Appetite : Butte μ l V (sendV Y p):=by
       intro i; let f(j):=(Y j).Vx; let v(j)(x:(Y j).St):= f j ((Y j).boat x); have hv: Grain μ l V v 0:= h.Vap; have hx:= (((Grain.const (RateLE.const (1:ℝ) h.light)).add hv h.light).pow h.light k); apply Grain.of_le (((Grain.const hf).mul hx).mint (le_of_eq (zero_add _)))
       · filter_upwards [hp] with j h; let B:=(Y j); let Z:=stake B.X (G:=G); have hv' : Continuous B.boat:=continuous_id.add continuous_const; exact Continuous.aestronglyMeasurable ((Funded.strong _ _ h i).comp (continuous_const.add (Z.continuous.comp hv')))
       filter_upwards [hp] with j h; filter_upwards with x; have he(i:I)(x):= (Y i).plume x; let a:=(Y j).V ((Y j).boat x); have hb: ‖a.2‖ ≤ v j x:= le_trans (le_max_right ‖a.1‖ ‖a.2‖) (he j _).2; exact (Funded.norm _ _ h a.2 hb i).trans (Real.le_norm_self _)
include H hx
lemma SlopeX : TallT (O!) l V (sendV Y p):=by
       intro j; let v:= Craft.ν Y ε B; refine ⟨_,(hf.mul (((RateLE.const (1:ℝ) h.light).add (h.costsν hx) h.light).pow k h.light)).mono (by norm_num),?_⟩
       filter_upwards [hp,hx.presents] with i hi ht x he; have hf:= Studio.valley H (Y i) ht.1 ht.2.1 ht.2.2 x he; let a:=(Y i).V ((Y i).boat x); have hb: ‖a.2‖≤ v i := le_trans (le_max_right ‖a.1‖ ‖a.2‖) hf.2.2; exact (Funded.norm _ _ hi a.2 hb j).trans (Real.le_norm_self _)
end
end YM.OPE.Crown
