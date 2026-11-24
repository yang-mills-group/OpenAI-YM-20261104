import YM.OPE.Compatible.Camo.Lilt
/-! # caps on all horizontal costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m n M:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:I→Host K T}{V W:I→ℝ}{l:Filter I}{b:I→ℕ}
variable (hp:Tendsto V l atTop)(hz:RateLE l V (fun i=> (b i:ℝ)) 0) {X:∀ i,Seats (L i).ForestQ}{q:∀ i,Sender (L i)} (x:∀ i,Site (L i).f)(U:I→ Train j)(Y:4 ≤ j)
include hp hz
abbrev StageS (L:Host K T)(x:Site L.f)(r:ℕ)(s:ℝ): Set (Bid.Dir G L.c):= {w|‖Qspot L x r w‖≤ crestPrice G s}
omit hp hz in lemma StageM (L:Host K T)(x:Site L.f)(r:ℕ)(s:ℝ): MeasurableSet (StageS L x r s):= IsClosed.measurableSet (isClosed_le (by fun_prop) (continuous_const (y:=crestPrice G s)))
local notation "SΘ"=> fun i=> StageS (L i) (x i) (b i) (W i)
local notation "μ'"=>fun i=> Υden (L i) (U i) Y
set_option quotPrecheck false
local notation "A!"=> ((terra_money K.K Y).choose+1)
lemma Dole (hW:∀ t:ℝ,RateLE l V (fun i=> Real.exp (-W i)) t)(h:∀ᶠ i in l,0≤ W i) (a:ℝ): RateLE l V (fun i=> (Υden (L i) (U i) Y).real (StageS (L i) (x i) (b i) (W i))ᶜ) a:=by
        have hx(t:ℝ):=RateLE.const t hp; refine RateLE.of_norm_le ((((κ_growth l V hp b hz).mul (hx (Fintype.card G.ColorIndex:ℝ))).mul ((hx (2*Real.exp (A!/2))).mul (hW a))).mono (by simp)) ?_; filter_upwards [h] with i hi; let L:= L i; rw[Real.norm_of_nonneg (measureReal_nonneg),show (StageS L (x i) (b i) (W i))ᶜ={w|crestPrice G (W i)<‖Qspot L (x i) (b i) w‖} from Set.ext fun w=>show (¬ ‖Qspot L (x i) (b i) w‖≤ crestPrice G (W i))↔crestPrice G (W i)<‖Qspot L (x i) (b i) w‖ from not_le]; exact Sz_S (x i) (Vessel K.K (U i) G L.c Y) (Chart.tangent G (Body 1 L.c)) (Seat_V ..).2 (b i) hi
lemma care : Grain (μ') l V (fun i y=> ‖Qspot (L i) (x i) (b i) y‖) 0:=by intro m hm; refine ⟨_,CrownΛ hp hz G m A!,?_⟩; filter_upwards with i; obtain ⟨hp,H⟩:= Seat_V (L:=L i) (U i) Y; exact (mac (x i) _ _ H hp (b i) m hm).NormT
end
section
variable {X:I→Type*}[∀ i,MeasurableSpace (X i)]{S:∀ i, Set (X i)}{μ:∀ i,Measure (X i)}[∀ i,IsProbabilityMeasure (μ i)] {p:PayR X}{l:Filter I}{T:I→ℝ}
lemma recoverP (ht:Tendsto T l atTop)(hS:∀ᶠ i in l,MeasurableSet (S i))(hm:∀ t:ℝ, RateLE l T (fun i=>(μ i).real (S i)ᶜ) t) (h:Large S l T p t)(he:Grain μ l T p s): Grain μ l T p t:=by
        let f(i):= (S i)ᶜ.indicator (p i); let z(i):=(S i).indicator (p i); let V(i):= (S i)ᶜ.indicator (fun _=>1: X i→ℝ) -- test
        have hz:Grain μ l T z t:= Large.crop hS h ((hS.and (he.integral.1)).mono fun i hi=>hi.2.aestronglyMeasurable.indicator hi.1)
        apply (hz.add (((indicatorX (fun i=> (S i)ᶜ) (hS.mono fun _ H=> H.compl) hm ht (t-s)).mul he).mint (le_of_eq (sub_add_cancel _ _))) ht).shift; filter_upwards with i; funext x; change z i x+ V i x*p i x=p i x; by_cases hx:x∈S i; · have h:x∉(S i)ᶜ:=fun hh=>hh hx; unfold z V; rw[indicator_of_notMem h,indicator_of_mem hx,zero_mul,add_zero]
        unfold z V; rw[indicator_of_notMem hx, indicator_of_mem (show x∈(S i)ᶜ from hx), one_mul,zero_add]
end
end YM.OPE.Borealis.Galea
