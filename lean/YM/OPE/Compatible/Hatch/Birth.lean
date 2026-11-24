import YM.OPE.Compatible.Hatch.Reef
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
variable (X Y:(i:I)→D i→ Bid.Dir G (A i))(hp:SkinQ A Z μ φ X)
section
omit [∀ i,IsProbabilityMeasure (μ i)] in
lemma SkinQ.Baste (hp:SkinQ A Z μ φ X)(hv:SkinQ A Z μ φ Y)(ht:Tendsto Z φ atTop): SkinQ A Z μ φ (X-Y):=by
       have he:∀ᶠ i in φ, Measurable (X i - Y i):= (hp.meat.and hv.meat).mono fun i hi=> hi.1.sub hi.2; refine ⟨he,(hp.Φ.add hv.Φ ht).of_le ?_ ?_⟩
       · exact he.mono fun i hi=> ((skinV (G:=G) _).comp hi).aestronglyMeasurable
       filter_upwards with i; filter_upwards with y; rw [Real.norm_of_nonneg (ros _)]; exact (rSub ..).trans (Real.le_norm_self _)
variable (L:I→Law (Chamber G r))
noncomputable def Chair (i:I)(x:D i):= pour (sailT G (V i)) (chrom (q i)) (L i) (X i x)
noncomputable def Coach (i:I)(x:D i):=mate (sailT G (V i)) (chrom (q i)) (L i) (X i x)
local notation "K!"=>pour
local notation "V!"=> Chair q V X L
local notation "M!"=> Coach q V X L
local notation "X!"=> HopPI A W X
local notation "Ω"=> Tfoil (G:=G) V
include h hp
variable (hc:∀ i,SiteL (sailT G (V i)) (chrom (q i)) (L i))
variable {δ:ℝ} (hv:0<δ)(hL:∀ i x,δ*‖x‖^2 ≤ (L i).P x x)
include hc hv hL
lemma TourK : SkyQ r Z μ φ 0 (Chair q V X L):=by
       obtain ⟨T,hT,H⟩:=pour_pay U q p h V L hc hv hL; have he:∀ᶠ i in φ,Measurable (Chair q V X L i):=hp.meat.mono fun i hi=> (pour (Ω i) (chrom (q i)) (L i)).measurable.comp hi
       let b(i:I)(x:D i):=Roster (X i x)+1; have hb: Grain μ φ Z b 0:=hp.Φ.add (Grain.const (RateLE.const 1 U.top.fair)) U.top.fair; refine ⟨he,(((Grain.const hT).mul hb).mint (by norm_num)).of_le (he.mono fun i hi=>hi.norm.aestronglyMeasurable) ?_⟩; filter_upwards [H] with i hi; filter_upwards with y; let v:= (X i y); rw[norm_norm]; exact (hi v (b i y) ((add_pos_of_nonneg_of_pos (ros v) zero_lt_one)) (le_add_of_nonneg_right zero_le_one)).trans (Real.le_norm_self _)
lemma TourDiff : SkyQ r Z μ φ a (V!- Chair q V (HopPI A W X) L):=by
       have ht:= TourK U q p h V X hp L hc hv hL; have he:=TourK U q p h V _ (hp.Rise X (W:=W)) L hc hv hL; let f:=V!; let g:=Chair q V (HopPI A W X) L; have hy:∀ᶠ i in φ, Measurable (f i-g i):= (ht.aug.and he.aug).mono fun i hi=> hi.1.sub hi.2; obtain ⟨T,hT,H⟩:=pour_drop (a:=a) U q p h V L hc hv hL; let b(i:I)(x:D i):=Roster (X i x)+1; have hb: Grain μ φ Z b 0:=hp.Φ.add (Grain.const (RateLE.const 1 U.top.fair)) U.top.fair; refine ⟨hy,(((Grain.const hT).mul hb).mint (by simp)).of_le (hy.mono fun i hi=>hi.norm.aestronglyMeasurable) ?_⟩; filter_upwards [H] with i hi; filter_upwards with y; let v:= (X i y); rw[norm_norm]; exact (hi v (b i y) ((add_pos_of_nonneg_of_pos (ros v) zero_lt_one)) (le_add_of_nonneg_right zero_le_one)).trans (Real.le_norm_self _)
lemma TourP : SkinQ A Z μ φ (Coach q V X L):=by
       have hx:= hp.Baste X _ ((TourK U q p h V X hp L hc hv hL).turns V _) U.top.fair; have he : Coach q V X L=X-fallS V V!:=by
           funext i x; unfold Coach; simp only [mate,_root_.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply]; unfold fallS Chair; with_reducible_and_instances rfl
       rw[he]; exact hx
end
end Sleeve
end YM.OPE.Merchant
