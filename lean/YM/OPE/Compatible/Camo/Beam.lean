import YM.OPE.Compatible.Camo.Lull
/-! # caps on all horizontal costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cameo
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
open Stroke Ibis Borealis Borealis.Galea
variable {L:I→Host K T}{V B W S F A:I→ℝ}{l:Filter I}{J:I→ℕ} (Y:∀ i,CoT (L i))(x:∀ i,Site (L i).f)(U:I→ Train j)(hv:4 ≤ j)
noncomputable abbrev CotV (L:Host K T)(Y:CoT L)(k:ℕ)(t w:ℝ):= TourF Y.P Y.T Y.a (k:=k) (b:=Y.b) (t:=t) w
variable (hV:Tendsto V l atTop)(hJ:RateLE l V (fun i=>(J i:ℝ)) 0)(hp:∀ᶠ i in l,Covered (L i) (Y i).x (Y i).b (x i) (J i)∧(Y i).Note (S i) (k+6)) (L':ℕ→ℝ)
variable (hB:RateLE l V B 0)(hz:RateLE l V (fun i=>((Y i).b:ℝ)) 0)(hT:RateLE l V (fun i=> CotV (L i) (Y i) (k+6) (S i) (W i)) 0)
-- choose spectral capsule
variable {τ:Phase→ℕ}(hx:Aware (k+6) τ)
local notation "θΠ"=>fun i=> Υden (L i) (U i) hv
set_option quotPrecheck false
local notation "PΘ"=> fun i=> CoT.hymn (Y i) (W i) (B i)
include hx hV hJ hp hB hz hT
abbrev WageJet (b:ℕ)(t:ℝ)(v:ℕ):= RoadK b ^ v*(1+t)^v
lemma ΛCare (p:Phase): Grain θΠ l V (fun i=> skry ((Y i).hymn (W i) (B i)) p) 0:=by
         let P' (i:I):= CoT.hymn (Y i) (W i) (B i); let f(j:ℕ)(i:I):=fun u:Bid.Dir G (L i).c=> Mā G j (Y i).b ‖Qspot (L i) (x i) (J i) u‖; let C'(i):=CotV (L i) (Y i) (k+6) (S i) (W i); have he(u:ℝ):= RateLE.const u hV; have hY:= care hV hJ x U hv; have hR:RateLE l V (fun i=> RoadK (Y i).b) 0:=((((he 2).mul ((he 4).mul hz)).mono (by norm_num)|>.add (he 2) hV).add (he 1) hV); have hf(j:ℕ): Grain θΠ l V (f j) 0:= by
                let u:= ((he (magnol G j)).mul (hR.pow j hV)).mono (show _≤ (0:ℝ) from by simp); exact ((Grain.const u).mul (((Grain.const (μ:=θΠ) (he 1)).add hY hV).pow hV j)).mint (le_of_eq (by ring))
         let t(i:I):=1+ ‖B i/2‖; have ht: RateLE l V t 0:=by
                have he' : RateLE l V (fun i=> B i/2) 0:= by simpa only [div_eq_mul_inv,add_zero] using hB.mul (RateLE.const ((2:ℝ)⁻¹) hV)
                exact (he 1).add he'.norm hV
         let v(i:I)(u:Bid.Dir G (L i).c):= t i*RedG G (Y i).b ‖Qspot (L i) (x i) (J i) u‖; have hv' : Grain θΠ l V v 0:= ((Grain.const ht).mul ((Grain.const (μ:=θΠ) (he 1)).add (((hf 1).add (hf 2) hV).add (hf 3) hV) hV)).mint (le_of_eq (by ring))
         let H':= Grain.const (μ:=θΠ) hT; let G':= (H'.mul hv').mint (le_of_eq (zero_add _)); let F(i:I)(u:Bid.Dir G (L i).c):= Jfare (v i u) (C' i); have hF:Grain θΠ l V F 0:= ((H'.add G' hV).add (G'.add ((H'.mul (hv'.pow hV 2)).mint (le_of_eq (zero_add _))) hV) hV); refine Grain.of_le hF (hp.mono fun i h=> ((CoT.LapH (Y i) (U i) hv _ _ h.2 hx) p).smooth.continuous.aestronglyMeasurable) ?_
         filter_upwards [hp] with i hi; filter_upwards with u; unfold skry; unfold CoT.hymn Elev; rw [Tess (L:=L i) (Y i).T (Y i).F (Y i).a (Y i).x (Y i).P (Y i).good (W i) (B i) hi.1]; apply le_trans _ (Real.le_norm_self _); exact TessPay _ _ _ _ _ _ hi.2 _ _ p _ le_rfl
end
end YM.OPE.Cameo
