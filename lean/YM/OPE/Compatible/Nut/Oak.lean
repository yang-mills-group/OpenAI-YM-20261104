import YM.OPE.Compatible.Nut.Bush
/-! # pan book scales before accepting. interior selection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lass
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*}{j i k m n B:ℕ}{R v t s u r:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Borealis Borealis.Galea Borealis.Lav
variable {K:Sponsor G}{T:Seasons K}
namespace Zest
section
variable {J:Type}[Fintype J]{k i:ℕ}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E]
variable {μ:Measure E}[μ.IsAddHaarMeasure]{X:Law E}{p q f:PAD J→ℝ}{L:E→L[ℝ] PAD J}
variable (hp:Stature p k)(hq:Stature q k)(hf:Stature f k)
private lemma FaAdd (h:f=p+q): FarG X μ L hf=FarG X μ L hp +FarG X μ L hq:=by
       funext i; ext1 x; by_cases he : i ≤ k; swap; · unfold FarG; simp [he]
       rw [show (FarG X μ L hp+ _) _ _= _ from (_root_.add_apply (FarG X μ L hp i) (FarG X μ L hq i) x),SemG X μ L hf _ he,SemG X μ L hp _ he,SemG X μ L hq _ he]; unfold taxA; rw[h,FlAdd ((hp.mono he).smooth) ((hq.mono he).smooth)]; erw [duneAdd X μ (exil X μ L (hp.mono he) x) (exil X μ L (hq.mono he) x),mul_add] -- names
private lemma FaSc (a:ℝ)(h:f=a • p): FarG X μ L hf=a • FarG X μ L hp:=by
       funext i; ext1 x; by_cases he:i ≤ k; swap; · unfold FarG; simp [he]
       rw[show (a • FarG X μ L hp) i x=a * FarG X μ L hp i x from rfl,SemG X μ L hf _ he,SemG X μ L hp _ he]; unfold taxA; rw[h, show Fline (a • p) x=a • Fline p x from (funext fun y=> DFunLike.congr_fun (iteratedFDeriv_const_smul_apply (a:=a) ((hp.mono he).smooth.contDiffAt)) x)]; change _ * (X.average μ (a • (Fline p x ∘ L)))=_; rw[scooted]; ring
lemma Care (h:f=p+q): CurveG X μ L f hf= CurveG X μ L p hp+ CurveG X μ L q hq:=by unfold CurveG Expire; rw [FaAdd hp hq hf h,map_add]
lemma CareS (a:ℝ)(h:f=a • p): CurveG X μ L f hf = a • CurveG X μ L p hp:=by unfold CurveG Expire; rw [FaSc hp hf a h,map_smul]
end
section induction
variable {b i m:ℕ}{p q f:Song (Scoop G b)}(hp:ReadyP p i)(hf:ReadyP f i)(hq:ReadyP q i)
lemma Locke (hx:f=p+q): Locket hf m= Locket hp m+ Locket hq m:=by
       refine Subtype.ext (lilies_inj _ _ _ ?_); erw[_root_.map_add]; rw[show lilies _ _ _ (Locket hf m).val=ShapeX f from sproutsX _ (TomX m i f hf),show lilies _ _ _ (Locket hp m).val=ShapeX p from sproutsX _ (TomX m i p hp),show lilies _ _ _ (Locket hq m).val=ShapeX q from sproutsX _ (TomX m i q hq)]; rw [hx]; funext i j; change Honey (Soul ((p+q) i)) j = Honey (Soul (p i)) j+Honey (Soul (q i)) j; unfold Honey; split; exact rfl; exact (add_zero (0:ℝ)).symm
lemma LockA (a:ℝ)(h:f=a • p): Locket hf m= a • Locket hp m:=by
       refine Subtype.ext (lilies_inj _ _ _ ?_); erw[_root_.map_smul]; rw[show lilies _ _ _ (Locket hf m).val=ShapeX f from sproutsX _ (TomX m i f hf),show lilies _ _ _ (Locket hp m).val=ShapeX p from sproutsX _ (TomX m i p hp)]; rw [h]; funext i j; change Honey (Soul ((a • p) i)) j = a * Honey (Soul (p i)) j; unfold Honey; split; exact rfl; simp
end induction
end Zest
end YM.OPE.Lass
