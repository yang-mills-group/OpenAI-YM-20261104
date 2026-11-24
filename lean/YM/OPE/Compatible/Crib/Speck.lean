import YM.OPE.Compatible.Crib.Slept
/-! # chart localized prices of strokes. Stencil independent nature, currency for Gaussians. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n c f:Side} {b i k r m:ℕ}{t C s u B v:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph
open Spells
variable (S:StepData c f)(H:Odd S.ratio.count.val)(o:Site f)
local notation "Fθ"=> forest S.ratio H
local notation "Yr"=>AxisChart G Fθ
local notation "Ix"=> crux S H o b
local notation "Yσ"=> Libra.Keys G (Ix:Type)
noncomputable abbrev gam (b:ℕ)(x:Libra.Keys G (crux S H o b:Type)):= ath S H o (stake (crux S H o b) x)
noncomputable abbrev Mā (G:Gauge)(k b:ℕ)(t:ℝ):= magnol G k*RoadK b^k*(1+t)^k
lemma Māhi(G:Gauge)(k b:ℕ)(ht:0 ≤t):0 ≤ Mā G k b t:=by
       apply mul_nonneg (mul_nonneg (show _ from (ozone G 1 1 _ zero_le_one (lumenD G) k).choose_spec.1) (pow_nonneg _ _)) (pow_nonneg (by positivity) _); unfold RoadK; positivity
lemma rhythm (p:Fpaper G b)(k:ℕ) : anthem k (fun x:Yσ=> PlateB k b (gam S H o b x) p):=by
       let v: Yσ→L[ℝ] Vec G f 1:= (flats G f).toContinuousLinearMap ∘L letter S H G ∘L stake Ix
       have ht(x:Yσ): gam S H o b x=Charu o v x:=by
            let f':=(flats G f).symm; change charW o _= _; rw [show letter S H G (stake Ix x)= f' (v x) from ((flats G f).symm_apply_apply _).symm]; exact climbsF o v x
       simp_rw [ht]; exact Clippy o v k p
lemma homes (k:ℕ)(x:Yσ)(hp:‖x‖ ≤ t): ‖PlateB k b (gam S H o b x)‖ ≤ Mā G k b t:=by
       have he: ‖InLine (4*b) (gam S H o b x)‖≤ t:= (woodK S H o (stake Ix x)).trans (((veil S H Ix (stake Ix x)).trans_eq (firmly Ix x)).trans hp); apply (PriceFl _ _ _).trans; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl he) _) (by simpa only [Mā,add_zero,one_pow,mul_one] using Māhi G k b (le_refl 0))
lemma feesF (x y:Yσ)(k:ℕ)(ht:1 ≤t)(hx:‖x‖≤ t)(hy:‖y‖≤ t): ‖PlateB k b (gam S H o b y)-PlateB k b (gam S H o b x)‖≤ Glee k*Mā G k b (3*t)*‖y-x‖:=by
       let ψ:= fun (i:Yσ)=> gam S H o b i; apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (GleeHi _) (Māhi G k b (by linarith))) (norm_nonneg _))).2; intro i; have ht':‖y-x‖≤2*t:= (norm_sub_le ..).trans (by linarith); exact Lap2 (rhythm S H o i k) x y (t:=2*t) (by linarith) ht' fun v hv=> ((norm_le_pi_norm (PlateB k b (ψ v)) i).trans (homes _ _ _ _ _ (hv.trans (by linarith))))
noncomputable abbrev CxT (G:Gauge)(b:ℕ)(t:ℝ):= Mā G 1 b t+Mā G 2 b t+Mā G 3 b t
noncomputable abbrev DxT (G:Gauge)(b:ℕ)(t:ℝ):= Glee 1*Mā G 1 b (3*t)+Glee 2*Mā G 2 b (3*t)+Glee 3*Mā G 3 b (3*t)
lemma payΦ (x:Yσ)(hx:‖x‖≤ t): scope (BFilm b (gam S H o b x)) (CxT G b t):=by
        have he(i:ℕ):= homes S H o i x hx; have hh(i:ℕ):0 ≤ Mā G i b t:=(norm_nonneg _).trans (he i); intro i; fin_cases i
        · apply (he 1).trans; unfold CxT;linarith only [hh 2,hh 3]
        · apply (he 2).trans; unfold CxT; linarith only [hh 1,hh 3]
        apply (he 3).trans; unfold CxT; linarith only [hh 1,hh 2]
lemma socketQ(x y:Yσ)(ht:1 ≤ t)(hx:‖x‖≤ t)(hy:‖y‖≤ t): fuel (BFilm b (gam S H o b y)) (BFilm b (gam S H o b x)) (DxT G b t*‖y-x‖):=by
        have he(i:ℕ):= feesF S H o x y i ht hx hy; have hh(i:ℕ):0 ≤ Glee i*Mā G i b (3*t)*‖y-x‖:=(norm_nonneg _).trans (he i); intro i; fin_cases i
        · apply (he 1).trans; unfold DxT; linarith only [hh 2,hh 3]
        · apply (he 2).trans; unfold DxT; linarith only [hh 1,hh 3]
        apply (he 3).trans; unfold DxT;linarith only [hh 1,hh 2]
end YM.OPE.Crown
