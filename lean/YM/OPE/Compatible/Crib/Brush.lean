import YM.OPE.Compatible.Crib.Stilt
/-! # numeric budget conversion Stone parchment.Note expansion coefficient charge. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n c f:Side} {b i k r m:ℕ}{t C s u z B v ε:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph
open Spells
variable (S:StepData c f)(H:Odd S.ratio.count.val)(o:Site f)
local notation "Fθ"=> forest S.ratio H
local notation "Yr"=>AxisChart G Fθ
local notation "Ix"=> crux S H o b
local notation "Yσ"=> Libra.Keys G (Ix:Type)
-- choose simplifying union
noncomputable abbrev LargeK (G:Gauge)(b:ℕ):= (1+(Mā G 1 b 0+Mā G 2 b 0+Mā G 3 b 0)*4^ (3:ℕ))*(1+Glee 1+Glee 2+Glee 3)
lemma bigK (G:Gauge)(b:ℕ):1 ≤ LargeK G b:=by
       unfold LargeK; refine one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (mul_nonneg (add_nonneg (add_nonneg (Māhi G 1 b le_rfl) (Māhi G 2 b le_rfl)) (Māhi G 3 b le_rfl)) (by norm_num))) ?_; linarith only [GleeHi 1,GleeHi 2,GleeHi 3]
private lemma Vμ (G:Gauge)(b:ℕ)(ht:0≤ t)(hv:0≤ s)(hx:s ≤3*t)(k:ℕ)(hk:k ≤3) : Mā G k b s ≤ Mā G k b 0*(4^(3:ℕ)*(1+t)^ (3:ℕ)):=by
        rw [show Mā G k b s=Mā G k b 0*(1+s)^k from (by simp [Mā])]; rw [←mul_pow]; exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity) (show 1+s≤4*(1+t) by linarith) k).trans (pow_le_pow_right₀ (by linarith) hk)) (Māhi G k b le_rfl) -- .. syntax
lemma VFμ (G:Gauge)(b:ℕ)(ht:0≤t): CxT G b t ≤ LargeK G b*(1+t)^(3:ℕ)∧ DxT G b t≤ LargeK G b*(1+t)^(3:ℕ):=by
       let a:=fun i=>Mā G i b 0*(4^(3:ℕ)*(1+t)^(3:ℕ)); let v:= (1+Glee 1+Glee 2+Glee 3); have ht'(i:ℕ):0 ≤ a i:= mul_nonneg (Māhi G i b le_rfl) (by positivity); have hs:1 ≤ v:=by unfold v; linarith only [GleeHi 1,GleeHi 2,GleeHi 3]
       have hx:v*a 1+v*a 2+v*a 3 ≤ LargeK G b*(1+t)^(3:ℕ):= by rw [show LargeK G b*_= v*a 1+v*a 2+v*a 3+v*(1+t)^ (3:ℕ) from (by unfold LargeK v a; ring)]; exact le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hs) (by positivity))
       have he(i:ℕ)(hi:i ≤ 3): Mā G i b t≤ v*a i:= (Vμ G b ht ht (by linarith) i hi).trans (le_mul_of_one_le_left (ht' i) hs); have hv(i:ℕ)(hp:i ≤3)(hf:Glee i ≤ v): Glee i*Mā G i b (3*t) ≤ v*a i:= (mul_le_mul_of_nonneg_left (Vμ G b ht (by positivity) (le_refl _) i hp) (GleeHi i)).trans (mul_le_mul_of_nonneg_right hf (ht' i))
       refine ⟨(add_le_add (add_le_add (he 1 (by decide)) (he 2 (by decide))) (he 3 (by decide))).trans hx,(add_le_add (add_le_add (hv 1 (by decide) ?_) (hv 2 (by decide) ?_)) (hv 3 (by decide) ?_)).trans hx⟩ <;> unfold v <;> linarith only [GleeHi 1,GleeHi 2,GleeHi 3]
variable {p:Scoop G b→ℝ}
lemma Approve (hp: Velvet p s k) (x:Yσ)(hx:‖x‖ ≤ t)(hk:CxT G b t ≤ z): scope (Autum p (gam S H o b x)) (Jfare z (s*(1+z)^k)):=by
        have he:scope (BFilm b (gam S H o b x)) z:= fun i=>(payΦ S H o x hx i).trans hk; have hv: 0≤ z :=(norm_nonneg _).trans (he 0); exact thickP he hp.roll (fun i hi x hx=>(hp.seats i hi x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith only [hx]) _) hp.pos)) (mul_nonneg hp.pos (by positivity)) -- field
lemma Appeal (hp: Velvet p s k)(x y:Yσ)(hx:‖x‖ ≤ t)(hy:‖y‖≤ t)(hh:1 ≤ t)(hk:CxT G b t ≤ z)(hr:DxT G b t ≤ z): fuel (Autum p (gam S H o b x)) (Autum p (gam S H o b y)) (Jfair z (s*(1+z)^k)*(z*‖x-y‖)):=by
        have he: scope (BFilm b (gam S H o b x)) z:=fun i=>(payΦ S H o x hx i).trans hk; have ht:scope (BFilm b (gam S H o b y)) z:=fun i=>(payΦ S H o y hy i).trans hk; have hv:0 ≤ z:= (norm_nonneg _).trans (he 0); have H':=socketQ S H o y x hh hy hx; have hs:fuel _ _ (z*‖x-y‖):=fun i=>(H' i).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _)); exact Sun he hp.roll (fun i hi x hx=> (hp.seats i hi x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith only [hx]) _) hp.pos)) ht hs (mul_nonneg hp.pos (by positivity))
end YM.OPE.Crown
