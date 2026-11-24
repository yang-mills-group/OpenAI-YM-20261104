import YM.RegulatorIR.Halo.Glob
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.DSlope

/-!
Finite group neighbor Ward path generator. Test moment order charged after
choosing closed analytic germ. Use parameter `A` and two site logs independent
before background substitutions. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Gain
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{W:Type}{f:Side}{u i p:ℕ}{l P:ℝ}

lemma sale {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{f : ℝ→ E}(h:ContDiffAt ℝ ω f 0)(hf:f 0=0) : ContDiffAt ℝ ω (dslope f 0) 0:=by
 have H : ((1:ℕ):ℕ∞)≤ analyticOrderAt f 0:= by have hp: analyticOrderAt f 0≠0:=h.analyticAt.analyticOrderAt_ne_zero.mpr hf; exact_mod_cast (Order.one_le_iff_pos.mpr (bot_lt_iff_ne_bot.mpr hp)) -- inspect
 obtain ⟨g,hg,he⟩:= (natCast_le_analyticOrderAt h.analyticAt (n:=1)).mp H
 have hx: HasDerivAt f (g 0) 0:=by
    have hv:= HasDerivAt.smul (hasDerivAt_id' (0:ℝ)) hg.differentiableAt.hasDerivAt; simp only [one_smul,zero_smul,zero_add] at hv
    exact hv.congr_of_eventuallyEq (he.mono (fun i hi=>by simpa using hi))
 apply AnalyticAt.contDiffAt hg |>.congr_of_eventuallyEq
 filter_upwards [he] with i hi; by_cases hw:i=0
 · subst i; rw [dslope_same,hx.deriv]
 rw [dslope_of_ne _ hw, slope_def_module, hf,sub_zero, hi]; simp [smul_smul,hw] -- E generic use slope_def_module

attribute [local instance] Gauge.frobInner
-- t log convention
abbrev Trip (G:Gauge):= G.Color×G.Color×G.Color -- A, f tail f head

def tiltU (x:Trip G): G.El:= G.lieExp x.2.1 * G.lieExp x.1 * (G.lieExp x.2.2)⁻¹
def billU (x:Trip G): G.Color := G.plog (G.mat (tiltU x))
def crest (x:Trip G)(t:ℝ):=dslope (fun t:ℝ=> billU (t • x)) 0 t
lemma tilt_z (G:Gauge): tiltU (0:Trip G)=1:= by simp [tiltU]
lemma bill_z (G:Gauge) : billU (0:Trip G)=0:=by simp [billU, tilt_z]
lemma tilt_smooth : ContDiffAt ℝ ω (fun i:Trip G=>G.mat (tiltU i)) 0:=by
 simp_rw [tiltU, G.mat_mul,G.mat_inv]
 apply ContDiffAt.mul
 · exact (G.exp_jet.contDiffAt.comp (f:=fun i:Trip G=>i.2.1) _ (contDiffAt_fst.comp (f:=Prod.snd) _ contDiffAt_snd)).mul (G.exp_jet.contDiffAt.comp (f:=Prod.fst) _ contDiffAt_fst)
 exact (starL' ℝ).contDiff.contDiffAt.comp _ (G.exp_jet.contDiffAt.comp (f:=fun i:Trip G=>i.2.2) _ (contDiffAt_snd.comp (f:=Prod.snd) _ contDiffAt_snd))
lemma bill_smooth : ContDiffAt ℝ ω (billU (G:=G)) 0:=by refine (show ContDiffAt ℝ ω G.plog (G.mat (tiltU (0:Trip G))) from ?_).comp (f:=fun i:Trip G=> G.mat (tiltU i)) 0 tilt_smooth; rw [tilt_z,G.mat_one]; exact G.plog_diff
lemma crest_v (x: Trip G)(t:ℝ): t • crest x t=billU (t • x):=by simpa [crest,bill_z] using sub_smul_dslope (fun v:ℝ=> billU (v • x)) 0 t
lemma crest_origin (x : Trip G): crest x 0=x.2.1+x.1-x.2.2:=by
 unfold crest; rw [dslope_same]; refine HasDerivAt.deriv ?_
 have hp : G.mat (tiltU ((0:ℝ) • x))=1:=by rw [zero_smul, tilt_z,G.mat_one]
 have hh: HasDerivAt (fun t:ℝ=> G.mat (tiltU (t • x))) (G.colorMat (x.2.1+x.1-x.2.2)) 0:= by
    unfold tiltU; simp only [G.mat_mul,G.mat_inv]
    apply (((vertical_deriv x.2.1).mul (vertical_deriv x.1)).mul (vertical_deriv x.2.2).star).congr_deriv
    simp [colorMat_skew,sub_eq_add_neg]
 have H: HasFDerivAt G.plog (fderiv ℝ G.plog 1) (G.mat (tiltU ((0:ℝ) • x))):=by rw [hp]; exact (G.plog_diff.differentiableAt (by simp)).hasFDerivAt
 exact (H.comp_hasDerivAt 0 hh).congr_deriv (plog_rotate ..)
lemma crest_smooth (x:Trip G) : ContDiffAt ℝ ∞ (crest x) 0:=
 (sale (show ContDiffAt ℝ ω (fun t:ℝ=> billU (t • x)) 0 from (show ContDiffAt ℝ ω billU ((0:ℝ) • x) from by rw [zero_smul];exact bill_smooth).comp (f:=fun t=>t • x) _ (contDiffAt_id.smul contDiffAt_const)) (by rw [zero_smul,bill_z])).of_le le_top
lemma signal (x:Trip G): ∀ᶠ t in 𝓝 0,G.lieExp (t • crest x t)= tiltU (t • x):=by
 have h : Tendsto (fun t:ℝ=> tiltU (t • x)) (𝓝 0) (𝓝 1):=by
    have hh : Continuous (tiltU (G:=G)):=by unfold tiltU;fun_prop
    convert (hh.comp (continuous_id.smul continuous_const)).tendsto (0:ℝ) using 1; try rfl
    change 𝓝 (1:G.El)=𝓝 (tiltU ((0:ℝ) • x)); rw [zero_smul,tilt_z]
 filter_upwards [h.eventually G.plog_right] with t ht; rw [crest_v]; exact ht

-- local link-only voice factorial

def song (G:Gauge)(i:ℕ) (v:G.ColorIndex)(u:Trip G):ℝ:= jet (fun x:Trip G=>billU x v) (i+1) u
def routeS (G:Gauge)(v:G.ColorIndex)(x:Trip G):ℝ⟦X⟧:= tale (fun t=> crest x t v)
lemma song_jet (i:ℕ)(x:Trip G)(v:G.ColorIndex): coeff i (routeS G v x)=song G i v x:=by
 let f(x:Trip G):=billU x v; let g(t:ℝ):= crest x t v
 let a : G.Color →L[ℝ] ℝ:= (PiLp.proj 2 (fun _:G.ColorIndex=>ℝ) v)
 have hg : ContDiffAt ℝ ∞ g 0:= a.contDiff.contDiffAt.comp _ (crest_smooth x)
 have hp: ContDiffAt ℝ ∞ f 0:= a.contDiff.contDiffAt.comp _ (bill_smooth.of_le le_top)
 change _=jet f (i+1) _; rw [show jet f _ _=PowerSeries.coeff (i+1) (inscription f x) from (by rw [inscription,coeff_mk]),← lore hp]
 rw [show (fun t:ℝ=>f (t • x)) = g*(fun t:ℝ=>t^1) from ?_,tale_mul (f:=g) (g:=fun t:ℝ=>t^1) hg (contDiffAt_id.pow _),Script.dictates (f:=fun t:ℝ=>t^1) (contDiffAt_id.pow _) (Script.predicts_pow _),coeff_mul_X_pow]; rfl
 ext t; unfold f;rw [← crest_v,Pi.mul_apply];change t* g t=_;rw [mul_comm,pow_one]
lemma crest_rev (x:Trip G): ∀ᶠ t in 𝓝 0,crest (-x.1,x.2.2,x.2.1) t= -crest x t:=by
 let y:Trip G:=(-x.1,x.2.2,x.2.1)
 have hp(t:ℝ): tiltU (t • y)=(tiltU (t • x))⁻¹:=by simp [y,tiltU,Work.F03.exp_neg_color]; group
 have H: ∀ᶠ t:ℝ in 𝓝 0,t • crest y t=t • -crest x t:=by
    have hh (X: Trip G): Tendsto (fun t:ℝ=> t • crest X t) (𝓝 0) (𝓝 0):= by
       convert ((continuousAt_id (x:=0)).smul (crest_smooth X).continuousAt).tendsto using 1 <;> first|rfl | skip
       change 𝓝 (0:G.Color)= 𝓝 ((0:ℝ) • _); rw [zero_smul]
    have he : Tendsto (fun t:ℝ=> t • -crest x t) (𝓝 0) (𝓝 0):=by simp_rw [smul_neg]; simpa only [neg_zero] using (hh x).neg
    filter_upwards [signal x,signal y,(hh y).eventually G.plog_left,he.eventually G.plog_left] with t hx hy Ht Hb
    have hz : G.lieExp (t • -crest x t)= tiltU (t • y):=by rw [smul_neg,Work.F03.exp_neg_color,hx,hp]
    exact Ht.symm.trans ((congr_arg (G.plog ∘ G.mat) (hy.trans hz.symm)).trans Hb)
 change ∀ᶠ t in 𝓝 0,crest y t= _
 filter_upwards [H] with t h; by_cases ht:t=0
 · subst t; rw [crest_origin, crest_origin]; unfold y;dsimp only;abel
 exact smul_right_injective (G.Color) ht h
end YM.RegulatorIR.Gain
