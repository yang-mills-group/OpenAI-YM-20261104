import YM.MSbar.Dim.Radial
import YM.MSbar.Symbol.HolJet
/-!
Scale-coordinate divided differences, without analyticity/integer irreps restrictions in momentum
or global scale Taylor. Use Hadamard repeatedly, but avoid combinatorics of higher F derivatives.
Regulator-analytic version included.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Symbol
open Dim Function Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {E X:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {f:ℝ→E} (hf: ContDiff ℝ ∞ f) {t:ℝ}

def strip (f:ℝ→E) := dslope f 0
omit [CompleteSpace E] in
lemma roll (f:ℝ→E): t • strip f t=f t-f 0:=by simpa only [sub_zero,strip] using sub_smul_dslope f 0 t
omit [CompleteSpace E] in
lemma strip_zero : strip (0:ℝ→E)=0:=by funext y; rcases eq_or_ne y 0 with rfl|h; simp [strip]; simp [strip,dslope_of_ne _ h, slope_def_module]
include hf
lemma strip_integral (t) : strip f t= ∫ u in Icc (0:ℝ) 1, deriv f (u*t):= by
   have hd := contDiff_infty_iff_deriv.mp hf; unfold strip; rcases eq_or_ne t 0 with rfl|hn
   · simp
   apply smul_right_injective E hn; dsimp only; rw [show t • dslope f 0 t=f t-f 0 from roll f,← integral_smul,integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
   have hD(u:ℝ): HasDerivAt (fun s:ℝ=> f (s*t)) (t • deriv f (u*t)) u := (hd.1 (u*t)).hasDerivAt.scomp u (by simpa using (hasDerivAt_id' u).mul_const t)
   rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>hD x)]; simp
   exact ((hd.2.continuous.comp (by fun_prop)).const_smul t).intervalIntegrable ..
private abbrev μ:= volume.restrict (Icc (0:ℝ) 1)
omit hf
lemma strip_tame {F:X × ℝ → E} (h:F.HasTemperateGrowth): (fun t:X × ℝ=> strip (fun u=> F (t.1,u)) t.2).HasTemperateGrowth :=by
   have H(x:X × ℝ): ContDiff ℝ ∞ (fun u=> F (x.1,u)):= h.1.comp (contDiff_const.prodMk contDiff_id)
   simp_rw [strip_integral (H _)]
   let g(x:(X × ℝ) × ℝ):= (x.1.1,x.2*x.1.2)
   have hw := (radial_tame h).comp (show HasTemperateGrowth g by unfold g; fun_prop)
   haveI:IsFiniteMeasure μ := by unfold μ; infer_instance
   simpa [one_smul,id,g,Function.comp,μ] using average_growth (ContinuousLinearMap.lsmul ℝ ℝ) aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc (μ:=μ) (integrable_const (1:ℝ)) hw
local notation "δ" => fun g : ℝ→E=> strip g
variable {U:Set ℂ}
omit [FiniteDimensional ℝ X] in
lemma AH.rad_deriv {F:ℂ × (X × ℝ) → ℂ}(hf: AH U F)(hu:IsOpen U): AH U (fun p:ℂ × (X × ℝ)=> deriv (fun t=> F (p.1,p.2.1,t)) p.2.2):=by
   refine (hf.diff_smooth hu (0,0,1)).congr hu fun z hz x=> ?_; unfold diff
   exact (((hf.smooth (z,x) hz).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x.2 ((hasDerivAt_const x.2 z).prodMk ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)))).deriv.symm
lemma AH.rad_strip {F:ℂ × (X × ℝ)→ℂ}(hf: AH U F)(hu:IsOpen U): AH U (fun p:ℂ × (X × ℝ)=> strip (fun t=>F (p.1,p.2.1,t)) p.2.2):=by
   let g(x:(X × ℝ) × ℝ):= (x.1.1,x.2*x.1.2)
   have hw := (hf.rad_deriv hu).arguments (show HasTemperateGrowth g by unfold g; fun_prop)
   haveI:IsFiniteMeasure μ:= by unfold μ; infer_instance
   refine (hw.after_average (p:=id) (μ:=μ) (integrable_const 1) aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc).congr hu fun z hz x=> ?_
   simpa [id,one_mul,g,μ,Function.comp] using! (strip_integral ((hf.slice hz).1.comp (contDiff_const (c:=x.1)|>.prodMk (contDiff_id (E:=ℝ)))) x.2).symm
-- Higher stripped coefficients (no combinatorial Nov point powers)
def layer (i:ℕ) : (ℝ→E)→ℝ→E:= strip^[i]
omit [CompleteSpace E] in
@[simp] lemma layer_next (i:ℕ):layer (i+1) f= strip (layer i f):=iterate_succ_apply' ..
omit [CompleteSpace E] in
@[simp] lemma first : layer 0 f=f := rfl
lemma AH.rad_tail (i:ℕ) {F:ℂ × (X × ℝ)→ℂ}(hf: AH U F)(hu:IsOpen U): AH U (fun p:ℂ × (X × ℝ)=> layer i (fun t=>F (p.1,p.2.1,t)) p.2.2):=by
   induction i with | zero=>exact hf | succ i ih=> simp_rw [layer_next]; exact ih.rad_strip hu
omit [CompleteSpace E] in
lemma deriv_tame_ray (hf: f.HasTemperateGrowth): (deriv f).HasTemperateGrowth:=
   (radial_tame (X:=ℝ) (hf.comp tame_projR)).comp (tame_pair (HasTemperateGrowth.const 0) (by fun_prop : HasTemperateGrowth (@id ℝ)))
lemma strip_tame_ray (hf: f.HasTemperateGrowth) : (strip f).HasTemperateGrowth :=
   (strip_tame (X:=ℝ) (hf.comp tame_projR)).comp (tame_pair (HasTemperateGrowth.const 0) (by fun_prop : HasTemperateGrowth (@id ℝ)))
lemma layer_tame_ray (i) (hf:f.HasTemperateGrowth): (layer i f).HasTemperateGrowth := by induction i with | zero=> exact hf | succ i ih=> rw [layer_next]; exact strip_tame_ray ih
end YM.MSbar.Symbol
