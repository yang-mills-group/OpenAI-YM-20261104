import YM.MSbar.Dim.Radial
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Analytic normalization of the dimensionally continued radial integral.
Squared radius variable. No disallowing exceptional external vector arguments: tensor kernel
smooth and even in the perpendicular radius. Holomorphic as operation on the smooth radial compact
symbol (verification here on each such symbol; not using Frechet-space analyticity in this whole
calculation). We'll give parameter estimates and more identities separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function MeasureTheory Filter Set Complex intervalIntegral Asymptotics
open scoped Topology ContDiff BigOperators Classical

variable {H U : ℝ} {s z : ℂ} {f : ℝ → ℂ} (h : Radius H f)
include h

lemma sqrt_above (hx : H^2 < U) : f (Real.sqrt U)=0:= h.ends _ (Real.lt_sqrt_of_sq_lt hx)
lemma sqrt_deriv (hx : 0 < U) : HasDerivAt (fun ν => f (Real.sqrt ν)) (raised f (Real.sqrt U)) U:=by
   let r:=Real.sqrt U; have hr:0<r:=Real.sqrt_pos.mpr hx
   have hp:= ((h.smooth.differentiable (by simp) r).hasDerivAt).scomp U (Real.hasDerivAt_sqrt hx.ne'); rw [one_div] at hp; change HasDerivAt (fun ν=> f (Real.sqrt ν)) ((2*r)⁻¹ • deriv f r) U at hp
   rw [← raised_id h.smooth h.even r, inv_smul_smul₀ (by positivity : 2*r≠0)] at hp;exact hp

omit h in
def rootM (f : ℝ→ℂ) := mellin (fun t=>f (Real.sqrt t))
lemma sqrt_mellin (hs : 0<s.re) {B : ℝ} : IntervalIntegrable (fun u:ℝ=> (u:ℂ)^(s-1)*f (Real.sqrt u)) volume 0 B:=by
   exact (intervalIntegrable_cpow' (by simpa using hs)).mul_continuousOn (h.smooth.continuous.comp Real.continuous_sqrt).continuousOn
lemma support_mellin (hx : H^2 ≤ U) : rootM f s=∫ u in (0:ℝ)..U,(u:ℂ)^(s-1)*f (Real.sqrt u):=by
   unfold rootM mellin; rw [integral_of_le ((sq_nonneg _).trans hx)]; simp only [smul_eq_mul]
   refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self (fun v hV=> ?_)
   rw [sqrt_above h (hx.trans_lt (lt_of_not_ge fun q=> hV.2 ⟨hV.1,q⟩)),mul_zero]
lemma move (hs : 0<s.re) : s*rootM f s= -rootM (raised f) (s+1):=by
   let U:= H^2+1; have hU : 0≤U:= by unfold U; positivity
   have ht : H^2<U:= lt_add_one _
   let e (v:ℝ):=(v:ℂ)^s*f (Real.sqrt v); let g (v:ℝ):=(v:ℂ)^s*raised f (Real.sqrt v)+ s*((v:ℂ)^(s-1)*f (Real.sqrt v))
   have he : Continuous e:= (continuous_ofReal_cpow_const hs).mul (h.smooth.continuous.comp Real.continuous_sqrt)
   have ht' : IntervalIntegrable (fun v:ℝ=>(v:ℂ)^s*raised f (Real.sqrt v)) volume 0 U:= ((continuous_ofReal_cpow_const hs).mul (h.raising.smooth.continuous.comp Real.continuous_sqrt)).intervalIntegrable ..
   have hf' : IntervalIntegrable (fun v:ℝ=> s*((v:ℂ)^(s-1)*f (Real.sqrt v))) volume 0 U:= (sqrt_mellin h hs).const_mul _
   have hd (x:ℝ) (hx : x∈ Ioo 0 U): HasDerivAt e (g x) x:=by
      have hpow : HasDerivAt (fun v:ℝ=>(v:ℂ)^s) (s*(x:ℂ)^(s-1)) x:= by
         simpa using! (((hasDerivAt_id (x:ℂ)).cpow_const (c:=s) (ofReal_mem_slitPlane.mpr hx.1)).comp_ofReal)
      unfold e; rw [show g x=(s*(x:ℂ)^(s-1))*_+(x:ℂ)^s*raised f (Real.sqrt x) from (show g x=(s*(x:ℂ)^(s-1))*f (Real.sqrt x)+(x:ℂ)^s*raised f (Real.sqrt x) by unfold g; ring)]; exact hpow.mul (sqrt_deriv h hx.1)
   have heq:= integral_eq_sub_of_hasDerivAt_of_le hU he.continuousOn hd (ht'.add hf'); dsimp only [e,g] at heq -- g?
   -- rearrange
   have hN : s ≠ 0:= fun he=> (by simp [he] at hs)
   rw [sqrt_above h ht,mul_zero,Complex.ofReal_zero,zero_cpow hN,zero_mul,sub_zero] at heq
   rw [intervalIntegral.integral_add ht' hf',intervalIntegral.integral_const_mul] at heq
   rw [support_mellin h ht.le,support_mellin h.raising ht.le,add_sub_cancel_right]; exact eq_neg_of_add_eq_zero_right heq

lemma rootM_diff (hs : 0<s.re) : MellinConvergent (fun t=> f (Real.sqrt t)) s ∧ DifferentiableAt ℂ (rootM f) s:=by
   let g:=fun t=> f (Real.sqrt t)
   have he: LocallyIntegrableOn g (Ioi (0:ℝ)) := ((h.smooth.continuous.comp Real.continuous_sqrt).continuousOn).locallyIntegrableOn measurableSet_Ioi
   have hz : g =O[𝓝[>] 0] (fun t=>t ^ (-(0:ℝ))) :=by
       simp only [neg_zero,Real.rpow_zero]
       exact isBigO_const_of_tendsto ((h.smooth.continuous.comp Real.continuous_sqrt).continuousWithinAt (x:=0) (s:=Ioi 0)) one_ne_zero
   have ht : g =O[atTop] (fun (t:ℝ)=> t ^ (-(s.re+1))) :=by
      simp_rw [isBigO_iff]; refine ⟨1,?_⟩
      filter_upwards [eventually_gt_atTop (H^2)] with t ht; simp [g,sqrt_above h ht]
   exact ⟨mellinConvergent_of_isBigO_rpow he ht (lt_add_one _) hz hs,mellin_differentiableAt_of_isBigO_rpow he ht (lt_add_one _) hz hs⟩

omit h in
/-- radial integral in complex `z` pairs of dimensions; formula at stage n. Use 0<z.re+n. -/
def stage (f : ℝ→ℂ) (n : ℕ) (z : ℂ) := (↑Real.pi:ℂ)^z * (-1)^n * (Gamma (z+n))⁻¹ * rootM (raised^[n] f) (z+n)
omit h in
def need (z : ℂ) := Nat.ceil (-z.re)+1
omit h in
def radial (f : ℝ→ℂ) (z : ℂ) := stage f (need z) z
omit h in
lemma enough (z : ℂ) : 0 < z.re + need z:=by
   unfold need; push_cast; linarith [Nat.le_ceil (-z.re)]
lemma stage_succ {n : ℕ} (hz : 0<z.re+n) : stage f n z=stage f (n+1) z:=by
   let g:= raised^[n] f; let r:ℂ:= z+n; have hr :0<r.re:=by simpa [r] using hz
   have he : r≠0:= fun he=> (by simp [he] at hr); have hG:= Gamma_ne_zero_of_re_pos hr
   have ht:= move (h.repeat n) hr
   unfold stage; rw [Nat.cast_add,Nat.cast_one,← add_assoc,iterate_succ_apply',Gamma_add_one (z+n) he,pow_succ]
   rw [show rootM (raised _) _= -(r*rootM g r) from eq_neg_of_add_eq_zero_right (eq_neg_iff_add_eq_zero.mp ht)]
   change _ = _ * (r * Gamma r)⁻¹ * -(r*rootM _ _); dsimp only [r,g] at *; field_simp

lemma formula {n : ℕ} (hz : 0<z.re+n) : radial f z=stage f n z:=by
   have he (n m : ℕ) (hx:0<z.re+n) (hw:n≤m):stage f n z=stage f m z:=by
      induction m,hw using Nat.le_induction with
      | base => rfl
      | succ m hN ih => exact ih.trans (stage_succ h (by linarith only [hx,(show (n:ℝ)≤m by exact_mod_cast hN)]))
   rcases le_total n (need z) with ht|ht
   · exact (he n (need z) hz ht).symm
   · exact he _ _ (enough z) ht
lemma stage_diff {n : ℕ} (hz : 0<z.re+n) : DifferentiableAt ℂ (stage f n) z :=by
   have he:= (differentiable_id (𝕜:=ℂ)).add_const (n:ℂ)
   have hp:= Complex.differentiable_one_div_Gamma.comp he
   have hr := (rootM_diff (h.repeat n) (show 0< (z+n).re by simpa using hz)).2
   exact ((((differentiableAt_id (x:=z)).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))).mul_const ((-1:ℂ)^n)).mul (hp z)).mul (hr.comp z (he z))
lemma differentiable : Differentiable ℂ (radial f) :=by
   intro z; let n:=need z; have he:0< z.re+n:=enough z
   apply (stage_diff h he).congr_of_eventuallyEq
   filter_upwards [(isOpen_lt continuous_const (Complex.continuous_re.add_const (n:ℝ))).mem_nhds (show z ∈ {x:ℂ|0<x.re+n} from he)] with t ht
   exact formula h ht
lemma analytic (z : ℂ) : AnalyticAt ℂ (radial f) z := (differentiable h).analyticAt z
lemma actual (hz : 0<z.re) : radial f z=(↑Real.pi:ℂ)^z*(Gamma z)⁻¹*rootM f z:=by
    rw [formula h (n:=0) (by simpa)]; simp [stage]
lemma radial_zero : radial f 0=f 0:=by
    let U:= H^2+1; have hU :0≤U:= by unfold U; positivity
    have ht : H^2<U:= lt_add_one _
    rw [formula h (n:=1) (by simp),stage]
    simp only [Nat.cast_one,zero_add,cpow_zero,pow_one,Gamma_one,one_mul,inv_one,mul_one,iterate_one]
    rw [support_mellin h.raising ht.le]; simp only [neg_mul,one_mul,sub_self,cpow_zero]
    rw [integral_eq_sub_of_hasDerivAt_of_le hU (h.smooth.continuous.comp Real.continuous_sqrt).continuousOn (fun x hx=>sqrt_deriv h hx.1) ((h.raising.smooth.continuous.comp Real.continuous_sqrt).intervalIntegrable ..)]; simp [sqrt_above h ht]
end YM.MSbar.Dim
