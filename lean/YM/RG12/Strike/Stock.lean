import YM.RG12.Strike.BreezeJet
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
/-! # Store kernel laws & jet escalation including shifted endpoints

Length-polarized homogeneous separated continuum kernels with at most one origin singularity.
No RG measures or lattice factors included. IR and UV prices don't cover coincident or
quasilocal clamped lines here. Homo powers NATURAL (positive singular orders).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter Metric MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {f g:R→ℂ}{a b:ℕ}
structure Garden (f:R→ℂ)(a:ℕ):Prop where
   openSite: silk puncture f
   line : VectorLaw f a
variable (h:Garden f a)
include h
lemma Garden.radial {x:R}(hx:x≠0){s:ℝ}(hs:0<s) : f (s•x)= (s:ℂ)⁻¹^a * f x:= by rw [h.line _ hx _ hs,zpow_neg,zpow_natCast, inv_pow]
lemma Garden.me : Measurable f:=measurable_of_continuousOn_compl_singleton 0 fun _ hx=> (h.openSite _ hx).continuousAt.continuousWithinAt
-- can't `VectorLaw.mul` directly if ℕ exponents, adapt.
lemma Garden.times (H:Garden g b) : Garden (f*g) (a+b):=by
   refine ⟨fun _ h' => ContDiffAt.mul (h.openSite _ h') (H.openSite _ h'),?_⟩
   push_cast; exact h.line.mul H.line
omit h in
lemma Garden.lineage (T:Foil)(L:Poke)(i:Axis4)(V:Poke):Garden (leg T L i V) (V.length+L.length+3):=by
   refine ⟨?_,?_⟩
   · intro x hx; unfold leg at *; exact ContDiffAt.sum (s:=Finset.univ) (fun j _=>contDiffAt_const.mul (vellum punct_open punct_field _ x hx))
   convert escalates T L V i using 1;push_cast; ring_nf
-- differentiated kernel at scaled point (not d on transformed F(t•x)).
lemma Garden.trim (i:Axis4):Garden (hit i f) (a+1):=by
   refine ⟨silken punct_open h.openSite i,?_⟩
   intro x hx t ht
   have htn:(t:ℂ)≠0:=by exact_mod_cast ht.ne'
   let c:=(t:ℂ)^(-(a:ℤ)); let H(y z):= f (palette i y z)
   have hp : t • x ≠ 0:= smul_ne_zero ht.ne' hx
   have he : (fun z:ℝ=> f (palette i (t•x) (t*z))) =ᶠ[𝓝 0] (fun z=> c*f (palette i x z)):=by
     have he : Tendsto (palette i x) (𝓝 (0:ℝ)) (𝓝 x):=by nth_rw 2 [show x=palette i x 0 from (born ..).symm];exact (drawing x i).continuousAt
     filter_upwards [he.eventually_ne hx] with z hz
     rw [show (palette i (t • x) (t * z))= t • palette i x z from by unfold palette; rw [smul_add,smul_smul]];exact h.line _ hz t ht
   have hH(y:R)(hy:y≠0):DifferentiableAt ℝ (H y) 0 := by exact (DifferentiableAt.comp (𝕜:=ℝ) _ ((h.openSite (palette i y 0) (by rw [born]; exact hy)).differentiableAt (by decide)) (drawing y i).differentiableAt)
   have hh: (t:ℂ)* hit i f (t•x)= c*hit i f x:=by
        have hti: HasDerivAt (fun z:ℝ=> t*z) t 0 := by simpa only [zero_mul,id_eq, mul_one,zero_add] using! (hasDerivAt_const (0:ℝ) t).mul (hasDerivAt_id' 0)
        have ha := (show DifferentiableAt ℝ (H (t • x)) (t*0) from by rw [mul_zero]; exact (hH (t•x) hp)).hasDerivAt.scomp (h:=fun z:ℝ=>t*z) 0 hti
        have hx := ((hasDerivAt_const (0:ℝ) c).mul (hH x hx).hasDerivAt)
        have hz := (ha.congr_of_eventuallyEq he.symm).unique hx
        rw [Complex.real_smul] at hz
        simpa only [hit,H,mul_zero,zero_mul,zero_add] using! hz
   apply mul_left_cancel₀ htn
   rw [hh]; unfold c;push_cast;rw [neg_add,zpow_add₀ htn]; norm_num; field_simp
lemma Garden.roam (L:Poke) : Garden (barrage f L) (a+L.length):=by
   induction L with
   | nil=>exact h
   | cons i L he=> convert he.trim i using 1  <;> simp only [barrage,List.length_cons,add_assoc] -- [barrage,add_assoc]
-- joint scaling exactly F law on Taylor of looked up F at remote point -- true for all integer orders
lemma Garden.fleece (n:ℕ){x:R}(hx:x≠0){y:R}{t:ℝ}(ht:0<t) : fresco n f (t•x) (t•y)=(t:ℂ)⁻¹^a*fresco n f x y := by
   unfold fresco gauge fall rain; simp only [Function.comp_apply, PiLp.smul_apply,smul_eq_mul, Complex.ofReal_mul, Finset.prod_mul_distrib, prod_const,card_univ,Fintype.card_fin]
   simp_rw [(h.roam ..).radial hx ht, List.length_ofFn]
   have htn:(t:ℂ)≠0:=by exact_mod_cast ht.ne'
   have he(c d:ℂ):(t:ℂ)⁻¹^(a+n)*c*((t:ℂ)^n*d)=(t:ℂ)⁻¹^a*(c*d):=by rw [pow_add,inv_pow,inv_pow]; field_simp
   simp_rw [he]; rw [← mul_sum];ring
lemma Garden.fiber (n:ℕ){x:R}(hx:x≠0){y:R}{t:ℝ}(ht:0<t) : rainJet n f (t•x) (t•y)=(t:ℂ)⁻¹^a* rainJet n f x y := by unfold rainJet; simp_rw [h.fleece _ hx ht,Finset.mul_sum]
variable (v:R)
omit h
abbrev shift (f:R→ℂ)(x:R)(y:R):ℂ:= f (y+x)
abbrev desert (x:R):Set R:=({-x}:Set R)ᶜ
include h
lemma Garden.many (x:R) : silk (desert x) (shift f x) := fun y hy=> ContDiffAt.comp (𝕜:=ℝ) (g:=f) (f:=fun y:R=>y+x) y (h.openSite (_:R) (show y+x≠0 from by exact mt eq_neg_of_add_eq_zero_left hy)) (contDiffAt_id.add contDiffAt_const) -- syntax reversed
omit h in
lemma carriage (i:Axis4) : hit i (shift f v)=shift (hit i f) v := by
   ext1 x; unfold hit shift palette
   congr 1; ext1 t; simp only [Function.comp_apply]; rw [add_right_comm]
omit h in
lemma river (p:Poke): barrage (shift f v) p=shift (barrage f p) v:=by induction p with
                                                                   | nil=> rfl
                                                                   | cons i p he=> simp only [barrage,he, carriage]
omit h in
lemma fresco_river (p:ℕ)(z:R) : fresco p (shift f v) 0 z = fresco p f v z:=by unfold fresco; simp_rw [river,shift,zero_add]
omit h in
lemma rain_river (p:ℕ)(z:R) : rainJet p (shift f v) 0 z=rainJet p f v z:=by unfold rainJet;simp_rw [fresco_river]
lemma Garden.zone (n:ℕ)(hv:v≠0):∃ B:ℝ,0 ≤ B ∧ ∀ᶠ y:R in 𝓝 0, ‖f (y+v)-rainJet n f v y‖ ≤ ‖y‖^n*B:=by
   have hv': (0:R) ∈ desert v:= show ¬ ((0:R) ∈ ({-v}:Set R)) from fun he=> hv (neg_eq_zero.mp ((mem_singleton_iff.mp he).symm))
   obtain ⟨B,hB,he⟩:= tower (shift f v) n isOpen_compl_singleton (h.many v) hv'
   simp_rw [rain_river] at he; exact ⟨B,hB,he⟩
lemma Garden.prix: ∃ C:ℝ,0 < C ∧ ∀ x:R,x≠0→ ‖f x‖ ≤ C/‖x‖^a:=by
   let s:=Metric.sphere (0:R) 1
   obtain ⟨A,hA⟩:=(isCompact_sphere (0:R) 1).exists_bound_of_continuousOn (f:=f) (fun x hx=> (h.openSite x (by rintro rfl; simp at hx)).continuousAt.continuousWithinAt)
   refine ⟨|A|+1,by positivity,fun x hx=>?_⟩
   let y:=‖x‖⁻¹ • x; have ht:=norm_pos_iff.mpr hx; have hy:y∈s:=by unfold y s;rw [mem_sphere_iff_norm,sub_zero,norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ ht.ne']
   have he : f x=(‖x‖:ℂ)⁻¹^a*f y := by rw [←h.radial (by unfold y; exact smul_ne_zero (inv_ne_zero ht.ne') hx) ht,show ‖x‖• y=x by unfold y;rw [← mul_smul, mul_inv_cancel₀ ht.ne',one_smul]]
   rw [he, norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
   grw [hA _ hy, ← le_abs_self A];rw [div_eq_mul_inv,inv_pow];nth_rw 1 [mul_comm];gcongr; linarith
lemma Garden.outer (x:R) :∃ D:ℝ,0 < D∧ ∀ᶠ w:R in cocompact R, ‖f (w-x)‖ ≤ D/(1+‖w‖)^a:=by
   obtain ⟨C,hC,he⟩:= h.prix
   refine ⟨C*2^a,by positivity,?_⟩
   filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (1+2*‖x‖))] with w hw
   change 1+2*‖x‖ ≤ ‖w‖ at hw
   have hz:= norm_sub_norm_le w x; have ht: (1+‖w‖)/2 ≤ ‖w-x‖:= by linarith --? norm_sub_norm_le abs?
   have hr:w-x≠0:= norm_pos_iff.mp ((by positivity: 0 < (1+‖w‖)/2).trans_le ht)
   apply (he (w-x) hr).trans
   grw [←ht];rw [div_pow]; field_simp; linarith
end YM.RG12.Strike
