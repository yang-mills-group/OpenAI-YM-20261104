import YM.SchemeConversionRG11.FirstMS.Triad.NormalScale

/-! Compact local test of any position distribution here. Keep actual open hat radial square
 variable on test for Taylor. Smooth across u=0. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

abbrev sheet := ℂ × Patch → ℂ

def swell (p : Patch) : Patch := (p.1,p.2^2)

def total (p : Patch):ℝ:= ‖p.1‖^2+p.2
def Q (p:Patch):ℝ:= total (swell p)
lemma total_smooth : ContDiff ℝ ∞ total := ((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_snd
lemma q_smooth : ContDiff ℝ ∞ Q:= total_smooth.comp (f:=swell) (by unfold swell; fun_prop)
lemma q_nonneg (p:Patch): 0≤ Q p:= by change 0≤ ‖_‖^2+p.2^2; positivity
lemma q_square (p : Patch) : ‖p‖^2 ≤ Q p := by
    rw [Prod.norm_def]; unfold Q total swell; dsimp only
    rcases le_total ‖p.2‖ ‖p.1‖ with h|h
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (sq_nonneg _)
    rw [max_eq_right h,Real.norm_eq_abs,sq_abs]; simp
lemma q_scale(t:ℝ)(p:Patch): Q (t • p)= t^2*Q p:=by
    change ‖t • p.1‖^2+(t*p.2)^2=t^2*(‖p.1‖^2+p.2^2)
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]; ring

/-- T needs support only for u really hat squared. Λ=4R is one sufficient
  finite shell-stop radius: R physical bound on √Q. Need smooth across square hats u=0. -/
structure Touch (R:ℝ)(T:sheet) : Prop where
   inside : 0<R
   -- at ALL patches with nonnegative squared hats
   hol : ∀ z∈neighborhood, ∀ p:Patch,0≤p.2 → DifferentiableAt ℂ (fun z=> T (z,p)) z
   smooth : ∀ q:ℂ × Patch, q.1∈neighborhood→0≤q.2.2→ ContDiffAt ℝ ∞ T q
   ends : ∀ z∈neighborhood, ∀ p:Patch,0≤p.2 → R^2 < total p → T (z,p)=0

section Compact
variable {F:ℂ→E4→ℝ→ℂ} (hF:Off F) {T : sheet} {R:ℝ}
variable (hT : Touch R T)

def shape (F:ℂ→E4→ℝ→ℂ)(z:ℂ)(p:Patch):= (↑(lip (Q p)):ℂ)*F z p.1 (p.2^2)

lemma shape_ends {z:ℂ}(F:ℂ→E4→ℝ→ℂ){p:Patch}(hp:1<‖p‖): shape F z p=0:= by
   rw [shape,lip_ends (by nlinarith [q_square p]),ofReal_zero,zero_mul]
lemma shape_flip (F:ℂ→E4→ℝ→ℂ)(z:ℂ)(v:E4)(r:ℝ): shape F z (v,-r)=shape F z (v,r):= by simp [shape,Q,swell,total]
include hF
lemma shape_bill : AH neighborhood (uncurry (shape F)):= by
   apply upon_packed opened (isCompact_closedBall (0:Patch) 1) (fun z hz p hp=> shape_ends F (lt_of_not_ge (fun he=>hp (mem_closedBall.mpr (by simpa using he)))))
   · rintro ⟨z,p⟩ hz
     rcases eq_or_lt_of_le (q_nonneg p) with he|hp
     · apply contDiffAt_const (x:=(z,p)) (c:=(0:ℂ))|>.congr_of_eventuallyEq
       have h : ∀ᶠ x in 𝓝 (z,p),Q x.2 < 1/4 := ((q_smooth.continuous.comp continuous_snd).continuousAt (x:=(z,p))|>.tendsto).eventually (gt_mem_nhds (show Q p < 1/4 from he ▸ by norm_num))
       filter_upwards [h] with x hx
       change (↑(lip (Q x.2)):ℂ) * _ = 0; rw [lip_flats (by simpa [abs_of_nonneg (q_nonneg _)] using hx), ofReal_zero, zero_mul]
     exact (((ofRealCLM.contDiff.comp (lip_smooth.comp q_smooth)).comp contDiff_snd).contDiffAt).mul ((hF.smooth _ hz _ hp).comp (f:=fun x:ℂ × Patch=> (x.1,swell x.2)) (z,p) (by unfold swell; fun_prop))
   intro z p hz; rcases eq_or_lt_of_le (q_nonneg p) with he|hp
   · have ht(w:ℂ): shape F w p=0:= by simp only [shape,←he,lip_flats (by norm_num : |(0:ℝ)|<1/4), ofReal_zero,zero_mul]
     simp_rw [uncurry_apply_pair,ht]; exact differentiableAt_const _
   exact (hF.colors _ hz _ hp).const_mul  (↑(lip (Q p)):ℂ)

def servo (F:ℂ→E4→ℝ→ℂ)(T:sheet): ℂ × ℝ × Patch → ℂ:= fun x=> vert x.1*shape F x.1 x.2.2 * T (x.1,swell (x.2.1 • x.2.2))

include hT

lemma servo_ok : Window neighborhood 1 (servo F T) := by
   have hp(z:ℂ) (t u:ℝ)(v:E4) : T (z,swell (t • (v,-u)))=T (z,swell (t • (v,u))) := by
       unfold swell; simp
   have he (z:ℂ)(hz:z∈neighborhood)(x:ℝ × Patch)(ht:‖x‖>8*R+1):servo F T (z,x)=0:= by
       rcases lt_or_ge 1 ‖x.2‖ with hem|hem
       · simp only [servo,shape_ends F hem,mul_zero,zero_mul]
       rcases lt_or_ge (Q x.2) (1/4) with hf|hf
       · simp only [servo,shape, lip_flats (show |Q x.2|<1/4 by rw [abs_of_nonneg (q_nonneg _)];exact hf),ofReal_zero,mul_zero,zero_mul]
       have hr:= hT.inside
       have hm : 8*R < ‖x.1‖ := by change 8*R+1 < ‖x‖ at ht; rw [Prod.norm_def,lt_max_iff] at ht; rcases ht with ht|ht <;> linarith
       have hw : R^2 < Q (x.1 • x.2) := by
           rw [q_scale]; apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left hf (sq_nonneg _)); rw [← sq_abs x.1, ← Real.norm_eq_abs]; nlinarith only [hm,hr,pow_lt_pow_left₀ hm (by positivity : 0≤8*R) (by omega : (2:ℕ)≠0),sq_nonneg R]
       simp only [servo,hT.ends _ hz _ (sq_nonneg _) hw,mul_zero]
   refine ⟨?_,by norm_num,(fun z _ t v r=> by simp only [servo,shape_flip,hp]),fun z _ t r hr=> by simp only [servo,shape_ends F hr,mul_zero,zero_mul]⟩
   apply upon_packed opened (isCompact_closedBall (0:ℝ × Patch) (8*R+1))
     (fun z hz x hx=> he z hz x (lt_of_not_ge (fun hy=>hx (mem_closedBall.mpr (by simpa using hy)))))
   · intro x hx
     have ha : ContDiffAt ℝ ∞ vert x.1 := ((vert_analytic.analyticAt _).restrictScalars).contDiffAt
     refine ((ha.comp x contDiffAt_fst).mul ((shape_bill hF|>.smooth (x.1,x.2.2) hx).comp _
       (f:=fun x:ℂ×ℝ×Patch=> (x.1,x.2.2)) (by fun_prop))).mul ?_
     exact (hT.smooth (x.1,swell (x.2.1 • x.2.2)) hx (sq_nonneg _)).comp (f:=fun x:ℂ×ℝ×Patch=> (x.1,swell (x.2.1 • x.2.2))) x (by unfold swell; fun_prop)
   intro z x hz
   exact ((vert_analytic z).mul (shape_bill hF|>.cr z x.2 hz)).mul (hT.hol _ hz (swell (x.1 • x.2)) (sq_nonneg _))
end Compact

end YM.SchemeConversionRG11.FirstMS.Triad
