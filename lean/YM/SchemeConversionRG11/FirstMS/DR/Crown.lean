import YM.SchemeConversionRG11.FirstMS.DR.Mellin
import YM.SchemeConversionRG11.FirstMS.Triad.Touch
import YM.MSbar.Dim.Trace

/-! Open hat quadratic coefficient continuation proof. Not from integer interpolation:
 normalize via peel of genuine 2d plane and compact symbol Mellin continuation.
 This addresses one subdiagram with two evanescent derivative endpoints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.DR
open Function Set Filter MSbar MeasureTheory Metric Complex intervalIntegral
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

namespace crown
open MSbar.Dim MSbar.Symbol
local notation "π" => Real.pi

variable {H:ℝ} {h : ℝ → ℂ}
structure Fiber (H:ℝ) (h:ℝ→ℂ):Prop where
    size : 0<H
    smooth : ∀ t, 0 ≤ t → ContDiffAt ℝ ∞ h t
    ends : ∀ t,H^2 < t→ h t=0

variable (hn:Fiber H h)
include hn
lemma Fiber.radius : Radius H fun t:ℝ=> h (t^2) := ⟨hn.size.le,contDiff_iff_contDiffAt.mpr (fun t=> (hn.smooth _ (sq_nonneg _)).comp (f:=fun t:ℝ=> t^2) t ((contDiffAt_id (x:=t)).pow 2)), fun t=> by simp,
   fun t ht=> hn.ends _ (pow_lt_pow_left₀ ht hn.size.le (by decide))⟩
lemma Fiber.addition {t:ℝ} (ht:0≤t): Fiber H (fun u=>h (t+u)):= ⟨hn.size,
    fun r hr=> (hn.smooth _ (add_nonneg ht hr)).comp r (contDiffAt_const.add contDiffAt_id),fun _ hu=> hn.ends _ (hu.trans_le (le_add_of_nonneg_left ht))⟩
lemma Fiber.multiplies : Fiber H fun r=> r*h r := ⟨hn.size,fun r hr=> ofRealCLM.contDiff.contDiffAt.mul (hn.smooth _ hr),fun r hr=> by rw [hn.ends _ hr,mul_zero]⟩ -- coercion ?

lemma Fiber.shift2 (z:ℂ) : radial (fun t:ℝ=> (↑(t^2):ℂ)*h (t^2)) z = z/π * radial (fun t:ℝ=> h (t^2)) (z+1) := by
   let f (z:ℂ) := radial (fun t:ℝ=>h (t^2)) z
   refine congr_fun (wide (analytic hn.multiplies.radius) (g:=fun z=> z/π*f (z+1)) (fun z=> ?_) 0 ?_) z
   · exact (AnalyticAt.mul (analyticAt_id (𝕜:=ℂ)|>.div analyticAt_const (ofReal_ne_zero.mpr Real.pi_ne_zero)) ((analytic hn.radius _).comp (analyticAt_id (𝕜:=ℂ)|>.add analyticAt_const)))
   intro s hs
   dsimp only [f]; rw [actual hn.radius (show 0<(s+1).re by simp; linarith), actual hn.multiplies.radius hs, support_mellin hn.radius (U:=H^2) le_rfl,support_mellin hn.multiplies.radius (U:=H^2) le_rfl, add_sub_cancel_right, integral_of_le (sq_nonneg H), integral_of_le (sq_nonneg H)]
   have he (u:ℝ)(hu : u∈ Ioc 0 (H^2)): (u:ℂ)^(s-1)*((↑((Real.sqrt u)^2):ℂ)*h ((Real.sqrt u)^2))=(u:ℂ)^s * h ((Real.sqrt u)^2):= by
      have hh : (u:ℂ)≠0:= ofReal_ne_zero.mpr hu.1.ne'
      rw [Real.sq_sqrt hu.1.le,cpow_sub _ _ hh,cpow_one]
      field_simp
   -- arrangement
   have hh : (↑π:ℂ)≠0:= by exact_mod_cast Real.pi_ne_zero
   have hv : s≠0:= by rintro he; rw [he] at hs; exact lt_irrefl _ hs
   have hw := Gamma_ne_zero_of_re_pos hs
   rw [setIntegral_congr_fun measurableSet_Ioc he, Gamma_add_one s hv,cpow_add _ _ hh,cpow_one]; field_simp

lemma Fiber.body (m : ℕ) : HasTemperateGrowth (fun p: Hat m × ℝ=> h (‖p.1‖^2+p.2^2)) := by
   let f(p: Hat m×ℝ):= h (‖p.1‖^2+p.2^2)
   have he : ContDiff ℝ ∞ f := contDiff_iff_contDiffAt.mpr fun p => (hn.smooth _ (show 0≤ ‖p.1‖^2+p.2^2 by positivity)).comp p (((contDiff_norm_sq ℝ).contDiffAt.comp _ contDiffAt_fst).add (contDiffAt_snd.pow 2))
   refine HasCompactSupport.hasTemperateGrowth ?_ he
   apply (isCompact_closedBall (0:Hat m×ℝ) H).of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun x hx=> ?_) isClosed_closedBall)
   apply mem_closedBall_zero_iff.mpr
   refine le_of_not_gt (fun ht=> hx (hn.ends _ ((pow_lt_pow_left₀ ht hn.size.le (by decide : (2:ℕ)≠0)).trans_le ?_)))
   rw [Prod.norm_def]; rcases le_total ‖x.2‖ ‖x.1‖ with ht|ht
   · rw [max_eq_left ht]; exact le_add_of_nonneg_right (sq_nonneg _)
   rw [max_eq_right ht,Real.norm_eq_abs,sq_abs]; exact le_add_of_nonneg_left (sq_nonneg _)

def offset (h:ℝ→ℂ)(z:ℂ)(q:ℝ):= radial (fun t:ℝ=> h (q+t^2)) (z-1)
lemma Fiber.offset_ok (m:ℕ)(z:ℂ): Integrable (fun x:Hat m=> offset h z (‖x‖^2)) := by
   let f(v:Hat m) := offset h z (‖v‖^2)
   have hp : AH univ (fun p:ℂ × (Hat m×ℝ)=> h (‖p.2.1‖^2+p.2.2^2)) := AH.param_tame (hn.body m)
   have hb:= radial_AH (X:=Hat m) (t:=id) (H:=H) (differentiableOn_id (𝕜:=ℂ)) isOpen_univ hp (fun _ _ x=> (hn.addition (t:=‖x‖^2) (sq_nonneg _)).radius)
   have hk : Vanish H f := by
      intro x hx; unfold f offset; rw [show (fun t:ℝ=> h (‖x‖^2+t^2))=0 from funext fun t=> hn.ends _ ((pow_lt_pow_left₀ hx hn.size.le (by decide : (2:ℕ)≠0)).trans_le (le_add_of_nonneg_right (sq_nonneg _))), emit_zero]
   exact ((hb.slice (mem_univ (z-1))).1.continuous).integrable_of_hasCompactSupport (hk.compact)

lemma Fiber.fourplane (z:ℂ): radial (fun t:ℝ=> h (t^2)) (z+1)= ∫ v:Hat 2, offset h z (‖v‖^2) := by
   let f (x:Plane) := radial (fun t=> h (‖x‖^2+t^2)) z
   let g (x:Hat 2) := offset h z (‖x‖^2)
   have he (x:Plane×Plane): g (grow 1 x)= radial (fun t=>h (‖x.1‖^2+(‖x.2‖^2+t^2))) (z-1) := by unfold g offset; simp_rw [grow_sq,add_assoc]
   have hx : (∫ x:Plane,f x)= radial (fun t:ℝ=> h (t^2)) (z+1):= by
      have hh := descending hn.radius (hn.body 1) (fun a=> (hn.addition (t:=‖a‖^2) (sq_nonneg _)).radius) (fun x:Plane=> fun t=> show h _ = h ((Real.sqrt (‖x‖^2+t^2))^2) from by rw [Real.sq_sqrt (by positivity)]) (z+1)
      simpa only [f,add_sub_cancel_right] using hh
   have hb(x:Plane): (∫ y:Plane,g (grow 1 (x,y)))=f x:= by
      simp_rw [he]; let F:=hn.addition (t:=‖x‖^2) (sq_nonneg _)
      refine descending F.radius (F.body 1) (fun y=> (F.addition (t:=‖y‖^2) (sq_nonneg _)).radius) (fun y t=> ?_) z
      exact congr_arg (fun w=> h (‖x‖^2+w)) (Real.sq_sqrt (show 0≤‖y‖^2+t^2 by positivity)).symm
   change _=∫ v:Hat 2,g v
   rw [←hx, ← (bearing 1).integral_comp ((grow 1).toHomeomorph.measurableEmbedding)]
   change _= ∫ x,(g ∘ grow 1) x ∂(Measure.prod volume volume)
   rw [MeasureTheory.integral_prod (μ:=volume) (ν:=volume) (g ∘ grow 1) (((bearing 1).integrable_comp_emb ((grow 1).toHomeomorph.measurableEmbedding)).2 (hn.offset_ok 2 z))]
   exact integral_congr_ae (Eventually.of_forall fun a=> (hb a).symm)

omit hn in
private lemma planar (h:ℝ→ℂ) : (∫ v:Hat 2,h (‖v‖^2)) = (↑π:ℂ)*(∫ v:Plane, (↑‖v‖:ℂ)^2*h (‖v‖^2)) := by
   rw [integral_fun_norm_addHaar (volume:Measure (Hat 2)) (fun x=> h (x^2)),integral_fun_norm_addHaar (volume:Measure Plane) (fun x=> (x:ℂ)^2*h (x^2))]
   have hA : volume.real (ball (0:Plane) 1)=π:=by rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (hat_dim 1)]; norm_num [Real.pi_pos.le]
   have hB : volume.real (ball (0:Hat 2) 1)=π^2/2:=by rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (hat_dim 2),ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity)]; norm_num
   simp only [hat_dim,hA,hB,nsmul_eq_mul,real_smul]; norm_num
   simp only [← mul_assoc,pow_two]; ring_nf

omit hn in
private lemma symmetry (i j : Dim.fin 1) (h:ℝ→ℂ):
   (∫ v:Plane,(↑(v i):ℂ)^2*h (‖v‖^2))=∫ v:Plane,(↑(v j):ℂ)^2*h (‖v‖^2):=by
   let e:= LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
   rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
   apply MeasureTheory.integral_congr_ae (Eventually.of_forall _)
   intro v; change (↑((e v) i):ℂ)^2 * h (‖e v‖^2)=_
   rw [e.norm_map, show (e v) i=v j from ?_]
   unfold e; rw [LinearIsometryEquiv.piLpCongrLeft_apply]; simp

-- projection at external work with 1 ordinary plane and one extra radial handle.
def frameLine (h:ℝ→ℂ)(i : Dim.fin 1)(x:Hat (1+1)):ℂ:= (↑(((grow 1).symm x).1 i):ℂ)^2 *h (‖x‖^2) -- parsing
omit hn in
lemma frame_in (x:Plane)(r:ℝ)(i : Dim.fin 1): frameLine h i (push 1 (x,r))= (↑(x i):ℂ)^2 * h (‖x‖^2+r^2) := by
   unfold frameLine push; rw [(grow 1).symm_apply_apply,grow_sq,norm_smul,axis_norm]; change (↑(x i):ℂ)^2*h (‖x‖^2+(‖r‖*1)^2)=_; rw [mul_one (‖r‖),Real.norm_eq_abs,sq_abs]

/-- Open tensor nontrivial evan direction: trace multiplier paid BEFORE pole extraction. -/
theorem canonical_hat (s:ℂ)(i : Dim.fin 1): 2*s*plate s (frameLine h i)= radial (fun t:ℝ=> (↑(t^2):ℂ)*h (t^2)) s := by
   let H'(v:Plane):= offset h s (‖v‖^2)
   have he(j:Dim.fin 1)(v:Plane): face s (frameLine h j) v = (↑(v j):ℂ)^2*H' v:= by
      unfold face; simp_rw [frame_in]; rw [Nat.cast_one]; exact radial_smul (hn.addition (t:=‖v‖^2) (sq_nonneg _)|>.radius) _ _
   have hi(j:Dim.fin 1): Integrable (face s (frameLine h j)) := by
      have hN : Vanish H (frameLine h j) := fun x hx=> by rw [frameLine,hn.ends _ (pow_lt_pow_left₀ hx hn.size.le (by decide)),mul_zero]
      have hk: Packed 1 H (frameLine h j) := by
         refine ⟨hn.size.le,hN.compact.hasTemperateGrowth (contDiff_iff_contDiffAt.mpr ?_),hN,fun x t=>?_⟩
         · intro x
           apply ContDiffAt.mul (f:=fun x:Hat (1+1) => (↑(((grow 1).symm x).1 j):ℂ)^2) (?_) ((hn.smooth _ (sq_nonneg _)).comp x (contDiff_norm_sq ℝ).contDiffAt)
           exact (ofRealCLM.contDiff.comp (f:=fun x:Hat (1+1)=> ((grow 1).symm x).1 j) ((EuclideanSpace.proj (ι:=fin 1) (𝕜:=ℝ) j).contDiff.comp (contDiff_fst.comp ((grow 1).symm.contDiff)))).contDiffAt.pow 2
         change frameLine h j _=_; simp_rw [frame_in,neg_sq]
      exact hk.integrable _
   have hh : (∑ j:Dim.fin 1,plate s (frameLine h j))=∫ v:Plane,(↑‖v‖:ℂ)^2 * H' v:= by
      unfold plate; rw [←MeasureTheory.integral_finsetSum _ (fun j _=> hi j)]; refine integral_congr_ae (Eventually.of_forall fun v=>?_)
      change ∑ j:Dim.fin 1,_=(↑‖v‖:ℂ)^2 * _; simp_rw [he]; rw [← Finset.sum_mul,← ofReal_pow, EuclideanSpace.real_norm_sq_eq,ofReal_sum]
      simp only [ofReal_pow] -- fin
   have hq(j:Dim.fin 1): plate s (frameLine h j)=plate s (frameLine h i):= by unfold plate; simp_rw [he]; exact symmetry j i (offset h s)
   have ht:= hn.fourplane s; rw [planar (fun x=> offset h s x)] at ht
   rw [hn.shift2,ht]; change _= s/π * ((↑π:ℂ)*∫ v:Plane,(↑‖v‖:ℂ)^2 * H' v); rw [← hh]; simp_rw [hq]; norm_num [Dim.fin]; field_simp

end crown
end YM.SchemeConversionRG11.FirstMS.DR
