import YM.SchemeConversionRG11.FirstMS.Triad.Mouth

/-! Local test of exterior lines factors, from triple attachments at single integrated vertex. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

structure Stem where
   loc : P
   dual : Bool
   i : Fin 3
   axis : Axis
variable {x:Nodes} {R ρ:ℝ} (h:Box x R ρ)

/- stems includes one on ∂A (V has one derivative). Others ordinary A. -/
variable (l:P→Stem)(j:P)(a:Axis)

def kind (k:P):ℂ→E4→ℝ→ℂ:= if k=j then fun z=>bar z (l k).dual (l k).i a (l k).axis else rotate (l k).dual (l k).i (l k).axis
lemma off_kind (k:P): Off (kind l j a k) := by rw [kind]; split_ifs; exact off_bar ..; exact off_lane ..
def S (j:P) (k:P) (z:ℂ):ℂ:= if k=j then -4-2*z else -3-2*z
lemma owns_kind (k:P): owns (kind l j a k) (S j k):= by
   by_cases hk:k=j
   · rw [kind,if_pos hk,show S j k=fun z=>-4-2*z from funext fun z=>if_pos hk]; exact owns_bar _ _ _ _
   rw [kind,if_neg hk,show S j k=fun z=>-3-2*z from funext fun z=>if_neg hk]; exact owns_lane _ _ _
-- Absolute coords sheets

def vines (x:Nodes)(K:Finset P)(z:ℂ)(p:Patch) := ∏ k∈K, kind l j a k z (move (x (l k).loc) p).1 p.2

lemma vine_deriv {K:Finset P}{p:ℂ × Patch} (hz:p.1∈neighborhood)
   (hs:∀ k∈K,move (x (l k).loc) p.2∈region) : ContDiffAt ℝ ∞ (fun p:ℂ × Patch=> vines l j a x K p.1 p.2) p:= by
   unfold vines; apply contDiffAt_prod
   intro k hk; exact ((off_kind l j a k).smooth _ hz _ (hs k hk)).comp (f:=fun p:ℂ × Patch=> (p.1,move (x (l k).loc) p.2)) p (by unfold move; fun_prop)

lemma vine_color {K:Finset P}{p:ℂ × Patch} (hz:p.1∈neighborhood)
   (hs:∀ k∈K,move (x (l k).loc) p.2∈region) : DifferentiableAt ℂ (fun z=> vines l j a x K z p.2) p.1:=
   DifferentiableAt.fun_finsetProd (u:=K) (fun k hk=> (off_kind l j a k).colors p.1 hz _ (hs k hk)) -- name?

def cluster (l:P→Stem) (i:P):=Finset.univ.filter fun k:P=> (l k).loc=i

def locals (x:Nodes)(R:ℝ)(i:P):sheet:= fun q=> (cap (total q.2/R^2):ℂ) *vines l j a x (cluster l i)ᶜ q.1 (move (-(x i)) q.2)

include h

lemma cut_local(i:P): Touch R (locals l j a x R i):= by
   refine ⟨h.mass,?_,?_,?_⟩
   · intro z hz p hp
     rcases le_or_gt (total p) (R^2) with ht|ht
     · apply (vine_color l j a (p:=(z,move (-(x i)) p)) hz ?_).const_mul (↑(cap (total p/R^2)):ℂ)
       intro k hk; unfold cluster at hk; simp at hk; exact h.jammed p hk hp ht
     have he (w:ℂ): locals l j a x R i (w,p)=0:= by
       unfold locals; rw [cap_ends ((one_le_div (pow_pos h.mass _)).mpr ht.le), ofReal_zero,zero_mul]
     simp_rw [he]; exact differentiableAt_const _
   · intro q hq hp
     rcases le_or_gt (total q.2) (R^2) with ht|ht
     · apply ContDiffAt.mul (f:=fun q:ℂ×Patch=>(cap (total q.2/R^2):ℂ)) (ofRealCLM.contDiff.comp (cap_smooth.comp ((total_smooth.comp contDiff_snd).div_const _))).contDiffAt
          ((vine_deriv l j a (p:=(q.1, move (-(x i)) q.2)) hq ?_).comp (f:=fun p:ℂ×Patch=> (p.1,move (-(x i)) p.2)) q (by unfold move; fun_prop))
       intro k hk; unfold cluster at hk; simp at hk; exact h.jammed _ hk hp ht
     apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
     filter_upwards [((total_smooth.continuous.comp continuous_snd).continuousAt (x:=q) |>.tendsto).eventually (lt_mem_nhds ht)] with q hq
     change R^2 < total q.2 at hq; unfold locals; rw [cap_ends ((one_le_div (pow_pos h.mass _)).mpr hq.le),ofReal_zero,zero_mul]
   intro z hz p hp ht; unfold locals; rw [cap_ends ((one_le_div (pow_pos h.mass _)).mpr ht.le),ofReal_zero,zero_mul]

def mid (x:Nodes)(R ρ:ℝ):sheet:= fun p=> vert p.1*(waist x R ρ p.2:ℂ)*vines l j a x Finset.univ p.1 p.2

lemma cut_middle : Touch ρ⁻¹ (mid l j a x R ρ):= by
   let F := mid l j a x R ρ
   have hv (k:P) (p:Patch)(hp : 0≤p.2)(hz : p ≠ (x k, 0)) : move (x k) p∈region := by
      by_cases he:p.1= x k
      · exact show 0<‖p.1-x k‖^2+p.2 by rw [he,sub_self,norm_zero];exact add_pos_of_nonneg_of_pos (sq_nonneg _) (lt_of_le_of_ne hp (fun h=> hz (Prod.ext he h.symm)))
      exact show 0< ‖p.1-x k‖^2+p.2 from add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr he))) hp
   refine ⟨inv_pos.mpr h.size,?_,?_,?_⟩
   · intro z hz p hp
     by_cases he : ∃ k:P,p=(x k,0)
     · obtain ⟨k,rfl⟩:= he
       have hh:= (h.waist_vanish k).eq_of_nhds; unfold mid; simp only [hh,ofReal_zero,mul_zero,zero_mul]; exact differentiableAt_const _
     exact ((vert_analytic _).mul_const (↑(waist x R ρ p):ℂ)).mul (vine_color l j a (x:=x) (K:=Finset.univ) (p:=(z,p)) hz (fun k _=> hv _ p hp (fun hh=>he ⟨_,hh⟩)))
   · intro p hp hq
     by_cases he : ∃ k:P,p.2=(x k,0)
     · obtain ⟨k,hk⟩:= he; have he : waist x R ρ=ᶠ[𝓝 p.2] fun _=> 0:= hk ▸ h.waist_vanish k
       refine (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq ?_
       filter_upwards [continuousAt_snd.tendsto.eventually he] with q hq
       unfold mid; rw [show waist x R ρ q.2=0 from hq,ofReal_zero,mul_zero,zero_mul]
     apply ContDiffAt.mul (f:=fun p:ℂ×Patch=> vert p.1*(waist x R ρ p.2:ℂ)) (( ((vert_analytic.analyticAt p.1).restrictScalars).contDiffAt.comp p contDiffAt_fst).mul ((ofRealCLM.contDiff.comp (smooth_waist.comp contDiff_snd)).contDiffAt))
       (vine_deriv l j a hp (fun k _=> hv _ _ hq (fun hh=>he ⟨_,hh⟩)))
   intro z hz p hp ht; unfold mid; rw [h.waist_ends p hp ht,ofReal_zero,mul_zero,zero_mul]

def pivot (x:Nodes)(R ρ:ℝ)(z:ℂ) := billAt z (fun v=> mid l j a x R ρ (z,swell v))

omit h in
lemma Touch.folded {T:sheet} (ht:Touch R T) : Window neighborhood R (fun p:ℂ×ℝ×Patch=> T (p.1, swell p.2.2)) := by
   refine ⟨ht.entrance.arguments (w:=Prod.snd) tame_projR,ht.inside.le,fun z hz t v r=> by simp [swell],fun z hz x p hp=> ht.ends z hz _ (sq_nonneg _) ?_⟩
   exact (pow_lt_pow_left₀ hp ht.inside.le (by decide : (2:ℕ)≠0)).trans_le (q_square _)

lemma pivot_ok : AnalyticAt ℂ (pivot l j a x R ρ) 0 := (((cut_middle h l j a).folded).integral opened).analytic opened occurs 0

lemma middle_zero : pivot l j a x R ρ 0 = ∫ v:E4, mid l j a x R ρ (0,v,0):= by
   have he:= (cut_middle h l j a).folded.zero 0 occurs; simpa [pivot,swell] using he

lemma middle_pays : Integrable fun v:E4=>mid l j a x R ρ (0,v,0) := by
   let H:=cut_middle h l j a
   exact (H.effective 0 (by rfl) occurs).continuous.integrable_of_hasCompactSupport (H.supports occurs 0 (by rfl))

end YM.SchemeConversionRG11.FirstMS.Triad
