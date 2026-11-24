import YM.OPE.Measuring.Rectangles

/-! # Two-depth rectangular axis bound uniform through compact parameters -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring.Axes
open Filter Set Function Asymptotics
open scoped ContDiff Topology
variable {V B : Type*}[NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup B][NormedSpace ℝ B]

section Layer
variable {W : Type*}[TopologicalSpace W]{t:Set W}
lemma smooth_tube (ht:IsCompact t) {p:ℝ×W→ Prop} (h:∀ b∈t, ∀ᶠ q in 𝓝 ((0:ℝ),b),p q): ∀ᶠ x:ℝ in 𝓝 0,∀ b∈t,p (x,b):=by
    obtain ⟨u,v,hu,hv,hU,hV,hO⟩:= generalized_tube_lemma (s:={(0:ℝ)}) isCompact_singleton ht isOpen_interior (n:=interior (setOf p)) (by rintro ⟨x,b⟩ ⟨hx,hb⟩; exact Eq.symm (show x=(0:ℝ) from hx) ▸ mem_interior_iff_mem_nhds.mpr (h _ hb))
    filter_upwards [hu.mem_nhds (hU (mem_singleton _))] with x hx b hb using interior_subset (hO (⟨hx,hV hb⟩: (x,b)∈u×ˢv))
end Layer

variable {n e:ℕ}{g:ℝ×ℝ×V→B}{S:Set V}(K:Set V) (ht:IsCompact S)(hk:K⊆S)
       (hG:∀ y∈Icc (0:ℝ) 1,∀ b∈S, ∀ᶠ i in 𝓝 ((0:ℝ),y,b),ContDiffAt ℝ ∞ g i)
include ht hk hG

lemma strong_grid (H:∀ ε>0, ∃ c:V→ℝ, ∀ᶠ (x:ℝ) in 𝓝[>] 0,∀ y : ℝ, 0<y→y≤1→ ∀ b∈K, ‖g (x,y,b)‖ ≤ c b * x^((n:ℝ)-ε)*y^((e:ℝ)-ε)):
    ∃ C:ℝ, ∀ᶠ x:ℝ in 𝓝[>]0, ∀ y:ℝ, 0<y→ y≤1→∀ b∈K, ‖g (x,y,b)‖ ≤ C*x^n*y^e:=by
      let P(x:ℝ×ℝ×V):= ∀ᶠ i in 𝓝 x,ContDiffAt ℝ ∞ g i
      let U:= Icc (0:ℝ) 1 ×ˢ S
      have hU:∀ᶠ x in 𝓝[>]0,∀ b∈U,P (x,b) := (smooth_tube (p:=P) (isCompact_Icc.prod ht) (by rintro ⟨y,b⟩ ⟨hy,hb⟩; exact eventually_eventually_nhds.mpr (hG _ hy _ hb))).filter_mono nhdsWithin_le_nhds
      obtain ⟨b₀,H0⟩:=H (1/2) (by norm_num)
      obtain ⟨r,hr,hc⟩ := Metric.mem_nhdsWithin_iff.mp (hU.and H0)
      let vx:ℝ×ℝ×V:=(1,0,0); let vy:ℝ×ℝ×V:=(0,1,0); let fn:= path vx (path vy g e) n
      let A:=r/2; have hA:0<A:=half_pos hr
      have hh{x:ℝ}(hx:x∈Ioc (0:ℝ) A) : dist x 0<r:=by rw [dist_zero_right,Real.norm_of_nonneg hx.1.le]; exact hx.2.trans_lt (half_lt_self hr)
      have h₁{x y b} (hx:x∈Ioc 0 A)(hy:y∈Ioc (0:ℝ) 1)(hb:b∈K) : ‖g (x,y,b)‖ ≤ b₀ b*x^((n:ℝ)-1/2)*y^((e:ℝ)-1/2):= (hc ⟨Metric.mem_ball.mpr (hh hx),hx.1⟩).2 y hy.1 hy.2 b hb
      have h₂ (x y:ℝ){b:V} (hx:x∈Icc 0 A)(hy:y∈Icc (0:ℝ) 1)(hb:b∈S) :∀ᶠ i in 𝓝 (x,y,b),ContDiffAt ℝ ∞ g i :=by
             rcases eq_or_lt_of_le hx.1 with he|hK
             · rw [← he]; exact hG _ hy _ hb
             exact (hc ⟨Metric.mem_ball.mpr (hh ⟨hK,hx.2⟩),hK⟩).1 ⟨y,b⟩ ⟨hy,hb⟩
      have hcont(x)(hx:x∈(Icc (0:ℝ) A ×ˢ (Icc (0:ℝ) 1 ×ˢ S))):ContDiffAt ℝ ∞ fn x:=
         path_live vx n (path_live vy e ((h₂ _ _ hx.1 hx.2.1 hx.2.2).self_of_nhds))
      obtain ⟨C₀,hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod ht)|>.bddAbove_image (show ContinuousOn (fun x=>‖fn x‖) _ from fun x hx=> (hcont x hx).continuousAt.norm.continuousWithinAt))
      refine ⟨max C₀ 0, (by
        filter_upwards [(eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hA)),(self_mem_nhdsWithin (s:=Ioi (0:ℝ)))] with x hX hXp
        change 0<x at hXp
        intro y hY hY' q hq
        let p:ℝ×ℝ×V:=⟨0,0,q⟩
        have hz(r s:ℝ):cross p vx vy r s=(r,s,q):=by ext1 <;> simp [cross,p,vx,vy]
        have huv:∀ᶠ z:ℝ in 𝓝[>]0, z∈Ioc (0:ℝ) A:= (show ∀ᶠ z:ℝ in 𝓝[>]0, 0<z from self_mem_nhdsWithin).and (eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds hA))
        have hπ:∀ᶠ z:ℝ in 𝓝[>]0, z∈Ioc (0:ℝ) 1:= (show ∀ᶠ z:ℝ in 𝓝[>]0, 0<z from self_mem_nhdsWithin).and (eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one))
        have fill(w:ℝ)(hw:w∈Ioo (0:ℝ) 1): ‖g ((x,w,q):ℝ×ℝ×V)‖ ≤ max C₀ 0*x^n*w^e:=by
          rw [← hz]
          refine mixed (A:=A) (C:=max C₀ 0) ⟨hXp,hX⟩ ⟨hw.1,hw.2⟩ n e (by intro r hr s hs; rw [hz]; exact h₂ _ _ hr hs (hk hq)) ?_ ?_ ?_
          · intro i hi z hz'; refine pre_jets (a:=(n:ℝ)-1/2) (C:=b₀ q * z^((e:ℝ)-1/2)) (?_) (?_) (?_)
            · have he: (↑(i+1):ℝ) ≤ n:= by exact_mod_cast hi
              push_cast at he; linarith
            · rw [show p+z•vy=cross p vx vy 0 z by rw [cross,zero_smul,add_zero],hz]; exact h₂ _ _ ⟨le_rfl,hA.le⟩ ⟨hz'.1.le,hz'.2.le⟩ (hk hq)
            filter_upwards [huv] with i hi; rw [add_right_comm,← cross,hz]; exact (h₁ hi ⟨hz'.1,hz'.2.le⟩ hq).trans <| le_of_eq <| mul_right_comm ..
          · intro i hi z hz'; refine pre_jets (a:=(e:ℝ)-1/2) (C:=b₀ q * z^((n:ℝ)-1/2)) ?_ (?_) (?_)
            · have he: (↑(i+1):ℝ) ≤ e:= by exact_mod_cast hi
              push_cast at he; linarith
            · rw [show p+z•vx=cross p vx vy z 0 by rw [cross,zero_smul,add_zero],hz]; exact h₂ _ _ ⟨hz'.1.le,hz'.2.le⟩ ⟨le_rfl,zero_le_one⟩ (hk hq)
            filter_upwards [hπ] with i hi; rw [← cross,hz]; exact h₁ ⟨hz'.1,hz'.2.le⟩ hi hq
          intro r hr s hs; rw [hz]; exact (hC (mem_image_of_mem _ ⟨hr,hs,hk hq⟩)).trans (le_max_left ..)
        by_cases ht':y=1; swap
        · exact fill y ⟨hY,lt_of_le_of_ne hY' ht'⟩
        subst y
        have ht:(fun w:ℝ=> ‖g (x,w,q)‖) ≤ᶠ[𝓝[<] (1:ℝ)] fun w=> max C₀ 0*x^n*w^e:= ((eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds zero_lt_one)).and (self_mem_nhdsWithin (s:=Iio (1:ℝ)))).mono (fun y hy=> fill y hy)
        have hX':ContinuousAt (fun w:ℝ => ‖g (x,w,q)‖) 1:=((h₂ _ _ (⟨hXp.le,hX.le⟩: x∈Icc (0:ℝ) A) (by simp: (1:ℝ)∈Icc (0:ℝ) 1) (hk hq)).self_of_nhds.continuousAt.norm.comp (g:=fun u=> ‖g u‖) (f:=fun u:ℝ=>(x,u,q)) (x:=1) (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousAt)
        have hg':ContinuousAt (fun w:ℝ=> max C₀ 0*x^n*w^e) 1:= by fun_prop
        exact le_of_tendsto_of_tendsto (a₁:=‖g (x,1,q)‖) (a₂:=max C₀ 0*x^n*(1:ℝ)^e) hX'.continuousWithinAt hg'.continuousWithinAt ht)⟩
end YM.OPE.Measuring.Axes
