import YM.SchemeConversionRG11.FirstMS.Triad.Graft

/-! Local split of dimension integration. Geometric inequalities with real hat squared. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

abbrev P := Fin 3
abbrev Nodes := Points 3

structure Box (x:Nodes)(R ρ:ℝ):Prop where
    mass : 0<R
    size : 0<ρ
    cleft : ∀ i j:P,i≠j→8*R<‖x i-x j‖
    edge : 128*R*ρ<1
    chest : ∀ i:P,128*‖x i‖*ρ<1

-- x points expressed absolute, insertion graph vertex coordinates as w absolute.
variable {x:Nodes} {R ρ:ℝ}
lemma shelter (h:x∈conf 3) : ∃ R ρ,Box x R ρ:= by
   classical
   let d := min ‖x 0 - x 1‖ (min ‖x 0 - x 2‖ ‖x 1 - x 2‖)
   have hx(i j:P)(hp:i≠j): 0<‖x i-x j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne hp))
   have hp:0<d:= lt_min (hx _ _ (by decide)) (lt_min (hx _ _ (by decide)) (hx _ _ (by decide)))
   have hh (i j:P)(hj:i≠j): d ≤ ‖x i-x j‖:= by
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals first | exact min_le_left .. | exact (min_le_right ..).trans (min_le_left ..)| exact (min_le_right ..).trans (min_le_right ..)| rw [norm_sub_rev]; first | exact min_le_left .. | exact (min_le_right ..).trans (min_le_left ..)|exact (min_le_right ..).trans (min_le_right ..)
   let R:= d/9; have hr : 0<R:=by unfold R; linarith
   let a (i:P) := ‖x i‖
   let L:= 129*(∑ i:P,(a i + R + 1)) -- parses
   have hL(i:P): 129*(a i+R+1)≤L:= mul_le_mul_of_nonneg_left (Finset.single_le_sum (s:=Finset.univ) (f:=fun j:P=>a j+R+1) (fun j _=>by unfold a; positivity) (Finset.mem_univ i)) (by norm_num)
   have hu (i:P):0 ≤ a i:=norm_nonneg _
   have hk : 0<L:=by linarith [hu 0,hL 0]
   refine ⟨R,L⁻¹,hr,by positivity,fun i j hj=> lt_of_lt_of_le ?_ (hh i j hj), ?_,fun i=> ?_⟩
   · unfold R; linarith
   · rw [← div_eq_mul_inv,div_lt_one hk]; linarith [hL 0,hu 0]
   rw [← div_eq_mul_inv,div_lt_one hk]; change 128*a i<_; linarith [hL i,hu i]

-- compact/far tap; total R², p.1 actual position of integration vertex

def move (y:E4)(p:Patch):Patch:=(p.1-y,p.2)
@[simp] lemma move_inverse (y:E4)(p:Patch): move y (move (-y) p)=p:=by simp [move]
lemma move_smooth (y:E4) : ContDiff ℝ ∞ (move y) := by unfold move; fun_prop

def bitnear (x:Nodes)(R:ℝ)(i:P)(p:Patch):= cap (total (move (x i) p)/R^2)
def last (ρ:ℝ)(p:Patch):= cap (total p*ρ^2)
def waist (x:Nodes)(R ρ:ℝ)(p:Patch):= last ρ p-∑ i:P,bitnear x R i p

theorem smooth_near (i:P): ContDiff ℝ ∞ (bitnear x R i):= cap_smooth.comp ((total_smooth.comp (move_smooth _)).div_const _)
theorem smooth_waist : ContDiff ℝ ∞ (waist x R ρ):= (cap_smooth.comp (total_smooth.mul contDiff_const)).sub (contDiff_iff_contDiffAt.mpr fun _=> ContDiffAt.sum fun i _=> (smooth_near i).contDiffAt)

variable (h:Box x R ρ)
include h
lemma Box.jammed (q:Patch){i j:P}(hj : j≠i)(hu:0≤q.2)(he: total q ≤ R^2): move (x j) (move (-(x i)) q)∈region:= by
   have hm := h.cleft j i hj
   have hv : ‖q.1‖≤R:= by
      change ‖q.1‖^2+_≤_ at he; nlinarith only [he,hu,h.mass,norm_nonneg q.1]
   change 0 < ‖(q.1- -(x i))-(x j)‖^2+q.2
   apply add_pos_of_pos_of_nonneg _ hu
   apply pow_pos (norm_pos_iff.mpr ?_)
   intro ha
   have hh : q.1=x j-x i:= by rw [show x j=q.1- -(x i) from (sub_eq_zero.mp ha).symm]; simp
   rw [hh] at hv; linarith [h.mass]
lemma Box.cut_radius (p:Patch)(hp:0≤p.2)(i:P)(he: total (move (x i) p)≤ R^2) : total p * ρ^2 < 1/4:= by
   have hq := h.mass; have hσ:=h.size; have hv:=h.chest i
   have hh:=h.edge; have hd:=norm_sub_norm_le p.1 (x i)
   change ‖p.1-x i‖^2+p.2≤R^2 at he
   have ht : ‖p.1-x i‖≤ R:= by nlinarith only [he,hp,norm_nonneg (p.1-x i),hq]
   unfold total; rw [add_mul,← mul_pow]
   have hx : ‖p.1‖*ρ < 2/128:= by nlinarith only [hv, hh, mul_le_mul_of_nonneg_right (show ‖p.1‖≤‖x i‖+R by linarith) hσ.le]
   have hy : p.2*ρ^2 < (1/128)^2:= by
      apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (show p.2 ≤ R^2 by nlinarith only [he,sq_nonneg (‖p.1-x i‖)]) (sq_nonneg _))
      rw [← mul_pow]; apply pow_lt_pow_left₀ _ (by positivity) (by decide); linarith
   nlinarith only [hp,hx,hy,pow_lt_pow_left₀ hx (by positivity : 0≤‖p.1‖*ρ) (by decide : (2:ℕ)≠0)]
lemma Box.waist_vanish (i:P) : waist x R ρ =ᶠ[𝓝 ((x i),(0:ℝ))] fun _=>0:= by
   have hr := h.mass
   let p:Patch:=(x i,0)
   have he : bitnear x R i =ᶠ[𝓝 p] fun _=>1:= by
      let f:= fun q:Patch=> total (move (x i) q)/R^2
      have hf: Continuous f:= ((total_smooth.comp (move_smooth _)).continuous).div_const _
      have hh: f p=0:= by simp [f,move,total,p]
      apply (hf.continuousAt.tendsto.eventually (p:=fun z=>cap z=1) ?_)
      rw [hh]; exact DR.edge.eventuallyEq_one
   have hb(j:P)(hj:j≠i):bitnear x R j=ᶠ[𝓝 p] fun _=>0:= by
      let f(q:Patch):= total (move (x j) q)/R^2
      have hf:Continuous f:= ((total_smooth.comp (move_smooth _)).continuous).div_const _
      have hy:1<f p:= by
         rw [show f p= ‖x i-x j‖^2/R^2 by simp [f,total,move,p],lt_div_iff₀ (by positivity)]; nlinarith only [h.cleft i j hj.symm,norm_nonneg (x i-x j),hr]
      exact ((hf.continuousAt.tendsto.eventually (lt_mem_nhds hy))).mono fun q hz=> cap_ends hz.le
   have hk:last ρ =ᶠ[𝓝 p] fun _=>1:= by
      let f:=fun q:Patch=> total q*ρ^2
      have hu:Continuous f:=total_smooth.continuous.mul_const _
      have hh: |f p|<1/4 := by
         rw [abs_of_nonneg (show 0≤f p by change 0≤(‖x i‖^2+0)*_; positivity)]
         exact h.cut_radius p (by change 0≤(0:ℝ); rfl) i (by simp [p,move,total]; positivity)
      exact (hu.abs.continuousAt.tendsto.eventually (gt_mem_nhds hh)).mono fun q hx=> cap_flat hx.le
   filter_upwards [hk,he,eventually_all_finset (Finset.univ.erase i)|>.mpr (fun j hj=> hb j (Finset.ne_of_mem_erase hj))] with q hx hc hm
   rw [waist,show last ρ q=1 from hx, Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j hj hN=> hm j (Finset.mem_erase.mpr ⟨hN,hj⟩)),show bitnear x R i q=1 from hc,sub_self]
lemma Box.waist_ends (p:Patch)(hp:0≤p.2)(ht: (ρ⁻¹)^2< total p): waist x R ρ p=0:= by
   have hρ:=h.size
   have hy : 1 < total p * ρ^2 := by grw [← ht]; rw [inv_pow,inv_mul_cancel₀ (pow_ne_zero _ hρ.ne')]
   unfold waist last; rw [cap_ends hy.le,Finset.sum_eq_zero,sub_zero]; intro i _
   apply cap_ends
   apply (one_le_div (pow_pos h.mass _)).mpr
   by_contra! he
   linarith only [hy,h.cut_radius p hp i he.le]

end YM.SchemeConversionRG11.FirstMS.Triad
