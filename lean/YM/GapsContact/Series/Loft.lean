import YM.GapsContact.Series.Region
/-! # Real-slice seed: from Euclidean prices on pure Wick data -/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Pattern
open Function Filter Set Metric Complex Complex.HadamardThreeLines
open scoped Topology Classical
variable {E F H: Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
       [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℂ H]

-- parametrisation small upright complex motion to reach I exactly; entire, real on line Re=0
private def Δ :ℂ := Complex.exp (1/2)- Complex.exp (-1/2)
private def curve (z:ℂ):= I * (Complex.exp z-Complex.exp (-z))/Δ
private theorem delta : Δ.im=0 ∧ Δ.re>0 :=by
    let e:ℝ:=1/2
    have he:0<e:=by norm_num [e]
    have ht: Δ=((↑(Real.exp e- Real.exp (-e))):ℂ):=by simp [Δ,Complex.ofReal_exp,e]; ring_nf
    rw [ht]; simp only [ofReal_im,ofReal_re,true_and]; exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
private theorem nz : Δ≠0:= fun h=> delta.2.ne' (congr_arg Complex.re h)
private theorem eClock : curve (1/2) = I :=by unfold curve; rw [show -(1/2:ℂ)= -1/2 by ring]; change _*Δ/Δ=_; field_simp [nz]
private theorem curve_real {z:ℂ} (h:z.re=0): curve z=((curve z).re:ℂ):=by
   apply Complex.ext
   · simp
   have H: (-z).re=0:=by simp[h]
   rw[ofReal_im,curve,div_im,
      delta.1]; simp only [mul_zero, I_mul_im,Complex.sub_re,exp_re,h,H,neg_im,Real.cos_neg]; ring
private theorem curve_bound (z:ℂ)(h:z∈band) : ‖curve z‖ ≤ (Real.exp 1+Real.exp 1)/‖Δ‖:=by
   have ht:z.re≤1:= (show z.re∈Icc (0:ℝ) 1 from h).2; have hx:0≤z.re:=(show z.re∈ Icc (0:ℝ) 1 from h).1
   unfold curve; rw [norm_div, norm_mul, norm_I, one_mul]; gcongr; exact norm_sub_le_of_le (by rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr ht) (by rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; rw [Complex.neg_re]; linarith)
private theorem curved : Differentiable ℂ curve:= by unfold curve; fun_prop

def sky (M:F →L[ℝ] E) : (F × F)→L[ℝ] E := M.comp (ContinuousLinearMap.fst ℝ F F) + I • M.comp (ContinuousLinearMap.snd ℝ F F)
lemma sky_at (M:F→L[ℝ] E)(x:F × F): sky M x= M x.1 + I • M x.2:=rfl

variable (M:F→L[ℝ] E)

-- real span version available for Wick by Work.C20.wick_span
lemma merges (hm: Submodule.span ℂ (Set.range M)= ⊤) : Surjective (sky M) :=by
    intro z
    change z∈ Set.range _
    have hx:z∈ Submodule.span ℂ (Set.range M):=by rw[hm]; trivial
    induction hx using Submodule.span_induction with
    | mem p h=> obtain ⟨x,rfl⟩:=h; exact ⟨(x,0),by simp [sky_at]⟩
    | zero => exact ⟨0,map_zero _⟩
    | add p q _ _ hx hy=> obtain ⟨p,rfl⟩:=hx; obtain ⟨q,rfl⟩:=hy; exact ⟨p+q,map_add ..⟩
    | smul c p _ hx=>
       obtain ⟨x,rfl⟩:=hx
       refine ⟨(c.re • x.1-c.im • x.2,c.re • x.2+c.im • x.1),?_⟩
       simp only [sky_at,map_sub,map_add,map_smul]
       have hc (v:E): c • v=c.re • v+ I • c.im • v:=by
          have h (s:ℝ): s • v = (s:ℂ) • v:= RCLike.real_smul_eq_coe_smul (K:=ℂ) s v
          rw [h,h,smul_smul,mul_comm I,← add_smul,Complex.re_add_im]
       have ht:c • (I • M x.2) = I • c.re • M x.2-c.im • M x.2:=by
          rw [smul_comm c I,hc (M x.2),smul_add,smul_smul I I,I_mul_I,neg_one_smul,sub_eq_add_neg]
       rw [smul_add c (_:E), hc (M x.1), ht, smul_add I]
       abel

variable [CompleteSpace F] [CompleteSpace E]
lemma splash (hm : Surjective (sky M))(x:F){r δ:ℝ}(hr:0<r)(hd:0<δ):
    ∃ p:ℝ,0<p∧ p < r ∧ Covered (M '' closedBall x δ) (closedBall (M x) r) (closedBall (M x) p):=by
   let D:ℝ:= (Real.exp 1+Real.exp 1)/‖Δ‖; have hD:0 ≤ D:=by unfold D; positivity
   obtain ⟨ε,hε0,hε,hx⟩:∃ ε:ℝ,0<ε∧ (1+D)*ε ≤ δ ∧ ‖M‖*((1+D)*ε) ≤ r:= by
      let C:=(1+‖M‖)*(1+D); have hc:0<C:=by unfold C; positivity
      refine ⟨min δ r / C,div_pos (lt_min hd hr) hc, ?_,?_⟩
      · calc
           _ ≤ C*(min δ r/C):=mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) (by simp)) (by positivity)
           _ = _ := ?_ -- min δ r
           _ ≤ δ := min_le_left δ r
        field_simp
      rw [← mul_assoc ‖M‖]; apply le_trans (mul_le_mul_of_nonneg_right (show ‖M‖ * (1+D) ≤ C from by unfold C; gcongr; linarith) (show 0≤ min δ r/C from by positivity))
      field_simp; exact min_le_right ..
   obtain ⟨u,hu,hU⟩:= Metric.mem_nhds_iff.mp (show sky M '' ball (x,0) ε ∈ 𝓝 (M x) from (by
       apply ((sky M).isOpenMap hm _ isOpen_ball).mem_nhds; exact ⟨(x,0),mem_ball_self hε0,by simp [sky_at]⟩))
   refine ⟨min (r/2) (u/2),lt_min (half_pos hr) (half_pos hu), (min_le_left ..).trans_lt (half_lt_self hr),?_⟩
   intro z hz
   obtain ⟨⟨x',t⟩,ht,rfl⟩:=hU (closedBall_subset_ball ((min_le_right ..).trans_lt (half_lt_self hu)) hz)
   have he : ‖x'-x‖ ≤ ε ∧ ‖t‖ ≤ ε:=by
      rw [← ball_prod_same] at ht
      exact ⟨by simpa [dist_eq_norm] using (mem_ball.mp ht.1).le, by simpa using (mem_ball.mp ht.2).le⟩
   let Q (z:ℂ):= M x' + curve z • M t; refine ⟨Q,by simp only [Q,eClock,sky_at], fun z hz=> ((show Differentiable ℂ Q from (differentiable_const _).add (curved.smul_const (M t))).analyticAt _), ?_, ?_⟩
   · intro z hz; change dist (Q z) _ ≤ _; rw [dist_eq_norm]; unfold Q; rw[add_sub_right_comm,← map_sub]; apply (norm_add_le ..).trans
     rw [norm_smul]; have hx' : ‖M (x'-x)‖ ≤ ‖M‖*ε:= (M.le_opNorm _).trans (by gcongr; exact he.1); have ht' : ‖M t‖ ≤ ‖M‖*ε:= (M.le_opNorm _).trans (by gcongr; exact he.2); apply le_trans (add_le_add hx' (mul_le_mul (curve_bound z hz) ht' (norm_nonneg _) hD)); linarith only [hx]
   intro z hz; let y:=x'+(curve z).re • t
   have ht: ‖(curve z).re‖ ≤ D:= (Complex.abs_re_le_norm _).trans (curve_bound z (show z.re∈Icc (0:ℝ) 1 from (by simp [hz])))
   refine ⟨y,?_,?_⟩
   · rw [mem_closedBall, dist_eq_norm]; unfold y; rw [add_sub_right_comm]; apply (norm_add_le ..).trans; rw [norm_smul]; exact (add_le_add he.1 (mul_le_mul ht he.2 (norm_nonneg _) hD)).trans (by linarith only [hε])
   unfold y Q; rw [map_add,map_smul]; congr 1; exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) _ (M t)).trans (congr_arg (· • M t) (curve_real hz).symm)
-- relay any estimates posted at a real subspace's relatively open ball
omit [CompleteSpace F] [CompleteSpace E] [IsScalarTower ℝ ℂ E] [NormedSpace ℂ E] [NormedSpace ℂ H] in
lemma tract {Ω :Type*}{f:Filter Ω}{F':Ω→ E→ H}{w:Ω→ℝ}{K:Set F} (h:TagPrice f (fun i=> F' i ∘ M) K w): TagPrice f F' (M '' K) w:=by
   obtain ⟨C,hC,ht⟩:=h; exact ⟨C,hC,ht.mono (fun i h=> Set.forall_mem_image.mpr h)⟩
lemma Support.hails {Ω ι : Type*}{t:Filter ι}{f:Filter Ω}{A:ι→Ω→E→H}{V U:Set E}{u:Ω→ℝ}[ProperSpace E]{x:F}{δ:ℝ}(h:Support A t f u U)(hh:U∈ 𝓝 (M x))(hs:Submodule.span ℂ (Set.range M)=⊤) (he:0<δ)(ha:M '' closedBall x δ⊆V) (hp:Ready A t f u V): (Live A t f u U).Nonempty:=by
   obtain ⟨b,hb,h⟩:= Metric.mem_nhds_iff.mp hh -- h shadow
   obtain ⟨d,hd,hK,hx⟩:= splash M (merges M hs) x (half_pos hb) he
   have hq: closedBall (M x) (b/2) ⊆ U := (closedBall_subset_ball (half_lt_self hb)).trans h
   exact ⟨_,d,hd,(closedBall_subset_closedBall hK.le).trans hq,(show Support A t f u U from by assumption).carries (isCompact_closedBall ..) hq hx (hp.mono ha)⟩
end YM.GapsContact.Pattern
