import YM.AveragedStep.Parcel.Slopes
/-! Exact derivative identity holding the entire exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Lattice RG Precision MeasureTheory Function Filter Tree Loops Wilson Set Metric
open scoped Topology BigOperators Matrix.Norms.Frobenius ENNReal Classical ContDiff
variable {c f:Side}{G:Gauge}{A:ChartRatio G}{S:StepData c f}
variable (F:Forest S.ratio)(C:Cuff S.patch S.kernel A) (b:Site c)
abbrev Hand (G:Gauge)(c f:Side):= Rim c f→ G.Color
def grasp (p:TopologyQ F G):Hand G c f:= C.logC ∘ aboard F b p
def live (j:F.Free)(p:TopologyQ F G):= ∏ i∈home S (.inl j.val), C.ticket (aboard F b p i)
lemma lives (j:F.Free)(p:TopologyQ F G):live F C b j p=outerGate F C b j p*C.ticket (F.drape p.1 j.val):=
  (Finset.prod_erase_mul (home S (Sum.inl j.val)) (fun i=>C.ticket (aboard F b p i)) (home_self _ _)).symm
lemma grasps (U:F.Slice G)(V:Config G c)(j:F.Free)(x:G.El): grasp F C b (ramp F j U x,V)=
    update (grasp F C b (U,V)) (.inl j.val) (C.logC x):=by
 unfold grasp; rw [aboard_ramp]; funext z; by_cases hz:z = .inl j.val <;> simp [hz]

def sdEq (M:Hand G c f → ℝ) (j:F.Free)(v:G.Color)(τ:ℝ)(p:TopologyQ F G) :ℝ :=
    let X:=grasp F C b p
    let I:=(introAt (Sum.inl j.val:Rim c f)) v
    let J:=τ • I
    let u:= aboard F b p (Sum.inl j.val)
    let L:=flame C (Sum.inl j.val:Rim c f) X v
    outerGate F C b j p * C.incline v u * M (τ • X) +
      live F C b j p*(fderiv ℝ M (τ • X) J + M (τ • X)*(Cuff.haarScore (A:=A) (C.logC u) v-τ^2*L))
lemma sd_safe (M:Hand G c f→ℝ)(hM:ContDiff ℝ 1 M)(j:F.Free)(v:G.Color)(τ:ℝ)(hA:LocalRatio A):
    Envelope (sdEq F C b M j v τ):=by
 let i:Rim c f:=Sum.inl j.val
 let u(l:Rim c f)(p:TopologyQ F G):=aboard F b p l
 have hu (l:Rim c f): Measurable (u l):= (measurable_pi_apply l).comp ((aboard_cont F b).measurable)
 let Z:=grasp F C b
 let R(p:TopologyQ F G):=τ • Z p
 have hz:Measurable Z:=measurable_pi_lambda _ fun l=> C.log_meas.comp (hu l)
 have hf:Measurable R:= (measurable_const (a:=τ)).smul hz
 have hQ(s:Finset (Rim c f)): Envelope (fun x:TopologyQ F G=> ∏ l∈s,C.ticket (u l x)):= env_product s _ fun l _=> env_comp C.ticket_paid (hu l)
 let T:=τ • introAt i v
 have hd (g:Hand G c f → ℝ)(h:Continuous g):Envelope (fun x:TopologyQ F G=> g (R x)):=by
   obtain ⟨D,hD⟩:=isCompact_closedBall (0:Hand G c f) (‖τ‖*(2*C.width))|>.exists_bound_of_continuousOn h.continuousOn
   refine ⟨h.measurable.comp hf,D,fun x=>hD _ ?_⟩
   rw [mem_closedBall_zero_iff]; unfold R; rw [norm_smul]; gcongr
   exact (pi_norm_le_iff_of_nonneg (by have :=C.active; positivity)).mpr fun l=> C.log_max _
 let hM':=hd M hM.continuous
 have he:=env_comp (C.incline_env v) (hu i)
 unfold sdEq; dsimp only; exact ((hQ _|>.mul he).mul hM').add
    ((hQ _).mul ((hd (fun X=> fderiv ℝ M X T) ((hM.continuous_fderiv (by simp)).clm_apply continuous_const)).add (by
       apply hM'.mul; simp_rw [sub_eq_add_neg]
       exact (env_comp (log_j_env C hA v) (hu i)).add (((Envelope.const (τ^2)).mul (env_comp (flame_env C i v) hz)).neg))))
lemma sd_held (M:Hand G c f → ℝ)(hM:ContDiff ℝ 1 M)(j:F.Free)(v:G.Color)(τ:ℝ)
    (hA:LocalRatio A)(hS:S.patch.Branches S.kernel G)(U:F.Slice G)(V:Config G c):
    let X(z:G.El): TopologyQ F G:=(ramp F j U z,V)
    (∫ z:G.El,assay F (τ^2) b (X z)*sdEq F C b M j v τ (X z) ∂G.probHaar)=0:=by
 intro X
 let p: TopologyQ F G:=(U,V)
 let O:=outerGate F C b j p
 have ho(z:G.El):outerGate F C b j (X z)=O:=outer_same F C b j U V z
 have hl(z:G.El): live F C b j (X z)=O*C.ticket z:=by
   rw [lives,ho, F.off_tree]; unfold X; exact congr_arg (fun u=>O*C.ticket u) (update_self ..)
 by_cases H: O=0
 · simp_rw [sdEq,ho,hl,H,zero_mul,zero_add,mul_zero,integral_zero]
 let i:Rim c f:=.inl j.val
 let u(z:G.El):=aboard F b (X z)
 let G₀:=grasp F C b p
 let Y:=fun y:G.Color=>update G₀ i y
 have hey(z): u z i=z:=by unfold u X; rw [aboard_ramp]; exact update_self ..
 have hx(z:G.El): grasp F C b (X z)= Y (C.logC z):= grasps ..
 obtain ⟨k,hK⟩:= by_law F C b j hS (τ^2) U V H
 let E(z:G.Color):=close (S:=S) i (Y z)
 let W:=tsupport (C.trigger:G.Color→ℝ)
 have hT{z:G.Color}(he:z∈ W): ‖z‖ ≤ 3*C.width:=by unfold W at he; rw [C.trigger.tsupport_eq,mem_closedBall_zero_iff] at he; exact he.trans (show C.width/2 ≤ 3*C.width from by linarith [C.active])
 have hg{x:G.Color}(he: x∈C.horizon):∀ z∈home S i,‖update G₀ i x z‖≤ 2*C.width:=by
   intro z h; by_cases hz:z=i; · subst z; rw [update_self]; simpa [Cuff.horizon] using he
   rw [update_of_ne hz]; exact C.log_max _
 have hw{x:G.Color}(hx:x∈W):x∈ C.horizon:=by unfold W at hx; rw [C.trigger.tsupport_eq] at hx; exact closedBall_subset_closedBall (show C.trigger.rOut≤2*C.width from by unfold Cuff.trigger; dsimp only; linarith [C.active]) hx
 let D(z:G.El):=assay F (τ^2) b (X z)
 have ht(z:G.Color)(he:z∈C.horizon):=close_deriv C G₀ i z (hg he)
 have hX:Measurable X:= (show Continuous X from by unfold X ramp; fun_prop).measurable
 have hD : Envelope D:=env_comp (assay_env F b hS (τ^2)) hX
 let M'(x:G.Color):=M (τ • Y x)
 have hi:ContDiff ℝ 1 Y:=contDiff_pi.mpr fun l=>by
    unfold Y; by_cases h:l=i; · subst l; simp_rw [update_self]; exact contDiff_id
    simp_rw [update_of_ne h]; exact contDiff_const
 have hM0:ContDiff ℝ 1 M':=hM.comp (hi.const_smul τ)
 have hmz(z): fderiv ℝ M' z v=fderiv ℝ M (τ • Y z) (τ • introAt i v):=by
   have h:= ((hM.differentiable (by simp) (τ • Y z)).hasFDerivAt.comp (f:=fun y=>τ • Y y) z (sends G₀ i z|>.const_smul τ)).fderiv
   rw [show fderiv ℝ M' z=_ from h,ContinuousLinearMap.comp_apply,smul_apply]
 let L(z:G.Color):= Cuff.haarScore (A:=A) z v-τ^2*(fderiv ℝ E z) v
 let J(z:G.El):=D z*(C.incline v z*M' (C.logC z)+C.ticket z*((fderiv ℝ M' (C.logC z)) v+ M' (C.logC z)*L (C.logC z)))
 have hq(z:G.El):assay F (τ^2) b (X z)*sdEq F C b M j v τ (X z)=O*J z:=by
   have he' : C.logC z∈ C.horizon:=by rw [Cuff.horizon,mem_closedBall_zero_iff]; exact C.log_max z
   unfold sdEq; dsimp only; rw [ho,hl]; change D z* (O*C.incline v (u z i)*_+O*C.ticket z*(_+_*(Cuff.haarScore (A:=A) (C.logC (u z i)) v -_)))=_
   unfold J; rw [hmz,hey,hx]
   unfold L
   rw [show fderiv ℝ E (C.logC z) v=_ from (ht _ he').2 v]; unfold M' Y; ring
 have hJ:Measurable J:=by
   have hh:= (env_comp (sd_safe F C b M hM j v τ hA) hX).meas
   have he:J=fun z=>O⁻¹* (assay F (τ^2) b (X z)*sdEq F C b M j v τ (X z)):=by funext z; rw [hq,inv_mul_cancel_left₀ H]
   rw [he]; exact measurable_const.mul (hD.meas.mul hh)
 simp_rw [hq,integral_const_mul,show (∫ z:G.El,J z∂G.probHaar)=0 from C.balance hA (E:=E) (k:=k) v (τ^2) hD.meas (fun z hz=> hK z (hT hz)) (fun z hz=> (ht z (hw hz)).1.of_le le_top) hM0 hJ, mul_zero]
end YM.AveragedStep
