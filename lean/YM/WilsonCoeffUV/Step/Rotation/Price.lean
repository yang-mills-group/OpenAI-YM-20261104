import YM.WilsonCoeffUV.Step.Rotation.Offset
/-!
# Recentered jacobian and Haar in the formal coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power.Freedom
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Work.F05 Function Filter Gauge PowerSeries
open YM.PertExtension.Chart (expLinks jacobian physical)
open MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)
variable {B T:Forest S.ratio}(e:B.Free≃T.Free)
variable (M M' : Matrix (Woods G f) (Woods G c) ℝ) (Ñ:ChartRatio G)
local notation "θ"=> internal S e M M'
private abbrev hub := Lawn (Active G B⊕ Woods G c)
local notation "𝔾"=>hub (S:=S) (G:=G) (B:=B)
lemma det_index (p:LocalRatio Ñ)(he:M=reveal G S B*((reveal G S B).transpose*M))(ht:M'=reveal G S T*((reveal G S T).transpose*M')) :
      ∀ᶠ v:𝔾 in 𝓝 0, |(edgeM θ v).det| * Real.exp (city S T M' Ñ (pan S e M M' v)) = Real.exp (city S B M Ñ v) := by
  let F := fresh S e (G:=G); let H:= notch S e M M'
  let I := index (G:=G) e
  have hk:= fresh_green S (G:=G) e
  have h₀:= hk.continuousAt.tendsto; rw [fresh_zero] at h₀
  have hp:I 0=0:=map_zero _
  have hy : Tendsto (ride S B M id) (𝓝 0) (𝓝 0) := ride_zero S B M id rfl ▸ (ride_diff S B M id contDiffAt_id).continuousAt
  have hg : Tendsto I (𝓝 0) (𝓝 0) := hp ▸ I.continuous.tendsto 0
  filter_upwards [hy.eventually (fresh_area S e Ñ p),hy.eventually (h₀.eventually (hg.eventually (log_event S T p))),hy.eventually ((continuous_fst.tendsto _).eventually (log_event S B p)), (internal_green S e M M').eventually (by simp), hy.eventually ((notch_green S e M M').eventually (by simp))] with v hv hb hc hd hh
  let u := ride S B M id v
  have hj : (fderiv ℝ (fun y=> H (y,rightArm v)) u.1)=(fderiv ℝ (fun y=>F (y,rightArm v)) u.1) := by simp_rw [H,notch_lit,fderiv_add_const]; rfl
  rw [internal, surface_det S B M id id v _ (hh.differentiableAt (by simp)) (hd.differentiableAt (by simp)), hj, city,city,pan_H S e M M' v ht,outset S M he v]
  have hN: Fintype.card T.Free= Fintype.card B.Free:=(Fintype.card_congr e).symm
  rw [hN] at hb
  apply mul_left_cancel₀ (a:=Ñ.scale^Fintype.card B.Free) (pow_ne_zero _ p.scale.ne')
  rw [mul_left_comm]; change _ * (Ñ.scale^Fintype.card B.Free * Real.exp _) = _
  rw [hb,hc,j_shift]; exact hv
lemma det_anchor (p:LocalRatio Ñ)(he:M=reveal G S B*((reveal G S B).transpose*M))(ht:M'=reveal G S T*((reveal G S T).transpose*M')) :
   |(edgeM θ 0).det|=1 := by
  have hh := mem_of_mem_nhds (det_index S e M M' Ñ p he ht)
  change |(edgeM θ 0).det| * Real.exp _ = Real.exp _ at hh
  rw [expose_zero] at hh; simp only [city, Matrix.mulVec_zero,unhaar_zero p,Real.exp_zero,mul_one] at hh; exact hh

lemma det_anchored {U V: Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
   {d:Lawn (U⊕V)→Lawn U}(H:Green d)(e:d 0=0){p q:Lawn (U⊕V)→ℝ}(hp:Green p)(hq:Green q)(p0:p 0=0)(q0:q 0=0)
   (ht: ∀ᶠ v in 𝓝 0,|(edgeM d v).det| * Real.exp (q v) = Real.exp (p v)) :
   (motionJ (spool d)).det*raiseE (jet q)=realS ((edgeM d 0).det) * raiseE (jet p) := by
  let m v:=(edgeM d v).det
  have hm: |m 0|=1 := by
    have hh := mem_of_mem_nhds ht; change |m 0| * Real.exp (q 0)= Real.exp (p 0) at hh
    simpa only [p0,q0,Real.exp_zero,mul_one] using hh
  have hg: Green m := by unfold m; simp_rw [Matrix.det_apply']; apply ContDiffAt.sum; intro i _; exact ContDiffAt.mul contDiffAt_const (contDiffAt_prod (fun _ _=> edge_green d H _ _))
  have hy: ∀ᶠ v in 𝓝 0, (m v)*Real.exp (q v)=m 0*Real.exp (p v):=by
    rcases abs_eq_abs.mp (by rwa [abs_one]: |m 0|=|(1:ℝ)|) with ok|ok
    · filter_upwards [ht,hg.continuousAt.eventually (lt_mem_nhds (show 0<m 0 by norm_num [ok]))] with v hv hy; change |m v| * _=_ at hv; rwa [ok,one_mul, ← abs_of_pos hy]
    filter_upwards [ht,hg.continuousAt.eventually (gt_mem_nhds (show m 0<0 by norm_num [ok]))] with v hv hy; change |m v| * _=_ at hv; rw [ok, ←hv,abs_of_neg hy]; ring
  rw [← solar_motion d H e,← literal_exp hp p0,← literal_exp hq q0, ←jet_const (r:=m 0), ← jet_mul (f:=m) (g:=fun v=>Real.exp (q v)) hg hq.exp, ←jet_mul (f:=fun _=>m 0) (g:=fun v=> Real.exp (p v)) contDiffAt_const hp.exp]; exact jet_congr hy
lemma stayId {U:Type}[Fintype U] : spool (id:Lawn U→ Lawn U)=path := by
  classical
  rw [show (id:Lawn U→ Lawn U)=fun v=>(1:Matrix U U ℝ) *ᵥ v from funext fun x=> (Matrix.one_mulVec _).symm]
  funext i; rw [spool_board,loom_pin,Finset.sum_eq_single i]
  · simp
  · intro b _ h; rw [Matrix.one_apply_ne h.symm,zero_smul]
  simp
lemma windV (p:Ink (Active G T⊕ Woods G c)) :
    reroll (path (U:=Woods G c)) (spool θ) (loom (beam S e) p)=train (spool (pan S e M M')) p := by
  have he : reroll (path (U:=Woods G c)) (spool θ)=train (spool (spoke S e M M')) := by
    rw [← stayId]; exact roll_shawl θ id (internal_zero ..) contDiffAt_id rfl
  rw [he]; exact rolled_loom _ (spoke_zero ..) (spoke_green ..) (beam S e) p
lemma det_tariff (p:LocalRatio Ñ)(he:M=reveal G S B*((reveal G S B).transpose*M))(ht:M'=reveal G S T*((reveal G S T).transpose*M')) :
    (motionJ (spool θ)).det* raiseE (reroll (path (U:=Woods G c)) (spool θ) (loom (beam S e) (loom (camSlice G S T M') (jet (unhaar Ñ)))))=
    realS ((edgeM θ 0).det) * raiseE (loom (camSlice G S B M) (jet (unhaar Ñ))) := by
  have hg (T:Forest S.ratio) (N) : Green (city S T N Ñ) := by
    have hx: camSlice G S T N *ᵥ 0=0:=Matrix.mulVec_zero _
    exact (show ContDiffAt ℝ ω (unhaar (n:=f) Ñ) _ from hx.symm ▸ (show ContDiffAt ℝ ω _ _ from unhaar_green p)).comp (f:=fun v=>camSlice G S T N *ᵥ v) 0 (board _)
  rw [windV,show loom _ _=jet (city S T M' Ñ) from loom_jet _ _ (unhaar_green p)]
  rw [traveling _ (expose_green ..) (expose_zero ..) _ (hg ..),show loom _ _= jet (city S B M Ñ) from loom_jet _ _ (unhaar_green p)]
  exact det_anchored (internal_green ..) (internal_zero ..) (hg ..) ((show ContDiffAt ℝ ω (city S T M' Ñ) (pan S e M M' 0) from (expose_zero S e M M').symm ▸ hg ..).comp _ (expose_green ..)) (by rw [city,Matrix.mulVec_zero,unhaar_zero p]) (by rw [Function.comp_apply,expose_zero,city,Matrix.mulVec_zero,unhaar_zero p]) (det_index S e M M' Ñ p he ht)
end YM.WilsonCoeffUV.Power.Freedom
