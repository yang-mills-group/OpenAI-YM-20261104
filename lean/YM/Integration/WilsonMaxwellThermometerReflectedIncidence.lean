import YM.Integration.WilsonMaxwellThermometerLowerGramPrice
import YM.Euclid.RPPeak

/-! The two genuine smooth reflected energy readings share one positive,
normalized compact test. Both points keep their separately rounded addresses. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedIncidence
open Filter Set Function MeasureTheory Metric Lattice Wilson Maxwell XSpace XSpace.Cirrus
open Table.Pairing WilsonMaxwellThermometerLowerPointGram WilsonMaxwellThermometerLowerFiledGram
open WilsonMaxwellThermometerLowerGramPrice
open scoped Topology BigOperators Classical
variable {G:Gauge}(a:Axis)(x:E4)

def site (x:E4):Points 1:=points fun _=>x
abbrev Pair:=Points 1×Points 1

private theorem concentrated (hx:0<x a){r:ℝ}(hr:0<r):
    ∃B:Bulb (site x) a,∀y z,y∈tsupport B.bump → z∈tsupport B.bump →
      dist (closedUp a y z) (center a x)<r:=by
  let p:=site x
  have co:ContinuousAt (fun w:Pair=>closedUp a w.1 w.2) (p,p):=
    (pairIso a (n:=1) (m:=1)).symm.continuous.continuousAt
  obtain ⟨u,hu,hpair⟩:=Metric.continuousAt_iff.mp co r hr
  have up:{y:Points 1|0<y 0 a}∈𝓝 p:=
    (show Continuous (fun y:Points 1=>y 0 a) from by fun_prop).continuousAt.preimage_mem_nhds
      (lt_mem_nhds (show 0<p 0 a from hx))
  obtain ⟨v,hv,hin⟩:=Metric.mem_nhds_iff.mp up
  let d:=min u v
  have hd:0<d:=lt_min hu hv
  let B:ContDiffBump p:=⟨d/4,d/2,by linarith,by linarith⟩
  have near (y:Points 1)(hy:y∈tsupport B):dist y p<d:=by
    rw [B.tsupport_eq] at hy
    exact (Metric.mem_closedBall.mp hy).trans_lt (by change d/2<d; linarith)
  refine ⟨⟨B,?_⟩,?_⟩
  · intro y hy
    refine ⟨fun _ _ _=>Subsingleton.elim _ _,?_⟩
    intro i
    have hi:i=(0:Fin 1):=Subsingleton.elim _ _
    rw [hi]
    exact hin (Metric.mem_ball.mpr ((near y hy).trans_le (min_le_right ..)))
  · intro y z hy hz
    have together:dist (y,z) (p,p)<u:=by
      rw [Prod.dist_eq,max_lt_iff]
      exact ⟨(near y hy).trans_le (min_le_left ..),(near z hz).trans_le (min_le_left ..)⟩
    exact @hpair (y,z) together

def mass (B:Bulb (site x) a)(y:Pair):ℝ:=B.r y.1*B.r y.2

theorem one (B:Bulb (site x) a):(∫y:Pair,mass a x B y)=1:=by
  calc
    _=(∫y:Points 1,B.r y)*(∫y:Points 1,B.r y):=integral_prod_mul .. 
    _=1:=by unfold Bulb.r; rw [B.bump.integral_normed,one_mul]

def atPair (W:Initialize G)(V:Normalize.Store G)(M:Mesh)(c:Four ℝ)
    (i:Index G a x)(s:Bool)(y:Pair):ℂ:=
  finiteEntries a x W V ⟨M,draw (closedUp a y.1 y.2) M c,c⟩ i s

private theorem readable (W:Initialize G)(V:Normalize.Store G)(M:Mesh)(c:Four ℝ)
    (i:Index G a x)(s:Bool):Measurable (atPair a x W V M c i s):=by
  apply (measurable_of_countable
    (fun u:pack 2=>finiteEntries a x W V ⟨M,u,c⟩ i s)).comp
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro b
  apply Int.measurable_ceil.comp
  let C:Pair→Points (1+1):=(pairIso a (n:=1) (m:=1)).symm
  change Measurable (fun y:Pair=>((C y+Mesh.room c : Points (1+1)) j) b / M.spacing)
  have h:Continuous C:=(pairIso a (n:=1) (m:=1)).symm.continuous
  fun_prop

def Gram (W:Initialize G)(V:Normalize.Store G)(B:Bulb (site x) a)(M:Mesh)(c:Four ℝ)
    (i:Index G a x)(s:Bool):ℂ:=∫y:Pair,mass a x B y • atPair a x W V M c i s y

private theorem tested (W:Initialize G)(V:Normalize.Store G)(B:Bulb (site x) a)
    (M:Mesh)(c:Four ℝ)(i:Index G a x)(s:Bool){δ:ℝ}
    (paid:∀y:Pair,mass a x B y≠0 → ‖entry a x i s-atPair a x W V M c i s y‖≤δ):
    ‖entry a x i s-Gram a x W V B M c i s‖≤δ:=by
  let w:=mass a x B
  let e:=entry a x i s
  let f:=atPair a x W V M c i s
  have hp (y:Pair):0≤w y:=mul_nonneg (B.bump.nonneg_normed _) (B.bump.nonneg_normed _)
  have hw:Integrable w:=B.bump.integrable_normed.mul_prod B.bump.integrable_normed
  have hf:Measurable f:=readable a x W V M c i s
  have bound (y:Pair):‖w y • (e-f y)‖≤w y*δ:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hp y)]
    by_cases hy:w y=0
    · simp [hy]
    exact mul_le_mul_of_nonneg_left (paid y hy) (hp y)
  have hdiff:Integrable (fun y=>w y • (e-f y)):=by
    refine (hw.mul_const δ).mono' (hw.aestronglyMeasurable.smul
      (aestronglyMeasurable_const.sub hf.aestronglyMeasurable)) (ae_of_all _ bound)
  have hfull:Integrable (fun y=>w y • f y):=by
    have eq:(fun y=>w y • f y)=(fun y=>w y • e)-(fun y=>w y • (e-f y)):=by
      funext y
      change w y • f y=w y • e-w y • (e-f y)
      rw [smul_sub]; abel
    rw [eq]
    exact (hw.smul_const e).sub hdiff
  change ‖e-∫y,w y • f y‖≤δ
  have same:(∫y:Pair,w y • e)=e:=by rw [integral_smul_const,one a x B,one_smul]
  rw [←same,←integral_sub (hw.smul_const e) hfull]
  simp_rw [←smul_sub]
  calc
    _ ≤ ∫y:Pair,‖w y • (e-f y)‖:=norm_integral_le_integral_norm _
    _ ≤ ∫y:Pair,w y*δ:=integral_mono hdiff.norm (hw.mul_const _) bound
    _ = δ:=by rw [integral_mul_const,one,one_mul]

/-- One honest pair of smooth reflected tests pays every cutoff-dependent
lower coordinate on the original common auxiliary board. -/
theorem original (W:Initialize G)(V:Normalize.Store G)(hx:0<x a):
    ∃B:Bulb (site x) a,∃C:ℝ,0<C ∧
    ∀ᶠ M in Front,∀c∈M.Box,∀z:occupied G a x,
      ‖token a x z‖≤C*‖reassemble a x (Gram a x W V B M c) z‖:=by
  obtain ⟨C,δ,r,hC,hδ,hr,book,cap⟩:=WilsonMaxwellThermometerLowerGramPrice.original a x W V hx
  obtain ⟨B,bill⟩:=concentrated a x hx (half_pos hr)
  refine ⟨B,C,hC,?_⟩
  have step: Tendsto (fun M:Mesh=>(8:ℝ)*M.spacing) Front (𝓝 0):=by
    have arrival:=frontier.endpt.const_mul (8:ℝ)
    rw [mul_zero] at arrival
    exact arrival
  filter_upwards [book,step.eventually (gt_mem_nhds (half_pos hr))] with M income fine
  intro c hc
  apply cap
  intro i s
  apply tested a x W V B M c i s
  intro y hy
  have h1: B.r y.1≠0:=left_ne_zero_of_mul hy
  have h2: B.r y.2≠0:=right_ne_zero_of_mul hy
  have inside (z:Points 1)(hz:B.r z≠0):z∈tsupport B.bump:=by
    have hh:z∈ Function.support (B.bump.normed volume):=hz
    rw [B.bump.support_normed_eq] at hh
    rw [B.bump.tsupport_eq]
    exact Metric.ball_subset_closedBall hh
  let v:=closedUp a y.1 y.2
  let u:=draw v M c
  apply income u c hc _ i s
  have htail:=M.upper_corner c (x:=u) (z:=v) rfl
  have front:=bill y.1 y.2 (inside y.1 h1) (inside y.2 h2)
  have ht:dist (M.rel u c) v≤8*M.spacing:=by convert htail using 1; norm_num
  exact (dist_triangle (M.rel u c) v (center a x)).trans_lt (by linarith)

end YM.Integration.WilsonMaxwellThermometerReflectedIncidence
