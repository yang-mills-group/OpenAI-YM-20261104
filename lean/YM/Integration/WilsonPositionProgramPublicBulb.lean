import YM.Integration.WilsonPositionProgramPublicReflectedRead

/-! A single positive, smooth compact pair of reflected tests buys the
complete finite Gram, on one actual public inversion board at a time. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicBulb
open Filter Set Function MeasureTheory Metric Lattice Maxwell MS MS.Menus Local.Physical
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Rose Table.Pairing
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicReflectedRead
open scoped Topology BigOperators Classical
variable {G:Gauge}{d:ℕ}{I:Type} [Fintype I] {B:Deck G} (a:Axis)
abbrev Pair := Points 1 × Points 1

theorem concentrated {r:ℝ}(hr:0<r):
    ∃B:Bulb (center a) a,∀y z,y∈tsupport B.bump → z∈tsupport B.bump →
      dist (closedUp a y z) (lower a)<r:=by
  let p:=center a
  have co:ContinuousAt (fun w:Pair=>closedUp a w.1 w.2) (p,p):=
    (pairIso a (n:=1) (m:=1)).symm.continuous.continuousAt
  obtain ⟨u,hu,hpair⟩:=Metric.continuousAt_iff.mp co r hr
  have up:{y:Points 1|0<y 0 a}∈𝓝 p:=
    (show Continuous (fun y:Points 1=>y 0 a) from by fun_prop).continuousAt.preimage_mem_nhds
      (lt_mem_nhds (show 0<p 0 a from positive a))
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

def weight (B:Bulb (center a) a)(y:Pair):ℝ:=B.r y.1*B.r y.2

theorem one (B:Bulb (center a) a):(∫y:Pair,weight a B y)=1:=by
  calc
    _=(∫y:Points 1,B.r y)*(∫y:Points 1,B.r y):=integral_prod_mul .. 
    _=1:=by unfold Bulb.r; rw [B.bump.integral_normed,one_mul]

def node (M:Mesh)(c:Four ℝ)(y:Pair) : Sample 2 :=
  ⟨M,draw (closedUp a y.1 y.2) M c,c⟩

variable (W:Initialize G) (V:Normalize.Store G) (leg:I→Glyph B d)
def Gram (b:Bulb (center a) a)(M:Mesh)(c:Four ℝ)(i j:I) : ℂ :=
  ∫ y:Pair, weight a b y • matrix W V a leg (node a M c y) i j

omit [Fintype I] in
theorem readable (M:Mesh)(c:Four ℝ)(i j:I):
    Measurable (fun y:Pair=>matrix W V a leg (node a M c y) i j) := by
  apply (measurable_of_countable (fun u:pack 2=>matrix W V a leg ⟨M,u,c⟩ i j)).comp
  apply measurable_pi_lambda
  intro t
  apply measurable_pi_lambda
  intro e
  apply Int.measurable_ceil.comp
  let C:Pair→Points (1+1):=(pairIso a (n:=1) (m:=1)).symm
  change Measurable (fun y:Pair=>((C y+Mesh.room c : Points (1+1)) t) e / M.spacing)
  have h:Continuous C:=(pairIso a (n:=1) (m:=1)).symm.continuous
  fun_prop

private theorem tested (b:Bulb (center a) a) (f:Pair→ℂ) (e:ℂ) (hf:Measurable f) {δ:ℝ}
    (paid:∀y:Pair,weight a b y≠0 → ‖e-f y‖≤δ):
    ‖e-(∫ y:Pair,weight a b y • f y)‖≤δ:=by
  let w:=weight a b
  have hp (y:Pair):0≤w y:=mul_nonneg (b.bump.nonneg_normed _) (b.bump.nonneg_normed _)
  have hw:Integrable w:=b.bump.integrable_normed.mul_prod b.bump.integrable_normed
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
  have same:(∫y:Pair,w y • e)=e:=by rw [integral_smul_const,one a b,one_smul]
  rw [←same,←integral_sub (hw.smul_const e) hfull]
  simp_rw [←smul_sub]
  calc
    _ ≤ ∫y:Pair,‖w y • (e-f y)‖:=norm_integral_le_integral_norm _
    _ ≤ ∫y:Pair,w y*δ:=integral_mono hdiff.norm (hw.mul_const _) bound
    _ = δ:=by rw [integral_mul_const,one,one_mul]


theorem filed {δ:ℝ} (hδ:0<δ) : ∃ b:Bulb (center a) a, ∀ᶠ M in Front, ∀c∈M.Box,
    ‖Gram a W V leg b M c-reading a (nodes a) leg‖ ≤ δ := by
  obtain ⟨r,hr,book⟩ := gate_senses (lower a) (Metric.tendsto_nhds.mp (earned W V a leg) δ hδ)
  obtain ⟨b,bill⟩:=concentrated a (half_pos hr)
  refine ⟨b,?_⟩
  have step:Tendsto (fun M:Mesh=>(8:ℝ)*M.spacing) Front (𝓝 0):=by
    have arrival:=frontier.endpt.const_mul (8:ℝ)
    rw [mul_zero] at arrival
    exact arrival
  filter_upwards [book,step.eventually (gt_mem_nhds (half_pos hr))] with M income fine c hc
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  intro j
  change ‖Gram a W V leg b M c i j-reading a (nodes a) leg i j‖ ≤ δ
  rw [norm_sub_rev]
  apply tested a b _ _ (readable a W V leg M c i j)
  intro y hy
  have inside (z:Points 1)(hz:b.r z≠0):z∈tsupport b.bump:=by
    have hh:z∈Function.support (b.bump.normed volume):=hz
    rw [b.bump.support_normed_eq] at hh
    rw [b.bump.tsupport_eq]
    exact Metric.ball_subset_closedBall hh
  let v:=closedUp a y.1 y.2
  let u:=draw v M c
  have htail:=M.upper_corner c (x:=u) (z:=v) rfl
  have ht:dist (M.rel u c) v≤8*M.spacing:=by convert htail using 1; norm_num
  have front:=bill y.1 y.2 (inside y.1 (left_ne_zero_of_mul hy)) (inside y.2 (right_ne_zero_of_mul hy))
  have close:=income u c hc ((dist_triangle (M.rel u c) v (lower a)).trans_lt (by linarith))
  rw [dist_eq_norm] at close
  rw [norm_sub_rev]
  exact ((norm_le_pi_norm ((matrix W V a leg ⟨M,u,c⟩-reading a (nodes a) leg) i) j).trans
    (norm_le_pi_norm _ i)).trans close.le

theorem original (each:Injective leg) :
    ∃ (b:Bulb (center a) a) (k δ:ℝ), 0<k ∧ 0<δ ∧ ∀ᶠ M in Front, ∀c∈M.Box,
      ∀ p:I→I→ℂ, ‖p-Gram a W V leg b M c‖≤δ →
        ∀ v:I→ℂ, k*‖v‖^2≤‖WilsonPositionProgramPublicContrast.assay v v p‖ := by
  obtain ⟨k,t,hk,ht,cap⟩:=WilsonPositionProgramPublicWickGram.original a leg each
  obtain ⟨b,price⟩:=filed a W V leg (half_pos ht)
  refine ⟨b,k,t/2,hk,half_pos ht,?_⟩
  filter_upwards [price] with M good c hc p hp
  apply cap
  exact (norm_sub_le_norm_sub_add_norm_sub p (Gram a W V leg b M c) _).trans
    ((add_le_add hp (good c hc)).trans (by linarith))
end YM.Integration.WilsonPositionProgramPublicBulb
