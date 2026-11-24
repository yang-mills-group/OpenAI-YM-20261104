import YM.Integration.WilsonMaxwellThermometerReflectedIncidence

/-! The genuine first coefficient of the public bare prescription on the
two reflected probes, with all independently reannounced faces and the
shared normalizer. The Gram and these probe fees use the same smooth test. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedFirstPrice
open Filter Set Metric Function MeasureTheory Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus XSpace.Rose
open XSpace.Normalize XSpace.Structure1 XSpace.Photo XSpace.Tornado XSpace.Retirement
open WilsonMaxwellThermometerPublicReflection WilsonMaxwellThermometerLowerPointGram
open WilsonMaxwellThermometerLowerGramPrice WilsonMaxwellThermometerReflectedIncidence Table.Pairing
open scoped Topology BigOperators Classical
variable {G:Gauge}(a:Axis)(x:E4)(W:Initialize G)(V:Normalize.Store G)

def targets (b:Sec G 6)(s:Bool):Tags G 6 2:=
  Fin.append (fun _:Fin 1=>up (by decide:4≤6) (ori (Signed.reflect a) 4 (reel 4 (energy G s))))
    (fun _:Fin 1=>b)

def response (b:Sec G 6)(s:Bool)(t:Sample 2):ℂ:=
  slope (face W V (targets a b s) t 0) (face W V (targets a b s) t 1)

def placed (b:Sec G 6)(s:Bool)(M:Mesh)(c:Four ℝ)(y:Pair):ℂ:=
  response a W V b s ⟨M,draw (closedUp a y.1 y.2) M c,c⟩

def filed (B:Bulb (site x) a)(b:Sec G 6)(M:Mesh)(c:Four ℝ)(s:Bool):ℂ:=
  ∫y:Pair,mass a x B y • placed a W V b s M c y

private theorem cash (b:Sec G 6)(s:Bool){K:Set (Points 2)}(hk:IsCompact K)(ha:K⊆conf 2):
    ∃D:ℝ,∀ᶠ M in Front,∀t:Sample 2,grab t=M→welcome t→familiar t∈K →
    ‖response a W V b s t‖≤D:=by
  let p:=targets a b s
  let F:=fun z:Points 2=>slope (fun S=>WilsonMaxwellThermometerPublicReflection.limit W V p 0 S z)
    (fun S=>WilsonMaxwellThermometerPublicReflection.limit W V p 1 S z)
  have law:= (centered W V p).2
  obtain ⟨D,hD⟩:=((hk.image_of_continuousOn (continuous_norm.comp_continuousOn
    (law.priced.mono ha))).bddAbove)
  refine ⟨1+D,?_⟩
  filter_upwards [law.placed hk ha 1 zero_lt_one] with M fee t ht hu hist
  change ‖slope (face W V p t 0) (face W V p t 1)‖≤1+D
  calc
    _=dist (slope (face W V p t 0) (face W V p t 1)) 0:=(dist_zero_right _).symm
    _≤dist (slope (face W V p t 0) (face W V p t 1)) (F (familiar t))+
      dist (F (familiar t)) 0:=dist_triangle .. 
    _≤1+D:=add_le_add (fee t ht hu hist) (by
      rw [dist_zero_right]; exact hD (Set.mem_image_of_mem _ hist))

theorem bounded (B:Bulb (site x) a)(b:Sec G 6):
    ∃D:ℝ,0≤D ∧ ∀ᶠ M in Front,∀c∈M.Box,‖filed a x W V B b M c‖≤D:=by
  let window:=tsupport B.bump
  let geom:Pair→Points 2:=fun y=>closedUp a y.1 y.2
  let K:=geom '' (window ×ˢ window)
  have compact:IsCompact K:=(B.bump.hasCompactSupport.prod B.bump.hasCompactSupport).image
    (pairIso a (n:=1) (m:=1)).symm.continuous
  have apart:K⊆conf 2:=by
    rintro _ ⟨y,hy,rfl⟩
    exact Table.Pairing.spans (B.active y.1 hy.1) (B.active y.2 hy.2)
  obtain ⟨r,hr,admit⟩:=compact.exists_cthickening_subset_open (conf_open _) apart
  have cc:IsCompact (cthickening r K):=compact.cthickening
  choose D fee using fun s:Bool=>cash a W V b s cc admit
  let budget:=max 0 (max (D false) (D true))
  have cashD (s:Bool):D s≤budget:=by
    apply le_trans _ (le_max_right ..); cases s
    · exact le_max_left .. 
    · exact le_max_right ..
  have bd:0≤budget:=le_max_left ..
  refine ⟨budget,bd,?_⟩
  have shrink:=frontier.endpt.const_mul (8:ℝ)
  rw [mul_zero] at shrink
  filter_upwards [(eventually_all.mpr fee),shrink.eventually (gt_mem_nhds hr)] with M cert fine
  intro c hc
  refine (pi_norm_le_iff_of_nonneg bd).mpr fun s=>?_
  let w:=mass a x B
  have wh:Integrable w:=B.bump.integrable_normed.mul_prod B.bump.integrable_normed
  have pos (y:Pair):0≤w y:=mul_nonneg (B.bump.nonneg_normed _) (B.bump.nonneg_normed _)
  have price (y:Pair):‖w y • placed a W V b s M c y‖≤w y*budget:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pos y)]
    by_cases h:w y=0
    · simp [h]
    apply mul_le_mul_of_nonneg_left _ (pos y)
    have live (z:Points 1)(hz:B.r z≠0): z∈window:=by
      have h₁:z∈Function.support (B.bump.normed volume):=hz
      rw [B.bump.support_normed_eq] at h₁
      change z∈tsupport B.bump
      rw [B.bump.tsupport_eq]; exact ball_subset_closedBall h₁
    have hy:geom y∈K:=⟨y,⟨live _ (left_ne_zero_of_mul h),live _ (right_ne_zero_of_mul h)⟩,rfl⟩
    let u:=draw (geom y) M c
    have corner:=M.upper_corner c (x:=u) (z:=geom y) rfl
    have edge:dist (M.rel u c) (geom y)≤8*M.spacing:=by convert corner using 1; norm_num
    have home:=mem_cthickening_of_dist_le (M.rel u c) (geom y) r K hy (edge.trans (by exact le_of_lt fine))
    exact (cert s ⟨M,u,c⟩ rfl hc home).trans (cashD s)
  calc
    _≤∫y:Pair,‖w y • placed a W V b s M c y‖:=norm_integral_le_integral_norm _
    _≤∫y:Pair,w y*budget:=integral_mono_of_nonneg (ae_of_all _ (fun _=>norm_nonneg _))
      (wh.mul_const _) (ae_of_all _ price)
    _=budget:=by rw [integral_mul_const,one a x B,one_mul]

/-- The complete signed response of an authentic other prescription enters
once in each row. The residual is the first-incidence remainder after its
universal action and its same-weight changes have been restored. -/
theorem original (hx:0<x a)(b:Sec G 6):
    ∃B:Bulb (site x) a,∃C D:ℝ,0<C ∧ 0≤D ∧ ∀ᶠ M in Front,∀c∈M.Box,
    ∀z:occupied G a x,∀signed:Bool→ℂ,∀fee:ℝ,
      ‖(signed-filed a x W V B b M c)-reassemble a x (Gram a x W V B M c) z‖≤fee →
      ‖token a x z‖≤C*(‖signed‖+D+fee):=by
  obtain ⟨B,C,hC,price⟩:=WilsonMaxwellThermometerReflectedIncidence.original a x W V hx
  obtain ⟨D,hD,charge⟩:=bounded a x W V B b
  refine ⟨B,C,D,hC,hD,?_⟩
  filter_upwards [price,charge] with M allowed sum
  intro c hc z signed fee delta
  have p:=allowed c hc z
  apply p.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  calc
    _≤‖signed-filed a x W V B b M c‖+‖(signed-filed a x W V B b M c)-
      reassemble a x (Gram a x W V B M c) z‖:=by
      simpa only [sub_sub_cancel] using norm_sub_le (signed-filed a x W V B b M c)
        ((signed-filed a x W V B b M c)-reassemble a x (Gram a x W V B M c) z)
    _≤‖signed‖+D+fee:=add_le_add ((norm_sub_le ..).trans (add_le_add le_rfl (sum c hc))) delta

end YM.Integration.WilsonMaxwellThermometerReflectedFirstPrice
