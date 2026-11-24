import YM.Integration.WilsonEpochUniformPositions
import YM.Integration.WilsonEpochUniformReports

/-! The independent continuum MS distribution evaluated on the true finite
centered mesh, with its own regulator rate. Both archived estimates concern
the identical posted field, which cancels before the mesh limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorMSQuadrature
open Function Filter Set Finset Metric MeasureTheory Lattice XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Arrival FVA2.Register MS MS.Land
open scoped Topology BigOperators Classical
variable {n:ℕ}

def corners (m:Mesh) (f:Test n) (F:Points n→ℂ) (c:Four ℝ) : ℂ :=
  (m.spacing:ℂ)^(4*n)*∑x:m.Tuple,
    f (m.rel (m.back x) c)*F (m.rel (m.back x) c)

def quadrature (m:Mesh) (f:Test n) (F:Points n→ℂ) : ℂ :=
  (m.vol:ℂ)⁻¹*∫ c in m.Box,corners m f F c

private theorem sampled (m:Mesh) (f:Test n) (F:Points n→ℂ) (hf:ContinuousOn F (conf n)) :
    IntegrableOn (corners m f F) m.Box := by
  have all : Continuous (fun x:Points n=> f x*F x):=by
    apply continuous_iff_continuousAt.mpr;intro x
    by_cases h:x∈tsupport f
    · exact f.continuous.continuousAt.mul ((hf x (f.tsupport_subset h)).continuousAt
        ((conf_open n).mem_nhds (f.tsupport_subset h)))
    · have he: (fun z:Points n=>f z*F z) =ᶠ[𝓝 x] 0 := Filter.Eventually.mono
        ((isClosed_tsupport _).isOpen_compl.mem_nhds (show x∈(tsupport f)ᶜ from h))
        (fun z hz=>mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hz) (F z))
      exact ContinuousAt.congr (g:=fun z:Points n=>f z*F z) continuousAt_const he.symm
  apply ContinuousOn.integrableOn_compact m.compact_box
  apply Continuous.continuousOn;unfold corners;apply continuous_const.mul
  apply continuous_finsetSum;intro x _
  apply all.comp
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _=>
    continuous_const.sub (PiLp.continuous_toLp 2 _))

private theorem centered {m:Mesh} (small:m.spacing≤1) {K:Set (Points n)} {V:ℝ}
    (region:∀x∈K,‖x‖≤V) (Y:Sample n→ℂ) (shape:Centered Y) (F:Points n→ℂ)
    (f:Test n) (sub:tsupport f⊆K) {b E:ℝ} (hf:TestBudget.Bound f b) (hE:0≤E)
    (budget:∀v:Sample n,v.F=m→welcome v→familiar v∈K→‖Y v-F (familiar v)‖≤E)
    (c:Four ℝ) (hc:c∈m.Box) :
    ‖paths m f Y c-corners m f F c‖≤b*E*volume.real (closedBall (0:Points n) (V+4*n)) := by
  let U:=closedBall (0:Points n) (V+4*n)
  let v(x:m.Tuple (n:=n)):=m.rel (m.back x) c
  let diff(x:m.Tuple (n:=n)):=f (v x)*(Y ⟨m,m.back x,c⟩-F (v x))
  have form: paths m f Y c-corners m f F c = ∫z,m.levels c diff z := by
    rw [stroll,corners,m.stair_exact]
    simp only [←mul_sub,←sum_sub_distrib];congr 1
    apply sum_congr rfl;intro i _;dsimp only [diff,v];rw [shape m (m.back i) c,mul_sub]
  have hb:=TestBudget.bound_nonneg f hf
  have control(z:Points n):‖m.levels c diff z‖≤b*E ∧ (z∉U→m.levels c diff z=0):=by
    by_cases h:∃i:m.Tuple (n:=n),z∈m.cell c (m.back i)
    · obtain ⟨i,hi⟩:=h;rw [m.stair_at c z hi]
      by_cases hk:v i∈K
      · have inv:=budget ⟨m,m.back i,c⟩ rfl hc hk
        refine ⟨?_,fun h=>False.elim (h ?_)⟩
        · dsimp only [diff];rw [norm_mul];exact mul_le_mul (hf (v i)).1 inv (norm_nonneg _) hb
        · apply mem_closedBall_zero_iff.mpr
          exact m.norm_near small (region _ hk) (by rw [dist_comm z (v i)]; exact m.upper_corner c hi)
      · have zero:f (v i)=0:=image_eq_zero_of_notMem_tsupport (fun h=>hk (sub h))
        simp only [diff,zero,zero_mul,norm_zero];exact ⟨mul_nonneg hb hE,fun _=>trivial⟩
    · rw [m.stair_off c z (fun i hi=>h ⟨i,hi⟩)];simp only [norm_zero]
      exact ⟨mul_nonneg hb hE,fun _=>trivial⟩
  rw [form,←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=U) (fun z=> (control z).2)]
  exact norm_setIntegral_le_of_norm_le_const (isCompact_closedBall ..).measure_lt_top
    (fun z _=>(control z).1)

private theorem compared {m:Mesh} (small:m.spacing≤1) {K:Set (Points n)} {V:ℝ}
    (region:∀x∈K,‖x‖≤V) (Y:Sample n→ℂ) (shape:Centered Y) (F:Points n→ℂ)
    (smooth:ContinuousOn F (conf n)) (f:Test n) (sub:tsupport f⊆K)
    {b E:ℝ} (hf:TestBudget.Bound f b) (hE:0≤E)
    (budget:∀v:Sample n,v.F=m→welcome v→familiar v∈K→‖Y v-F (familiar v)‖≤E) :
    ‖Deposit m Y f-quadrature m f F‖≤b*E*volume.real (closedBall (0:Points n) (V+4*n)) := by
  rw [homeward,quadrature,←mul_sub,←integral_sub (on_board m f Y) (sampled m f F smooth),
    norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg m.vol_pos.le]
  apply (mul_le_mul_of_nonneg_left
    (norm_setIntegral_le_of_norm_le_const m.compact_box.measure_lt_top
      (centered small region Y shape F f sub hf hE budget)) (inv_nonneg.mpr m.vol_pos.le)).trans_eq
  rw [show volume.real m.Box=m.vol from rfl,mul_left_comm m.vol⁻¹,inv_mul_cancel₀ m.vol_pos.ne',mul_one]

/-- All original real subtraction scales, every later compact test with its
first derivative price, and the actual centered mesh with its original box.
The difference in this theorem contains no historical marked prescription. -/
theorem independent {G:Gauge} {hG:G.Simple} (N:WilsonPrescription G)
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S:Prescription (Press.portDeck G)} {dial:Bool} (issued:Main.Match N hG M S dial)
    {d:ℕ} (p:Tags G d n) (k:ℕ) (K:Set (Points n)) (hc:IsCompact K) (sep:K⊆conf n) :
    ∃C:ℝ,0<C ∧ ∃e:ℕ,∀ᶠ m in Front,∀f:Test n,tsupport f⊆K→
      ∀b:ℝ,TestBudget.Bound f b→∀ν:ℝ,
        ‖quadrature m f (fun x=>Dframe.meteor ν M d x k p)-Reg.CoverTest.Rates ν M d k n f p‖
          ≤b*(C*(1+|ν|)^e*m.spacing^MS.Tide.mildG) := by
  obtain ⟨A,hA,i,point⟩:=WilsonEpochUniformPositions.measured N issued p k K hc sep
  obtain ⟨B,hB,j,test⟩:=WilsonEpochUniformReports.measured N issued p k K hc sep
  obtain ⟨V,hV⟩:=(hc.image continuous_norm).bddAbove
  let v:=volume.real (closedBall (0:Points n) (V+4*n))
  have hv:0≤v:=ENNReal.toReal_nonneg
  refine ⟨A*v+B,add_pos_of_nonneg_of_pos (mul_nonneg hA.le hv) hB,max i j,?_⟩
  filter_upwards [point,test,frontier.smaller] with m hp ht small f supp b hf ν
  let Y:=fun a:Sample n=>Dframe.postedPoint ν N.scheme S d a k p
  let F:=fun x:Points n=>Dframe.meteor ν M d x k p
  have h:=compared small (fun x hx=>hV (mem_image_of_mem _ hx)) Y (Reg.CoverTest.regular ν N.scheme S p k)
    F (Reg.CoverTest.measurable (n:=n) (d:=d) ν M k p) f supp hf
    (mul_nonneg (mul_nonneg hA.le (pow_nonneg (by positivity) _)) (Real.rpow_nonneg m.positive.le _))
    (fun a ha hb h=>hp a ha hb h ν)
  have t:=ht f supp b hf ν
  rw [Reg.CoverTest.price_m m ν N.scheme S f k p] at t
  have a:1≤1+|ν|:=le_add_of_nonneg_right (abs_nonneg _)
  have e₁: (1+|ν|)^i≤(1+|ν|)^(max i j):=pow_le_pow_right₀ a (le_max_left ..)
  have e₂: (1+|ν|)^j≤(1+|ν|)^(max i j):=pow_le_pow_right₀ a (le_max_right ..)
  have hb:=TestBudget.bound_nonneg f hf
  have hm:=Real.rpow_nonneg m.positive.le MS.Tide.mildG
  calc
    _≤‖quadrature m f F-Deposit m Y f‖+‖Deposit m Y f-Reg.CoverTest.Rates ν M d k n f p‖:=
      by simpa only [dist_eq_norm] using dist_triangle (quadrature m f F) (Deposit m Y f) (Reg.CoverTest.Rates ν M d k n f p)
    _≤b*(A*(1+|ν|)^i*m.spacing^MS.Tide.mildG)*v+b*(B*(1+|ν|)^j*m.spacing^MS.Tide.mildG):=
      add_le_add (by rw [norm_sub_rev (quadrature m f F) (Deposit m Y f)]; exact h) t
    _≤b*(A*(1+|ν|)^(max i j)*m.spacing^MS.Tide.mildG)*v+b*(B*(1+|ν|)^(max i j)*m.spacing^MS.Tide.mildG):=by gcongr
    _=_:=by ring

end YM.Integration.WilsonPhysicalExteriorMSQuadrature
end
