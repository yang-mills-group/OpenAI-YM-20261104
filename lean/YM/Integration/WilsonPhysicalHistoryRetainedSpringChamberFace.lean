import YM.Integration.WilsonPhysicalHistoryRetainedSpringFaceAverage

/-! The direct plaquette trace and its polynomial are evaluated on exactly
the same previously enrolled compact chamber, forest, rotation, and sample. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function MeasureTheory Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonMeasuredPathTaylor IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {P : Teller G} {η r cap Y : ℝ} {X : Coat T F}
variable {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W} {R : Rep G f}

theorem face_measured (A : Rotator P L η r cap Y X) (x : Site f) (q l : ℕ) (g : ℝ) :
    let e:=fun z : Air f G=>facePriceAt x (represent (g • angularSample F z))-
      faceTaylorAt x (angularSample F z) q g
    let M:=speedPrice G L η r cap ((q+1)*(l+1)-1)
    AEStronglyMeasurable e X.dice ∧ Integrable (fun z=>|e z|^(l+1)) X.dice ∧ (∫ z,|e z|^(l+1) ∂X.dice)≤
      ((Fintype.card PlaqAxes:ℝ)*(faceCost G (q+1) M*|g|^(q+1)))^(l+1) := by
  intro e M
  let v (i : Signed) (z : Air f G):=collect G (pulled (angularSample F z) i)
  let d (i : Signed×PlaqAxes) (z : Air f G):=
    G.price (faceValue (field (v i.1 z) g) (x,i.2))-faceRay (v i.1 z) x i.2 q g
  have same : e=fun z=>(Fintype.card Signed:ℝ)⁻¹*∑ i,d i z:=funext fun z=>face_at x (angularSample F z) q g
  have read (i : Signed×PlaqAxes) : AEStronglyMeasurable (d i) X.dice:=by
    have raw : Continuous (fun z : Air f G=>field (v i.1 z) g):=continuous_pi fun b=>
      G.lieExp_cont.comp (((continuous_apply b).comp (rotated_continuous F i.1)).const_smul g)
    exact ((G.continuous_price.comp ((continuous_travel (square i.2.val.1 i.2.val.2) x).comp raw)).sub
      ((face_ray_continuous x i.2 q g).comp (rotated_continuous F i.1))).aestronglyMeasurable
  have M0 : 0≤M:=(speed_price_pos ..).le
  have paid:=signed_average X.dice d l (mul_nonneg (face_cost_nonneg G _ M0) (pow_nonneg (abs_nonneg _) _)) read
    (fun i=>measured_face A i.1 x i.2 q l g)
  rw [same]
  exact ⟨(Finset.aestronglyMeasurable_fun_sum _ fun i _=>read i).const_mul _,paid⟩

private theorem scale_real {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (f : Ω→ℝ) (w : ℝ) (l : ℕ)
    {M : ℝ} (read : AEStronglyMeasurable f ν) (mean : Integrable (fun z=>|f z|) ν)
    (paid : Integrable (fun z=>|f z|^(l+1)) ν ∧ (∫ z,|f z|^(l+1) ∂ν)≤M^(l+1)) :
    let d:=fun z=>(w:ℂ)*(f z:ℂ)
    Integrable d ν ∧ Integrable (fun z=>‖d z‖^(l+1)) ν ∧ (∫ z,‖d z‖^(l+1) ∂ν)≤(|w| *M)^(l+1) := by
  intro d
  have full : Integrable (fun z=>(f z:ℂ)) ν:=mean.mono'
    (Complex.continuous_ofReal.comp_aestronglyMeasurable read)
    (ae_of_all _ fun z=>by rw [Complex.norm_real,Real.norm_eq_abs])
  have norm (z : Ω) : ‖d z‖^(l+1)=|w|^(l+1)*|f z|^(l+1):=by
    simp only [d,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow]
  refine ⟨full.const_mul _,by simp_rw [norm]; exact paid.1.const_mul _,?_⟩
  simp_rw [norm]
  rw [integral_const_mul,mul_pow]
  exact mul_le_mul_of_nonneg_left paid.2 (pow_nonneg (abs_nonneg _) _)

theorem chamber_face (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (fan : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (x : Site f) (q l : ℕ) (g w : ℝ) (hg : 0<g) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 fan i tag
    let F:=Greenbelt.allot i
    let d:=fun z : Air f G=>(w:ℂ)*((facePriceAt x ((X.wrapY y).input
      ((X.wrapY y).liftA (Integral.temperature g) z))-faceTaylorAt x (angularSample F z) q g:ℝ):ℂ)
    let M:=speedPrice G L o.eta o.gap o.ample ((q+1)*(l+1)-1)
    Integrable d X.dice ∧ Integrable (fun z=>‖d z‖^(l+1)) X.dice ∧ (∫ z,‖d z‖^(l+1) ∂X.dice)≤
      (|w| *((Fintype.card PlaqAxes:ℝ)*(faceCost G (q+1) M*|g|^(q+1))))^(l+1) := by
  intro X F d M
  have manifest : X.manifest:=by
    change (roster (LocalLTE.Fan.arm (S:=S) fan)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  obtain ⟨turn,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  let e:=fun z : Air f G=>facePriceAt x (represent (g • angularSample F z))-faceTaylorAt x (angularSample F z) q g
  have bg : 0<Integral.temperature g:=by unfold Integral.temperature; positivity
  have actual (z : Air f G) : (X.wrapY y).input ((X.wrapY y).liftA (Integral.temperature g) z)=
      represent (g • angularSample F z):=by
    simpa only [inverse_temperature_step hg,mul_inv_cancel₀ hg.ne',one_smul] using
      chamber_path H.laws.data.funds.funds s o.K χ i fan tag bg y z g
  have rewrite : d=fun z=>(w:ℂ)*(e z:ℂ):=by funext z; dsimp only [d,e]; rw [actual]
  rw [rewrite]
  have h:=face_measured turn x q l g
  exact scale_real X.dice e w l h.1 (by simpa only [Nat.zero_add,pow_one] using (face_measured turn x q 0 g).2.1) h.2

end YM.Integration.OriginalMarkedRunAction
