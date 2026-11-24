import YM.Integration.WilsonPhysicalHistoryRetainedSpringSiteMoment
import YM.Integration.WilsonPhysicalHistoryRetainedSpringGrade

/-! All positive integral moments of the actual occupied prior on its one
measured chamber, with the original kinetic and engineering weights. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert
open scoped Topology BigOperators Classical
open Work.F03 Bid Coat Matter
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f}
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}

theorem registered_moment {F : Forest S.ratio} {X : Coat T F} {η r cap expense : ℝ}
    (A : Rotator P L η r cap expense X) {k : ℕ} (V : ℕ→Atom G k) {σ D : ℝ}
    (hs : 0<σ) (enrolled : SumBudget (fun j=>(V j).budget σ) D) (x : Site f) (q l : ℕ)
    (g w : ℝ) (raw : Air f G→ Config G f) (same : raw=fun z=>represent (g • angularSample F z)) :
    let d:=fun z=>(sitePacket V x (raw z):ℂ)-siteTaylor V x (angularSample F z) q g
    Integrable (fun z=>‖(w:ℂ)*d z‖^(l+1)) X.dice ∧
      (∫ z,‖(w:ℂ)*d z‖^(l+1) ∂X.dice)≤(|w| *(D*
        (2*speedPrice G L η r cap ((q+1)*(l+1)-1)*|g|/σ)^(q+1)))^(l+1) := by
  subst raw
  intro d
  have measured:=site_moment A V hs enrolled x q l g
  have scaled z : ‖(w:ℂ)*d z‖^(l+1)=|w| ^(l+1)*‖d z‖^(l+1):=by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow]
  simp only [scaled,integral_const_mul]
  rw [mul_pow |w|]
  exact ⟨measured.1.const_mul _,mul_le_mul_of_nonneg_left measured.2 (pow_nonneg (abs_nonneg _) _)⟩

theorem chamber_error_moment (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) {σ D : ℝ} (hs : 0<σ) (filed : Draw Z σ D)
    (a : PrismA G) (member : a∈Z) (x : Site f) (q l : ℕ) (g p : ℝ) (hg : 0<g) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let F:=Greenbelt.allot i
    let β:=Integral.temperature g
    let w:=β*p*(g/Real.sqrt p)^(a.grade-a.rise)
    let d:=fun z : Air f G=>(sitePacket a.cells x ((X.wrapY y).input ((X.wrapY y).liftA β z)):ℂ)-
      siteTaylor a.cells x (angularSample F z) q g
    Integrable (fun z=>‖(w:ℂ)*d z‖^(l+1)) X.dice ∧ (∫ z,‖(w:ℂ)*d z‖^(l+1) ∂X.dice)≤
      (|w| *(D*(2*speedPrice G L o.eta o.gap o.ample ((q+1)*(l+1)-1)*|g|/σ)^(q+1)))^(l+1) := by
  let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
  let F:=Greenbelt.allot i
  let β:=Integral.temperature g
  let w:=β*p*(g/Real.sqrt p)^(a.grade-a.rise)
  have manifest : X.manifest:=by
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  have βpos : 0<β:=by dsimp only [β,Integral.temperature]; positivity
  have sample (z : Air f G) : (X.wrapY y).input ((X.wrapY y).liftA β z)=
      represent (g • angularSample F z) := by
    simpa only [β,inverse_temperature_step hg,mul_inv_cancel₀ hg.ne',one_smul] using
      chamber_path H.laws.data.funds.funds s o.K χ i v tag βpos y z g
  intro _ _ _ _ _
  exact registered_moment A a.cells hs (filed.2 a member).toll x q l g w
    (fun z=>(X.wrapY y).input ((X.wrapY y).liftA β z)) (funext sample)

theorem chamber_power_moment (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) {σ D : ℝ} (hs : 0<σ) (filed : Draw Z σ D)
    (a : PrismA G) (member : a∈Z) (x : Site f) (r l : ℕ) (g p : ℝ) (hg : 0<g) (lo : 1/2≤p) (hi : p≤3/2) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let F:=Greenbelt.allot i
    let β:=Integral.temperature g
    let w:=β*p*(g/Real.sqrt p)^(a.grade-a.rise)
    let d:=fun z : Air f G=>(sitePacket a.cells x ((X.wrapY y).input ((X.wrapY y).liftA β z)):ℂ)-
      siteTaylor a.cells x (angularSample F z) (r+1) g
    let M:=speedPrice G L o.eta o.gap o.ample ((r+2)*(l+1)-1)
    Integrable (fun z=>‖(w:ℂ)*d z‖^(l+1)) X.dice ∧
      (∫ z,‖(w:ℂ)*d z‖^(l+1) ∂X.dice)≤(2^(a.grade-a.rise+1)*D*(2*M/σ)^(r+2)*g^(a.grade-a.rise+r))^(l+1) := by
  intro X F β w d M
  obtain ⟨hi',bound⟩:=chamber_error_moment H temp χ v i tag y Z hs filed a member x (r+1) l g p hg
  refine ⟨hi',bound.trans ?_⟩
  have hm:=(speed_price_pos G L o.eta o.gap o.ample ((r+2)*(l+1)-1)).le
  change (|w| *(D*(2*M*|g|/σ)^(r+2)))^(l+1)≤_
  rw [abs_of_pos hg,show 2*M*g/σ=(2*M/σ)*g by ring]
  apply pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (mul_nonneg filed.1
    (pow_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hm) hs.le) hg.le) _) ))
  exact weighted_power hg lo hi (by positivity) filed.1 (a.grade-a.rise) r

theorem chamber_grade_moment (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) {σ D : ℝ} (hs : 0<σ) (filed : Draw Z σ D)
    (a : PrismA G) (member : a∈Z) (x : Site f) (l : ℕ) (g p : ℝ) (hg : 0<g) (lo : 1/2≤p) (hi : p≤3/2) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let β:=Integral.temperature g
    let w:=β*p*(g/Real.sqrt p)^(a.grade-a.rise)
    let M:=speedPrice G L o.eta o.gap o.ample ((a.rise+2)*(l+1)-1)
    let field:=fun z : Air f G=>(sitePacket a.cells x ((X.wrapY y).input ((X.wrapY y).liftA β z)):ℂ)
    Integrable (fun z=>‖(w:ℂ)*field z‖^(l+1)) X.dice ∧
      (∫ z,‖(w:ℂ)*field z‖^(l+1) ∂X.dice)≤(2^(a.grade-a.rise+1)*D*(2*M/σ)^(a.rise+2)*g^a.grade)^(l+1) := by
  intro X β w M field
  have zero (z : Dir G f) : siteTaylor a.cells x z (a.rise+1) g=0 :=
    flat_site_polynomial a.cells x _ (Nat.lt_succ_self _) g
  have quoted:=chamber_power_moment H temp χ v i tag y Z hs filed a member x a.rise l g p hg lo hi
  simpa only [zero,sub_zero,Nat.sub_add_cancel a.rankA] using quoted

end YM.Integration.OriginalMarkedRunAction
