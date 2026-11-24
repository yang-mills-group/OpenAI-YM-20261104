import YM.Integration.WilsonPhysicalHistoryRetainedSpringChamberFace
import YM.Integration.WilsonPhysicalHistoryRetainedSpringKineticTariff

/-! The full old quadratic at its own original site consists of the direct
Wilson square and all ordered pairs of its kinetic paths. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function MeasureTheory Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W} {R : Rep G f}

theorem added_error {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (f g : Ω→ℂ) (l : ℕ) {a b : ℝ}
    (a0 : 0≤a) (b0 : 0≤b)
    (ha : Integrable f ν ∧ Integrable (fun z=>‖f z‖^(l+1)) ν ∧ (∫ z,‖f z‖^(l+1) ∂ν)≤a^(l+1))
    (hb : Integrable g ν ∧ Integrable (fun z=>‖g z‖^(l+1)) ν ∧ (∫ z,‖g z‖^(l+1) ∂ν)≤b^(l+1)) :
    let E:=fun z=>f z+g z
    Integrable E ν ∧ Integrable (fun z=>‖E z‖^(l+1)) ν ∧ (∫ z,‖E z‖^(l+1) ∂ν)≤(a+b)^(l+1) := by
  intro E
  let d : Bool→Ω→ℂ:=fun t=>if t then f else g
  let cost : Bool→ℝ:=fun t=>if t then a else b
  have h (t) : Integrable (d t) ν ∧ Integrable (fun z=>‖d t z‖^(l+1)) ν ∧
      (∫ z,‖d t z‖^(l+1) ∂ν)≤cost t^(l+1):=by cases t <;> assumption
  have good (t) : 0≤cost t:=by cases t <;> assumption
  obtain ⟨whole,price⟩:=pool_finite ν univ cost (fun t z=>‖d t z‖) (fun t _=>good t)
    (fun _ _ _=>norm_nonneg _) (fun t _=>(h t).1.norm.aestronglyMeasurable) l (fun t _=>(h t).2)
  have inc (z : Ω) : ‖E z‖^(l+1)≤(∑ t,‖d t z‖)^(l+1):=by
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa [d,Fintype.sum_bool] using norm_add_le (f z) (g z)
  have integ : Integrable E ν:=ha.1.add hb.1
  have measured:=whole.mono' ((continuous_pow (l+1)).comp_aestronglyMeasurable integ.norm.aestronglyMeasurable)
    (ae_of_all _ fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact inc z)
  exact ⟨integ,measured,(integral_mono measured whole inc).trans (by simpa [cost,Fintype.sum_bool] using price)⟩

def kineticTaylor (B : Clip) (K : PathData G) (x : Site f) (z : Dir G f) (q : ℕ) (g : ℝ) : ℂ:=
  (B.direct*faceTaylorAt x z q g:ℝ)+siteTaylor (gramEntries K) x z q g

theorem kinetic_first (B : Clip) (K : PathData G) (x : Site f) (z : Dir G f) (g : ℝ) :
    kineticTaylor B K x z 1 g=0:=by
  rw [kineticTaylor,face_first,flat_site_polynomial (gramEntries K) x z (by decide : 1<2) g]
  simp

def kineticPrice (G : Gauge) (B : Clip) (D σ : ℝ) (h : ℕ) (M : ℝ) : ℝ:=
  |B.direct| *((Fintype.card PlaqAxes:ℝ)*faceCost G h M)+Stationary.gramCost G D*(2*M/σ)^h

theorem chamber_kinetic (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (fan : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) {K : PathData G} {B : Clip} {σ D Λ : ℝ}
    (paid : K.Bounds B σ D Λ) (x : Site f) (q l : ℕ) (g w : ℝ) (hg : 0<g) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 fan i tag
    let F:=Greenbelt.allot i
    let e:=fun z : Air f G=>(w:ℂ)*((secondAt B K x ((X.wrapY y).input
      ((X.wrapY y).liftA (Integral.temperature g) z)):ℂ)-kineticTaylor B K x (angularSample F z) q g)
    let M:=speedPrice G L o.eta o.gap o.ample ((q+1)*(l+1)-1)
    Integrable e X.dice ∧ Integrable (fun z=>‖e z‖^(l+1)) X.dice ∧ (∫ z,‖e z‖^(l+1) ∂X.dice)≤
      (|w| *kineticPrice G B D σ (q+1) M*|g|^(q+1))^(l+1) := by
  intro X F e M
  let U (z : Air f G):=(X.wrapY y).input ((X.wrapY y).liftA (Integral.temperature g) z)
  let face (z : Air f G):=((w*B.direct:ℝ):ℂ)*((facePriceAt x (U z)-faceTaylorAt x (angularSample F z) q g:ℝ):ℂ)
  let gram (z : Air f G):=(w:ℂ)*((sitePacket (gramEntries K) x (U z):ℂ)-siteTaylor (gramEntries K) x (angularSample F z) q g)
  let a:=|w*B.direct| *((Fintype.card PlaqAxes:ℝ)*(faceCost G (q+1) M*|g|^(q+1)))
  let b:=|w| *(Stationary.gramCost G D*(2*M*|g|/σ)^(q+1))
  have Mpos : 0≤M:=(speed_price_pos ..).le
  have a0 : 0≤a:=by dsimp only [a]; positivity [face_cost_nonneg G (q+1) Mpos]
  have D0 : 0≤D:=(tsum_nonneg paid.three.1).trans paid.three.2.2
  have b0 : 0≤b:=by dsimp only [b,Stationary.gramCost]; positivity [paid.width]
  have hf:=chamber_face H temp χ fan i tag y x q l g (w*B.direct) hg
  have ha:=chamber_gram_rows H temp χ fan i tag y paid x q l g w hg
  have both:=added_error X.dice face gram l a0 b0 hf ha
  have same : e=fun z=>face z+gram z:=by
    funext z
    change (w:ℂ)*((secondAt B K x (U z):ℂ)-kineticTaylor B K x (angularSample F z) q g)=_
    rw [gram_at K paid]
    simp only [face,gram,kineticTaylor,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add]
    ring
  have price : a+b=|w| *kineticPrice G B D σ (q+1) M*|g|^(q+1):=by
    simp only [a,b,kineticPrice,abs_mul,div_eq_mul_inv,mul_pow]
    ring
  rw [same,←price]
  exact both

end YM.Integration.OriginalMarkedRunAction
