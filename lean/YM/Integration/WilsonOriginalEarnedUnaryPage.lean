import YM.Integration.WilsonOriginalEarnedUnaryDriver

/-! The booked native forest jets of a general one-mark sheet, truncated at the actual requested response. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalEarnedUnaryPage
open Function Filter Set Finset Lattice Laurent Wilson RG Source Labels Marker Multi Precision Tree Exterior Bloch Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Order AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series Series.Radial Series.Tested
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos Next.Rank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative credit)
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  {V:Type}[DecidableEq V][Fintype V]{C:Marker.Census V}(Y:Bulk.Colors C G (fine R i per))
local notation "S" => step R i per
local notation "K" => model R N i per hi
local notation "φ" => relative R N i per hi F (covered R N i per)
variable (B:fieldDir G (coarse R i per) 1)


open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonOriginalSingleGaussianPass (deposit read_deposit)
open PhysicalForestMarkedRay
open WilsonOriginalSingleGaussianReceipt
variable (s₀:Hot C)(a:ℂ)(T:PChart G (fine R i per))(r:ℕ)
local notation "word" => WilsonOriginalFoldedMarkedRightColumn.before R N i per hi F T
local notation "rng" => Woods G (coarse R i per)
local notation "arg" => saddle R N i per F

def Ray :Prop := ∀(t:Hot C)(j:ℕ),j≤r → ∀ z:Precision.Key F G→ℝ,
  readJet (Y.power t+j) (chartMark S F arg K B z Y t)=
    if t=s₀ then a*((MvPolynomial.eval (Sum.elim z (flatten B)) (coeff j word):ℝ):ℂ) else 0

include hi tag in
private theorem center : arg=reveal G S F*((reveal G S F).transpose*arg):=by
  have h:=(K).hessian_pos F tag
  rw [OriginalMarkedHeatCovariance.precision R N i per hi F tag] at h
  apply sweeps G S F (prediction R N i per) (lower R N i) (isUnit_iff_ne_zero.mpr h.det_pos.ne')
  exact horizon_step (levels R) i N hi _ _ (step R i per).sizes

omit [Fintype V] in
include tag in
private theorem value (t:Hot C)(z:Precision.Key F G→ℝ)(j:ℕ)(well:Bulk.Well Y):
    Cloud.paint z (kernelJet (Bulk.stage K F B) (Bulk.hinge F) (Bulk.markFn S F Y t) (Y.power t+j))=
      readJet (Y.power t+j) (chartMark S F arg K B z Y t):=by
  rw [Assembly.reading]
  apply PhysicalForestMarkedRay.coefficient S F arg K B z tag Y well t (center R N i per hi F tag)

private theorem occupied (e:ℕ)(Z:SeriesA G)(well:Bulk.Well Y)
    (ray:Ray R N i per hi F Y B s₀ a T r)
    (s:Hot (Board C r))(hc:(Join.left s.val).val.Nonempty)(z:Precision.Key F G→ℝ):
    let t:Hot C:=⟨Join.left s.val,hc⟩
    let j:=(Join.right s.val).val.card
    Cloud.paint z (driver R N i per hi F tag Y B e Z r s) =
      (j.factorial:ℂ) * (if t=s₀ then a*(MvPolynomial.eval (Sum.elim z (flatten B)) (coeff j word):ℝ) else 0):=by
  intro t j
  unfold driver family generator
  simp only [if_pos hc,dif_pos hc,map_smul,smul_eq_mul]
  apply congrArg ((j.factorial:ℂ)*·)
  exact (value R N i per hi F tag Y B t z j well).trans (ray t j (Order.order_limit r (Join.right s.val)) z)

theorem income (e:ℕ)(Z:SeriesA G)(well:Bulk.Well Y)
    (ray:Ray R N i per hi F Y B s₀ a T r)(s:Hot (Board C r))(z:Precision.Key F G→ℝ):
    Cloud.paint z (driver R N i per hi F tag Y B e Z r s)=
      (deposit r (flatten B) φ (fun _:Unit=>word) (fun _=>a) z s₀.val).part s.val:=by
  rw [←Join.pair_reunite s.val, read_deposit]
  by_cases hc:(Join.left s.val).val.Nonempty
  · let t:Hot C:=⟨Join.left s.val,hc⟩
    have hv:=occupied R N i per hi F tag Y B s₀ a T r e Z well ray s hc z
    simp only [if_neg ((hot_iff_ne _).1 hc),zero_add,Fintype.sum_unique]
    by_cases same:t=s₀
    · have he:Join.left s.val=s₀.val:=congrArg Subtype.val same
      simp only [t] at same
      simpa only [same,he,if_pos,Fintype.sum_unique,mul_assoc] using hv
    · have he:Join.left s.val≠s₀.val:=fun h=>same (Subtype.ext h)
      simp only [t] at same
      simpa only [if_neg he,if_neg same,mul_zero] using hv
  · have hq:Join.left s.val=C.quiet:=of_not_not (mt (hot_iff_ne _).2 hc)
    have hn:Join.left s.val≠s₀.val:=fun eq=>hc (eq.symm ▸ s₀.property)
    simp only [driver,if_neg hc,if_pos hq,if_neg hn,add_zero,map_smul,smul_eq_mul,WilsonOriginalGaussianFibre.reading]

private theorem centered_zero {A:Type}[CommRing A](F:PowerSeries A):
    constantCoeff (F-PowerSeries.C (constantCoeff F))=0:=by simp

def page (e:ℕ)(Z:SeriesA G)(well:Bulk.Well Y)(ray:Ray R N i per hi F Y B s₀ a T r) :
    Page (Precision.Key F G) rng Unit C r where
  B:=flatten B
  source:=s₀.val
  live:=s₀.property
  phase:=φ
  zero:=centered_zero _
  mark:=fun _=>word
  amplitude:=fun _=>a
  driver:=driver R N i per hi F tag Y B e Z r
  written:=income R N i per hi F tag Y B s₀ a T r e Z well ray

end YM.Integration.WilsonOriginalEarnedUnaryPage
