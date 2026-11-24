import YM.Integration.WilsonThermometerPositionFilmCloudCommission

/-! Exact finite side fee for changing the quiet action under an occupied deposited word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmCloudQuiet
open Finset Function MeasureTheory Lattice RG Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Assembly Comparison.RG02.Cumulants Comparison.RG02.Order
open YM.Next.SectorChange YM.Primitives.GCC.Anchor WilsonThermometerPositionFilmChartContact
open WilsonThermometerPositionFilmCloudReading WilsonThermometerPositionFilmCloudCommission
open scoped Classical BigOperators
variable {G:Gauge} {c f:Side} {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
  {V':Type} [DecidableEq V'] [Fintype V'] {R':Census V'}
  {S:StepData c f} {clip:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S clip P O) (F:Forest S.ratio) (tag:S.Choices)
  (C:Bulk.Colors R G f) (D:Bulk.Colors R' G f) (a:R'.Mode) (x:fieldDir G c 1)
local notation "μ" => Gaussian.cloud (K.covariance F tag)
local notation "M" => mounted C D
local notation "coupling" z:max => (noise K F tag C x z - noise K F tag D x z)
local notation "groundD" z:max => paid K F tag D a x 0 z

/-- The complete score covariance at the common genuine affine conditional mean. -/
def bill : ℂ :=
  (∫ z,coupling z * groundD z ∂μ) - (∫ z,coupling z ∂μ) * ∫ z,groundD z ∂μ

omit [Fintype V] in
private theorem unchanged (z:Precision.Key F G→ℝ) :
    paid K F tag M a x 0 z=groundD z:=by rw [ground,ground];rfl

omit [Fintype V] in
private theorem issued (z:Precision.Key F G→ℝ) :
    (paid K F tag D a x 1 z-paid K F tag M a x 1 z)=coupling z*groundD z := by
  simp only [first,ground]
  have paidNoise: noise K F tag M x z=noise K F tag C x z:=rfl
  have marked (k:ℕ) (u:Bulk.SliceDir S F G):bent S F M a k u=bent S F D a k u:=rfl
  rw [paidNoise,marked,marked]
  ring

theorem original (p:ℕ) (hp:0<p) :
    (First.buc (ratio (Bulk.Fk K F tag M x p))).part a=(First.buc (ratio (Bulk.Fk K F tag D x p))).part a ∧
    (First.ind (ratio (Bulk.Fk K F tag M x p))).part a=(First.ind (ratio (Bulk.Fk K F tag D x p))).part a -
      bill K F tag C D a x := by
  have paidM:=normalized K F tag M a x p hp
  have paidD:=normalized K F tag D a x p hp
  have base:(First.buc (Bulk.Fk K F tag M x p)).part a=∫ z,groundD z ∂μ:=by
    rw [First.buc,observed _ _ _ _ _ _ _ _ (Nat.zero_le p)]
    apply integral_congr_ae
    filter_upwards [] with z
    exact unchanged K F tag C D a x z
  have same:(First.buc (Bulk.Fk K F tag D x p)).part a=∫ z,groundD z ∂μ:=
    observed _ _ _ _ _ _ _ _ (Nat.zero_le p)
  have singles:(First.ind (Bulk.Fk K F tag D x p)).part a-(First.ind (Bulk.Fk K F tag M x p)).part a=
      ∫z,coupling z*groundD z ∂μ:=by
    rw [First.ind,First.ind,observed _ _ _ _ _ _ _ _ hp,observed _ _ _ _ _ _ _ _ hp,
      ←integral_sub (integrable K F tag D a x 1) (integrable K F tag M a x 1)]
    apply integral_congr_ae
    filter_upwards [] with z
    exact issued K F tag C D a x z
  have normD: (First.ind (Bulk.Fk K F tag D x p)).part R'.quiet= -(∫z,noise K F tag D x z ∂μ):=by
    rw [quiet K F tag D x p hp,integral_neg]
  have normM: (First.ind (Bulk.Fk K F tag M x p)).part R'.quiet= -(∫z,noise K F tag C x z ∂μ):=by
    rw [quiet K F tag M x p hp,integral_neg];rfl
  have subtraction:=integral_sub (integrable_noise K F tag C x) (integrable_noise K F tag D x)
  constructor
  · rw [paidM.1,paidD.1,base,same]
  · rw [paidM.2,paidD.2,base,same,normD,normM,bill,←singles,subtraction]
    ring

theorem summed (s:R.Mode) {Q:Type} [Fintype Q] (Ds:Q→Bulk.Colors R' G f) (v:Q→ℂ)
    (H:∀(w:Bulk.SliceDir S F G)(b:Fin 2),bent S F C s b.val w=
      ∑q:Q,v q * bent S F (Ds q) a b.val w) (p:ℕ) (hp:0<p) :
    (First.buc (ratio (Bulk.Fk K F tag C x p))).part s=
      ∑q:Q,v q * (First.buc (ratio (Bulk.Fk K F tag (Ds q) x p))).part a ∧
    (First.ind (ratio (Bulk.Fk K F tag C x p))).part s=
      ∑q:Q,v q * ((First.ind (ratio (Bulk.Fk K F tag (Ds q) x p))).part a - bill K F tag C (Ds q) a x) := by
  have row:=WilsonThermometerPositionFilmCloudCommission.original K F tag C s x Ds a v H p hp
  constructor
  · refine (row 0).trans (Finset.sum_congr rfl (fun q _=>?_))
    exact congrArg (v q * ·) (original K F tag C (Ds q) a x p hp).1
  · refine (row 1).trans (Finset.sum_congr rfl (fun q _=>?_))
    exact congrArg (v q * ·) (original K F tag C (Ds q) a x p hp).2

end YM.Integration.WilsonThermometerPositionFilmCloudQuiet

