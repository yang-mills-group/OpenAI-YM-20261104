import YM.Integration.WilsonReportingPositiveSpine
import YM.Integration.WilsonReportingTopEnvelope

/-! The normalized, fully displaced field is controlled at every physical
coarse configuration, before the period, by the ultraviolet physical field
in the correct reporting units and the true affine angular profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingCoarseQuotient
open Filter Function Finset Lattice Wilson RG Source RG12 RG05Readout Address Native
open Extra.Histories MergeProof Accent Trace.Physical WilsonReportingBareCell
open WilsonReportingPositiveSpine Extra.Multi.BasisCost
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {N per m b d:ℕ}
variable {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d per} {U:Emblems C d}

theorem entrance (h:C.Makes) (starts:∀e ≤ d, C.ref e ≤ N) (t:Letter d) (x:C.label (kept t))
    (K:ℝ) (price:∀X,‖C.O N per x 0 X‖ ≤ K) :
    Covered C N per N t K (pulseOut (basisTop C d N per
      (chunk t ((C.factory (kept t) N per).terminal.symm x)))) := by
  intro φ c paid X
  have entered:=incidence h t φ (0:Site (C.side N per)) x
  have neutral (g:Goods G (C.side N per)):stepUp (1,false) 0 g=g:=Motion.dance_nil g
  rw [neutral] at entered
  have eq:=congrFun entered X
  change ‖(basisTop C d N per (chunk t ((C.factory (kept t) N per).terminal.symm x)) φ).1 X‖ ≤ _
  rw [basis_agrees C d N per h starts φ X,eq]
  change ‖((C.path.rep N per N).eval X:ℂ)*((readJ t 0 φ*(C.S.a N:ℂ)^kept t)*C.O N per x 0 X)‖ ≤ _
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos N).le,
    Real.norm_of_nonneg (C.path.nonnegative h.wilson N per N le_rfl X)]
  have gate:=paid 0 box0
  have co:0 ≤ c:=(norm_nonneg _).trans gate
  have cost:=mul_le_mul (mul_le_mul_of_nonneg_right gate (pow_nonneg (C.S.a_pos N).le (kept t)))
    (price X) (norm_nonneg _) (mul_nonneg co (pow_nonneg (C.S.a_pos N).le (kept t)))
  exact (mul_le_mul_of_nonneg_left cost (C.path.nonnegative h.wilson N per N le_rfl X)).trans_eq (by ring)

theorem original (h:C.Makes) (spine:Spine D B h b per d N V U) (starts:∀e ≤ d,C.ref e ≤ N)
    (beginning:b ≤ m) (live:m ≤ N) (t:Letter d) (x:C.label (kept t)) (K:ℝ)
    (price:∀X, ‖(C.S.a m:ℂ)^kept t*C.O N per x 0 X‖ ≤ K)
    (φ:Body) (c:ℝ) (paid:∀y∈Native.box, ‖readJ t y φ‖ ≤ c) (W:Config G (C.side m per)) :
    ‖Juniper.Caret.ratio (C.path.rep N per m)
      (pulseOut (V m (Many.point U (chunk t ((C.factory (kept t) N per).terminal.symm x)) N m)) φ) W‖ ≤ c*K := by
  obtain ⟨q,rfl⟩:=Nat.exists_eq_add_of_le live
  let k:=kept t
  let v:=(C.factory k (m+q) per).terminal.symm x
  let g:ℝ:=C.S.a m^k
  have gpos:0<g:=pow_pos (C.S.a_pos m) _
  have top (X:Config G (C.side (m+q) per)):‖C.O (m+q) per x 0 X‖ ≤ K/g := by
    apply (le_div_iff₀ gpos).2
    have hx:=price X
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos m).le] at hx
    simpa only [g,k,mul_comm] using hx
  have begin:=entrance h starts t x _ top
  have booked:=WilsonReportingPositiveSpine.route h t _ q le_rfl _ begin
  have issued:=WilsonReportingCellRoute.bare h spine beginning (chunk t v)
  have field:=booked φ c paid W
  rw [issued] at field
  have denom:0<(C.path.rep (m+q) per m).eval W:=WardBin.Wheels.gravity h.wilson live W
  rw [show Juniper.Caret.ratio (C.path.rep (m+q) per m)
      (pulseOut (V m (Many.point U (chunk t v) (m+q) m)) φ) W =
      (pulseOut (V m (Many.point U (chunk t v) (m+q) m)) φ W)/((C.path.rep (m+q) per m).eval W:ℂ) from rfl,
    norm_div,Complex.norm_real,Real.norm_of_nonneg denom.le]
  apply (div_le_iff₀ denom).2
  refine field.trans_eq ?_
  change g*c*(K/g)*(C.path.rep (m+q) per m).eval W=c*K*(C.path.rep (m+q) per m).eval W
  field_simp

end YM.Integration.WilsonReportingCoarseQuotient
