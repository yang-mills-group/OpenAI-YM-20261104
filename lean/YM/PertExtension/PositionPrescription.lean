import YM.PertExtension.PureBasis
import YM.PertExtension.FlagPosition
import YM.PertExtension.FrameLimit

/-!
# Formal coefficients on separated product tests

`kernel` uses the finite-regulator stencil and Wilson denominator before
the position and coupling changes. The position test system fixes the basis,
and the connected triangle fixes the coupling parameter. To use the physical
coupling, the triangle must realize the oriented `b,U,U` test or a proved
equivalent linear combination, with nonzero first variation.
`output_converges` takes coefficientwise limits along the prescribed period rule.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
namespace YM.PertExtension.PositionPrescription
open Set Function Filter PowerSeries MeasureTheory Labels Source Extraction
open scoped Topology ContDiff BigOperators Classical
open Position LatticePT Extra.FD Triangle

variable {G : Gauge} (F : Frames G)(d : ℕ)
abbrev Index := Fin ((YM.Extra.FD.RStage.m (recorded F d))+1)
local notation "J" => Index F d

variable (H : Hol G)(S : ∀ n, SectionData (F.level n))(hS : ∀ n, (S n).Sound H)(hB : ∀ n, Bid.pop (S n))

def labels := Horizon.word d F H S hS hB

def free : Mark J Physical.Profile.n→ℝ := Physical.free (L:=YM.Maxwell.standard F) (recorded F d).b

def systemData (D : TestSystem J Physical.Profile Physical.Profile.n)(q:ℕ+)(m:ℕ):Mark J Physical.Profile.n→fps :=
 fun i=>mk (Mixed.polynomialTop (labels F d H S hS hB ∘ i.2) q m
   (fun x=> (i.1.test (WithLp.toLp 2 x)).re)) -- Points is WithLp axis? 

abbrev testedTree (D : TestSystem J Physical.Profile Physical.Profile.n)(q:ℕ+)(m:ℕ) :=
  TestSystem.leadingAdjust D (free F d) (fun v=>constantCoeff (systemData F d H S hS hB D q m v))

def kernel (D : TestSystem J Physical.Profile Physical.Profile.n)(q:ℕ+)(m:ℕ) :=
  let X:= testedTree F d H S hS hB D q m
  X.positioned (systemData F d H S hS hB D q m)

def formal (D : TestSystem J Physical.Profile Physical.Profile.n)(T : Triangle Physical.Profile.n J)(q:ℕ+)(m:ℕ) :=
  T.remeasured (kernel F d H S hS hB D q m)

theorem regulator_comparison (D : TestSystem J Physical.Profile Physical.Profile.n)(q:ℕ+)(m:ℕ)(i:Mark J Physical.Profile.n) :
    Series.Tested.Aspiration
      (Mixed.realTop (labels F d H S hS hB ∘ i.2) q m (fun x=>(i.1.test (WithLp.toLp 2 x)).re))
      (fun j=>coeff j (systemData F d H S hS hB D q m i)) := by
  simp only [systemData, coeff_mk]; exact Mixed.comparison _ _ _ _

theorem regulator_positions (D : TestSystem J Physical.Profile Physical.Profile.n)(q:ℕ+)(m:ℕ)
    (h : (testedTree F d H S hS hB D q m).Regular (fun v=>constantCoeff (systemData F d H S hS hB D q m v)))
    (j : ℕ) :
    D.select (fun v=>coeff j (kernel F d H S hS hB D q m (markIn _ v))) = if j=0 then D.target else 0 :=
  TestSystem.normalizes (testedTree F d H S hS hB D q m) (a:=systemData F d H S hS hB D q m) h j

theorem regulator_coupling (D : TestSystem J Physical.Profile Physical.Profile.n)(T : Triangle Physical.Profile.n J)(q:ℕ+)(m:ℕ)
    (h: coeff 1 (T.connected (kernel F d H S hS hB D q m)) ≠ 0):
    T.parameter (formal F d H S hS hB D T q m) = X := T.calibrated h

/-- Coefficientwise convergence of the position-test series in the chosen bare parameter, regularity at the free constant terms and a nonzero connected triangle slope give convergence of the calibrated output. -/
theorem output_converges (D : TestSystem J Physical.Profile Physical.Profile.n)(T : Triangle Physical.Profile.n J)(q:ℕ+)
    (B : Mark J Physical.Profile.n→fps)(hconst : ∀ i,constantCoeff (B i)=free F d i)
    (ht : ∀ i, AlignSeries atTop (fun m=>systemData F d H S hS hB D q m i) (B i))
    (hh : D.Regular (free F d))
    (hc : coeff 1 (T.connected (D.positioned B))≠0) (i:Mark J Physical.Profile.n) :
    AlignSeries atTop (formal F d H S hS hB D T q · i) (T.remeasured (D.positioned B) i) := by
  rw [←funext_iff] at hconst
  let A := fun m=>systemData F d H S hS hB D q m
  have hv:= AlignSeries.calibrates T (l:=atTop) (q:=fun v=>(D.systemAt B A v).positioned (A v)) hc
    (D.positions_align B A (hconst ▸ hh) ht) i
  change AlignSeries atTop (fun m=>T.remeasured ((D.leadingAdjust (free F d) (fun v=>constantCoeff (A m v))).positioned (A m)) i) _
  rw [← hconst]
  exact hv

end YM.PertExtension.PositionPrescription
