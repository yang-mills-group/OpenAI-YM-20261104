import YM.Integration.WilsonOriginalSingleGaussianPass

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSingleGaussianReceipt
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonOriginalSingleMarkedRegister WilsonVacuumPreResetFiniteRegister
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
variable {I Y V A:Type}[Fintype I][DecidableEq I][Fintype Y][Fintype V][DecidableEq V]
  [Fintype A]{J:Census V}{r:ℕ}

structure Page (I Y A:Type)[Fintype I][DecidableEq I][Fintype A](J:Census V)(r:ℕ) where
  B : Y→ℝ
  source : J.Mode
  live : source.val.Nonempty
  phase : Ink (I⊕Y)
  zero : constantCoeff phase=0
  mark : A→Ink (I⊕Y)
  amplitude : A→ℂ
  driver : Hot (Board J r)→Normal.poly I
  written : ∀(s:Hot (Board J r))(z:I→ℝ),Cloud.paint z (driver s)=
    (WilsonOriginalSingleGaussianPass.deposit r B phase mark amplitude z source).part s.val

def realTable (W:Page I Y A J r)(q:Matrix I I ℝ)(h:q.IsSymm) := Cloud.prescription q h 0 W.driver

def mass (W:Page I Y A J r)(q:Matrix I I ℝ) := Wick Y q (raiseE W.phase)
def numerator (W:Page I Y A J r)(q:Matrix I I ℝ)(a:A) := Wick Y q (raiseE W.phase*W.mark a)
def filed (W:Page I Y A J r)(q:Matrix I I ℝ) :=
  register J r (observed W.B (mass W q)) +
    token J r W.source*(∑a,W.amplitude a • register J r (observed W.B (numerator W q a)))

theorem integral (W:Page I Y A J r)(q:Matrix I I ℝ)(h:q.IsSymm):
    realTable W q h=filed W q :=
  WilsonOriginalSingleGaussianPass.original r W.B q h W.source W.live W.phase W.zero W.mark W.amplitude W.driver
    (WilsonOriginalSingleGaussianPass.hot r W.B W.phase W.zero W.mark W.amplitude W.source W.live W.driver W.written)

end YM.Integration.WilsonOriginalSingleGaussianReceipt
