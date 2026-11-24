import YM.Integration.WilsonReceivedCanonicalVerseChart
import YM.Integration.WilsonOriginalLoweredChartSource
import YM.Integration.WilsonOriginalJointForestRay

/-! The actual canonical slit on every fine forest and positive real block, with its Laurent shift. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalSocketSeed
open Function Finset Lattice Laurent Wilson RG Source Labels Precision Tree Exterior Bloch Matrix PowerSeries
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil Stationary
open OriginalMarkedSourceComet IndependentSourcePathFamily PhysicalForestMarkedRay
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalThermometerPalette WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

def contact (h:ℕ):Knob h:=⟨0,Fin.elim0⟩
def sheet (h:ℕ):Scroll h:=⟨fun _=>1,show ContDiff ℝ (↑h) (fun _=>1) from contDiff_const⟩
def present {V:Type}(h:V→ℕ):Case h:=fun j=>page _ (sheet (h j))

variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V](R:Run G)(d:V→ℕ){h:V→ℕ}(pt:V→Chamber)
  (q:(j:V)→Choice R d j)(j:V)(addresses:V → Lattice.Cover)
local notation "κ" => (fun j=>contact (h j))
local notation "a" => WilsonReceivedCanonicalVerseBasis.basis R d κ pt j (q j)
local notation "entry₀" => entry R d j (q j)
local notation "T" => raw R d entry₀
local notation "P₀" => OriginalMarkedSourceComet.colour (a).path (a).color (a).weight (a).quadrant
local notation "ink" => current (P₀) (petal h j (claim (h j) (a).knob (a).point))

omit [Fintype V] in
theorem measured {n:Side}(U:Config G n)(o:Site n):
    (dip (ink) (touch (present h) {j})).unmasked U o=(T).unmasked U o:=by
  have val:=OriginalMarkedSourceComet.paired h j (a).path (a).color (a).weight (a).quadrant
    (Nat.zero_le (h j)) Fin.elim0 (pt j) (fun l=>sheet (h l)) U o
  have hx:crease (sheet (h j)) (Fin.elim0:Fin 0→Axis) (pt j).val=1:=by
    simp [crease,sheet,iteratedFDeriv_zero_apply]
  calc
    _=crease (sheet (h j)) Fin.elim0 (pt j).val*((a).quadrant ((a).weight*
         NativeCurvatureTensor.value (a).color (fun l=>((a).path l).atSite U o))):=val
    _=(P₀).unmasked U o:=by rw [hx,one_mul];exact (OriginalMarkedSourceComet.colour_poly ..).symm
    _=_:=WilsonReceivedCanonicalVerseBasis.field R d κ pt j (q j) U o

variable (N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
local notation "K" => WilsonVacuumPreResetStationaryChange.model R N i per hi
local notation "S" => step R i per
local notation "M" => saddle R N i per F
local notation "ρ" => fderiv ℝ ((K).b F) 0
local notation "era" => WilsonReceivedCanonicalVerseRegister.start R d κ pt q addresses {j}
local notation "read₀" => SignedMeasuredSourceSeries.probe (S) F (M) (ρ) (readO (present h) (era) (fine R i per))

include tag in
theorem cleared {toll:ℕ}(cost:pole R d entry₀ ≤ toll+1):
    (X:Ink (Active G F ⊕ Woods G (coarse R i per)))^(toll+1)*read₀=
      X^(toll+1-pole R d entry₀)*jet (fun v:Sloc (S) F G=>(T).unmasked
        (Work.F03.live F (SignedMarkedChartGerm.chart (S) F (ρ) v)) (wrap (fine R i per) (addresses j))):=by
  let old:Seed G (h j):={a with head:=(a).rank}
  have placed:=WilsonReceivedCanonicalVerseChart.filed R d κ pt q addresses j
  dsimp only at placed
  rw [placed]
  have fit:=WilsonOriginalStarSceneWords.low R d entry₀
  have shifted:=WilsonOriginalLoweredChartSource.shift R N i per hi F j old (present h) (addresses j)
    (pole R d entry₀) rfl fit
  have first:=SignedOpeningSourceCurrent.series (K) F (M) j old (present h) (addresses j) rfl
    (WilsonOriginalJointForestRay.swept R N i per hi F tag)
  have paid:SignedOpeningSourceCurrent.independent (K) F (M) j old (present h) (addresses j)=
      X^(pole R d entry₀)*SignedOpeningSourceCurrent.independent (K) F (M) j (a) (present h) (addresses j):=shifted
  rw [first] at paid
  have identity:(fun v:Sloc (S) F G=>(dip (ink) (touch (present h) {j})).unmasked
       (Work.F03.live F (SignedMarkedChartGerm.chart (S) F (ρ) v)) (wrap (fine R i per) (addresses j)))=
      fun v=>(T).unmasked (Work.F03.live F (SignedMarkedChartGerm.chart (S) F (ρ) v)) (wrap (fine R i per) (addresses j)):=by
    funext u
    exact measured R d pt q j _ _
  change jet _ = _ at paid
  rw [identity] at paid
  change X^(toll+1)*SignedOpeningSourceCurrent.independent (K) F (M) j (a) (present h) (addresses j)=_
  conv_lhs=>rw [show toll+1=toll+1-pole R d entry₀+pole R d entry₀ from (Nat.sub_add_cancel cost).symm,pow_add,mul_assoc,←paid]

include tag in
theorem kernel {toll:ℕ}(cost:pole R d entry₀ ≤ toll+1)(B:fieldDir G (coarse R i per) 1)
    (z:Precision.Key F G→ℝ)(grade:ℕ):
    Cloud.paint z (Assembly.kernelJet (Bulk.stage (K) F B) (Bulk.hinge F)
      (Bulk.posed (S) F (SignedRegisteredKernelPolynomial.primitive (T) (wrap (fine R i per) (addresses j))
        (toll+1-pole R d entry₀))) (toll+1+grade))=
      (MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B z) (coeff grade (read₀)):ℝ):=by
  rw [SignedRegisteredKernelPolynomial.kernel (K) F,←cleared R d pt q j addresses N i per hi F tag cost,
    coeff_X_pow_mul',if_pos (Nat.le_add_right _ _),Nat.add_sub_cancel_left]

end YM.Integration.WilsonReceivedCanonicalSocketSeed
