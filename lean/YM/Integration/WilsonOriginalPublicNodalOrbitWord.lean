import YM.Integration.WilsonOriginalPublicNodalWord
import YM.Integration.WilsonThermometerInversionSockets
import YM.Integration.WilsonIndependentMatchedClosedPlan

/-! The complete unmasked physical top word of a submitted socket face is
a Wilson test on the independent inversion torus. Its previously deposited
series is the genuine normalized orbital Haar expansion on that very side. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalOrbitWord
open Finset Lattice Wilson PhysicalNext.Repeat.Legato Source Labels Function
open PertExtension PertExtension.Orb RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Laplace
open XSpace FVA2
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonOriginalStarSceneWords (raw)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonIndependentMatchedOrbitReading (insert originalClock)
open WilsonOriginalPublicNodalWord (sheet)
open private allowed from YM.Integration.WilsonThermometerInversionSockets
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}(d:I→ℕ){h:I→ℕ}
  (κ:(j:I)→Knob (h j))(pt:I→Chamber)(S:Finset I)(z:I→ Cover)(c:Selection R d S)(P:Period)

def body (U:Config G P.side):ℝ:=∏j:S,(raw R d (entry R d j (c j))).unmasked U (wrap P.side (z j))

theorem source (U:Config G P.side):
    word R d κ pt 1 (fun j=>wrap P.side (z j)) S c U=(body R d S z c P U:ℂ):=by
  simp only [word,WilsonReceivedCanonicalVerseBasis.restored,Complex.ofReal_one,one_zpow,one_mul,
    WilsonReceivedCanonicalVerseBasis.field,body,Complex.ofReal_prod]

theorem test:Orb.PreTest (body R d S z c P):=by
  let atom(j:S)(U:Config G P.side):ℝ:=(raw R d (entry R d j (c j))).unmasked U (wrap P.side (z j))
  have each(j:S):Orb.PreTest (atom j):=(allowed R d (entry R d j (c j)) (wrap P.side (z j))).1
  have finite (a:Finset S):Orb.PreTest (∏j∈a,atom j):=by
    induction a using Finset.induction_on with
    | empty => rw [Finset.prod_empty]; exact ⟨fun _ _ _=>rfl,Orb.one_test,continuous_const⟩
    | insert j a hj ih =>rw [Finset.prod_insert hj];exact WilsonIndependentMatchedClosedPlan.product (each j) ih
  convert finite univ using 1
  funext U
  simp [body,atom,Finset.prod_apply]

theorem stencil (T:P.Tree):
    sheet R d κ pt S z 1 c P T=Bare.normalized T G (BareOrb.stencil T (body R d S z c P)):=by
  unfold sheet BareOrb.stencil TreeFormal.enter
  exact congrArg (fun f=>Bare.normalized T G (Taylor.expandTaylor (T.basis G) f))
    (funext fun X=>source R d κ pt S z c P (T.links X))

theorem original (T:P.Tree):
    sheet R d κ pt S z 1 c P T=TaylorWick.into
      (PowerSeries.mk (storyPT originalClock (insert (body R d S z c P)))):=by
  rw [stencil]
  have filed:=test R d S z c P
  exact WilsonIndependentMatchedOrbitReading.diagram T _ filed
    (WilsonIndependentMatchedClosedPlan.actual (even_iff_two_dvd.mpr P.even) _ filed)

end YM.Integration.WilsonOriginalPublicNodalOrbitWord
end
