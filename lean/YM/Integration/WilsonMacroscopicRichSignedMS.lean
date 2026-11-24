import YM.Integration.WilsonMacroscopicRichMeasuredGram

/-! The real Wilson minus independent finite MS series on one literal
smooth two-field probe. Every submitted coefficient is the native MS tour;
the residual retains its sign inside the original test integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSignedMS
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Extraction Table Spec Climb Filter Set Finset PhysMS MeasureTheory Next.UVStress
open private entry from YM.Integration.MSSeparatedSmearedTreeGram
open private regular from YM.Integration.WilsonMacroscopicRichMeasuredGram
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (B : Deck G) {O : Booked B} (M : MS_Data G O)
variable (F : Spec.Final C f S) (J : ℝ→PhysMS.tower S) {h : ℕ}

def jet (h : ℕ) (g : Test 2) (μ : ℝ) (q : ℕ) (t : ℝ) : Matrix (Glyph B h) (Glyph B h) ℂ :=
  fun a b=>∑ k ∈ range (q+1),(t:ℂ)^k*MSSeparatedTestGram.matrix M h μ k g a b

def integrand (a b : Glyph B h) (μ : ℝ) (q : ℕ) (t : ℝ) (x : Points 2) : ℂ :=
  ∑ k ∈ range (q+1),(t:ℂ)^k*MSDeckProbeGram.raw M ![a,b] x μ k

theorem scope (a b : Glyph B h) (μ : ℝ) (q : ℕ) (t : ℝ) : ContinuousOn (integrand B M a b μ q t) (conf 2) :=
  continuousOn_finsetSum _ fun k _=>continuousOn_const.mul (fun x hx=>(entry M a b μ k x hx).continuousWithinAt)

theorem in_test (g : Test 2) (a b : Glyph B h) (μ : ℝ) (q : ℕ) (t : ℝ) :
    g.applyTo (integrand B M a b μ q t)=jet B M h g μ q t a b := by
  let E (k : ℕ) (x : Points 2) := MSDeckProbeGram.raw M ![a,b] x μ k
  let w (k : ℕ) := (t:ℂ)^k
  have integrable (k : ℕ) : Integrable (fun x=>g x*E k x) := g.smearing (fun x hx=>(entry M a b μ k x hx).continuousWithinAt)
  have distribute (x : Points 2) : g x*(∑ k ∈ range (q+1),w k*E k x)=∑ k ∈ range (q+1),w k*(g x*E k x) := by
    rw [mul_sum];exact sum_congr rfl fun i _=>mul_left_comm ..
  change (∫x,g x*(∑ k ∈ range (q+1),w k*E k x))=∑ k ∈ range (q+1),w k*(∫x,g x*E k x)
  simp_rw [distribute]
  rw [integral_finsetSum _ (fun k _=>(integrable k).const_mul (w k))]
  simp only [integral_const_mul]

def defect (h : ℕ) (g : Test 2) (μ : ℝ) (q : ℕ) (γ : ℝ→ℝ) (r : ℝ) : Matrix (Glyph B h) (Glyph B h) ℂ :=
  fun a b=>g.applyTo (fun x=>PhysMS.measured F none (J r) (d:=fun _ : Fin 2=>h)
    (WilsonMacroscopicRichFree.basis C B h ∘ ![a,b]) r x - integrand B M a b μ q (γ r) x)

theorem difference (h : ℕ) (g : Test 2) (μ : ℝ) (q : ℕ) (γ : ℝ→ℝ) {r : ℝ} (hr : 0<r) :
    defect B M F J h g μ q γ r = WilsonMacroscopicRichMeasuredGram.bank B F J h g r-jet B M h g μ q (γ r) := by
  ext a b
  change g.applyTo (PhysMS.measured F none (J r) (d:=fun _ : Fin 2=>h) (WilsonMacroscopicRichFree.basis C B h ∘ ![a,b]) r-integrand B M a b μ q (γ r))=_
  rw [test_sub _ _ (regular B F J a b hr) (scope B M a b μ q (γ r)) g,in_test B M]
  rfl

theorem at_zero (h : ℕ) (g : Test 2) (μ : ℝ) (q : ℕ) : jet B M h g μ q 0=MSSeparatedTestGram.matrix M h μ 0 g := by
  ext a b
  simp [jet,sum_range_succ']

theorem continuous (h : ℕ) (g : Test 2) (μ : ℝ) (q : ℕ) : Continuous (jet B M h g μ q) := by
  apply continuous_pi;intro a;apply continuous_pi;intro b
  exact continuous_finsetSum _ fun k _=>(Complex.continuous_ofReal.pow k).mul continuous_const

theorem original (hG : G.Simple) (L : PhysMS.Leading F J) (h : ℕ) (g : Test 2) (μ : ℝ) (q : ℕ) {γ : ℝ→ℝ}
    (hγ : Trace.Pilot.Coupling G γ) : Tendsto (defect B M F J h g μ q γ) Trace.Pilot.trail (𝓝 0) := by
  have named := (continuous B M h g μ q).continuousAt.tendsto.comp (hγ.conforms hG)
  rw [at_zero] at named
  have actual := WilsonMacroscopicRichMeasuredGram.original B F J L M h g μ
  have compare := actual.sub named
  rw [sub_self] at compare
  exact compare.congr' (RG17.positiveLength.mono fun r hr=>(difference B M F J h g μ q γ hr).symm)

end YM.Integration.WilsonMacroscopicRichSignedMS
