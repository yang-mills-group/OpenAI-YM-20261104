import YM.Integration.FVA1Physical.Wilson.BatchHistory
import YM.Integration.FVA1Physical.Sources.TestedFields

/-! A true complete mixed-payoff table on the physical clock. One price
is chosen before all independent bounded choices of signs or phases on
the marker modes and before the positive coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Function MeasureTheory Lattice RG YM.Wilson Tree Precision Marker
open LocalLTE.Sail Source MergeProof MergeProof.Accent Comparison.RG02 PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FVA2.CityHistory FormalOPE.RG10 FormalOPE.RG10.MultiGauge Pert.Asymptotics
open scoped Classical Topology ContDiff
variable {G : Gauge} {I : Type} [DecidableEq I] {n N m : ℕ}
    (R : Census I) (A : Run G) (Y : Batch A.family.path N n I) (T : Slices A.family.path.levels n)
    (hm : m ≤ N) (h : (traversal T hm).Room G) (t : (traversal T hm).Tags)
    (u : Pins G (A.family.side m n))

def batchComponent (s : R.Mode) (L : ℂ →L[ℝ] ℝ) (r : ℕ) (g : ℝ) :=
  let d := traversal T hm
  let a := actualOffset A.family n N m
  let Z := (RunFormalChain.fromRun A).O
  peval (term (Stack.read u (skyread Z d t h (Delay.stones a) (exPay (L ∘ fullProduct Y.wavelengths s.val))))) r g

def batchQuote (r : ℕ) (g : ℝ) : Poly R := Poly.inject fun s =>
  ⟨batchComponent R A Y T hm h t u s Complex.reCLM r g,
   batchComponent R A Y T hm h t u s Complex.imCLM r g⟩

theorem batch_test_price (r : ℕ) :
    let d := traversal T hm
    let a := actualOffset A.family n N m
    let V (g : ℝ) := expLinks G _ (g • u)
    let E := batchQuote R A Y T hm h t u r
    let g₀ := regulatorRun A.family N n N
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ g > (0:ℝ), let X := d.moments R (offset a g) Y.wavelengths (V g) - E g
        Poly.price (fun _=>1) X ≤ C*g^(r+1) ∧
        ∀ τ : R.Mode → ℂ, (∀ s, ‖τ s‖ ≤ 1) → ‖modeTest τ X‖ ≤ C*g^(r+1)) ∧
      let X := Round2.momentTable R Y m hm (V g₀) - E g₀
      Poly.price (fun _=>1) X ≤ C*g₀^(r+1) ∧
        ∀ τ : R.Mode → ℂ, (∀ s, ‖τ s‖ ≤ 1) → ‖modeTest τ X‖ ≤ C*g₀^(r+1) := by
  intro d a V E g₀
  choose C hC all at0 using (fun s B => measured_batch R A Y T hm h t u s B r)
  let cap (s : R.Mode) := C s Complex.reCLM + C s Complex.imCLM
  let M := ∑ s, cap s
  have full (g : ℝ) (X : Poly R) (price : ∀ s B, ‖B (X.part s) - batchComponent R A Y T hm h t u s B r g‖ ≤ C s B*g^(r+1)) :
      Poly.price (fun _=>1) (X-E g) ≤ M*g^(r+1) := by
    change Poly.price _ _ ≤ (∑ s, cap s)*_
    rw [Finset.sum_mul]
    unfold Poly.price
    apply Finset.sum_le_sum
    intro s _
    simp only [Poly.toll,Finset.prod_const_one,one_mul]
    let z := (X-E g).part s
    have re : ‖z.re‖ ≤ C s Complex.reCLM*g^(r+1) := price s Complex.reCLM
    have im : ‖z.im‖ ≤ C s Complex.imCLM*g^(r+1) := price s Complex.imCLM
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    change _ ≤ (C s Complex.reCLM + C s Complex.imCLM) * _
    rw [add_mul]
    exact add_le_add re im
  have grant (g : ℝ) (X : Poly R) (p : Poly.price (fun _=>1) X ≤ M*g^(r+1)) :
      Poly.price (fun _=>1) X ≤ M*g^(r+1) ∧ ∀ τ : R.Mode → ℂ, (∀ s, ‖τ s‖ ≤ 1) → ‖modeTest τ X‖ ≤ M*g^(r+1) :=
    ⟨p,fun τ hτ=>(norm_modeTest_le_price τ X hτ).trans p⟩
  refine ⟨M,Finset.sum_nonneg (fun s _=>add_nonneg (hC s _) (hC s _)),?_,?_⟩
  · intro g hg; exact grant g _ (full g _ (fun s B=>all s B g hg))
  exact grant g₀ _ (full g₀ _ (fun s B=>at0 s B))

end YM.Integration.FVA1Physical.Wilson
