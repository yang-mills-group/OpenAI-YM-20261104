import YM.Integration.FVA1Physical.Wilson.BatchTests

/-! Independent test linearity for the *true* finite-history FVA2 coefficients
and a single remainder price before all bounded combinations of a fixed
admissible source bank. Both use the same normalized Haar integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson Tree Precision
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FVA2.CityHistory FormalOPE.RG10.MultiGauge Comparison.RG02
open scoped Classical Topology ContDiff BigOperators
variable {I : Type} [Fintype I] {G : Gauge} {n c : Side} (d : Descent n c)
  {Z : ChartRatio G} (hZ : LocalRatio Z) (h : d.Room G) (tag : d.Tags)
  (u : Pins G c) (a : ℕ→ℝ)

def scalarWilsonBank (Z : ChartRatio G) (O : Config G n→ℝ) : ℕ→ℝ :=
  term (Stack.read u (skyread Z d tag h (Delay.stones a) (exPay O)))

def testBank (w : I→ℝ) : (I→ℝ) →L[ℝ] ℝ := ∑ i,w i • ContinuousLinearMap.proj i

private theorem testBank_read (w : I→ℝ) (x : I→ℝ) : testBank w x = ∑ i,w i*x i := by
  simp [testBank,smul_eq_mul]

include h in
theorem conditioned_bank (F : I → Config G n→ℝ) (hc : ∀ i,Continuous (F i)) (β : ℕ→ℝ)
    (w : I→ℝ) (V : Config G c) :
    d.conditioned β (fun U=>∑ i,w i*F i U) V = ∑ i,w i*d.conditioned β (F i) V := by
  let W := fun U : Config G n=>fun i=>F i U
  have hW : Continuous W := continuous_pi hc
  have each (i : I) : d.conditioned β (F i) V = (d.conditioned β W V) i :=
    measured (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ) β (room_ok d h) hW V
  calc
    _ = d.conditioned β (testBank w ∘ W) V :=
      congrArg (fun O=>d.conditioned β O V) (funext fun U=>(testBank_read w (W U)).symm)
    _ = testBank w (d.conditioned β W V) := measured (testBank w) β (room_ok d h) hW V
    _ = _ := by
      rw [testBank_read]
      exact sum_congr rfl fun i _=>congrArg (w i*·) (each i).symm

include hZ in
theorem uniform_test_bank (F : I → Config G n→ℝ) (hc : ∀ i,Continuous (F i))
    (invar : ∀ i,GaugeInvariant (F i)) (hot : ∀ i,ContDiffAt ℝ ω
      ((F i) ∘ expLinks G (Edge (Site n))) 0) (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : I→ℝ), (∀ i, |w i| ≤ 1) →
      let O := fun U : Config G n=>∑ i,w i*F i U
      let A := scalarWilsonBank d h tag u a Z O
      (∀ i ≤ r, A i = ∑ j,w j * scalarWilsonBank d h tag u a Z (F j) i) ∧
      ∀ g> (0:ℝ), ‖d.conditioned (offset a g) O (expLinks G _ (g • u)) - peval A r g‖ ≤ K*g^(r+1) := by
  let E (j : I) := scalarWilsonBank d h tag u a Z (F j)
  have point (j : I) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g > (0:ℝ),
      ‖d.conditioned (offset a g) (F j) (expLinks G _ (g • u)) - peval (E j) r g‖ ≤ C*g^(r+1) := by
    obtain ⟨C,hC,rate⟩ := Wilson.all_coupling_price d hZ h tag u a (F j) (hc j) (invar j)
      (Assembly.GradeAt.unchecked (hot j)) r
    refine ⟨C,hC,fun g hg=>?_⟩
    change ‖d.conditioned (offset a g) (F j) (expLinks G _ (g • u)) -
      peval (fun i=>PowerSeries.coeff i (Stack.read u (skyread Z d tag h (Delay.stones a) (exPay (F j))))) r g‖ ≤ _
    simpa only [pow_zero,one_smul,Nat.zero_add] using rate g hg
  choose C hC rate using point
  refine ⟨∑ j,C j,sum_nonneg (fun j _=>hC j),?_⟩
  intro w bound O A
  let E' (i : ℕ) := ∑ j,w j * E j i
  have sumP (g : ℝ) : peval E' r g = ∑ j,w j*peval (E j) r g := by
    simp only [peval,Zone.eval,E',smul_eq_mul,mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun j _=> sum_congr rfl fun i _=> mul_left_comm .. 
  have component (g : ℝ) (hg : 0<g) :
      ‖d.conditioned (offset a g) O (expLinks G _ (g • u)) - peval E' r g‖ ≤ (∑ j,C j)*g^(r+1) := by
    rw [show d.conditioned (offset a g) O _ = _ from conditioned_bank d h F hc _ w _,sumP,←sum_sub_distrib,sum_mul]
    refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_ )
    rw [←mul_sub,norm_mul,Real.norm_eq_abs (w j)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (bound j)).trans (rate j g hg)
  have formal := Wilson.physical_ray d u a hZ h tag O
    (continuous_finsetSum _ (fun j _=>(hc j).const_mul (w j)))
    (fun k V=>sum_congr rfl (fun j _=>congrArg (w j*·) (invar j k V)))
    (ContDiffAt.sum fun j _=> contDiffAt_const.mul (hot j))
  have eqn (i : ℕ) (hi : i ≤ r) : A i=E' i := Laplace.trial_gap (formal r)
    ⟨∑ j,C j,sum_nonneg (fun j _=>hC j), eventually_pos.mono (fun g hg=>component g hg)⟩ i hi
  refine ⟨eqn,fun g hg=>?_⟩
  have eh : peval A r g = peval E' r g := sum_congr rfl fun i hi=>
    congrArg (fun x : ℝ=>g^i • x) (eqn i (Nat.lt_succ_iff.mp (mem_range.mp hi)))
  rw [eh]; exact component g hg
end YM.Integration.FVA1Physical.Round2
