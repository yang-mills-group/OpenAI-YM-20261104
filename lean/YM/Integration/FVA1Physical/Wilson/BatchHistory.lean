import YM.Integration.FVA1Physical.Wilson.BatchFields
import YM.Integration.FVA1Physical.Wilson.SceneLedger
import YM.Integration.FVA1Physical.Wilson.MovingAllCouplings

/-! The entire actual mixed moment table of a physical C18 batch is the
same normalized trajectory as the FVA2 skyreading. This permits arbitrary
physical voices, placements and real tests, even on a nonflat coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Function MeasureTheory Lattice RG YM.Wilson Tree Precision Marker
open LocalLTE.Sail Source MergeProof MergeProof.Accent Comparison.RG02 PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FVA2.CityHistory FormalOPE.RG10 FormalOPE.RG10.MultiGauge Pert.Asymptotics
open MSbar MSbar.Rolling MSbar.Midpoint
open scoped Classical Topology ContDiff
variable {G : Gauge} {I : Type} [DecidableEq I] {H : History G} {n N m : ℕ}
    (R : Census I) (Y : Batch H N n I) (T : Slices H.levels n) (hm : m ≤ N)

private theorem weighted_gust (sel : H.Selected) (f : Config G (H.S.side N n) → ℂ) :
    (traversal T hm).weighted (line H n m N) f =
      gust H N n N (fun v => (H.rep N n N).eval v • f v) m hm := by
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [traversal_self,weighted,depth,output_nil,gust_base,(sel.starts N n).2]
    rfl
  | of_succ j hj ih => rw [weighted_step T f hj,gust_step H N n N _ hj,ih]

theorem momentTable_descent (sel : H.Selected) (s : R.Mode) (v : Config G (H.S.side m n)) :
    (Round2.momentTable R Y m hm v).part s =
      ((traversal T hm).moments R (line H n m N) Y.wavelengths v).part s := by
  let O := fullProduct Y.wavelengths s.val
  let f := fun x => (H.rep N n N).eval x • O x
  have eqn : (fun x => ((H.rep N n N).eval x)⁻¹ • f x) = O := by
    funext x
    exact inv_smul_smul₀ (SectorNext.Vacuum.strictly H sel N n N le_rfl x).ne' _
  have e := congrFun (Round2.conditionalPath_gust H sel N n f m hm) v
  rw [eqn,← weighted_gust T hm sel O] at e
  change Round2.conditionalPath H N n O m hm v = _
  rw [e,moment_part,conditioned,vacuum_eq T sel hm]

open RGComparison.Core16.Spool in
theorem tested_batch (s : R.Mode) (B : ℂ →L[ℝ] ℝ) :
    let O := fullProduct Y.wavelengths s.val
    Continuous O ∧ GaugeInvariant O ∧
      ContDiffAt ℝ ω ((B ∘ O) ∘ expLinks G (Edge (Site (H.S.side N n)))) 0 := by
  intro O
  have W i := wavelength_witnessed H N n Y i
  exact ⟨continuous_finsetProd _ fun i _ => (W i).1,
    fun u v => Finset.prod_congr rfl fun i _ => (W i).2.1 u v,
    B.contDiff.contDiffAt.comp 0 (contDiffAt_prod (fun i _ => (W i).2.2))⟩

variable (room : (traversal T hm).Room G) (tag : (traversal T hm).Tags)
    (u : Pins G (H.S.side m n))

/-- Two positive-coupling statements for the fixed actual mixed product.
The first is its genuine all-order expansion along the retained scene's
analytic coupling trajectory. -/
theorem scene_batch {Z : ChartRatio G} {U : Horizon H.levels} {K : Kin U Z} {k r : ℕ} {e : G.Color}
    (S : Scene H.levels n r) (hs : Realized K N n k r e S) (lo : k ≤ m)
    (hZ : LocalRatio Z) (s : R.Mode) (B : ℂ →L[ℝ] ℝ) :
    let d := traversal T hm
    let O := fullProduct Y.wavelengths s.val
    let z := formalSceneClock S N m
    Aspiration (fun g : ℝ => B ((d.moments R (sceneTemperatures S m g) Y.wavelengths
      (expLinks G _ (g • u))).part s))
      (term (Stack.read u (skyread Z d tag room z (exPay (B ∘ O))))) := by
  intro d O z
  obtain ⟨hc,hi,hot⟩ := tested_batch R Y s B
  have h := varied_physical d u (relativeSceneClock S m) hZ room tag z
    (priced_clock S hs T hm lo) (B ∘ O) (B.continuous.comp hc) (fun k V=>congrArg B (hi k V)) hot
  have law (g : ℝ) : sceneTemperatures S m g=clockAt (relativeSceneClock S m) g := funext (clock_measures S m g)
  simp_rw [moment_part,law,← measured B _ (room_ok d room) hc]
  exact h

variable (A : Run G) {p j l : ℕ} (Y₁ : Batch A.family.path N p I) (T₁ : Slices A.family.path.levels p)
    (hj : j ≤ N) (h : (traversal T₁ hj).Room G) (t : (traversal T₁ hj).Tags) (v : Pins G (A.family.side j p))

/-- At the measured point the physical `momentTable` uses the very same
cutoff, positions, field/motion/engineering normalizations and denominator.
The finite-geometry constant is selected before the varying coupling. -/
theorem measured_batch (s : R.Mode) (B : ℂ →L[ℝ] ℝ) (r : ℕ) :
    let d := traversal T₁ hj
    let a := actualOffset A.family p N j
    let Z := (RunFormalChain.fromRun A).O
    let V (g : ℝ) := expLinks G _ (g • v)
    let E := term (Stack.read v (skyread Z d t h (Delay.stones a) (exPay (B ∘ fullProduct Y₁.wavelengths s.val))))
    let g₀ := regulatorRun A.family N p N
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ g > (0:ℝ), ‖B ((d.moments R (offset a g) Y₁.wavelengths (V g)).part s) - peval E r g‖ ≤ C*g^(r+1)) ∧
      ‖B ((Round2.momentTable R Y₁ j hj (V g₀)).part s) - peval E r g₀‖ ≤ C*g₀^(r+1) := by
  intro d a Z V E g₀
  let O := fullProduct Y₁.wavelengths s.val
  obtain ⟨hc,hi,hot⟩ := tested_batch R Y₁ s B
  obtain ⟨C,hC,rate⟩ := all_coupling_price d (RunFormalChain.fromRun A).receipt h t v a (B ∘ O)
    (B.continuous.comp hc) (fun k U=>congrArg B (hi k U)) (Assembly.GradeAt.unchecked hot) r
  have all (g : ℝ) (hg : 0 < g) : ‖B ((d.moments R (offset a g) Y₁.wavelengths (V g)).part s) - peval E r g‖ ≤ C*g^(r+1) := by
    change ‖B (d.conditioned (offset a g) O (V g)) - peval E r g‖ ≤ _
    rw [← measured B _ (room_ok d h) hc]
    have e := rate g hg
    rw [pow_zero,one_smul] at e
    simp_rw [Nat.zero_add] at e
    change ‖d.conditioned (offset a g) (B ∘ O) (expLinks G _ (g • v)) -
      peval (fun i => PowerSeries.coeff i (Stack.read v (skyread Z d t h (Delay.stones a) (exPay (B ∘ O))))) r g‖ ≤ _
    exact e
  refine ⟨C,hC,all,?_⟩
  have own := all g₀ (Local.RealStep.coupling_pos A.family N p N A.makes le_rfl)
  rw [show offset a g₀ = line A.family.path p j N from line_offset A.makes] at own
  rw [momentTable_descent R Y₁ T₁ hj A.makes.wilson]
  exact own

end YM.Integration.FVA1Physical.Wilson
