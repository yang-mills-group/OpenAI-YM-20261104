import YM.Integration.FVA1Physical.Sources.Round2.PhysicalKernelLawful
import YM.Integration.FVA1Physical.Sources.Round2.RetainedBoundaryTilt
import YM.Integration.FVA1Physical.Sources.Round2.FieldThermalStep

/-! Two consecutive physical blocking kernels with a genuine marked insertion.
The first incoming full Haar density and the second conditional mass are both
retained. On the purchased good collar only the covariance with a change of
the exterior retained bonds remains. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Set Filter Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk MSbar.Lis MSbar.Mosaic
open MSbar.Rolling MSbar.Bakery MSbar.Bakery.Film MSbar.Cacao Push.Uniform
open Pressure Comparison.RG02.Order RGComparison.Core16 RGComparison.Core16.Spool
open YM.Integration.FVA1Physical.Wilson Progress.DirectedRecipe Next.SectorChange
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

def externalScores (A : Issue G) (o : ι → Site A.f) (part : Bool) (V W : Config G A.c) : ℝ :=
  let φ:=fun U=>look part (tally J o U)
  let t:=retainedTilt A.S A.pre.beta V W
  let E:=expect A.S A.pre W
  (E (t*φ)-E t*E φ)/E t

theorem physical_exterior_score (A : Issue G) (o : ι → Site A.f) (part : Bool) (V W : Config G A.c)
    (branch : A.S.patch.Branches A.S.kernel G) {σ C δ Λ w : ℝ}
    (adm : ∀ U, Admitted U A.pre A.S σ C δ Λ w) :
    boundaryStencil J A o part V-boundaryStencil J A o part W=externalScores J A o part V W :=
  retained_covariance A.S branch A.pre V W _ (adm V).mass (adm W).mass

def coreBonds {c : Side} (Y : Support c) := univ.filter fun e : Bond c => e.1∈Y ∧ e.1+step e.2∈Y

theorem tilted_chamber (A : Issue G) {d : Side} (T : StepData d A.c) (F : Forest T.ratio)
    (X Y : Support A.c) (H : Voice G) (O : Config G d) (μ : Positions (Key F G))
    (cle : Clear G H) (sub : X⊆Y) {a b : ℝ} (ab : a ≤ b)
    (U : Config G A.c) (hit : U∈hotel F X Y H O μ a b) (V : Config G A.f) :
    let W:=chambers F Y H O μ U
    let U':=canoe (S:=T) F U
    retainedTilt A.S A.pre.beta U' W V =
      (∑ t,A.S.likelihood V t*A.S.noise A.pre.beta (A.S.prediction V t) W*
        exteriorTags A.S A.pre.beta (coreBonds Y) U' W V t) /
       (∑ t,A.S.likelihood V t*A.S.noise A.pre.beta (A.S.prediction V t) W) := by
  intro W U'
  apply retainedTilt_exterior
  intro e he
  exact cognizant F X Y H O μ cle sub hit ab e (mem_filter.mp he).2.1 (mem_filter.mp he).2.2

/-- Sharp replacement in the actual outer posterior, conditional on its live collar
and the already purchased single-step thermal reading. Its explicit covariance
is determined by the original kernel and source before either comparison. -/
theorem two_step_fields (A : Issue G) (χ : ChartRatio G) (p L : ℕ) (o : ι → Site A.f) (part : Bool)
    (b : Site A.f) (y η D : ℝ) (near : ∀ l : Slice J, separation b (legs J o l).1 ≤ L*closeN y)
    (branch : A.S.patch.Branches A.S.kernel G) (prem : Premier (main A.f A.pre.clip A.pre.path))
    (crit : Critical A.F A.pre.clip A.pre.path A.ρ) (pd : (mold A.pre A.F A.v).PosDef) (hg : 0 < A.fClock)
    (paid : ∀ Z, ‖A.fClock • Z‖ ≤ D*room y → PhysicalFieldComparison J A χ y η p L part b Z)
    {σ C δ Λ w : ℝ} (adm : ∀ U, Admitted U A.pre A.S σ C δ Λ w)
    {d : Side} (T : StepData d A.c) (R : Rep G A.c) (O : Config G d)
    {s c a l h : ℝ} (outer : Admitted O R T s c a l h)
    (F : Forest T.ratio) (X Y : Support A.c) (H : Voice G) (μ : Positions (Key F G))
    (cle : Clear G H) (sub : X⊆Y) (v rare : ℝ)
    (outside : chance T R O (hotel F X Y H O μ (pillow v) (room v))ᶜ ≤ rare)
    (inside : ∀ U∈hotel F X Y H O μ (pillow v) (room v),
      chambers F Y H O μ U∈regularInputs A.fClock (D*room y/A.fClock)) :
    let live:=hotel F X Y H O μ (pillow v) (room v)
    let copy:=chambers F Y H O μ
    let E:=expect T R O
    |E (boundaryStencil J A o part)-E (live.indicator (independentStencil J A χ p o part ∘ copy))| ≤
      stencilBound J*rare + |E (live.indicator (fun U => externalScores J A o part (canoe (S:=T) F U) (copy U)))| +
        A.fClock^((p:ℝ)+1-η) := by
  intro live copy E
  have inv:=boundaryStencil_invariant J A o part branch (adm 1).lawful
  have goodSet : MeasurableSet live := (garden_main F X Y H O μ cle sub).from_here
  have M : Measurable copy := (informed F X Y H O μ cle sub).1
  have cost:=true_posterior_exterior O outer goodSet (boundaryStencil_cont J A o part branch adm).measurable
    (independentStencil_meas J A χ p o part) M (stencilBound_pos J).le (Real.rpow_nonneg hg.le _)
    (fun U=>boundaryStencil_bounded J A o part U (adm U)) outside
    (fun U hit=>thermalStencil_price J A χ p L o part b y η D near branch prem crit pd hg paid (copy U) (inside U hit))
  have same (U) : boundaryStencil J A o part U-boundaryStencil J A o part (copy U)=
      externalScores J A o part (canoe (S:=T) F U) (copy U) := by
    rw [←physical_exterior_score J A o part (canoe (S:=T) F U) (copy U) branch adm]
    exact congrArg (·-boundaryStencil J A o part (copy U)) (inv (F.foldAt U) U).symm
  simp_rw [same] at cost
  exact cost

/-- If the purchased collar covers the period, the measured exterior covariance vanishes exactly. -/
theorem full_collar_fields (A : Issue G) (χ : ChartRatio G) (p L : ℕ) (o : ι → Site A.f) (part : Bool)
    (b : Site A.f) (y η D : ℝ) (near : ∀ l : Slice J, separation b (legs J o l).1 ≤ L*closeN y)
    (branch : A.S.patch.Branches A.S.kernel G) (prem : Premier (main A.f A.pre.clip A.pre.path))
    (crit : Critical A.F A.pre.clip A.pre.path A.ρ) (pd : (mold A.pre A.F A.v).PosDef) (hg : 0 < A.fClock)
    (paid : ∀ Z, ‖A.fClock • Z‖ ≤ D*room y → PhysicalFieldComparison J A χ y η p L part b Z)
    {σ C δ Λ w : ℝ} (adm : ∀ U, Admitted U A.pre A.S σ C δ Λ w)
    {d : Side} (T : StepData d A.c) (R : Rep G A.c) (O : Config G d)
    {s c a l h : ℝ} (outer : Admitted O R T s c a l h)
    (F : Forest T.ratio) (X Y : Support A.c) (H : Voice G) (μ : Positions (Key F G))
    (cle : Clear G H) (sub : X⊆Y) (v rare : ℝ)
    (outside : chance T R O (hotel F X Y H O μ (pillow v) (room v))ᶜ ≤ rare)
    (allY : Y=Finset.univ) (ab : pillow v ≤ room v)
    (inside : ∀ U∈hotel F X Y H O μ (pillow v) (room v),
      chambers F Y H O μ U∈regularInputs A.fClock (D*room y/A.fClock)) :
    let H₀:=hotel F X Y H O μ (pillow v) (room v)
    let copy:=chambers F Y H O μ
    let E:=expect T R O
    |E (boundaryStencil J A o part)-E (H₀.indicator (independentStencil J A χ p o part ∘ copy))| ≤
      stencilBound J*rare + A.fClock^((p:ℝ)+1-η) := by
  intro H₀ copy E
  have inv:=boundaryStencil_invariant J A o part branch (adm 1).lawful
  have good := (garden_main F X Y H O μ cle sub (A:=pillow v) (B:=room v)).from_here
  apply true_posterior_copy_agrees O outer good (boundaryStencil_cont J A o part branch adm).measurable
    (independentStencil_meas J A χ p o part) (informed F X Y H O μ cle sub).1
    (stencilBound_pos J).le (Real.rpow_nonneg hg.le _) (fun U=>boundaryStencil_bounded J A o part U (adm U)) outside
  · intro U hit
    have agree:=cognizant F X Y H O μ cle sub hit ab
    have eq : canoe (S:=T) F U=copy U := by
      funext e
      exact agree e (by simp [allY]) (by simp [allY])
    exact (inv (F.foldAt U) U).symm.trans (congrArg (boundaryStencil J A o part) eq)
  exact fun U hU=>thermalStencil_price J A χ p L o part b y η D near branch prem crit pd hg paid _ (inside U hU)

end YM.Integration.FVA1Physical.Round2.Curvature
