import YM.Integration.FVA1Physical.Round2.FieldSharpSeason
import YM.Integration.FVA1Physical.Wilson.CoarseRows
import YM.Integration.FVA1Physical.Wilson.LocalExterior

/-! A genuine mixed stencil passed through its measured conditional Haar kernel
becomes a continuous field on the next boundary. The independent Wilson field
is the finite polynomial in the boundary logarithm, with its own interacting
vacuum normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Set Filter Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk MSbar.Lis MSbar.Mosaic
open MSbar.Rolling MSbar.Bakery MSbar.Bakery.Film MSbar.Cacao Push.Uniform
open Comparison.RG02.Order RGComparison.Core16 RGComparison.Core16.Spool
open YM.Integration.FVA1Physical.Wilson Progress.DirectedRecipe Next.SectorChange
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

def boundaryStencil (A : Issue G) (o : ι → Site A.f) (part : Bool) (W : Config G A.c) :=
  expect A.S A.pre W fun U => look part (tally J o U)

def independentStencil (A : Issue G) (χ : ChartRatio G) (p : ℕ) (o : ι → Site A.f)
    (part : Bool) (W : Config G A.c) :=
  ∑ i ∈ range (p+1), A.fClock^i * MvPolynomial.eval (chartLog A.fClock W)
    (PowerSeries.coeff i (emittedRows A χ (jointFieldBank J A o part) p))

theorem independentStencil_meas (A : Issue G) (χ : ChartRatio G) (p : ℕ) (o : ι → Site A.f) (part : Bool) :
    Measurable (independentStencil J A χ p o part) := by
  apply Finset.measurable_fun_sum
  intro i _
  exact measurable_const.mul ((MvPolynomial.continuous_eval _).measurable.comp (chartLog_meas _))

theorem boundaryStencil_bounded (A : Issue G) (o : ι → Site A.f) (part : Bool) (W : Config G A.c)
    {σ C δ Λ w : ℝ} (adm : Admitted W A.pre A.S σ C δ Λ w) :
    |boundaryStencil J A o part W| ≤ stencilBound J := by
  let K:=stencilBound J
  let φ:=fun U=>look part (tally J o U)
  have bound (U) : |φ U| ≤ K := stencil_bounded J o part U
  have env : Envelope φ := ⟨((look part).continuous.comp (tally_cont J o)).measurable,K,bound⟩
  have lo:=nn W adm env (Envelope.const (-K)) (fun U=>(abs_le.mp (bound U)).1)
  have hi:=nn W adm (Envelope.const K) env (fun U=>(abs_le.mp (bound U)).2)
  rw [e_const W adm] at lo hi
  exact abs_le.mpr ⟨lo,hi⟩

theorem boundaryStencil_cont (A : Issue G) (o : ι → Site A.f) (part : Bool)
    (branch : A.S.patch.Branches A.S.kernel G) {σ C δ Λ w : ℝ}
    (adm : ∀ V, Admitted V A.pre A.S σ C δ Λ w) : Continuous (boundaryStencil J A o part) := by
  let φ:=fun U=>look part (tally J o U)
  have env : Envelope φ := ⟨((look part).continuous.comp (tally_cont J o)).measurable,_,stencil_bounded J o part⟩
  have density:=A.pre.envelope (adm 1).lawful
  exact (continuous_push A.S A.pre.beta branch (φ*A.pre.eval) ((env.mul density).integrable _)).div
    (continuous_push A.S A.pre.beta branch A.pre.eval (density.integrable _)) (fun V=>(adm V).mass.ne')

theorem boundaryStencil_gauge (a : Levels G) (j n : ℕ)
    (R : Rep G (a.S.side (j+1) n)) (o : ι → Site (a.S.side (j+1) n)) (part : Bool)
    (env : Envelope R.eval) (inv : GaugeInvariant R.eval) :
    GaugeInvariant (fun W => expect (a.clock.op j n) R W fun U => look part (tally J o U)) := by
  let φ:=fun U=>look part (tally J o U)
  have e : Envelope φ := ⟨((look part).continuous.comp (tally_cont J o)).measurable,_,stencil_bounded J o part⟩
  have a₁:=push_orbit R.beta ((e.mul env).integrable _) (a:=a) (m:=j) (p:=n)
    (show GaugeInvariant (φ*R.eval) from fun k U=>congrArg₂ (·*·)
      (congrArg (look part) (tally_invariant J o k U)) (inv k U))
  have a₂:=push_orbit R.beta (env.integrable _) (a:=a) (m:=j) (p:=n) inv
  exact fun k U=>congrArg₂ (·/·) (a₁ k U) (a₂ k U)

theorem independentStencil_read (A : Issue G) (χ : ChartRatio G) (p : ℕ) (o : ι → Site A.f) (part : Bool)
    (branch : A.S.patch.Branches A.S.kernel G) (prem : Premier (main A.f A.pre.clip A.pre.path))
    (crit : Critical A.F A.pre.clip A.pre.path A.ρ) (pd : (mold A.pre A.F A.v).PosDef) (hg : 0 < A.fClock)
    (W : Config G A.c) :
    independentStencil J A χ p o part W =
      taste p (bulkColumn A χ (A.fClock • chartLog A.fClock W) (jointFieldBank J A o part) p) A.fClock := by
  unfold independentStencil taste
  apply sum_congr rfl
  intro i _
  apply congrArg (_ * ·)
  rw [emitted_read A χ _ p i branch prem crit pd,inv_smul_smul₀ hg.ne']

theorem thermalStencil_price (A : Issue G) (χ : ChartRatio G) (p L : ℕ) (o : ι → Site A.f) (part : Bool)
    (b : Site A.f) (y η D : ℝ) (near : ∀ l : Slice J, separation b (legs J o l).1 ≤ L*closeN y)
    (branch : A.S.patch.Branches A.S.kernel G) (prem : Premier (main A.f A.pre.clip A.pre.path))
    (crit : Critical A.F A.pre.clip A.pre.path A.ρ) (pd : (mold A.pre A.F A.v).PosDef) (hg : 0 < A.fClock)
    (paid : ∀ Z, ‖A.fClock • Z‖ ≤ D*room y → PhysicalFieldComparison J A χ y η p L part b Z)
    (W : Config G A.c) (good : W ∈ regularInputs A.fClock (D*room y/A.fClock)) :
    |boundaryStencil J A o part W-independentStencil J A χ p o part W| ≤ A.fClock^((p:ℝ)+1-η) := by
  let Z:=chartLog A.fClock W
  have h : ‖A.fClock • Z‖ ≤ D*room y := by
    rw [norm_smul,Real.norm_of_nonneg hg.le]
    exact (mul_le_mul_of_nonneg_left good.2 hg.le).trans_eq (by field_simp)
  have v:=paid Z h o near
  change |expect A.S A.pre (postcard G A.c A.fClock Z) _ - _| ≤ _ at v
  have same : postcard G A.c A.fClock Z=W := recover_chartLog hg.ne' W (Set.mem_univ_pi.mp good.1)
  rw [same] at v
  rw [independentStencil_read J A χ p o part branch prem crit pd hg W]
  exact v

end YM.Integration.FVA1Physical.Round2.Curvature
