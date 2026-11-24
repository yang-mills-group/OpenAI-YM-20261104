import YM.Integration.WilsonMacroscopicRichReportedPosterior
import YM.Push.LOCAL_SPLITTING.Response

/-! The true fixed-scale posterior as the smooth complete last Wilson transition at all lower fields. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichLastResponse
open Filter Function Set MeasureTheory Lattice Wilson RG Source OPE PhysMS Next.Foundations
open PhysicalNext.Repeat.Legato RGComparison.Core16 Push.Local Push.Local.Kernel
open scoped BigOperators Topology Classical
variable {G : Gauge} (R : Run G) {N p u : ℕ}

/-- Both inputs of the last step still carry every earlier Wilson transition. -/
theorem chart (T : Slices R.family.path.levels p) (live : u < N)
    (Y : Config G (R.family.side N p) → ℂ) (cont : Continuous Y) (inv : GaugeInvariant Y) :
    let H := R.family.path
    let S := H.levels.clock.op u p
    let β := H.β N p (u+1)
    let D := (H.rep N p (u+1)).eval
    let X := (traversal T live).weighted (line H p (u+1) N) Y
    Good S D X ∧ (traversal T live.le).conditioned (line H p u N) Y = response S β D X Finset.univ := by
  intro H S β D X
  let d := traversal T live
  let B := line H p (u+1) N
  have den : d.vacuum (G:=G) B = D := vacuum_eq T R.makes.wilson live
  have di : Integrable D (prior G _) := by
    rw [←den]
    exact Descent.output_integrable (traversal_ok T live) B (bare_integrable _)
  have ds : GaugeInvariant D := by
    rw [←den]; exact Descent.output_invariant (traversal_ok T live) B (bare_integrable _) (fun t U => bare_gauge _ _ _)
  have xs : GaugeInvariant X := by
    apply Descent.output_invariant (traversal_ok T live) B
    · exact ((bare_cont _).smul cont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · intro t U
      change bare (B d.depth) (Lattice.gauge t U) • Y (Lattice.gauge t U) = bare (B d.depth) U • Y U
      rw [bare_gauge,inv t U]
  refine ⟨⟨(H.levels.blocks u p).branches,di,weighted_integrable T live Y cont,
    fun U => den ▸ Descent.positive B (traversal_ok T live) U,ds,xs⟩,?_⟩
  funext V
  have low : (traversal T live.le).vacuum (G:=G) (line H p u N) = S.push β D :=
    (vacuum_eq (m:=u) T R.makes.wilson live.le).trans (R.makes.wilson.steps N p u live).1
  have num : (traversal T live.le).weighted (line H p u N) Y = S.push β X := weighted_step T Y live
  rw [Descent.conditioned,low,num]
  change ((S.push β D V)⁻¹) • (S.push β X V) = (S.push β X V) / ((S.push β D V : ℝ) : ℂ)
  rw [Complex.real_smul,Complex.ofReal_inv,div_eq_inv_mul]

/-- Smoothing is purchased by the last positive stage for the whole signed field, including hard histories. -/
theorem regular (T : Slices R.family.path.levels p) (live : u < N) (h : ℕ)
    (Y : Config G (R.family.side N p) → ℂ) (cont : Continuous Y) (inv : GaugeInvariant Y) :
    (R.family.path.rep N p u).p.Regular Finset.univ
      (WilsonMacroscopicRichReportedPosterior.observation R T live.le h Y) := by
  obtain ⟨good,full⟩ := chart R T live Y cont inv
  let P := (R.family.path.rep N p u).p
  have he : edges (Finset.univ : Support (R.family.side u p)) = Finset.univ := by ext e; simp [edges]
  change P.Regular _ ((R.family.S.a u : ℂ)^h • (traversal T live.le).conditioned (line R.family.path p u N) Y)
  rw [full,←he]; exact regular_smul _ (response_regular _ _ P good)

/-- Signed last-kernel derivative before the last Haar integral, for the complete numerator and vacuum. -/
theorem signed (T : Slices R.family.path.levels p) (live : u < N)
    (Y : Config G (R.family.side N p) → ℂ) (cont : Continuous Y)
    (l : List (Directions G (R.family.side u p))) (V : Config G (R.family.side u p)) :
    let H := R.family.path
    let S := H.levels.clock.op u p
    let β := H.β N p (u+1)
    let D := (H.rep N p (u+1)).eval
    let X := (traversal T live).weighted (line H p (u+1) N) Y
    let K := fun U => weights S U (fun Q => leftDerivs (noisy S β Finset.univ Q) l V)
    leftDerivs ((traversal T live.le).weighted (line H p u N) Y) l V = (∫ U,K U • X U ∂prior G _) ∧
    leftDerivs (H.rep N p u).eval l V = (∫ U,K U • D U ∂prior G _) := by
  intro H S β D X K
  have di : Integrable D (prior G _) := by
    change Integrable (H.rep N p (u+1)).eval _
    rw [←vacuum_eq T R.makes.wilson live]
    exact Descent.output_integrable (traversal_ok T live) _ (bare_integrable _)
  have num : (traversal T live.le).weighted (line H p u N) Y = S.push β X := weighted_step T Y live
  have den : (H.rep N p u).eval = S.push β D := (R.makes.wilson.steps N p u live).1
  rw [num,den]
  exact ⟨left_pass S β Finset.univ (H.levels.blocks u p).branches (weighted_integrable T live Y cont) V l,
    left_pass S β Finset.univ (H.levels.blocks u p).branches di V l⟩

end YM.Integration.WilsonMacroscopicRichLastResponse
