import YM.Integration.WilsonAddressedCollarFolds
import YM.Integration.WilsonSeparatedOffsetSites
import YM.Integration.WilsonOriginalThermometerFineCells

/-! Clear the original Wilson equation stencils on every occupied microscopic
    placement before returning the complete graded reading on a coarser cell. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedCollarEquations
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox OPE OPE.Orbits
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonOffsetReportingProducts
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "χ" r:max N:max p:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,p)
local notation "wt" => WilsonSeparatedOriginalThermometerCells.weight
private def horizon (i : Fin 3) : ℕ := (grade i).val

/-- One fixed microscopic distance clears every query, including the
    alternative equation stencil at each of the three genuinely different sites. -/
theorem clearance (V : ∀ t, SectionData (R.family.labels.level t)) (radius : ℕ → ℕ)
    (φ : Test 3) (legal : tsupport φ ⊆ conf 3) :
    ∃ (K : ℝ) (p₀ : ℕ), 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ p ≥ p₀, ∀ r : ℝ,
      0 < r → r ≤ 1 → R.family.S.a N * K ≤ r →
      ∀ o, wt φ (χ r N p) o ≠ 0 → Avoids (C:=R.family) V radius horizon o := by
  obtain ⟨c,cp,late⟩ := WilsonOriginalThermometerFineCells.separated R.family.S
    φ.hasCompactSupport legal
  obtain ⟨p₀,geometric⟩ := eventually_atTop.1 late
  choose vsize vfixed using fun i : Fin 3 => WilsonSeparatedOffsetSites.footprint (V (horizon i))
  choose asize afixed using fun i : Fin 3 => WilsonSeparatedOffsetSites.footprint (R.family.localSection (horizon i))
  let b := univ.sup (fun i : Fin 3 => radius (horizon i)) + (univ.sup vsize ⊔ univ.sup asize)
  let K : ℝ := ((b:ℝ)+3)/c
  refine ⟨K,p₀,div_pos (by positivity) cp,?_⟩
  filter_upwards [eventually_all.mpr vfixed,eventually_all.mpr afixed] with N vpaid apaid p hp r hr hs room o nonzero
  obtain ⟨x,hx,atSite⟩ := WilsonOriginalThermometerFineCells.occupied φ (χ r N p) o nonzero
  have enough : R.family.S.a N*((b:ℝ)+3) ≤ r*c := by
    apply (div_le_iff₀ cp).mp
    simpa only [K,mul_div_assoc] using room
  intro i j ij
  have far := geometric p hp N r hr hs x hx j i (Ne.symm ij)
  change r*c-2*R.family.S.a N ≤ R.family.S.a N*separation ((χ r N p) x j) ((χ r N p) x i) at far
  rw [atSite] at far
  have span : b < separation (o j) (o i) := by
    have ordered : R.family.S.a N*(b:ℝ) < R.family.S.a N*(separation (o j) (o i):ℕ) := by
      nlinarith only [far,enough,R.family.S.a_pos N]
    exact_mod_cast lt_of_mul_lt_mul_left ordered (R.family.S.a_pos N).le
  have rh : radius (horizon i) ≤ univ.sup (fun k : Fin 3 => radius (horizon k)) :=
    le_sup (f:=fun k : Fin 3 => radius (horizon k)) (mem_univ i)
  have vh : vsize j ≤ univ.sup vsize ⊔ univ.sup asize :=
    (le_sup (f:=vsize) (mem_univ j)).trans le_sup_left
  have ah : asize j ≤ univ.sup vsize ⊔ univ.sup asize :=
    (le_sup (f:=asize) (mem_univ j)).trans le_sup_right
  dsimp only [b] at span
  constructor
  · intro y hy
    have foot := apaid j p (o j) y hy
    have length := separation_triangle (o j) y (o i)
    rw [separation_comm (o j) y] at length
    change radius (horizon i) < separation y (o i)
    omega
  · intro y hy
    have foot := vpaid j p (o j) y hy
    have length := separation_triangle (o j) y (o i)
    rw [separation_comm (o j) y] at length
    change radius (horizon i) < separation y (o i)
    omega

def correctedRow (V : ∀ t, SectionData (R.family.labels.level t))
    (P : ∀ t, (ℕ × ℕ) → (R.family.label t ≃ₗ[ℂ] R.family.label t)) (b : Presentation R.family)
    (A : Group R.family 6) (z : UVIndex) (o : Fin 3 → Site (R.family.side z.1 z.2)) (s : Badge) : ℂ :=
  moment (R.family.beta z.1 z.2) (fun U => ∏ i, corrected R.family (V (horizon i)) z.1 z.2 (P (horizon i) z) b
    (A.station.wheel.atCut z (index A (grade i)) (vector A s i)) (o i) U)

/-- At every configuration of sites supported by the original compact test the
    complete measured face equals its projected primary plus signed equation
    discrepancy, after integration on the original Wilson probability. -/
theorem original (simple : G.Simple) :
    ∃ (V : ∀ t, SectionData (R.family.labels.level t)) (W : Mark.Weave G)
      (P : ∀ t, (ℕ × ℕ) → (R.family.label t ≃ₗ[ℂ] R.family.label t)) (b : Presentation R.family),
      (∀ t, Mark.Portfolio R.family.params (V t) (W t)) ∧
      Hearthside R.family V W P b (Bandage.fly R.alloy.B.a) ∧
      ∀ (φ : Test 3), tsupport φ ⊆ conf 3 → ∃ (K : ℝ) (p₀ : ℕ), 0 < K ∧
      ∀ᶠ N : ℕ in atTop, ∀ p ≥ p₀, ∀ r : ℝ, 0 < r → r ≤ 1 → R.family.S.a N * K ≤ r →
      ∀ (A : Group R.family 6) {w : ℕ} (wN : w ≤ N) (read : (Badge → ℂ) → ℂ),
        let cell := R.family.S.toDepth wN p
        φ.applyTo (fun y => read (row A (N,p) ((χ r N p) y))) =
          ∑ parent : Fin 3 → Site (R.family.side w p), ∑ t : Fin 3 → Site cell.count,
            let o := fun i => cell.assemble (parent i,t i)
            wt φ (χ r N p) o * read (correctedRow R V P b A (N,p) o) := by
  obtain ⟨V,W,P,b,radius,funds,law,erase⟩ := WilsonOffsetReportingProducts.purchased R simple
  refine ⟨V,W,P,b,funds,law,fun φ legal => ?_⟩
  obtain ⟨K,p₀,pos,geometric⟩ := clearance R V radius φ legal
  refine ⟨K,p₀,pos,?_⟩
  filter_upwards [geometric,erase (Fin 3) horizon] with N geo cancel p hp r hr cap mesh A w wN read
  let z : UVIndex := (N,p)
  have fold := (WilsonAddressedCollarFolds.original A r z wN φ read).1
  rw [fold]
  apply Finset.sum_congr rfl
  intro parent _
  apply Finset.sum_congr rfl
  intro t _
  let cell := R.family.S.toDepth wN p
  let o := fun i => cell.assemble (parent i,t i)
  by_cases live : wt φ (χ r N p) o = 0
  · change wt φ (χ r N p) o * _ = wt φ (χ r N p) o * _
    simp only [live,zero_mul]
  · change wt φ (χ r N p) o * read (row A z o) = _ * read (correctedRow R V P b A z o)
    congr 1
    apply congrArg read
    funext s
    let v := fun i : Fin 3 => A.station.wheel.atCut z (index A (grade i)) (vector A s i)
    have fixed := cancel p v o (fun _ => 1) (geo p hp r hr cap mesh o live)
      (fun _ _ _ _ => rfl) (Mark.cont_envelope continuous_const)
    rw [WilsonPositionThermometerJointFaces.ensemble]
    change Wilson.moment (R.family.beta N p) (fun U => ∏ i, R.family.O N p (v i) (o i) U) =
      Wilson.moment (R.family.beta N p) (fun U => ∏ i,
        corrected R.family (V (horizon i)) N p (P (horizon i) (N,p)) b (v i) (o i) U)
    simp only [mul_one] at fixed
    convert fixed using 3
    congr

end YM.Integration.WilsonAddressedCollarEquations
