import YM.Integration.WilsonGraphAppointedMixedShapeJets
import YM.GradedFar.Operands
import YangMills.WilsonProof.NativeSupport.SeparatedCorrelationBounds

noncomputable section
namespace YM.Integration.WilsonGraphUniformMixedShapeMass

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level FVA2.GradedFar
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff Integration.GradedFar.Tariff.Sunshine
open scoped Topology BigOperators Classical ContDiff

section Fields
variable {G : Gauge} {C : Family G} {S : Table C.book} {e : Extraction.Order}
variable {n : ℕ} {d : Fin n → ℕ}

/-- The filed all-center moment is multilinear on the actual, individually graded
fields, with precisely the original coefficients of each tensor of basis fields. -/
theorem fieldExpansion (F : Final C e S) (P : ℝ → tower S) (viewer : Viewers F)
    (o : E4) (r : ℝ) (x : Points n) (v : Inputs G d) :
    TrueCompact F P viewer r o x v =
      ∑ q : Picks G d, multipliers v q * TrueCompact F P viewer r o x (basisWord q) := by
  let M := OPE.Orbits.moment (S := S) (d := d) (spectator F viewer) (sites o r x)
  let f := M.compLinearMap (fun i => (assign P r (d i)).toLinearMap)
  exact basis_sum f v

/-- On the open separated chart each heat coefficient is the filed multilinear
arena on the same raised inputs. Its finite truncation preserves every basis term. -/
theorem formalExpansion (X : FVA2.Scale.Arenas G) {h : ℕ} (within : Through h d)
    (p : ℕ) (clock : ℝ) {x : Points n} (hx : x ∈ conf n) (v : Inputs G d) :
    FVA2.GradedFar.crop p clock (sent X h x (raised within v)) =
      ∑ q : Picks G d, multipliers v q *
        FVA2.GradedFar.crop p clock (sent X h x (raised within (basisWord q))) := by
  let M (k : ℕ) := (X h n ⟨x,hx⟩ k).compLinearMap (fun i => Normalize.up (within i))
  have row (k : ℕ) (u : Inputs G d) : PowerSeries.coeff k (sent X h x (raised within u)) = M k u :=
    cashed X (raised within u) hx k
  simp only [FVA2.GradedFar.crop_eq, row, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [basis_sum (M k) v, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [smul_eq_mul]
  ring

/-- Every chronological Cartesian derivative may be taken termwise, with the
label multipliers fixed while the insertion points vary over the separated chart. -/
theorem coordinateExpansion (f : Inputs G d → Points n → ℂ)
    (expand : ∀ v x, x ∈ conf n → f v x = ∑ q : Picks G d, multipliers v q * f (basisWord q) x)
    (smooth : ∀ q : Picks G d, ContDiffOn ℝ ∞ (f (basisWord q)) (conf n))
    (word : TraceOrder n) {x : Points n} (hx : x ∈ conf n) (v : Inputs G d) :
    δ word (f v) x = ∑ q : Picks G d, multipliers v q * δ word (f (basisWord q)) x := by
  rw [δ_congr (conf_open n) (fun y hy => expand v y hy) word hx]
  rw [δ_sum (conf_open n) Finset.univ (fun q y => multipliers v q * f (basisWord q) y)
    (fun q _ => contDiffOn_const.mul (smooth q)) word hx]
  apply Finset.sum_congr rfl
  intro q hq
  exact δ_const_mul (conf_open n) (smooth q) (multipliers v q) word hx
end Fields

/-- A finite family of scalar prices gives one price independent of the label.
The multiplicities remain in the original sums even when individual entries coincide. -/
theorem sumPrice {ι : Type*} [Fintype ι] (weight actual formal : ι → ℂ) (C : ι → ℝ)
    (M t : ℝ) (hM : 0 ≤ M) (hw : ∀ i, ‖weight i‖ ≤ M)
    (hp : ∀ i, ‖actual i - formal i‖ ≤ C i * t) :
    ‖(∑ i, weight i * actual i) - ∑ i, weight i * formal i‖ ≤ (∑ i, C i) * M * t := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    ‖∑ i, weight i * (actual i - formal i)‖ ≤ ∑ i, ‖weight i * (actual i - formal i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, M * (C i * t) := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul (hw i) (hp i) (norm_nonneg _) hM
    _ = (∑ i, C i) * M * t := by
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem dualBound {σ ι : Type*} [Fintype ι] (V : Submodule ℂ (MvPolynomial σ ℂ))
    (b : Module.Basis ι ℂ V) (L : V →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V,
      ‖L v‖ ≤ C * ∑ m ∈ v.val.support, ‖MvPolynomial.coeff m v.val‖ := by
  classical
  let s := Finset.univ.biUnion fun i : ι => (b i).val.support
  have expand (v : V) : v.val = ∑ i, b.repr v i • (b i).val := by
    calc
      v.val = V.subtype (∑ i, b.repr v i • b i) := congrArg V.subtype (b.sum_repr v).symm
      _ = _ := by rw [map_sum]; simp
  have support (v : V) : v.val.support ⊆ s := by
    intro m hm
    by_contra missing
    have zero (i : ι) : MvPolynomial.coeff m (b i).val = 0 :=
      MvPolynomial.notMem_support_iff.mp fun present =>
        missing (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, present⟩)
    apply (MvPolynomial.mem_support_iff.mp hm)
    rw [expand v, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro i _
    simp [MvPolynomial.coeff_smul, zero i]
  obtain ⟨W, hW⟩ := V.exists_isCompl
  let extension := L.comp (V.projectionOnto W hW)
  have restrict (v : V) : extension v.val = L v := by
    simp only [extension, LinearMap.comp_apply, Submodule.projectionOnto_apply_left]
  let column (m : σ →₀ ℕ) := ‖extension (MvPolynomial.monomial m (1 : ℂ))‖
  let C := ∑ m ∈ s, column m
  refine ⟨C, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro v
  have value : L v = ∑ m ∈ v.val.support, MvPolynomial.coeff m v.val *
      extension (MvPolynomial.monomial m (1 : ℂ)) := by
    calc
      L v = extension v.val := (restrict v).symm
      _ = extension (∑ m ∈ v.val.support, MvPolynomial.monomial m (MvPolynomial.coeff m v.val)) :=
        congrArg extension (MvPolynomial.as_sum v.val)
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro m _
        have hm : MvPolynomial.monomial m (MvPolynomial.coeff m v.val) =
            MvPolynomial.coeff m v.val • MvPolynomial.monomial m (1 : ℂ) := by
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [hm, map_smul, smul_eq_mul]
  rw [value]
  calc
    _ ≤ ∑ m ∈ v.val.support, ‖MvPolynomial.coeff m v.val * extension (MvPolynomial.monomial m 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ v.val.support, C * ‖MvPolynomial.coeff m v.val‖ := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Finset.single_le_sum (fun a _ => show 0 ≤ column a from norm_nonneg _)
        (support v hm)
    _ = _ := (Finset.mul_sum ..).symm

theorem coefficientBound (g : YangMills.GaugeGroup) (d : ℕ) (q : FVA2.Dframe.Toon g.core d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Sec g.core d, ‖FVA2.O.Score.coord q v‖ ≤
      C * YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) v := by
  exact dualBound _ (MS.Theater.Daylight (FVA2.Press.portDeck g.core) d) (FVA2.O.Score.coord q)

theorem multipliersMass (g : YangMills.GaugeGroup) {n : ℕ} (d : Fin n → ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (v : Inputs g.core d) (q : Picks g.core d),
      ‖multipliers v q‖ ≤ D * ∏ i, YangMills.Matching.sectorMass
        (B := YangMills.maxwellReference g) (v i) := by
  classical
  choose C positive price using fun (i : Fin n) (t : FVA2.Dframe.Toon g.core (d i)) =>
    coefficientBound g (d i) t
  let factor (i : Fin n) := ∑ t, C i t
  have nonnegative (i : Fin n) : 0 ≤ factor i := Finset.sum_nonneg fun t _ => positive i t
  refine ⟨∏ i, factor i, Finset.prod_nonneg (fun i _ => nonnegative i), ?_⟩
  intro v q
  rw [multipliers, norm_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i _
  apply (price i (q i) (v i)).trans
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun t _ => positive i t)
    (Finset.mem_univ (q i))) (YangMills.Matching.sectorMass_nonneg _)


section Appointed

universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : Axis}
variable {O : OrderS g.core} {E : Construction.{u} H ε e O} {ξ : Extraction.Order}
variable (Z : WilsonPrescription g.core) (V : Vision E ξ) (Q : Perspective H Z true)

local notation "field" => V.pupil.last
local notation "W" => V.Post Z
local notation "X" => FVA2.Scale.Measure.outlook Z.scheme Z.criterion
local notation "t" => V.T Z

def inputMass (g : YangMills.GaugeGroup) {n : ℕ} {d : Fin n → ℕ} (v : Inputs g.core d) : ℝ :=
  ∏ i, YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) (v i)

include Q in
theorem coordinateMass {ι : Type} (l : Filter ι) (r : ι → ℝ) (scale : Tendsto r l trail)
    {n h : ℕ} {d : Fin n → ℕ} (within : Through h d)
    (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n) (p : ℕ) (word : TraceOrder n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in l, ∀ (viewer : Peers V) (o : E4) (x : Points n), x ∈ K →
      ∀ v : Inputs g.core d,
      ‖δ word (fun y => TrueCompact field W viewer (r s) o y v) x -
        δ word (fun y => FVA2.GradedFar.crop p (t (r s)) (sent X h y (raised within v))) x‖ ≤
        A * inputMass g v * |t (r s)|^(p+1) := by
  classical
  let I := Peers V × E4 × K
  let a (s : ι) (i : I) (u : Inputs g.core d) (y : Points n) :=
    TrueCompact field W i.1 (r s) i.2.1 y u
  let f (s : ι) (u : Inputs g.core d) (y : Points n) :=
    FVA2.GradedFar.crop p (t (r s)) (sent X h y (raised within u))
  have per (q : Picks g.core d) : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in l, ∀ i : I,
      ‖δ word (a s i (basisWord q)) i.2.2.val - δ word (f s (basisWord q)) i.2.2.val‖ ≤
        A * |t (r s)|^(p+1) := by
    obtain ⟨A, hA, priced⟩ := WilsonGraphAppointedMixedShapeJets.coordinate Z V Q
      l r scale within (basisWord q) K hK separated (fun (_ : ι) (_ : I) => True)
      (fun _ i => i.2.2.val) (fun _ i _ => i.2.2.property) (fun _ i => i.1)
      (fun _ i => i.2.1) p word
    exact ⟨A, hA, priced.mono fun s hs i => hs i trivial⟩
  choose C nonnegative price using per
  obtain ⟨D, hD, bound⟩ := multipliersMass g d
  refine ⟨(∑ q, C q) * D, mul_nonneg (Finset.sum_nonneg fun q _ => nonnegative q) hD, ?_⟩
  have connected := WilsonGraphAppointedStationaryPrices.adjacent Z V Q
  filter_upwards [Filter.eventually_all.mpr price,
    scale.eventually (WilsonGraphAppointedMixedShapeJets.centers field W connected within),
    scale.eventually (show ∀ᶠ z in trail, 0 < z from self_mem_nhdsWithin)] with s allq center hr
  intro viewer o x hx v
  let i : I := (viewer, o, ⟨x, hx⟩)
  have left := coordinateExpansion (a s i) (fun u y _ => fieldExpansion field W viewer o (r s) y u)
    (fun q => (true_views field W viewer hr (raised within (basisWord q))).congr
      (center viewer o (basisWord q))) word (separated hx) v
  have right := coordinateExpansion (f s) (fun u _ hy => formalExpansion X within p (t (r s)) hy u)
    (fun q => WilsonGraphAppointedMixedShapeJets.cropSmooth Z V Q h p (t (r s))
      (raised within (basisWord q))) word (separated hx) v
  change ‖δ word (a s i v) x - δ word (f s v) x‖ ≤ _
  rw [left, right]
  have mass : 0 ≤ inputMass g v := Finset.prod_nonneg fun _ _ => YangMills.Matching.sectorMass_nonneg _
  have charged := sumPrice (multipliers v) (fun q => δ word (a s i (basisWord q)) x)
    (fun q => δ word (f s (basisWord q)) x) C (D * inputMass g v) (|t (r s)|^(p+1))
    (mul_nonneg hD mass) (bound v) (fun q => allq q i)
  simpa only [mul_assoc] using charged

include Q in
theorem original {ι : Type} (l : Filter ι) (r : ι → ℝ) (scale : Tendsto r l trail)
    {n h : ℕ} {d : Fin n → ℕ} (within : Through h d)
    (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n) (p j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in l, ∀ (viewer : Peers V) (o : E4) (x : Points n), x ∈ K →
      ∀ v : Inputs g.core d, YangMills.Matching.shapeJetEstimateAt j
        (fun y => TrueCompact field W viewer (r s) o y v)
        (fun y => FVA2.GradedFar.crop p (t (r s)) (sent X h y (raised within v))) x
        (A * inputMass g v * |t (r s)|^(p+1)) := by
  let I := Peers V × E4 × K × Inputs g.core d
  let current (s : ι) (i : I) (y : Points n) := TrueCompact field W i.1 (r s) i.2.1 y i.2.2.2
  let formal (s : ι) (i : I) (y : Points n) :=
    FVA2.GradedFar.crop p (t (r s)) (sent X h y (raised within i.2.2.2))
  let point (_ : ι) (i : I) : Points n := i.2.2.1.val
  let err (s : ι) (i : I) := inputMass g i.2.2.2 * |t (r s)|^(p+1)
  have errpos (s : ι) (i : I) : 0 ≤ err s i := mul_nonneg
    (Finset.prod_nonneg fun _ _ => YangMills.Matching.sectorMass_nonneg _) (pow_nonneg (abs_nonneg _) _)
  have connected := WilsonGraphAppointedStationaryPrices.adjacent Z V Q
  have smooth : ∀ᶠ s in l, ∀ i : I, point s i ∈ conf n ∧
      ContDiffOn ℝ ∞ (current s i) (conf n) ∧ ContDiffOn ℝ ∞ (formal s i) (conf n) := by
    filter_upwards [scale.eventually (WilsonGraphAppointedMixedShapeJets.centers field W connected within),
      scale.eventually (show ∀ᶠ z in trail, 0 < z from self_mem_nhdsWithin)] with s he hr
    intro i
    refine ⟨separated i.2.2.1.property, ?_, WilsonGraphAppointedMixedShapeJets.cropSmooth Z V Q h p _ _⟩
    exact (true_views field W i.1 hr (raised within i.2.2.2)).congr (he i.1 i.2.1 i.2.2.2)
  obtain ⟨A,hA,priced⟩ := WilsonGraphCompactCoordinateJets.original (I := fun _ => I)
    l j current formal point err errpos smooth (fun word => by
      obtain ⟨C,hC,pay⟩ := coordinateMass Z V Q l r scale within K hK separated p word
      refine ⟨C, hC, pay.mono fun s hs i => ?_⟩
      simpa only [err, mul_assoc] using hs i.1 i.2.1 i.2.2.1.val i.2.2.1.property i.2.2.2)
  refine ⟨A, hA, priced.mono fun s hs viewer o x hx v => ?_⟩
  simpa only [err, mul_assoc] using hs (viewer,o,⟨x,hx⟩,v)

end Appointed

end YM.Integration.WilsonGraphUniformMixedShapeMass


