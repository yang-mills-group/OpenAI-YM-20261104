import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphOrdinarySource
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.OrdinarySeparatedValidity
import YM.Integration.WilsonGraphNamedGraphForestLimits

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.GroupOrdinaryTarget

open YangMills YangMills.MSbar Filter Set
open WilsonGraphStandaloneCorrelation (Label bare)
open WilsonGraphPublicForestLimits (dimensional releasedAt)
open scoped Topology BigOperators Classical

variable (g : YangMills.GaugeGroup)

theorem price {n : ℕ} (a : Fin n → Label g) (p : Ordinary.Price (maxwellReference g) n) :
    Ordinary.ExteriorExpansion (maxwellReference g) (bare g) a p ↔
      Ordinary.ExteriorExpansion (maxwellReference g) (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation a p :=
  (Ordinary.SeparatedValidity.exteriorIff (B := maxwellReference g)
    (WilsonGraphGroupPositionReference.agreement g) a p).symm

theorem valid (hg : g.IsSimple) :
    Ordinary.Valid (maxwellReference g) (bare g) (_root_.IssuedMaxwell.GraphCoefficients.issued g).ope :=
  (Ordinary.SeparatedValidity.validIff (B := maxwellReference g)
    (WilsonGraphGroupPositionReference.agreement g) _).mp (_root_.IssuedMaxwell.GraphOrdinary.valid g hg)

theorem determined (hg : g.IsSimple) : Ordinary.Determined (maxwellReference g) (bare g) :=
  (Ordinary.SeparatedValidity.determinedIff (B := maxwellReference g)
    (WilsonGraphGroupPositionReference.agreement g)).mp (_root_.IssuedMaxwell.GraphOrdinary.original g hg)

theorem numerical (hg : g.IsSimple) :
    (_root_.IssuedMaxwell.GraphCoefficients.issued g).ope = Ordinary.read (maxwellReference g) (determined g hg) :=
  Ordinary.eq_read _ (determined g hg) (valid g hg)

theorem named (hg : g.IsSimple) :
    Ordinary.read (maxwellReference g) (determined g hg) = _root_.IssuedMaxwell.GraphReader.name g :=
  (numerical g hg).symm.trans ((_root_.IssuedMaxwell.GraphCoefficients.source g hg).2.trans
    (_root_.IssuedMaxwell.GraphOrdinary.numerical g hg))

theorem homogeneousPrice (hg : g.IsSimple) {n : ℕ} (a : Fin n → Label g)
    (hom : ∀ i, Ordinary.homogeneous (maxwellReference g) (a i).1 (a i).2.val) :
    let p := _root_.IssuedMaxwell.GraphHomogeneous.price g a
    Ordinary.ExteriorExpansion (maxwellReference g) (bare g) a p ∧
      (∀ q, Ordinary.ExteriorExpansion (maxwellReference g) (bare g) a q → q = p) ∧
      ∀ h k x, (Ordinary.read (maxwellReference g) (determined g hg) n h k a x).val =
        ∑ w : Fin (h + 1), (p w.val k 0 x).val := by
  let p := _root_.IssuedMaxwell.GraphHomogeneous.price g a
  have paid := _root_.IssuedMaxwell.GraphHomogeneous.original g hg a hom
  refine ⟨(price g a p).mpr paid, fun q hq =>
    _root_.IssuedMaxwell.GraphOnlyPrice.original g hg a q p ((price g a q).mp hq) paid, ?_⟩
  intro h k x
  rw [named g hg]
  exact _root_.IssuedMaxwell.GraphReconstituted.original g a hom h k x

def exteriorDifference {n m : ℕ} (A : Ordinary.Correlation (maxwellReference g))
    (a : Fin n → Label g) (b : Fin m → Label g) (p : Ordinary.Price (maxwellReference g) n)
    (h k : ℕ) (t : ℝ) (x : YangMills.Points n) (y : YangMills.Points m) : ℂ :=
  A (n + m) k (Fin.append a b) (WithLp.toLp 2 (Fin.append (Real.exp (-t) • x).ofLp y.ofLp)) -
    Ordinary.truncation (maxwellReference g) A p (∑ i, (a i).1) h k b t x y

theorem jointCrops (hg : g.IsSimple) {n m : ℕ} (a : Fin n → Label g)
    (hom : ∀ i, Ordinary.homogeneous (maxwellReference g) (a i).1 (a i).2.val)
    (K : Set (YangMills.Points n)) (hK : IsCompact K) (near : K ⊆ YangMills.separated n)
    (b : Fin m → Label g) (E : Set (YangMills.Points m)) (hE : IsCompact E)
    (far : ∀ y ∈ E, WithLp.toLp 2 (Fin.cons (0 : YangMills.Spacetime) y.ofLp) ∈ YangMills.separated (m + 1))
    (h k : ℕ) :
    let p := _root_.IssuedMaxwell.GraphHomogeneous.price g a
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ, ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, ∀ y ∈ E,
      let bound := c * (1 + t)^L * Real.exp ((((∑ i, (a i).1 : ℕ) : ℝ) - (h : ℝ) - 1) * t)
      ‖exteriorDifference g (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation a b p h k t x y‖ ≤ bound ∧
      ‖exteriorDifference g (bare g) a b p h k t x y‖ ≤ bound := by
  let p := _root_.IssuedMaxwell.GraphHomogeneous.price g a
  have paid := _root_.IssuedMaxwell.GraphHomogeneous.original g hg a hom
  obtain ⟨c, pos, L, estimate⟩ := paid.exterior K hK near m b E hE far h k
  refine ⟨c, pos, L, ?_⟩
  filter_upwards [estimate, Ordinary.SeparatedValidity.eventuallySeparated K hK near E hE far] with t bounds joined
  intro x xm y ym
  have same : exteriorDifference g (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation a b p h k t x y =
      exteriorDifference g (bare g) a b p h k t x y := by
    unfold exteriorDifference
    rw [WilsonGraphGroupPositionReference.agreement g _ k _ _ (joined x xm y ym),
      Ordinary.SeparatedValidity.truncationEq (B := maxwellReference g)
        (WilsonGraphGroupPositionReference.agreement g) p _ h k b t x y (far y ym)]
  exact ⟨bounds x xm y ym, same ▸ bounds x xm y ym⟩

theorem fixedPosition (hg : g.IsSimple) :
    (∀ t : YangMills.MSbar.Position.Triangle (maxwellReference g), t.Admissible →
      t.RawSlopeAgrees (_root_.IssuedMaxwell.GraphCoefficients.issued g)) ∧
    ConversionValid (_root_.IssuedMaxwell.GraphCoefficients.issued g)
      (WilsonGraphGroupPositionReference.external g hg).menu
      (WilsonGraphGroupPositionReference.external g hg).conversion :=
  ⟨_root_.IssuedBridge.PostedEveryBareSlope.original hg, _root_.IssuedBridge.PostedAppointedConversionValid.original hg true⟩

theorem original (hg : g.IsSimple) :
    (∀ (n k : ℕ) (a : Fin n → Label g) (x : YangMills.Points n), x ∈ YangMills.separated n →
      (∀ ρ : ℝ, 0 < ρ → Tendsto (dimensional a x k ρ) YM.MS.Shine.dotty (𝓝 (releasedAt a x k ρ))) ∧
      Tendsto (releasedAt a x k) atTop (𝓝 ((_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n k a x))) ∧
    Ordinary.Valid (maxwellReference g) (bare g) (_root_.IssuedMaxwell.GraphCoefficients.issued g).ope ∧
    Ordinary.read (maxwellReference g) (determined g hg) = _root_.IssuedMaxwell.GraphReader.name g :=
  ⟨fun _ k a x hx => WilsonGraphNamedGraphForestLimits.physical a x hx k, valid g hg, named g hg⟩

end YM.Integration.GroupOrdinaryTarget
end

