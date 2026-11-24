import YM.Integration.MSExteriorCompactTests
import YM.Integration.OPEProjectedMSRows
import YM.FVA2.SmoothPoint

/-! Integrating the actual independent MS front and its field-valued output table
against a native joint complex test, with every perturbative order partition. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.MSExteriorTestProjection
open Function Set Filter Finset Real MS MS.Rake MS.Menus MS.Land MS.Tone
open Pert.Position FVA2 FVA2.ColorCode MSExteriorDilation MSExteriorCompactTests
open RG11.Fields RG11.Grove RG11.Neighborhood
open scoped Topology BigOperators Classical
variable {G : Gauge} {B : MS.Local.Physical.Deck G} {Q : Booked B} {n m l H : ℕ}

/-- Separated continuity of each original signed MS tour row follows from its
native smoothness for arbitrary ordered Rake labels and all perturbative orders. -/
theorem front_continuous (M : MS_Data G Q) (R : Fin l → Label B) (μ : ℝ) (k : ℕ)
    (q : Points n → Fin l → QP) (hq : Continuous q) {x : Points n} (hx : Injective (q x)) :
    ContinuousAt (fun z => moment M R μ (q z) k) x := by
  exact ((Poesy.tourSmooth (S := M) univ k R μ).continuousOn.continuousAt
    ((Poesy.airT (Fin l)).mem_nhds hx)).comp hq.continuousAt

variable (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)

/-- Integrate only the shape values of the field table. The running scale remains explicit. -/
abbrev averaged (f : Test n) (C : Points n → MSExteriorDilation.Table B H) : MSExteriorDilation.Table B H :=
  fun a k v => f.applyTo (fun x => C x a k v)

/-- The measured front minus the matched independently measured exterior field. -/
def difference (f : Test n) (C : Points n → MSExteriorDilation.Table B H) (μ s : ℝ)
    (q : Points n → Fin (n+m) → QP) (u : Fin (1+m) → QP) (k : ℕ) : ℂ :=
  f.applyTo (fun x => moment M (Fin.append R L) μ (q x) k) - ∑ a : Glyph B H,
    ∑ p ∈ HasAntidiagonal.antidiagonal k,
      power ((weight R : ℝ)-a.size) s * averaged f C a p.1 (μ-s) * moment M (centered a L) μ u p.2

/-- This identity applies to every continuously moving cluster, common center, and
fixed exterior. Each table row is needed only at its one running scale and order. -/
theorem split (f : Test n) (C : Points n → MSExteriorDilation.Table B H) (μ s : ℝ)
    (q : Points n → Fin (n+m) → QP) (u : Fin (1+m) → QP) (k : ℕ)
    (hq : Continuous q) (hx : ∀ x ∈ tsupport f, Injective (q x))
    (hc : ∀ a j, j ≤ k → ∀ x ∈ tsupport f, ContinuousAt (fun z => C z a j (μ-s)) x) :
    f.applyTo (fun x => near M R L (C x) μ s (q x) u k) = difference M R L f C μ s q u k := by
  let t (a : Glyph B H) (p : ℕ × ℕ) (x : Points n) := power ((weight R : ℝ)-a.size) s * C x a p.1 (μ-s) *
    moment M (centered a L) μ u p.2
  have ht (a : Glyph B H) (p : ℕ × ℕ) (hp : p ∈ HasAntidiagonal.antidiagonal k)
      (x : Points n) (h : x ∈ tsupport f) : ContinuousAt (t a p) x := by
    have hpk := HasAntidiagonal.mem_antidiagonal.mp hp
    exact (continuousAt_const.mul (hc a p.1 (by omega) x h)).mul continuousAt_const
  have hs (a : Glyph B H) (x : Points n) (h : x ∈ tsupport f) :
      ContinuousAt (fun z => ∑ p ∈ HasAntidiagonal.antidiagonal k,t a p z) x :=
    tendsto_finsetSum _ fun p hp => ht a p hp x h
  unfold difference
  change f.applyTo (fun x => moment M (Fin.append R L) μ (q x) k -
    ∑ a : Glyph B H, ∑ p ∈ HasAntidiagonal.antidiagonal k,t a p x) = _
  rw [OPETreeTests.difference f _ _ (fun x h => front_continuous M _ _ _ q hq (hx _ h))
    (fun x h => tendsto_finsetSum _ fun a _ => hs a x h)]
  congr 1
  rw [OPETreeTests.sum f _ _ (fun a _ x h => hs a x h)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [OPETreeTests.sum f _ _ (ht a)]
  refine Finset.sum_congr rfl fun p _ => ?_
  let v := power ((weight R : ℝ)-a.size) s
  let w := moment M (centered a L) μ u p.2
  change f.applyTo (fun x => v*C x a p.1 (μ-s)*w) = v*f.applyTo (fun x => C x a p.1 (μ-s))*w
  simpa only [mul_right_comm v,← mul_assoc] using OPETreeTests.scalar f (v*w) (fun x => C x a p.1 (μ-s))

/-- With a compact far estimate for the original table the *distributed* tested
front-minus-independent-field difference has the same one-grade saving. -/
theorem measured (f : Test n) (C : Points n → MSExteriorDilation.Table B H) (Z : Set (Fin m → QP))
    (hz : IsCompact Z) (he : ∀ y ∈ Z, Injective (origin y)) (μ : ℝ) (k : ℕ)
    (hc : ∀ a j, j ≤ k → ∀ v : ℝ, ContinuousOn (fun z => C z a j v) (conf n))
    {K : ℝ} (hK : 0 ≤ K) (j : ℕ)
    (hf : ∀ᶠ s : ℝ in atTop, ∀ x ∈ tsupport f, ∀ y ∈ Z, ∀ v : ℝ,
      ‖far M R L (C x) v (receding s (positions x) y) (origin (stretch s y)) k‖ ≤
        K * (((1+|v|)*(1+s))^j * exp (-((H:ℝ)+1+weight L)*s))) :
    ∀ᶠ s : ℝ in atTop, ∀ y ∈ Z,
      ‖difference M R L f C μ s (fun x => contracted s (positions x) y) (origin y) k‖ ≤
        (∫ x, ‖f x‖) *((K*(1+|μ|)^j) * (exp (((weight R : ℝ)-H-1)*s) * (1+|s|)^(2*j))) := by
  obtain hsep := compact_separation (positions '' tsupport f) Z (f.hasCompactSupport.image continuous_positions) hz
    (fun _ ⟨x,hx,e⟩ => e ▸ Theater.out.injective.comp (f.tsupport_subset hx)) he
  have ht := MSExteriorCompactTests.tested M R L f C Z hz he μ k hK j hf
  filter_upwards [hsep,ht] with s hs h y hy
  have cq : Continuous (fun x : Points n => contracted s (positions x) y) := by
    apply continuous_pi
    intro a
    induction a using Fin.addCases with
    | left j =>
      have hcoord : Continuous (fun x : Points n => positions x j) :=
        (continuous_apply j).comp continuous_positions
      have hfixed : Continuous (fun p : QP => exp (-s) • p) := continuous_const_smul _
      simpa only [contracted,Fin.append_left,stretch,Function.comp_def] using hfixed.comp hcoord
    | right j => simpa only [contracted,Fin.append_right] using
        (continuous_const : Continuous (fun _ : Points n => y j))
  rw [← split M R L f C μ s _ _ k cq (fun x hx => hs _ ⟨_,hx,rfl⟩ y hy)
    (fun a r hr x hx => (hc a r hr _).continuousAt ((conf_open n).mem_nhds (f.tsupport_subset hx)))]
  exact h y hy

/-- The native selected OPE geometry at any center is continuous in every inner test shape. -/
theorem continuous_driven (y : Tail m) (s : ℝ) :
    Continuous (fun x : Points n => positions (driven (exp (-s)) x y)) :=
  continuous_positions.comp ((smooth_driving y).comp (continuous_const.prodMk continuous_id))

variable (V : Warehouse G) {Q' : Booked (wings G)} (M' : MS_Data G Q') (μ : ℝ) {i d : ℕ}

/-- The actual native MS `Design.inr` front is the finite sum of independently
integrated named Rake-word rows, at arbitrary engineering caps and common center. -/
theorem selected_front (f : Test n) (y : Tail m) (s : ℝ)
    (hf : ∀ x ∈ tsupport f,driven (exp (-s)) x y ∈ conf (n+m))
    (u : sheaf V.F n i) (v : sheaf V.F m d) (k : ℕ) :
    PowerSeries.coeff k (frontRow (OPEMSReport.report V M' μ) i d (.inr f) y s u v) =
      ∑ j : Fin (n+m) → BasisIx G (max i d), OPEProjectedMSRows.weights V.F (OPEMSReport.jointLabels V u v) j *
        f.applyTo (fun x => moment M' (labelAt (wings G) ∘ j) μ (positions (driven (exp (-s)) x y)) k) := by
  rw [OPEProjectedMSRows.profile V M' μ f y s hf u v k]
  let wt (j : Fin (n+m) → BasisIx G (max i d)) := OPEProjectedMSRows.weights V.F (OPEMSReport.jointLabels V u v) j
  let a (j : Fin (n+m) → BasisIx G (max i d)) (x : Points n) :=
    moment M' (labelAt (wings G) ∘ j) μ (positions (driven (exp (-s)) x y)) k
  change f.applyTo (fun x => ∑ j, wt j * a j x) = ∑ j, wt j * f.applyTo (a j)
  have ha (j : Fin (n+m) → BasisIx G (max i d)) (x : Points n) (hx : x ∈ tsupport f) : ContinuousAt (a j) x :=
    front_continuous M' (labelAt (wings G) ∘ j) μ k _ (continuous_driven y s) (Theater.out.injective.comp (hf x hx))
  rw [OPETreeTests.sum f univ (fun j x => wt j * a j x) (fun j _ x hx => continuousAt_const.mul (ha j x hx))]
  exact Finset.sum_congr rfl fun j _ => OPETreeTests.scalar f _ _

end YM.Integration.MSExteriorTestProjection
