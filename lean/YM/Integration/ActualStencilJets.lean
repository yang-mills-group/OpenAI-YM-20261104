import YM.Integration.ActualStencilCylinder

/-! All Taylor degrees of the original fixed cylinder, in the native mixed
derivative and RG06 polynomial conventions.  This identifies the full germ;
it does not identify its long-distance momentum symbol or assume `Fits`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStencilJets
open Function Lattice Wilson Source Labels
open MS.Cylinder MS.Cylinder.Taylor PertExtension.Series
open ActualStencilCylinder
open scoped BigOperators Classical ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}

/-- The two original full coefficient prescriptions have identical ordinary
factorial normalization, at every degree and for every input coefficient. -/
theorem book_casing (S : SectionData F) (c : F.Coeff)
    (A : Links ℤ G.Color) (k : ℕ) :
    PowerSeries.coeff k (Dict06.Wil.book S c A) =
      RG06.Tokens.applyHere A (RG06.Tokens.casing S c k) := by
  rw [RG06.Tokens.wrapRule, ← Dict06.Wil.echo_book, Dict06.Series.ps_at]
  rfl

theorem radial_book (S : SectionData F) (c : F.Coeff)
    (A : Links ℤ G.Color) (k : ℕ) :
    Radial.jet (realEcho S c) k (Dict06.Wil.restrictLog S.stencil A) =
      (PowerSeries.coeff k (Dict06.Wil.book S c A)).re := by
  let f : ℝ → ℂ := fun t =>
    Dict06.Wil.echo S c (t • Dict06.Wil.restrictLog S.stencil A)
  have hf : ContDiff ℝ ω f :=
    (Dict06.Wil.echo_smooth S c).comp (contDiff_id.smul contDiff_const)
  have hb : Dict06.Series.ordinary k f =
      PowerSeries.coeff k (Dict06.Wil.book S c A) := by
    have h := congrArg (PowerSeries.coeff k) (Dict06.Wil.echo_book S c A)
    simpa only [Dict06.Series.ps_at, Dict06.Wil.echo_exact] using h
  rw [Radial.homogeneous_derivative _ _ k
    ((realEcho_analytic S c).contDiffAt.of_le le_top)]
  change Dict06.Series.ordinary k (Complex.reCLM ∘ f) = _
  rw [Dict06.Series.ordinary_map f k (hf.contDiffAt.of_le le_top)
    Complex.reCLM, hb]
  rfl

theorem radial_casing (S : SectionData F) (c : F.Coeff)
    (A : Links ℤ G.Color) (k : ℕ) :
    Radial.jet (realEcho S c) k (Dict06.Wil.restrictLog S.stencil A) =
      (RG06.Tokens.applyHere A (RG06.Tokens.casing S c k)).re := by
  rw [radial_book, book_casing]

private def extend (S : SectionData F)
    (A : Dict06.Wil.Panel S.stencil G) : Links ℤ G.Color := fun e =>
  if h : e.1 ∈ S.stencil ∧ e.1 + step e.2 ∈ S.stencil then A ⟨e, h⟩ else 0

private theorem restrict_extend (S : SectionData F)
    (A : Dict06.Wil.Panel S.stencil G) :
    Dict06.Wil.restrictLog S.stencil (extend S A) = A := by
  funext i
  exact dif_pos i.property

/-- For an original real basis vector the native real cylinder is the full
complex-valued section germ, not merely its real part. -/
theorem echo_basis_real (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (i : F.Index) (A : Dict06.Wil.Panel S.stencil G) :
    (realEcho S (Pi.single i 1) A : ℂ) = Dict06.Wil.echo S (Pi.single i 1) A := by
  have hb : star (Pi.single i (1 : ℂ) : F.Coeff) = Pi.single i 1 := by
    funext j
    simp only [Pi.star_apply, Pi.single_apply]
    split_ifs <;> simp
  have hr := hS.ordinary_real (Pi.single i 1)
    (Dict06.Wil.positive (extend S A) 1)
  rw [hb, Dict06.Wil.echo_exact, restrict_extend, one_smul] at hr
  have hi := congrArg Complex.im hr
  apply Complex.ext
  · rfl
  change 0 = (Dict06.Wil.echo S (Pi.single i 1) A).im
  change (Dict06.Wil.echo S (Pi.single i 1) A).im =
    -(Dict06.Wil.echo S (Pi.single i 1) A).im at hi
  linarith

/-- Arbitrary mixed native derivatives equal the original coefficient
tensor, with exactly one factorial removed.  Every ordered slot is kept. -/
theorem mixed_author (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (i : F.Index) {J : Type*} (e : J → Dict06.Wil.Panel S.stencil G)
    (k : ℕ) (a : Fin k → J) :
    (k.factorial : ℝ)⁻¹ • ink e (realEcho S (Pi.single i 1)) (List.ofFn a) =
      Dict06.Wil.author S (Pi.single i 1) k (fun j => e (a j)) := by
  have he : Complex.ofRealCLM ∘ realEcho S (Pi.single i 1) =
      Dict06.Wil.echo S (Pi.single i 1) :=
    funext (echo_basis_real S hS i)
  rw [ActualStencilJetFloor.ink_ofFn e (realEcho_analytic S _).contDiffAt]
  unfold Dict06.Wil.author Tensor.coeff
  rw [← he, Complex.ofRealCLM.iteratedFDeriv_comp_left
    ((realEcho_analytic S _).contDiffAt.of_le le_top) le_rfl]
  rfl

theorem radial_basis (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (i : F.Index) (A : Links ℤ G.Color) (k : ℕ) :
    (Radial.jet (realEcho S (Pi.single i 1)) k
      (Dict06.Wil.restrictLog S.stencil A) : ℂ) =
      RG06.Tokens.applyHere A (RG06.Tokens.casing S (Pi.single i 1) k) := by
  rw [← book_casing, Dict06.Wil.reported]
  have h := mixed_author S hS i id k
    (fun _ : Fin k => Dict06.Wil.restrictLog S.stencil A)
  rw [ActualStencilJetFloor.ink_ofFn id (realEcho_analytic S _).contDiffAt] at h
  simpa only [id_eq, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.real_smul, Radial.jet, Tensor.diagonal] using h

/-- Slot lowering is the original rank shift; no derivative or field is
replaced when passing from the full germ to the RG06 stencil. -/
theorem radial_stencil (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (i : F.Index) (A : Links ℤ G.Color) (e : ℕ) :
    (Radial.jet (realEcho S (Pi.single i 1)) (e + (F.grades i).2)
      (Dict06.Wil.restrictLog S.stencil A) : ℂ) =
      RG06.Tokens.applyHere A (RG06.Tokens.stencil S i e) :=
  radial_basis S hS i A _

end YM.Integration.ActualStencilJets
