import YM.WilsonMS.Top.BareLPT
import YM.MS.Swirl.Resolute
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Reexpressing in a common formal coupling

Use explicit order substitution at *both* the vertices and the measure.
No field leg scale here, so `Stripped`. The Hessian and entire tree
propagator remain literally the same. Builds `Rescaled.gaussian` and
`Rescaled.expectation`, Wilson Laurent mark conventions in the bare
coupling with subsequent substitution.
-/

set_option autoImplicit false
noncomputable section

namespace YM.WilsonMS
open Function Filter Set Finset XSpace
open MS MS.Koszul MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Puff.Mom
open MS.Orbit MS.Orbit.Cog MS.Plane MS.Book MS.Book.Convolve MS.Book.Program MS.Swirl
open PowerSeries (coeff)
open scoped Topology ContDiff BigOperators

namespace Symbols
variable {I : Type}
open Next.Rank.Normal

lemma partial_encode (i : I) (p : poly I) : MvPolynomial.pderiv i p = modeD i p := by
  classical
  unfold modeD
  let c : I → ℂ := open Classical in Pi.single i 1
  change MvPolynomial.pderiv i p = slit c p
  suffices h : MvPolynomial.pderiv i = slit c by rw [h]
  apply MvPolynomial.derivation_ext
  intro j
  rw [slit_X]
  by_cases h : j = i
  · subst j
    rw [MvPolynomial.pderiv_X_self, show c i = 1 from Pi.single_eq_same _ _, map_one]
  rw [MvPolynomial.pderiv_X_of_ne h, show c j = 0 from Pi.single_eq_of_ne h _, map_zero]

theorem encode_injective (I : Type) : Injective (encode I) := by
  classical
  let S (m : I →₀ ℕ) : Prop :=
    ∀ x y, encode I x = encode I y → MvPolynomial.coeff m x = MvPolynomial.coeff m y
  have hstep (m : I →₀ ℕ) (i : I) (he : S m) : S (m + Finsupp.single i 1) := by
    intro x y h
    have hv :
      MvPolynomial.coeff m (MvPolynomial.pderiv i x) =
        MvPolynomial.coeff m (MvPolynomial.pderiv i y) :=
      he _ _ (by rw [partial_encode, partial_encode, ← encode_derivative, ← encode_derivative, h])
    rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv] at hv
    exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero (m i) : (m i : ℂ) + 1 ≠ 0) hv
  have owns (m : I →₀ ℕ) : S m := by
    induction m using Finsupp.induction with
    | zero =>
      intro x y h
      change MvPolynomial.constantCoeff x = MvPolynomial.constantCoeff y
      have he := congr_fun h []
      rw [encode_nil, encode_nil, MvPolynomial.aeval_zero, MvPolynomial.aeval_zero] at he
      exact he
    | single_add i b m _ _ h =>
      have he (n : ℕ) : S (m + Finsupp.single i n) := by
        induction n with
        | zero => simpa using h
        | succ n ih =>
          rw [Finsupp.single_add, ← add_assoc]
          exact hstep _ i ih
      rw [add_comm]
      exact he _
  intro x y h
  exact MvPolynomial.ext x y fun i => owns i x y h

lemma turn_injective (I : Type) : Injective (turn (I := I)) := fun _ _ h =>
  PowerSeries.ext fun n => encode_injective I (congr_fun h n)
end Symbols

namespace Coupling
variable {E : Type} [AddCommGroup E] [Module ℂ E] {x : Cn}

lemma substitute_initial (p : E) (r : Cn) : substitute r (useN.refineV p) = useN.refineV p := by
  funext n
  have hp : (0 : ℕ) ∈ Finset.Iic n := by simp
  rw [rules, sum_eq_single_of_mem 0 hp, lone_use]
  · unfold cut
    rw [pow_zero, PowerSeries.coeff_one]
    by_cases h : n = 0
    · rw [if_pos h, h, lone_use, one_smul]
    rw [if_neg h, zero_smul, SplitP.refineV, if_neg (show n ≠ useN.origin from h)]
  intro j _ hj
  rw [SplitP.refineV, if_neg (show j ≠ useN.origin from hj), smul_zero]

lemma tether (M : Actors E) (h : Rooted x) : Tether (substitute x) (M.stack useN) (M.stack useN) :=
  ⟨substitute_initial _ _, fun U V => (substitute_pair h U V M.core).symm⟩

lemma sub_cheer (M : Actors E) (h : Rooted x) (V : T E) (hp : V 0 = 0) :
    substitute x (M.Cheer useN V) = M.Cheer useN (substitute x V) := by
  funext i
  have hv : substitute x ((M.stack useN).cheers V i) i = M.Cheer useN (substitute x V) i :=
    congr_fun ((tether M h).cheersV i V) i
  rw [← hv, rules, rules]
  refine
    Finset.sum_congr rfl fun j hj =>
      congr_arg (cut x j i • ·) (M.overbook useN V hp (Finset.mem_Iic.mp hj) |>.symm)

section PS
variable {S Q : Type} [CommRing S] [Algebra ℂ S] [CommRing Q] [Algebra ℂ Q]

abbrev read (x : PowerSeries S) : T S := fun n => coeff n x

lemma const_coupling (h : Rooted x) :
    PowerSeries.constantCoeff (PowerSeries.map (algebraMap ℂ S) x) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, h, map_zero]

def composeS (r : Cn) (x : PowerSeries S) :=
  x.subst (PowerSeries.map (algebraMap ℂ S) r)

lemma explicit (h : Rooted x) (V : PowerSeries S) : substitute x (read V) = read (composeS x V) := by
  funext n
  have hz : Finset.Iic n = Finset.range (n + 1) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  rw [rules, hz]
  unfold read composeS
  rw [FPS.coeff_substituted V (const_coupling h)]
  apply Finset.sum_congr rfl
  intro j _
  unfold cut
  rw [← map_pow, PowerSeries.coeff_map, Algebra.smul_def, smul_eq_mul, mul_comm]

lemma comp_natural (h : Rooted x) (F : S →ₗ[ℂ] Q) (a : PowerSeries S) :
    composeS x (FPS.extending F a) = FPS.extending F (composeS x a) := by
  have he (v : PowerSeries S) : read (FPS.extending F v) = promote F (read v) :=
    funext fun i => FPS.coeff_extending F v i
  refine
    PowerSeries.ext
      (fun n =>
        congr_fun
          (show read (composeS x (FPS.extending F a)) = read (FPS.extending F (composeS x a)) from ?_)
          n)
  rw [← explicit h, he, ← Program.comm, explicit h, ← he]

lemma comp_mul (h : Rooted x) (a b : PowerSeries S) :
    composeS x (a * b) = composeS x a * composeS x b :=
  PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero (const_coupling (S := S) h)) a b

lemma comp_unit (h : Rooted x) : composeS x (1 : PowerSeries S) = 1 := by
  unfold composeS
  rw [←
    PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero (const_coupling (S := S) h)),
    map_one]
end PS
end Coupling

namespace Rescaled
open Root Coupling Quo Precision Lattice Function Next.Rank.Normal
open MS.Cylinder MS.Cylinder.Lab MS.Cylinder.Taylor MS.Native MS.Native.Wilsonian MS.Swirl.Near
open MS.Fleet MS.Orbit.LogReal
variable {P : Period} (T : P.Tree) (G : Gauge) (φ : Team) (x : ℝ)
local notation "N" => P.side
local notation "Σ'" => σbranch (G := G) (n := N)
local notation "Λ" => Master G N true
local notation "Q" => NRG (Stripped φ) x N G true
local notation "s" => shift φ x

lemma action : substitute s (promote (specialize (Position.fourier G N)) (bareX G N)) = Q := by
  have hs :
    promote (specialize (Position.fourier G N)) (bareX G N) =
      promote (SendB G N true) (Wilsonian.core G) - useN.refineV (pay true • flatH G N) := by
    funext k
    by_cases hh : k = 0
    · subst k
      rw [Pi.sub_apply, lone_use, promised, promised, bareX, if_pos rfl, map_zero]
      exact (sub_self _).symm
    rw [Pi.sub_apply, SplitP.refineV, if_neg (show k ≠ useN.origin from hh), sub_zero, promised,
      bareX, if_neg hh, map_smul, Position.unmarked_fourier]
    rfl
  rw [hs, map_sub, substitute_initial, ← Program.comm, Near.Orders]
  unfold style
  rw [strip_wobble]
  rfl

/-- Bare LPT scalar same action jets, log voice substituted, inverse covariance unchanged. -/
abbrev density :=
  composeS s (XSpace.Bare.weight T G)

def gaussian : XSpace.Bare.Series T G →ₗ[ℂ] PowerSeries ℂ :=
  FPS.extending (blend (XSpace.Bare.Q T G) 0) ∘ₗ LinearMap.mulLeft ℂ (density T G φ x)

def vacuumS :=
  gaussian T G φ x 1

lemma reexpression (V : XSpace.Bare.Series T G) :
    gaussian T G φ x (composeS s V) = composeS s (XSpace.Bare.diagrams T G V) := by
  unfold gaussian XSpace.Bare.diagrams
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [comp_natural (share φ x), comp_mul (share φ x)]

lemma vacuum_comp : vacuumS T G φ x = composeS s (XSpace.Bare.vacuum T G) := by
  unfold vacuumS
  nth_rw 1 [← comp_unit (share φ x)]
  exact reexpression T G φ x 1

lemma invert : PowerSeries.constantCoeff (vacuumS T G φ x) = 1 := by
  rw [vacuum_comp, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  change Coupling.read (composeS s _) 0 = 1
  rw [← explicit (share φ x), pay0]
  unfold Coupling.read
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, Bare.vacuum_start]

lemma vacuum_answer : ℶV Λ (exp0 Σ' Q) = read (vacuumS T G φ x) := by
  rw [vacuum_comp, ← explicit (share φ x)]
  let f := promote (specialize (Position.fourier G N))
  let X := f (bareX G N)
  rw [show read (XSpace.Bare.vacuum T G) = ℶV Λ (exp0 Σ' X) from
      funext fun i => (true_vacuum T G i).symm]
  change promote (View Λ) _ = substitute s (promote (View Λ) _)
  rw [← Program.comm, show Q = substitute s X from action (P := P) G φ x |>.symm,
    show exp0 Σ' (substitute s X) = substitute s (exp0 Σ' X) from
      (sub_cheer (actor Σ') (share φ x) X ?_).symm]
  unfold X f
  rw [promised, bareX, if_pos rfl, map_zero]

abbrev fourierMark (O : Wilson.Config G P.side → ℝ) (d : ℕ) :=
  substitute s (promote (specialize (Position.fourier G N)) (letterField G O d))

abbrev litMark (O : Wilson.Config G P.side → ℝ) (d : ℕ) :=
  composeS s (bareMark T G (asTree G O) d)

theorem common_numerator (O : Wilson.Config G P.side → ℝ) (d : ℕ) (hg : germ (in_chart G O))
    (hO : ∀ a : Site P.side → G.El, (∀ x, a (-x) = a x) → ∀ u, O (Lattice.gauge a u) = O u)
    (hv : From (ink (glow G (Site P.side)).e0 (in_chart G O)) d) :
    ℶV Λ ((PermV Σ').core (exp0 Σ' Q) (fourierMark G φ x O d)) =
      read (gaussian T G φ x (litMark T G φ x O d)) := by
  rw [litMark, reexpression, ← explicit (share φ x)]
  let f := promote (specialize (Position.fourier G N))
  let X := f (bareX G N)
  let V := f (letterField G O d)
  rw [show read (XSpace.Bare.diagrams _ _ _) = ℶV Λ ((PermV Σ').core (exp0 Σ' X) V) from
      funext fun i => (true_stencil T G O d hg hO hv i).symm]
  change promote (View Λ) ((PermV _).core _ (substitute s V)) = substitute s (promote (View Λ) _)
  rw [← Program.comm _ _ (View Λ),
    show
      substitute s ((PermV Σ').core (exp0 Σ' X) V) =
        ((PermV Σ').core (substitute s (exp0 Σ' X)) (substitute s V))
      from (tether (actor Σ') (share φ x)).craft _ _,
    show substitute s (exp0 Σ' X) = exp0 Σ' (substitute s X) from
      sub_cheer (actor Σ') (share φ x) X ?_,
    show substitute s X = Q from action (P := P) G φ x]
  unfold X f
  rw [promised, bareX, if_pos rfl, map_zero]

def expectation : XSpace.Bare.Series T G →ₗ[ℂ] PowerSeries ℂ :=
  LinearMap.mulLeft ℂ (vacuumS T G φ x)⁻¹ ∘ₗ gaussian T G φ x

lemma vacuum_times (v : XSpace.Bare.Series T G) :
    vacuumS T G φ x * expectation T G φ x v = gaussian T G φ x v := by
  change vacuumS T G φ x * ((vacuumS T G φ x)⁻¹ * _) = _
  rw [← mul_assoc,
    PowerSeries.mul_inv_cancel _
      (by
        rw [invert]
        norm_num),
    one_mul]

lemma comp_expectation (V : XSpace.Bare.Series T G) :
    expectation T G φ x (composeS s V) = composeS s (XSpace.Bare.normalized T G V) := by
  apply
    (PowerSeries.isUnit_iff_constantCoeff.mpr
          (by
            rw [invert]
            exact isUnit_one) :
        IsUnit (vacuumS T G φ x)).mul_right_inj.mp
  rw [vacuum_times, vacuum_comp, reexpression, ← comp_mul (share φ x),
    mul_comm (XSpace.Bare.vacuum T G), XSpace.Bare.normalize_denominator]

lemma gaussian_scalar (X : Cn) (V : XSpace.Bare.Series T G) :
    gaussian T G φ x (XSpace.Bare.scalar T X * V) = X * gaussian T G φ x V := by
  unfold gaussian XSpace.Bare.scalar
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [mul_left_comm (density T G φ x), FPS.extending_mul_self]

lemma formal_scalars (X : Cn) (V : XSpace.Bare.Series T G) :
    expectation T G φ x (XSpace.Bare.scalar T X * V) = X * expectation T G φ x V := by
  change (vacuumS T G φ x)⁻¹ * gaussian T G φ x (_ * _) = X * ((vacuumS T G φ x)⁻¹ * _)
  rw [gaussian_scalar, mul_left_comm]
end Rescaled
end YM.WilsonMS
