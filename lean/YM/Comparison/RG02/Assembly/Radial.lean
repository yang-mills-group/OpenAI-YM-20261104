import YM.Comparison.RG02.Assembly.Exponent
/-!
# No-hole vertices, before field re-expression

Microscopic field/test/coarse fluctuation variables collected in `E`, t is gᵢ. Real f action
with *t powers already included*, stationary order ≥2. Subtract flat completed-square grade 2
exactly before expanding. (Later prove that it is the genuine quadratic plus coarse terms; here
 `Stationary` doesn't mean positive.) Arbitrary supplementary analytic inputs `F`, here we require
 smooth at origin with nonnegative grades after the indicated valuation compensation. These will
 include ordinary log Haar and Wilson terms and input (not output) analytic generators. Rough `e`
 not among these. This proves the Taylor identification **before** integration, after the real
 `ζ`-free finite rescaling; `Z.Fits` below is for only fixed volume/step/coupling variable offsets
 (ρ chosen per-step, not calendar/β offset). Integration and mask comparisons are separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly
open Function Finset Filter MeasureTheory
open YM.Marker YM.Multi
open YM.PertExtension.Series YM.Comparison.RG02.Order
open YM.Extra.Trajectories (connected connected_quiet pass_connected pass_add)
open scoped Topology BigOperators Classical ContDiff

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ} {ρ : ℝ}
variable (l : Hot R→ℕ) (F : Hot R→ E→ℂ) (f : E→ℝ)

/-- Real positive-joint-core integrand apart from scalar and Gaussian. All markers;
    divided with their *own* orders. -/
def smoothMark (t : ℝ) (x : E) : Poly R := lit R (fun i=> divided (l i) (fun t u=> F i (t • u)) t x)
def vacuumLetter (x : E) (n : ℕ) : ℝ := if n=0 then 0 else -jet f (n+2) x
def markLetter (i : Hot R) (x : E) (n : ℕ) : ℂ := jet (F i) (l i + n) x
lemma vacuum_eq (u : E) (n : ℕ) : vacuumLetter f u n=Radial.layers f n u := by
  unfold vacuumLetter Radial.layers; rw [← jet_eq]; split
  next h=> subst n; simp
  next h=> rw [add_zero]
omit [Fintype V] in
lemma mark_read (t : ℝ) (x : E) (i : Hot R) : (smoothMark l F t x).part i.val=(t^ l i)⁻¹ • F i (t • x) :=
  part_lit _ i

def curve (x : E) : PTable R := PowerSeries.mk fun n=> lit R (fun i=> markLetter l F i x n)
def affine (x : E) : PTable R := realCurve R (vacuumLetter f x) + curve l F x
omit [Fintype V] in
lemma mark_curve_quiet (x : E) (n : ℕ) : (PowerSeries.coeff n (curve l F x)).part R.quiet=0 := by
   rw [curve,PowerSeries.coeff_mk]; exact part_lit_quiet _

def numeric (t : ℝ) (x : E) := Poly.bead R (Real.exp (Radial.higher f t x)) * (smoothMark l F t x).pass
variable [FiniteDimensional ℝ E]

/-- SmoothTaylor driver (per-entry estimates). -/
def expansions (x : E) := realCurve R (fun n=> Radial.expsum (Radial.layers f) n n x)*markExp (curve l F x)

omit [FiniteDimensional ℝ E] in
lemma mark_books (x : E) (r : ℕ) : (series R r (curve l F x)).part (Board R r).quiet=0 := by
  rw [← Join.pair_quiet,polarization, mark_curve_quiet, mul_zero]
omit [FiniteDimensional ℝ E] in
lemma vacancy_books (R : Census V) (x : E) (r : ℕ) : (series R r (realCurve R (vacuumLetter f x))).part (Board R r).quiet=0 := by
  rw [← Join.pair_quiet,polarization]
  change (Nat.factorial _ : ℂ)*((PowerSeries.coeff 0 (realCurve R (vacuumLetter f x))).part R.quiet)=0
  rw [realCoeff, vacuumLetter,if_pos rfl,Complex.ofReal_zero,map_zero,Poly.part_nil,mul_zero]

omit [FiniteDimensional ℝ E] in
lemma driver_quiet (x : E) (r : ℕ) : (series R r (affine l F f x)).part (Board R r).quiet=0 := by
 rw [affine,map_add, Poly.part_plus, mark_books,vacancy_books,add_zero]

lemma exponent_identity (x : E) : series R r (expansions l F f x)=
    Poly.pass (series R r (affine l F f x)) := by
  let u := Radial.layers f
  rw [expansions,map_mul, real_pass _ (funext fun x=>Radial.Stationary.layers_zero x) x,
    affine,map_add,pass_add (vacancy_books f ..) (mark_books l F ..),mark_exp _]
  congr 2
  · rw [show vacuumLetter f x=(fun i=> Radial.layers f i x) from funext (vacuum_eq f x)]; rfl
  exact mark_curve_quiet l F x

def Admissible : Prop :=
  Radial.Stationary f ∧ ∀ i : Hot R, ContDiffAt ℝ ∞ (F i) 0 ∧ ∀ n < l i,∀ u, jet (F i) n u=0

local notation "zoneE" => Radial.zone (E:=E)
omit [Fintype V] in
lemma mark_test (hf : Admissible l F f) : Zonal zoneE 1 (smoothMark l F) (curve l F) := by
  intro t;
  by_cases ht : t.val.Nonempty
  · let i : Hot R:=⟨t,ht⟩
    have he x y : (smoothMark l F x y).part t=(x^ l i)⁻¹ • F i (x • y) := mark_read l F x y i
    suffices hp : rows (curve l F) t=fun n y=>jet (F i) (l i+n) y by
      simp_rw [hp,he]; exact shifted (F i) (hf.2 i).1 (l i) (hf.2 i).2
    funext n y; rw [rows,curve,PowerSeries.coeff_mk]; exact (part_lit _ i)
  replace ht := of_not_not (mt (Cumulants.hot_iff_ne t).2 ht)
  simp_rw [ht,smoothMark,part_lit_quiet];
  unfold rows; simp_rw [mark_curve_quiet];
  simpa using! (Zone.Built.const (V:=1) (0:ℂ) (Z:=zoneE) (fun _=>le_rfl))
lemma radial_comparison (hf : Admissible l F f) (hρ : 0 < ρ) :
    Zonal (zoneE) (Radial.shade ρ) (numeric l F f) (expansions l F f) := by
  simpa only [mul_one] using! (from_real (R:=R) (Radial.Stationary.exponential hf.1 hρ)).mul (power_zonal (mark_test l F f hf))

/-- This includes the *finite-regulator* analytic estimate proving that the integrand's Taylor
    coefficients on the actual orders in `gᵢ` are the determined ones. It is a local t estimate
    under any required slight Gaussian exponential loss. Holds even if F originally a t-denominator
    supplied germ (w/ray powers l), but not for the full represented input w/flags; another, very
    different estimate on the RG norms is needed for RG01/03. -/
theorem identify_uniform (hf : Admissible l F f) (hρ : 0 < ρ) (s : R.Mode) (r : ℕ) :
    (zoneE).Fits (Radial.shade ρ) (r+1) (fun t u=> (numeric l F f t u).part s-
      (value (t:ℂ) (Poly.pass (series R r (affine l F f u)))).part s) := by
  simp_rw [← exponent_identity]; exact Zonal.remainder _ (radial_comparison l F f hf hρ) s r
end YM.Comparison.RG02.Assembly
