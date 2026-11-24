import YM.Integration.WilsonOrdinaryHomogeneousDetectors

/-! A before-cutoff, two-site physical mixed-table error at one fixed radius ratio and
the genuine resonant cancellation suffice for the complete observed ordinary exterior.
The normalized tree term, linear detector inversion, shears, double price, and original
sampled-clock comparison are all proved rather than supplied as inputs. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryMeasuredMarch
open Filter Set Spec Climb OPE RG12 RG12.Frames RG17 SharpGram Trace.Pilot
open WilsonOrdinaryGradedShear WilsonOrdinaryMarchStep WilsonOrdinaryEngineering
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryHomogeneousDetectors
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
local notation "V" => Desk.Sector F.sector.derivatives d
local notation "X" => Col V
local notation "t" => (Real.exp (1:ℝ))⁻¹
local notation "b!" => WilsonOrdinaryHomogeneousDetectors.basis F d

private def selectGrade : BlockMatrix V →ₗ[ℂ] BlockMatrix V where
  toFun U := diagonalMap V U
  map_add' _ _ := by apply LinearMap.ext; intro x; funext j; rfl
  map_smul' _ _ := by apply LinearMap.ext; intro x; funext j; rfl

private lemma select_id : selectGrade F d (LinearMap.id : BlockMatrix V) = LinearMap.id := by
  apply LinearMap.ext; intro x; funext i
  change (Pi.single i (x i)) i = x i; exact Pi.single_eq_same i _

private lemma select_bound {U : BlockMatrix V} {K : ℝ} (hK : 0 ≤ K)
    (bound : ∀ x : X, ‖U x‖ ≤ K*‖x‖) (x : X) : ‖selectGrade F d U x‖ ≤ K*‖x‖ := by
  change ‖diagonalMap V U x‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg _))).mpr
  intro i
  change ‖U (put V i (x i)) i‖ ≤ _
  calc
    ‖U (put V i (x i)) i‖ ≤ ‖U (put V i (x i))‖ := norm_le_pi_norm _ i
    _ ≤ K*‖put V i (x i)‖ := bound _
    _ ≤ _ := mul_le_mul_of_nonneg_left ((put_norm_le V i (x i)).trans (norm_le_pi_norm x i)) hK

def ResonantZero (A : Module.End ℂ D) : Prop :=
  diagonalMap V (coefficient F d A) = 0

/-- Finite numerical source, stated only for the native homogeneous real detector basis
and the independent linear/quadratic coefficients; no global chart cost is assumed. -/
def MixedError (g : ℝ → ℝ) (A B : Module.End ℂ D) (c : ℝ) : Prop :=
  ∀ᶠ r in trail, ∀ i j : Handle F d,
    |mixed F J d r (t*r) (b! i) (b! j) -
      trialStep F J d r t (second d (g r) A B) (b! i) (b! j)| ≤ c*(g r)^2

theorem local_cost (P : Pier.Lair.Present F J) (g : ℝ → ℝ) (coupled : Coupling G g)
    (A B : Module.End ℂ D) (cancel : ResonantZero F d A) {c : ℝ} (hc : 0 ≤ c)
    (table : MixedError F J d g A B c) : WilsonOrdinaryMarch.DiagonalCost F J d (chart F d) := by
  let T := chart F d
  let enter := (T.toLinearMap.comp (engineeringCoord F d).toLinearMap).toContinuousLinearMap
  let front := T.symm.toLinearMap.toContinuousLinearMap
  let back := T.toLinearMap.toContinuousLinearMap
  let ranked : X →L[ℂ] X := LinearMap.toContinuousLinearMap (scored F d B)
  obtain ⟨K,hK,read⟩ := WilsonOrdinaryMixedDetectors.read_frame F J d P b!
  obtain ⟨clock,hClock,ages⟩ := WilsonOrdinaryDyadicAge.square coupled
  let fee := ‖front‖*K*c*‖enter‖
  have nonneg : 0 ≤ fee := by dsimp [fee]; positivity
  have zero : selectGrade F d (scored F d A) = 0 := by
    change diagonalMap V (scored F d A) = 0; rw [WilsonOrdinaryEngineering.diagonal]; exact cancel
  refine ⟨‖back‖*(fee+‖ranked‖)*‖front‖*clock,by positivity,?_⟩
  filter_upwards [WilsonOrdinaryDyadicAge.approaching.eventually read,
    WilsonOrdinaryDyadicAge.approaching.eventually table,ages] with n hr ht ha
  let u := g (Sample.length n)
  let guess := second d u A B
  let N := (step F J d T n).toLinearMap
  let delta := N - scored F d guess
  have dates : Sample.length (n+1) = t*Sample.length n := by
    rw [(Sample.samples_spacing n).2.2,div_eq_mul_inv,mul_comm]; rfl
  have raw := hr (Sample.length (n+1)) (((Pert.Scale.gear C.labels d t).comp guess).restrictScalars ℝ)
    (c*u^2) (mul_nonneg hc (sq_nonneg _)) (by simpa only [dates,guess,u,trialStep] using ht)
  have close (y : X) : ‖delta y‖ ≤ (fee*u^2)*‖y‖ := by
    let a := (J (Sample.length n) d).symm (J (Sample.length (n+1)) d (enter y))
    let b := Pert.Scale.gear C.labels d t (guess (enter y))
    have raw_y : ‖a-b‖ ≤ K*(c*u^2)*‖enter y‖ := raw _
    have difference : delta y = front (a-b) := by
      change step F J d T n y - scored F d guess y = _
      rw [evaluated]; exact (front.map_sub a b).symm
    calc
      ‖delta y‖ = ‖front (a-b)‖ := congrArg _ difference
      _ ≤ ‖front‖*‖a-b‖ := front.le_opNorm _
      _ ≤ ‖front‖*(K*(c*u^2)*(‖enter‖*‖y‖)) := by
        exact mul_le_mul_of_nonneg_left (raw_y.trans (mul_le_mul_of_nonneg_left (enter.le_opNorm y) (by positivity))) front.opNorm_nonneg
      _ = _ := by dsimp [fee]; ring
  have undo (x : X) : (selectGrade F d delta) x + ((u:ℂ)^2) • ((selectGrade F d (scored F d B)) x) =
      (diagonalMap V N) x - x := by
    change _ = selectGrade F d N x - x
    simp only [delta,guess,second,map_sub,map_add,map_smul,WilsonOrdinaryEngineering.tree,
      select_id,zero,smul_zero,add_zero,LinearMap.sub_apply,LinearMap.add_apply,
      LinearMap.smul_apply,LinearMap.id_apply]
    abel
  have err (x : X) : ‖diagonalMap V N x - x‖ ≤ (fee+‖ranked‖)*u^2*‖x‖ := by
    have unitcost : ‖((u:ℂ)^2)‖ = u^2 := by rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    calc
      ‖diagonalMap V N x-x‖ = ‖selectGrade F d delta x + ((u:ℂ)^2) • (selectGrade F d (scored F d B) x)‖ := congrArg _ (undo x).symm
      _ ≤ ‖selectGrade F d delta x‖ + ‖((u:ℂ)^2) • (selectGrade F d (scored F d B) x)‖ := norm_add_le _ _
      _ ≤ (fee*u^2)*‖x‖ + u^2*(‖ranked‖*‖x‖) := by
        rw [norm_smul,unitcost]
        exact add_le_add (select_bound F d (mul_nonneg nonneg (sq_nonneg _)) close x)
          (mul_le_mul_of_nonneg_left (select_bound F d ranked.opNorm_nonneg ranked.le_opNorm x) (sq_nonneg _))
      _ = _ := by ring
  intro x
  let z := diagonalMap V N x
  have inverse : ‖x‖ ≤ ‖front‖*‖T x‖ := by simpa [front] using front.le_opNorm (T x)
  calc
    |‖T z‖ - ‖T x‖| ≤ ‖T z - T x‖ := abs_norm_sub_norm_le _ _
    _ = ‖back (z-x)‖ := by rw [back.map_sub]; rfl
    _ ≤ ‖back‖ * ‖z-x‖ := back.le_opNorm _
    _ ≤ ‖back‖ * ((fee+‖ranked‖) * u^2 * ‖x‖) := mul_le_mul_of_nonneg_left (err x) back.opNorm_nonneg
    _ ≤ ‖back‖ * ((fee+‖ranked‖) * (clock/Sample.age n) * (‖front‖*‖T x‖)) := by
      have hage : 0 < Sample.age n := by unfold Sample.age; positivity
      have hf := add_nonneg nonneg ranked.opNorm_nonneg
      exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hf)
        (norm_nonneg x)).trans (mul_le_mul_of_nonneg_left inverse (mul_nonneg hf (div_nonneg hClock.le hage.le)))) back.opNorm_nonneg
    _ = _ := by ring

/-- Original normalized fixed-scale mixed measurements followed all the way through the
original quotient and every row/inlet of its physical exterior. -/
theorem prices (P : Pier.Lair.Present F J) (H : PhysMS.Leading F J)
    (g : ℝ → ℝ) (coupled : Coupling G g) (A B : Module.End ℂ D)
    (cancel : ResonantZero F d A) {c : ℝ} (hc : 0 ≤ c) (table : MixedError F J d g A B c)
    (O : Prescription F.sector.derivatives) (coh : O.Coherent) {u : Filter (ℕ×ℕ)}
    (Q : Lenses.Mantle F u) (L : Layout F) (hL : Pegs Q L) (E : Services C f S) :
    RightPrice C S L.charts d ∧ ∀ w, RowPrice C S F.sector.derivatives L.charts d w :=
  WilsonOrdinaryMarch.prices F J d (chart F d) P O coh
    (aligned F d J H O coh) (local_cost F J d P g coupled A B cancel hc table) Q L hL E

end YM.Integration.WilsonOrdinaryMeasuredMarch
