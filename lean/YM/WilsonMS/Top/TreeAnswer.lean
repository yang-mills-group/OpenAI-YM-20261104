import YM.WilsonMS.Top.Exponential
import YM.MS.Swirl.Plane

/-!
# Tree with insertions to the acyclic ghost calculation

An all-orders Wick rule. `member` (one field, or let O be a product,
or even a finite polynomial in stencils) handles Laurent prefactors by
reading at the proper shifted index. No division by a formal `X` on
power series without checking the corresponding minimum rank.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Root
open XSpace XSpace.Bare Function Filter Set Finset Precision Lattice
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Book MS.Book.Convolve MS.Swirl MS.Orbit
  MS.Orbit.Cog
open MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom Symbols Darboux
open scoped Topology ContDiff BigOperators

variable {P : Period} (T : P.Tree) (G : Gauge)

local instance : DecidableEq (Root.Mode T G) :=
  Classical.decEq _
local notation "prop" => Darboux.propagator (cutCov T G) (cutL T G)
local notation "𝒲" => PermV (dg T G)
local notation "𝒥" => inclusion (embedP T G)

lemma slice_symm : Cog.Sym (plain (T.Key G)) (sliceK T G) := by
  let Q := XSpace.Bare.Q T G
  have he i j : Chill (sliceK T G) i j = Q.cov i j := slice_covariance T G i j
  intro i j
  obtain h := (he i j).trans ((Q.symm i j).trans (he j i).symm)
  simp only [Symbols.plain, cross_false, one_mul]
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

lemma continues {X : MS.Book.Convolve.T (Raw (Root.Mode T G) ℂ)} {V : Bare.Series T G}
    (hv : Γ X (dg T G))
    (hx : promote (specialize 𝒥) X = promote (specialize (sliceRows T G)) (turn V)) (i : ℕ) :
    View prop ((𝒲).core (exp0 (dg T G) (interaction T G)) X i) =
      PowerSeries.coeff i (XSpace.Bare.diagrams T G V) := by
  have hh : Γ (turn V) (fun _ => false) := fun _ _ => polynomial_input _
  rw [slice_answer T G (X := X) (Y := turn V) hv hh hx i, Bare.diagram_coeff]
  have ht :
    turn (weight T G * V) =
      (PermV (plain (T.Key G))).core (exp0 (plain (T.Key G)) (sliceInteraction T G)) (turn V) :=
    by rw [turn_mul, SLdensity]
  rw [show
      (PermV (fun _ : T.Key G => false)).core (exp0 (fun _ => false) (sliceInteraction T G)) (turn V)
          i =
        _
      from congr_fun ht.symm i]
  exact wick_row _ _ (slice_symm T G) (funext fun i => funext fun j => (slice_covariance T G i j).symm) _

lemma unit_answer (i : ℕ) :
    View prop (exp0 (dg T G) (interaction T G) i) = PowerSeries.coeff i (XSpace.Bare.vacuum T G) := by
  rw [← congr_fun ((𝒲).identityR (exp0 (dg T G) (interaction T G))) i]
  apply continues
  · exact refineπ useN _ (feeUnit (p := dg T G))
  rw [turn_unit]
  exact
    ((specialize_tether (incl_tie (embedP T G) (dg T G))).Extrapolation useN).unit.trans
      (((specialize_tether (projection_tied T G)).Extrapolation useN).unit.symm)

lemma exp_paid : Γ (interaction T G) (dg T G) := by
  intro i _
  unfold interaction
  split
  exact (FeeP (dg T G)).zero_mem
  exact
    ⟨(mask_symmetric _ (uncoupled_symm T G)).add (mask_symmetric _ (log_symm T G)),
      (Mini _).add_mem (minH (Limit.mod _ _)) (minH (Limit.mod _ _))⟩

lemma is_even : interaction T G ∈ (𝒲).guard := by
  have hv (F : Raw (Root.Mode T G) ℂ) (w : ℤ) (hh : Pure (dg T G) false F) :
    Pure (dg T G) false (mask w F) := by
    intro l h
    by_cases he : (l.length : ℤ) = w
    rw [enough _ he]
    exact hh l h
    exact strange _ he
  intro i _
  unfold interaction
  split
  exact Pure.zero (p := dg T G)
  exact Pure.add (hv _ _ (uncoupled_pure T G)) (hv _ _ (log_pure T G))

variable {C : Matrix (LinksI G P) (LinksI G P) ℂ} {L : Matrix (GhostI T G) (LinksI G P) ℂ}

variable (hc : Splitting (precisionM T G) (gradientM T G) C L)
local notation "prop'" => propagator C L

include hc in
lemma vacuum_comparison (i : ℕ) :
    View prop' (exp0 (dg T G) (interaction T G) i) = PowerSeries.coeff i (XSpace.Bare.vacuum T G) := by
  obtain ⟨ht, h⟩ := fee_spec (expΓ (exp_paid T G) i (Set.mem_univ _))
  rw [← unit_answer T G]
  exact
    Wick_cycle (quadratic T G) (rank2 T G) hc (tree_splitting T G) h ht
      (plain_cycles (is_even T G) (quadratic T G) (happy T G) (assemble T G |>.symm ▸ tok T G) i)

/-- Bare polynomial with the displayed external power removed. Use subject to
`From` (zero coefficients strictly below d). -/
def bareMark (O : P.Array G → ℝ) (d : ℕ) : Bare.Series T G :=
  PowerSeries.mk fun n =>
    XSpace.Taylor.divided (T.basis G) (n + d) (Complex.ofRealCLM ∘ ((O ∘ raised G) ∘ plantL T G))

variable (O : P.Array G → ℝ) (d : ℕ) (hg : germ (O ∘ raised G))
include hg

lemma bare_coeff :
    turn (bareMark T G O d) = rankLevel d (ink (T.basis G) ((O ∘ raised G) ∘ plantL T G)) := by
  ext1 n
  let D := plantL T G
  have h : germ ((O ∘ raised G) ∘ D) :=
    ContDiffAt.comp (f := ⇑D) 0
      (by
        rw [map_zero]
        exact hg)
      D.contDiff.contDiffAt
  rw [turn, bareMark, PowerSeries.coeff_mk, encode_expansion _ _ h]
  unfold rankLevel
  rw [Nat.cast_add]

lemma field_Γ : Γ (rankLevel d (stamped T G O)) (dg T G) := fun _ _ =>
  ⟨mask_symmetric _ (ink_s (coordinates T G).e0 (coordinates T G |>.never) hg), minH (Limit.mod _ _)⟩

variable (hk : ∀ k : P.Vertex → G.El, k T.root = 1 → ∀ U, O (P.act k U) = O U)
  (h : From (stamped T G O) d)
include hk h hc

/-- Core bridge: insertions from the chosen log chart. Verify the gauge-slice
change of their perturbative expectations in the very same theory, even at
positive mark and coupling degrees. `continues` reads the *tree* answer, using
the fact that the tilted tree cost has no higher FP terms on its slice. -/
lemma field_comparison (i : ℕ) :
    View prop' ((𝒲).core (exp0 (dg T G) (interaction T G)) (rankLevel d (stamped T G O)) i) =
      PowerSeries.coeff i (XSpace.Bare.diagrams T G (bareMark T G O d)) := by
  have hx := field_Γ T G O d hg
  obtain ⟨ht, hP⟩ := fee_spec (ΤΓ_pair (expΓ (exp_paid T G)) hx i (Set.mem_univ _))
  have he := field_closed T G O hg hk d h
  refine
    (Wick_cycle (quadratic T G) (rank2 T G) hc (tree_splitting T G) hP ht ?_).trans
      (continues T G hx
        (by
          rw [bare_coeff ..]
          exact plane_stencil T G d O hg
          exact hg)
        i)
  refine marked_cycles (is_even T G) (quadratic T G) (happy T G) ?_ ?_ i <;> rw [assemble]
  exacts [tok _ _, he]

theorem member :
    Endμ prop' (dg T G) (interaction T G) (rankLevel d (stamped T G O))
      (fun i => PowerSeries.coeff i (XSpace.Bare.normalized T G (bareMark T G O d))) := by
  ext1 i
  have he := XSpace.Bare.normalize_denominator T G (bareMark T G O d)
  rw [mul_comm] at he
  change View prop' ((𝒲).core _ _ i) = ∑ x ∈ Finset.antidiagonal i, _
  rw [field_comparison T G hc O d hg hk h, ← he, PowerSeries.coeff_mul]
  exact Finset.sum_congr rfl (fun i _ => congr_arg (· * _) (vacuum_comparison T G hc i.1).symm)
end YM.WilsonMS.Root
