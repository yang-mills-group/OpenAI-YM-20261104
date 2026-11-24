import YM.Integration.WilsonOrdinarySampleChart

/-! The original RG12 march's `ReadingAt` input is purchased on the same observed
finite labels and at its own sample index, with one linear lift for all field vectors. -/

noncomputable section
namespace YM.Integration.WilsonOrdinarySampleReader
open Filter Set Spec Climb OPE RG12 RG12.Frames RG17 SharpGram Trace.Pilot
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (P : Pier.Lair.Present F J)
variable {u : Filter (ℕ×ℕ)} (Q : Lenses.Mantle F u) (L : Layout F) (hL : Pegs Q L) (E : Services C f S)
variable {d : ℕ} (V : Grade d → Type) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
local notation "X" => Col V

private def dim (d : ℕ) := (((C.labels.level d).extra+1 : ℕ):ℝ)

private lemma sum_bill {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ X) (T : X ≃ₗ[ℂ] D)
    (Z : X →ₗ[ℂ] C.label d) (q : ℝ) (all : ∀ i : ι, ‖Z (b i)‖ ≤ q*‖T (b i)‖) :
    ∀ x : X, mass C d (Z x) ≤ (dim (C:=C) d * (∑ i : ι, ‖(b.coord i).toContinuousLinearMap‖*‖T (b i)‖)) * q * ‖x‖ := by
  classical
  intro x
  have unfoldZ : Z x = ∑ i : ι, (b.coord i x) • Z (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum,map_smul,Module.Basis.coord_apply]
  have bound : ‖Z x‖ ≤ (∑ i : ι, ‖(b.coord i).toContinuousLinearMap‖*‖T (b i)‖) * (q*‖x‖) := by
    rw [unfoldZ]
    refine (norm_sum_le ..).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro i hi; rw [norm_smul]
    calc
      _ ≤ (‖(b.coord i).toContinuousLinearMap‖ * ‖x‖) * (q*‖T (b i)‖) :=
        mul_le_mul ((b.coord i).toContinuousLinearMap.le_opNorm x) (all i) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ dim (C:=C) d * ‖Z x‖ := mass_le_norm C d _
    _ ≤ _ := by
      refine (mul_le_mul_of_nonneg_left bound (by dsimp [dim]; positivity)).trans_eq ?_; ring

include P E hL
/-- `T` fixes the linear label order on the selected free horizon before all
regulators. The same lift `Z k` realizes **every** source column exactly. -/
theorem original (T : X ≃ₗ[ℂ] D) : ∃ (p : ℕ) (Z : ℕ → X →ₗ[ℂ] C.label d), ∀ᶠ k : ℕ in atTop,
    let I := J (Sample.length (Sample.atMesh C k)) d
    (∀ x : X, engineering (S:=S) L.charts d k (Z k x) = I (T x)) ∧
    Nonempty (ReadingAt C S d V (fun y => ‖I.symm y‖) k L.charts (Z k) p) := by
  classical
  obtain ⟨n,buy⟩ := WilsonOrdinarySampleChart.sample F J P Q d L hL E
  let b := Module.finBasis ℂ X
  let K := dim (C:=C) d * (∑ i, ‖(b.coord i).toContinuousLinearMap‖*‖T (b i)‖)
  let S' := T.symm.toLinearMap.toContinuousLinearMap
  let area := fun k : ℕ => J (Sample.length (Sample.atMesh C k)) d
  let isGood := fun (k : ℕ) (Z : X →ₗ[ℂ] C.label d) =>
    (∀ x : X, engineering (S:=S) L.charts d k (Z x) = area k (T x)) ∧
      Nonempty (ReadingAt C S d V (fun y => ‖(area k).symm y‖) k L.charts Z (n+1))
  have grows := Next.Rank.Station.hat_rate C.path.levels E.simpleGate
  have good : ∀ᶠ k : ℕ in atTop, ∃ Z, isGood k Z := by
    filter_upwards [buy,grows.eventually_ge_atTop 1,grows.eventually_ge_atTop K,
        grows.eventually_ge_atTop ‖S'‖] with k purchased hb hK hS
    let β := C.path.levels.clock.hatBeta k
    have hβ : 1 ≤ β := hb
    let next := n+1
    choose w eq bill using (fun i => purchased.1 (T (b i)))
    let Z : X →ₗ[ℂ] C.label d := b.constr ℂ w
    have lift : (engineering (S:=S) L.charts d k).comp Z = (area k).toLinearMap.comp T.toLinearMap := by
      apply b.ext; intro i; simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,Module.Basis.constr_basis,Z] using eq i
    have realized (x : X) : engineering (S:=S) L.charts d k (Z x)=area k (T x) := LinearMap.congr_fun lift x
    have bill' (i) : ‖Z (b i)‖ ≤ β^n * ‖T (b i)‖ :=
      (norm_le_mass C d _).trans (by simpa only [Z,Module.Basis.constr_basis] using bill i)
    refine ⟨Z,realized,⟨?_⟩⟩
    constructor
    · intro x; refine (purchased.2 x).trans (mul_le_mul_of_nonneg_right ?_ (mass_nonneg ..))
      exact pow_le_pow_right₀ hβ (Nat.le_succ n)
    · intro x; refine (sum_bill V b T Z (β^n) bill' x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      change K*β^n ≤ β^(n+1); rw [pow_succ,mul_comm K]; exact mul_le_mul_of_nonneg_left hK (by positivity)
    · intro x; rw [realized,LinearEquiv.symm_apply_apply]
      have fst : ‖x‖ ≤ ‖S'‖ * ‖T x‖ := by simpa [S'] using S'.le_opNorm (T x)
      exact fst.trans (mul_le_mul_of_nonneg_right (hS.trans (le_self_pow₀ hβ (Nat.succ_ne_zero n))) (norm_nonneg _))
  let Z := fun k => if h : ∃ z, isGood k z then h.choose else (0 : X →ₗ[ℂ] C.label d)
  refine ⟨n+1,Z,good.mono ?_⟩
  intro k hk; change isGood k (Z k); dsimp only [Z]; rw [dif_pos hk]; exact hk.choose_spec

end YM.Integration.WilsonOrdinarySampleReader
