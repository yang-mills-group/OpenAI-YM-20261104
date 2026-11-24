import YM.WilsonMS.Top.ZeroParameter

/-! # All-orders physical readings at the bare coupling

From an ordinary gauge-invariant function on link variables. Coefficient
formula even for the numerator. The two step protocol for the change of
variables at the special momentum zero (change to a based c, only on the
support of the Wick evaluation) is necessary when using Stokes. No infinite
volume identity assumed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Quo
open XSpace Period Lattice Function Filter Set Finset Precision
open MS MS.Bare MS.Native MS.Native.Wilsonian MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Cylinder.Taylor
  MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Puff MS.Puff.Engine
  MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom MS.Swirl MS.Swirl.Near MS.Plane
open Root Position
open scoped Topology ContDiff BigOperators
variable {P : Period} (T : P.Tree) (G : Gauge)

local notation "D₀" => P.side
local notation "Σ'" => σbranch (G := G) (n := P.side)
local notation "Λ" => Master G P.side true
local notation "C'" => Darboux.propagator (landC P G) (landL T G)
local notation "Δ" => location T G (averageM T G)
local notation "Φ" => specialize (fourier G P.side)
local notation "Uv" => specialize (toLand T G)
local notation "Ψ" => specialize (location T G (averageM T G))
local notation "ℵ" => specialize (location T G (liftN T G))
local notation "℘" => (discard_wire T G)
local notation "Area" => Native.Chart.loco (G := G) (Native.Chart.drive P.side)

lemma full_log : Uv (Ψ ((2 : ℂ)⁻¹ • docket D₀ (Wilsonian.H G))) = Uv (Root.haarLog T G) := by
  rw [Wilsonian.shiftD, map_smul, halfHaar _ _ (real_average T G)]

lemma full_strength : Uv (Ψ ((2 : ℂ)⁻¹ • docket D₀ (Wilsonian.W G))) = Uv (Root.uncoupled T G) := by
  let Q := Native.Chart.rent (G := G) (Native.Chart.drive D₀)
  let B :=
    (pairs T G).hung (Focus.launch (coordinates T G) (colorTerm G T.Nonroot) (Root.localVector T G))
  let K := Root.uncoupled T G
  let Y := coordinates T G
  let R := ink Y.e0 (energyE P G)
  have hf : Uv (Ψ ((2 : ℂ)⁻¹ • wing P G)) = Uv (specialize (discard T G) B) := by
    rw [map_smul, map_smul, transmitted, compare_based, map_smul,
      inv_smul_smul₀ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [Wilsonian.witnessD]
  change Uv (Ψ ((2 : ℂ)⁻¹ • (ink (glow G (Site P.side)).e0 Q + wing P G))) = Uv (R + B)
  rw [smul_add, map_add, map_add, hf, map_smul, restrict_action T G (real_average T G),
    specialize_comp, Quo.absorbs, map_add]

def bareX (G : Gauge) (N : Side) (i : ℕ) : Raw (FixedMode G N) ℂ :=
  if i = 0 then 0 else (2 : ℂ)⁻¹ • docket N (Wilsonian.core G i)

lemma posΓ (G : Gauge) (P : Side) : Γ (bareX G P) σbranch := by
  intro i _
  unfold bareX
  split
  exact (FeeP _).zero_mem
  have h := (crisp G i).symm
  refine
    ⟨(show Symm σbranch (docket P (core G i)) from ?_).smul _,
      minH ((limit_sum P (participates G i)).smul _)⟩
  change Symm σbranch (sumHome (shown P _)).val
  rw [total_uses, sum_stack]
  exact Symm.sum _ fun j _ => (move_tie (fun x : Site P => j + x)).sym _ ((move_tie (wrap P)).sym _ h)

lemma input_compare : promote Uv (promote Ψ (bareX G D₀)) = promote Uv (Root.interaction T G) := by
  ext1 i
  by_cases hi : i = 0
  · subst i
    rw [promised, promised, promised, bareX, if_pos rfl, happy, map_zero]
  simp_rw [promised]
  unfold bareX Root.interaction
  rw [if_neg hi, if_neg hi]
  unfold Wilsonian.core Root.exponent
  simp only [Pi.add_apply, map_add, smul_add]
  rw [show docket D₀ (levels 2 _ i) = rankLevel 2 (docket D₀ (W G)) i from
      congr_fun (level_up 2 (W G) D₀ true) i,
    show docket D₀ (levels 0 _ i) = rankLevel 0 (docket D₀ (Wilsonian.H G)) i from
      congr_fun (level_up 0 (Wilsonian.H G) D₀ true) i]
  unfold rankLevel
  simp_rw [← map_smul (mask _), specialize_mask, full_strength, full_log]

variable {X : MS.Book.Convolve.T (Raw (FixedMode G P.side) ℂ)}
  {Y : MS.Book.Convolve.T (Raw (Root.Mode T G) ℂ)}

/-- Do the required insertion stitching entirely inside the same finite
symbol calculus, through the explicit Fourier/linear row changes. `X` and `Y`
are replacement mark variables (cover-position and based respectively). `hi`
shares the markings after putting `Uv ∘ Ψ`, i.e. the composite back projection
to the common Landau gauge *inside* the based theory. Does NOT establish that all
projected coefficients are unchanged after any later *field* and *coupling*
conversion: those require actual parameter identities in `PhysicalSum`. -/
lemma master_comparison (hi : promote Uv (promote Ψ X) = promote Uv Y) (hX : Γ X Σ')
    (hY : Γ Y (dg T G)) (i : ℕ) :
    View Λ ((PermV Σ').core (exp0 Σ' (promote Φ (bareX G D₀))) (promote Φ X) i) =
      View C' ((PermV (dg T G)).core (exp0 (dg T G) (Root.interaction T G)) Y i) := by
  let p := dg T G
  let s := σbranch (G := G) (n := P.side)
  let U := bareX G D₀
  let A := (PermV s).core (exp0 s U) X
  let V := (PermV p).core (exp0 p (Root.interaction T G)) Y
  have Hv : V i ∈ Mini _ := fee_spec (ΤΓ_pair (expΓ (exp_paid T G)) hY i (Set.mem_univ _)) |>.2
  have HL : A i ∈ Mini _ := fee_spec (ΤΓ_pair (expΓ (posΓ G P.side)) hX i (Set.mem_univ _)) |>.2
  let Z := specialize_tether (Position.role G (n := P.side))
  let H0 := specialize_tether (Quo.location_tie T G (averageM T G))
  let H1 := specialize_tether (Quo.plane_wire T G)
  have hz : promote Φ A = (PermV s).core (exp0 s (promote Φ U)) (promote Φ X) := by
    rw [show promote Φ A = _ from (Z.Extrapolation useN).craft ..]
    rw [show pointL ℕ Φ (exp0 s U) = exp0 s (promote Φ U) from funext fun i => Z.figure useN U i]
    rfl
  have hc : promote Uv (promote Ψ A) = promote Uv V := by
    have hx : promote Uv (promote Ψ (exp0 s U)) = exp0 p (promote Uv (promote Ψ U)) := by
      rw [show promote Ψ (exp0 s U) = exp0 p (promote Ψ U) from funext fun i => H0.figure useN U i]
      exact funext fun i => H1.figure useN _ i
    rw [show promote Ψ A = (PermV p).core (promote Ψ (exp0 s U)) (promote Ψ X) from
        (H0.Extrapolation useN).craft ..,
      show
        promote Uv _ = (PermV p).core (promote Uv (promote Ψ (exp0 s U))) (promote Uv (promote Ψ X))
        from (H1.Extrapolation useN).craft (promote Ψ (exp0 s U)) (promote Ψ X),
      hx, show promote Uv (promote Ψ U) = _ from input_compare T G, hi,
      show promote Uv V = (PermV p).core (promote Uv (exp0 p (Root.interaction T G))) (promote Uv Y)
        from (H1.Extrapolation useN).craft ..,
      show promote Uv (exp0 p (Root.interaction T G)) = exp0 p (promote Uv (Root.interaction T G))
        from funext fun i => H1.figure useN _ i]
  rw [show (PermV Σ').core _ _ i = (Φ (A i)) from (congr_fun hz i).symm, wick_natural _ _ HL]
  change View (foldedK G D₀) (A i) = View C' (V i)
  rw [← folding T G, ← wick_natural _ _ HL]
  nth_rw 1 [← prop_invariant T G]
  rw [← wick_natural _ _ ?_, show Uv (Ψ (A i)) = Uv (V i) from congr_fun hc i, wick_natural _ _ Hv,
    prop_invariant]
  obtain ⟨k, hk⟩ := HL
  exact minH (specialize_limit _ hk)

lemma true_vacuum (i : ℕ) :
    View Λ (exp0 Σ' (promote Φ (bareX G D₀)) i) = PowerSeries.coeff i (XSpace.Bare.vacuum T G) := by
  let X := (PermV Σ').unit
  let Y := (PermV (dg T G)).unit
  have ht : promote Φ X = X :=
    ((specialize_tether (Position.role G (n := P.side))).Extrapolation useN).unit
  have hp : promote Ψ X = Y :=
    ((specialize_tether (location_tie T G (averageM T G))).Extrapolation useN).unit
  have he :=
    master_comparison T G (X := X) (Y := Y) (by rw [hp]) (refineπ useN _ (feeUnit (p := Σ')))
      (refineπ useN _ (feeUnit (p := dg T G))) i
  rw [ht, (PermV Σ').identityR, (PermV (dg T G)).identityR] at he
  exact he.trans (Root.vacuum_comparison T G (Quo.split T G) i)

variable (O : Wilson.Config G P.side → ℝ)

abbrev in_chart (O : Wilson.Config G P.side → ℝ) :=
  O ∘ Native.Chart.nation

def letterField (d : ℕ) :=
  rankLevel (↑d) (ink (glow G (Site P.side)).e0 (in_chart G O))

def asTree (O : Wilson.Config G P.side → ℝ) :=
  O ∘ P.restore

variable (d : ℕ)

lemma restore_raise : asTree G O ∘ raised G = (O ∘ Native.Chart.nation) ∘ expander P G := by
  funext q
  exact congr_arg O (exponentiate G q).symm

variable (hg : germ (in_chart G O))
  (hO : ∀ a : Site P.side → G.El, (∀ x, a (-x) = a x) → ∀ u, O (Lattice.gauge a u) = O u)
  (h : From (ink (glow G (Site P.side)).e0 (in_chart G O)) d)
include hg

lemma stencilG : germ (asTree G O ∘ raised G) := by
  rw [restore_raise]
  exact
    ContDiffAt.comp (f := ⇑(expander P G)) 0
      (by
        rw [map_zero]
        exact hg)
      (expander P G).contDiff.contDiffAt

lemma put :
    specialize Δ (ink (glow G (Site P.side)).e0 (in_chart G O)) = Root.stamped T G (asTree G O) := by
  rw [restrict_germ _ _ (real_average T G) _ hg]
  unfold Root.stamped
  rw [restore_raise]

lemma Q_Γ : Γ (letterField G O d) Σ' := fun _ _ =>
  ⟨mask_symmetric _ (ink_s _ (Native.glow G (Site P.side) |>.never) hg), minH (Limit.mod _ _)⟩
include h

lemma carries_from : From (Root.stamped T G (asTree G O)) d := by
  rw [← put T G O hg]
  intro l he
  rw [←
    enough l (F := specialize Δ (ink _ (in_chart G O))) (h' :=
      show (l.length : ℤ) = l.length from rfl),
    ← specialize_mask]
  have ht {F : Raw (FixedMode G P.side) ℂ} (hp : From F d) : mask (↑l.length) F = 0 := by
    funext w
    by_cases hu : w.length = l.length
    rw [enough w (by omega), hp w (by omega)]
    rfl
    exact strange w (by omega)
  rw [ht h, map_zero]
  rfl
include hO

lemma true_stencil (i : ℕ) :
    View Λ ((PermV Σ').core (exp0 Σ' (promote Φ (bareX G D₀))) (promote Φ (letterField G O d)) i) =
      PowerSeries.coeff i (XSpace.Bare.diagrams T G (bareMark T G (asTree G O) d)) := by
  let Y := rankLevel (↑d) (Root.stamped T G (asTree G O))
  let V := letterField G O d
  have he : promote Ψ V = Y := by
    funext n
    unfold V Y letterField
    rw [promised]
    unfold rankLevel
    rw [specialize_mask, put T G O hg]
  refine
    (master_comparison T G (X := V) (Y := Y) (by rw [he]) (Q_Γ G O d hg)
          (Root.field_Γ T G _ d (stencilG G O hg)) i).trans
      (Root.field_comparison T G (Quo.split T G) _ d (stencilG G O hg) ?_ (carries_from T G O d hg h)
        i)
  intro a _ v
  rw [asTree, Function.comp_apply, P.act_restores, hO _ (fun x => congr_arg a (P.vertex_neg x))]
  rfl

def coefficientsR (O : Wilson.Config G P.side → ℝ) (d : ℕ) (i : ℕ) :=
  PowerSeries.coeff i (XSpace.Bare.normalized T G (bareMark T G (asTree G O) d))

theorem reads_member :
    Endμ Λ Σ' (promote Φ (bareX G D₀)) (promote Φ (letterField G O d)) (coefficientsR T G O d) := by
  ext1 i
  have he := XSpace.Bare.normalize_denominator T G (bareMark T G (asTree G O) d)
  rw [mul_comm] at he
  change View Λ _ = ∑ k ∈ Finset.antidiagonal i, _
  rw [true_stencil T G O d hg hO h i, ← he, PowerSeries.coeff_mul]
  exact
    Finset.sum_congr rfl fun j _ =>
      congr_arg (· * coefficientsR T G O d j.2) (true_vacuum T G j.1).symm

theorem any_tree (L : P.Tree) : coefficientsR T G O d = coefficientsR L G O d := by
  apply classicalμ _ (reads_member T G O d hg hO h) (reads_member L G O d hg hO h)
  rw [promised, bareX, if_pos rfl, map_zero]
end YM.WilsonMS.Quo
