import YM.WilsonMS.Top.TreePropagator
import YM.WilsonMS.Top.Pull

/-! # Restrict to the tree Lagrangian

`embedP` selects entries in the reduced calculation. The polynomial symbols
we use keep the FP terms until this restriction has been performed.

The ghost terms in the tree interaction at *positive* orders drop out.
Not by ignoring any field dependent determinant in the original gauge!
It uses the based choice of ghosts and the supports of the tree propagator.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Root
open XSpace Period Lattice Function Filter Set Finset
open MS MS.Bare MS.Bare.Focus MS.Cylinder MS.Cylinder.Taylor MS.Native
open MS.Koszul MS.Book MS.Book.Convolve MS.Swirl MS.Orbit MS.Orbit.Cog Darboux Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff

section
variable {X Y I : Type} [Fintype X] [DecidableEq X] (f : Y → X) (l : List Y) (F : Raw X ℂ)

lemma specialize_inclusion : specialize (inclusion f) F l = F (l.map f) := by
  induction l generalizing F with
  | nil => rfl
  | cons i l ih =>
    rw [List.map_cons, D_eval i (specialize _ _), specialize_deriv,
      Finset.sum_eq_single_of_mem (f i) (mem_univ (f i)), inclusion_at, one_smul]
    exact ih _
    intro a _ ha
    rw [inclusion_else _ _ _ (Ne.symm ha), zero_smul]

omit [Fintype X] in
lemma incl_tie (p : Sector X) : Tie p (p ∘ f) (inclusion f)ᵀ := fun i j hj => by
  change p i = p (f j)
  congr
  exact Classical.byContradiction fun he => hj (inclusion_else _ _ _ (Ne.symm he))

lemma include_specialize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ)
    (T : X → E) : specialize (inclusion f) (ink T F) = ink (T ∘ f) F := by
  ext l
  rw [specialize_inclusion]
  induction l generalizing F with
  | nil => rfl
  | cons a l ih => exact ih _

omit [Fintype X] in
lemma include_zero [Fintype Y] (K : Matrix Y I ℂ) (y) {i : X} (h : i ∉ Set.range f) :
    (inclusion f * K) i y = 0 := by
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun j _ => by rw [inclusion_else _ _ _ (fun he => h ⟨_, he⟩), zero_mul]
end

variable {P : Period} (T : P.Tree) (G : Gauge)

local instance polyDecide : DecidableEq (Root.Mode T G) :=
  Classical.decEq _

abbrev PlaneT :=
  T.Key G ⊕ (GhostI T G ⊕ GhostI T G)

def embedP : PlaneT T G → Root.Mode T G
  | .inl i => Darboux.a (freeI T G i)
  | .inr (.inl i) => Darboux.c i
  | .inr (.inr i) => Darboux.k (treeI T G i)

lemma plane_injective : Function.Injective (embedP T G) := by
  rintro (a | x | y) (b | i | j)
  all_goals
    simp only [embedP, Darboux.a, Darboux.c, Darboux.k, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq,
      imp_false, imp_self, not_false_eq_true]
  all_goals
    first
    | exact fun h => free_inj T G h
    | exact fun h => tree_inj T G h

local notation "𝒥" => inclusion (embedP T G)
local notation "p'" => Darboux.parity ∘ embedP T G
local notation "tprop" => propagator (cutCov T G) (cutL T G)

def sliceRows : Matrix (T.Key G) (PlaneT T G) ℂ :=
  open Classical in (inclusion (fun i : T.Key G => (Sum.inl i : PlaneT T G)))ᵀ

abbrev planeK : Grain (PlaneT T G) := fun i j => tprop (embedP T G i) (embedP T G j)

lemma noOff (i : Root.Mode T G) (hi : i ∉ Set.range (embedP T G)) (j) : tprop i j = 0 := by
  suffices H : Darboux.covariance (cutCov T G) (cutL T G) i j = 0 by simp [propagator, H]
  let L := cutL T G
  let V := inclusion (treeI T G)
  rcases i with (i | i) | (i | i)
  · rcases j with (j | j) | (j | j) <;> try rfl
    change cutCov T G i j = 0
    rw [cutCov, Matrix.mul_assoc]
    refine include_zero (freeI T G) _ _ (fun ⟨y, hy⟩ => hi ⟨Sum.inl y, ?_⟩)
    simp [embedP, hy, Darboux.a]
  · exact (hi ⟨Sum.inr (Sum.inl i), rfl⟩).elim
  · rcases j with (j | j) | (j | j) <;> try rfl
    have he : Lᵀ = V * ((treeMatrix T G)⁻¹)ᵀ := by
      unfold L cutL
      rw [transpose_mul, transpose_transpose]
    change Lᵀ i j = 0
    rw [he]
    refine include_zero (treeI T G) _ _ (fun ⟨y, hy⟩ => hi ⟨Sum.inr (Sum.inr y), ?_⟩)
    simp [embedP, hy, Darboux.k]
  rfl

lemma plane_covariance : induce 𝒥 (planeK T G) = tprop := by
  let f := embedP T G
  let L := Matrix.of tprop
  let W := Matrix.of (planeK T G)
  let Q : Grain (Root.Mode T G) := tprop
  have hv : Cog.Sym Darboux.parity tprop := propSym (tree_splitting T G |>.symmC)
  funext i j
  by_cases he : i ∈ Set.range f
  swap
  · rw [noOff T G i he j]
    change (𝒥 * W * 𝒥ᵀ) i j = 0
    rw [Matrix.mul_assoc]
    exact include_zero _ _ _ he
  by_cases hh : j ∈ Set.range f
  swap
  · rw [show tprop i j = 0 from (by rw [hv i j, noOff T G j hh i, mul_zero])]
    change (𝒥 * W * 𝒥ᵀ)ᵀ j i = 0
    rw [transpose_mul, transpose_transpose]
    exact include_zero _ _ _ hh
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := hh
  have hu := inclusion_mul (plane_injective T G)
  rw [induce_value]
  rw [sum_eq_single_of_mem j (mem_univ j), sum_eq_single_of_mem i (mem_univ i),
    show 𝒥 _ i = _ from inclusion_at (embedP T G) i, show 𝒥 _ j = _ from inclusion_at (embedP T G) j,
    one_mul, mul_one]
  · intro x _ hx
    rw [inclusion_else _ _ _ (fun he => hx (plane_injective T G he)), zero_mul, zero_mul]
  intro y _ hy
  rw [Finset.sum_eq_zero]
  intro x _
  rw [inclusion_else (embedP T G) (f j) _ (fun he => hy (plane_injective T G he)), mul_zero]

lemma projection_tied : Tie (fun _ : T.Key G => false) (p') (sliceRows T G)ᵀ := by
  intro i j h
  unfold sliceRows at h
  rw [transpose_transpose] at h
  have hj : Sum.inl i = j := Classical.byContradiction fun he => h (inclusion_else _ _ _ he)
  subst j
  rfl

lemma plane_ink (f : LogSpace G P → ℝ) (hf : germ f) :
    specialize 𝒥 (ink (coordinates T G).e0 f) =
      specialize (sliceRows T G) (ink (T.basis G) (f ∘ plantL T G)) := by
  classical
  let g := f ∘ plantL T G
  rw [include_specialize, ink_ctrl_one _ _ hf]
  let Y := plantL T G ∘ T.basis G
  let X : Matrix (PlaneT T G) (T.Key G) ℝ := fun i j => if Sum.inl j = i then (1 : ℝ) else 0
  have he : (sliceRows T G)ᵀ = X.map Complex.ofReal := by
    unfold sliceRows
    rw [transpose_transpose]
    ext i j
    unfold X inclusion
    rw [Matrix.map_apply]
    dsimp only
    split_ifs <;> simp
  rw [show specialize (sliceRows T G) (ink Y f) = shade (sliceRows T G)ᵀ (region.symm (ink Y f)) from
      specialize_shade _ (region.symm (ink Y f)),
    he]
  refine (scale_pos Y _ (fun i j => X i j) (fun i => ?_) hf)
  rcases i with i | j | j
  · rw [sum_eq_single_of_mem i (mem_univ i)]
    · unfold X
      rw [if_pos rfl, one_smul]
      exact (plantA_basis T G _).symm
    intro j _ hj
    unfold X
    rw [if_neg (fun he => hj (Sum.inl.inj he)), zero_smul]
  all_goals
    change (0 : LogSpace G P) = _
    symm
    apply Finset.sum_eq_zero
    intro k _
    unfold X
    rw [if_neg (by simp), zero_smul]

lemma projection_ghost (y : LinksI G P) (j : GhostI T G) (hh : y.1 ∈ T.edges) :
    ∃ x : ℂ,
      specialize 𝒥 (ink (coordinates T G).e0 ((coordinates T G).seed y ∘ localVector T G j)) =
        coin x := by
  let g : LogSpace G P → ℝ := ((coordinates T G).seed y ∘ localVector T G j)
  have he (z : T.Field G) : g (plantL T G z) = g 0 := by
    change projector y _ = projector y (localVector T G j 0)
    rw [projector_k, projector_k, value_local, value_local T G j 0, plant_apply, Tree.prolong,
      dif_pos hh]
    rfl
  refine ⟨↑(g 0), ?_⟩
  rw [plane_ink _ _ g (site_lie T G |>.vectorSeed _ y j),
    funext (show ∀ z, (g ∘ plantL T G) z = g 0 from he), ink_const, specialize_coin]

lemma interaction_ghost :
    Book.rank 2
      (specialize 𝒥
        ((pairs T G).hung
          (launch (coordinates T G) (Native.colorTerm G T.Nonroot) (localVector T G)))) := by
  classical
  let J := specialize 𝒥
  let Y := coordinates T G
  let X := chartFocus T G
  let B := pairs T G
  let V := localVector T G
  let L := launch Y (colorTerm G T.Nonroot) V
  let s : Sector (PlaneT T G) := Darboux.parity ∘ embedP T G
  have ht (p q : Raw (Mode T G) ℂ) : J (product (dg T G) p q) = product s (J p) (J q) :=
    (specialize_tether (incl_tie (embedP T G) _)).craft p q
  have hv i (h : i ∉ Set.range (embedP T G)) : J (atLetter i) = 0 := by
    unfold J
    rw [specialize_letter]
    exact Finset.sum_eq_zero fun j _ => by rw [inclusion_else _ _ _ (fun he => h ⟨j, he⟩), zero_smul]
  unfold Bonded.hung
  rw [map_sum]
  refine Rails.sum _ (fun i _ => ?_)
  rw [map_smul]
  apply Rails.smul
  change Book.rank _ (J (product (dg T G) _ (L i)))
  rw [ht]
  rcases i with i | i
  · by_cases he : i.1 ∈ T.edges
    swap
    · rw [hv (B.dual (Sum.inl i))
          (by
            rintro ⟨j, hj⟩
            rcases j with j | j | j
            cases hj
            cases hj
            unfold B pairs ports at hj
            have hh : treeI T G j = i := Sum.inl.inj (Sum.inr.inj hj)
            apply he
            rw [← hh]
            exact (T.mem_edges _).mpr ⟨_, _, rfl⟩),
        map_zero]
      exact Rails.zero
    apply Rails.product (v := fun _ => 1) (h := 1) (h' := 1) (specialize_rank _ (Rails.letter _))
    rw [show L (.inl i) = stone Y V i from launch_stone .., stone, map_sum]
    refine Rails.sum _ (fun j _ => ?_)
    rw [ht]
    obtain ⟨x, hx⟩ := projection_ghost T G i j he
    rw [show J _ = coin x from hx]
    exact Rails.product (h := 1) (h' := 0) (specialize_rank _ (Rails.letter _)) (Rails.coin x)
  rw [hv (B.dual (Sum.inr i))
      (show b i ∉ Set.range (embedP T G) from fun ⟨x, hx⟩ => by rcases x with x | x | x <;> cases hx),
    map_zero]
  exact Rails.zero

def sliceInteraction (i : ℕ) : Raw (T.Key G) ℂ :=
  if i = 0 then 0
  else
    rankLevel 2 (ink (T.basis G) (-T.action (G := G))) i +
      rankLevel 0 (ink (T.basis G) (orbitLog G ∘ plantL T G)) i

lemma transfers :
    promote (specialize 𝒥) (interaction T G) =
      promote (specialize (sliceRows T G)) (sliceInteraction T G) := by
  ext1 n
  by_cases hv : n = 0
  · subst n
    rw [promised, happy, map_zero, promised, sliceInteraction, if_pos rfl, map_zero]
  rw [promised, promised, sliceInteraction, interaction, if_neg hv, if_neg hv]
  unfold exponent uncoupled haarLog Sourced
  simp_rw [Pi.add_apply, rankLevel, map_add, specialize_mask]
  rw [rank_off (interaction_ghost T G) (by omega), add_zero, plane_ink _ _ _ (energy_germ P G),
    relative_action, plane_ink _ _ _ (orbit_germ G)]

lemma plane_stencil (d : ℕ) (O : P.Array G → ℝ) (hf : germ (O ∘ raised G)) :
    promote (specialize 𝒥) (rankLevel d (stamped T G O)) =
      promote (specialize (sliceRows T G))
        (rankLevel d (ink (T.basis G) ((O ∘ raised G) ∘ plantL T G))) := by
  funext n
  unfold promote rankLevel
  simp_rw [LinearMap.coe_mk, AddHom.coe_mk, specialize_mask, stamped, plane_ink T G _ hf]

def sliceK : Grain (T.Key G) :=
  induce (sliceRows T G) (planeK T G)

lemma slice_covariance (i j : T.Key G) : Chill (sliceK T G) i j = ((T.covariance G i j : ℝ) : ℂ) := by
  unfold Chill sliceK induce sliceRows
  rw [transpose_transpose, col_inclusion, row_inclusion]
  let f := freeI T G
  rw [Matrix.of_apply]
  change Chill tprop (a (f i)) (a (f j)) = _
  rw [correlation]
  change cutCov T G (f i) (f j) = _
  rw [← row_inclusion f (cutCov T G), ← col_inclusion f ((inclusion f)ᵀ * cutCov T G), cutCov]
  have he := inclusion_mul (free_inj T G)
  dsimp only [f]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, he, Matrix.one_mul, Matrix.mul_assoc, he,
    Matrix.mul_one]
  rfl

open MS.Puff MS.Puff.Engine MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom

lemma slice_answer {X : MS.Book.Convolve.T (Raw (Root.Mode T G) ℂ)}
    {Y : MS.Book.Convolve.T (Raw (T.Key G) ℂ)} (hp : Γ X (dg T G)) (hq : Γ Y (fun _ => false))
    (hx : promote (specialize 𝒥) X = promote (specialize (sliceRows T G)) Y) (i : ℕ) :
    let p := dg T G
    let q : T.Key G → Bool := fun _ => false
    View tprop ((PermV p).core (exp0 p (interaction T G)) X i) =
      View (sliceK T G) ((PermV q).core (exp0 q (sliceInteraction T G)) Y i) := by
  intro p q
  let U := interaction T G
  let S := sliceInteraction T G
  let V := (PermV p).core (exp0 p U) X
  let W := (PermV q).core (exp0 q S) Y
  have hU : Γ U p := by
    intro j _
    unfold U interaction
    split
    · exact (FeeP p).zero_mem
    exact
      ⟨(mask_symmetric _ (uncoupled_symm T G)).add (mask_symmetric _ (log_symm T G)),
        (Mini _).add_mem (minH (Limit.mod _ _)) (minH (Limit.mod _ _))⟩
  let Y' : T.Field G → ℝ := -T.action
  have hY : germ (orbitLog G ∘ plantL T G) :=
    (ContDiffAt.comp (f := ⇑(plantL T G)) 0
      (by
        rw [map_zero]
        exact orbit_germ G)
      (plantL T G).contDiff.contDiffAt)
  have hSig : Γ S q := by
    intro j _
    unfold S sliceInteraction
    split
    · exact (FeeP q).zero_mem
    have hs : ContDiffAt ℝ ω Y' 0 := (T.continuousJet G).neg
    exact
      ⟨(mask_symmetric _ (ink_s _ (p := q) (fun _ h => Bool.noConfusion h) hs)).add
          (mask_symmetric _ (ink_s _ (fun _ h => Bool.noConfusion h) hY)),
        (Mini _).add_mem (minH (Limit.mod _ _)) (minH (Limit.mod _ _))⟩
  have hv : V i ∈ Mini _ := (fee_spec (ΤΓ_pair (expΓ hU) hp i (Set.mem_univ _))).2
  have hw : W i ∈ Mini _ := (fee_spec (ΤΓ_pair (expΓ hSig) hq i (Set.mem_univ _))).2
  let J := specialize 𝒥
  let M := specialize (sliceRows T G)
  have H : Tether J (actor p) (actor (p')) := specialize_tether (incl_tie (embedP T G) (dg T G))
  have HG : Tether M (actor q) (actor (p')) := specialize_tether (projection_tied T G)
  have he : promote J V = promote M W := by
    have ht : promote J (exp0 p U) = exp0 (p') (promote J U) := funext fun i => H.figure useN U i
    have hu : promote M (exp0 q S) = exp0 (p') (promote M S) := funext fun i => HG.figure useN S i
    rw [show promote J V = (PermV (p')).core (promote J (exp0 p U)) (promote J X) from
        (H.Extrapolation useN).craft ..,
      show promote M W = (PermV (p')).core (promote M (exp0 q S)) (promote M Y) from
        (HG.Extrapolation useN).craft ..,
      ht, hu, hx, show promote J U = promote M S from transfers T G]
  rw [← plane_covariance T G, ← wick_natural 𝒥 (planeK T G) hv,
    show specialize 𝒥 _ = specialize (sliceRows T G) (W i) from congr_fun he i,
    wick_natural (sliceRows T G) (planeK T G) hw]
  rfl
end YM.WilsonMS.Root
