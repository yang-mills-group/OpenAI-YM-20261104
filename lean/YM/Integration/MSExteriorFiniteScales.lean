import YM.Integration.MSExteriorOrigins
import YM.FVA2.PlaneTime
import YM.MS.Wind.Dawn

/-! Reducing the original independent MS exterior estimate over every subtraction
scale to estimates at finitely many fixed scales, uniformly on all separated
configurations in a family. The only extra input concerns the proposed output table. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.MSExteriorFiniteScales
open Function Filter Set Finset Real MS MS.Tone MS.Rake MS.Menus MS.Land MS.Logarithm
open MSExteriorDilation
open MeasureTheory
open scoped BigOperators Topology Classical

variable {I : Type} {G : Gauge} {B : MS.Local.Physical.Deck G} {Q : Booked B} {n m H : ℕ}

/-- The genuine original MS polynomial log law holds on a family with arbitrarily
receding points. No common-mesh radius is required. -/
theorem tour_polynomial (M : MS_Data G Q) (R : Fin n → Label B) (q : I → Fin n → QP)
    (hq : ∀ i, Injective (q i)) (k : ℕ) : Ready (fun v i => moment M R v (q i) k) :=
  FV2Mod.toured M q hq R univ k

/-- All exterior perturbative orders in the finite projected OPE inherit the
logarithmic polynomial law of the original measured moments. -/
theorem residual_polynomial (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (C : I → MSExteriorDilation.Table B H) (q : I → Fin (n+m) → QP) (u : I → Fin (1+m) → QP)
    (hq : ∀ i, Injective (q i)) (hu : ∀ i, Injective (u i)) (k : ℕ)
    (hc : ∀ a j,j ≤ k → Ready (fun v i => C i a j v)) :
    Ready (fun v i => far M R L (C i) v (q i) (u i) k) := by
  let A (a : Glyph B H) (p : ℕ × ℕ) (v : ℝ) (i : I) := C i a p.1 v * moment M (centered a L) v (u i) p.2
  have hA (a : Glyph B H) (p : ℕ × ℕ) (h : p ∈ HasAntidiagonal.antidiagonal k) : Ready (A a p) := by
    obtain hp := HasAntidiagonal.mem_antidiagonal.mp h
    exact Ready.pair (LinearMap.mul ℝ (I → ℂ)) (hc a p.1 (by omega)) (tour_polynomial M _ u hu _)
  have hor (a : Glyph B H) : Ready (fun v => ∑ p ∈ HasAntidiagonal.antidiagonal k,A a p v) :=
    FV2Mod.latSum _ (hA a)
  have hsum := FV2Mod.latSum (E := I → ℂ) univ (fun a _ => hor a)
  have hd := (tour_polynomial M (Fin.append R L) q hq k).sub hsum
  simpa only [far,A,Finset.sum_apply,Pi.sub_def] using hd

/-- Uniform polynomial growth of a real interpolation coefficient. -/
theorem polynomial_bound (P : Poly) : ∃ B : ℝ,0≤B ∧ ∃ j : ℕ,∀ v : ℝ,
    ‖P.eval v‖ ≤ B*(1+|v|)^j := by
  obtain ⟨k,C,hC,h⟩ := (Wind.poly_t P).norm_iteratedFDeriv_le_uniform 0
  exact ⟨C,hC,k,fun v => by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h 0 le_rfl v⟩

theorem weights (s : Finset ℕ) (P : ℕ → Poly) : ∃ B : ℝ,0≤B ∧ ∃ j : ℕ,∀ v : ℝ,
    ∑ i ∈ s,‖(P i).eval v‖ ≤ B*(1+|v|)^j := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0,le_rfl,0,by simp⟩
  | insert i s hi ih =>
    obtain ⟨A,hA,j,hj⟩ := polynomial_bound (P i)
    obtain ⟨C,hC,l,hl⟩ := ih
    refine ⟨A+C,add_nonneg hA hC,j+l,fun v => ?_⟩
    have hb : (1:ℝ) ≤ 1+|v| := le_add_of_nonneg_right (abs_nonneg v)
    rw [Finset.sum_insert hi,add_mul]
    exact add_le_add ((hj v).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (by omega)) hA))
      ((hl v).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (by omega)) hC))

/-- The same finite list of integer log scales determines all members of a
family. The constants depend on that list alone. -/
theorem finite_observations {F : ℝ → I → ℂ} (h : Ready F) :
    ∃ N : ℕ, ∃ A : ℝ,0≤A ∧ ∃ j : ℕ,∀ i v,∀ B : ℝ,0≤B →
      (∀ p ∈ Finset.range N,‖F p i‖ ≤ B) → ‖F v i‖ ≤ A*(1+|v|)^j*B := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨A,hA,j,hj⟩ := weights (Finset.range N) (plate N)
  refine ⟨N,A,hA,j,fun i v B hB hf => ?_⟩
  have he := congrFun (interpret hN v) i
  simp only [evaluate,Finset.sum_apply,Pi.smul_apply] at he
  rw [he]
  calc
    _ ≤ ∑ p ∈ Finset.range N,‖(plate N p).eval v • F p i‖ := norm_sum_le ..
    _ ≤ ∑ p ∈ Finset.range N,‖(plate N p).eval v‖*B := Finset.sum_le_sum fun p hp => by
      rw [norm_smul];exact mul_le_mul_of_nonneg_left (hf p hp) (norm_nonneg _)
    _ = (∑ p ∈ Finset.range N,‖(plate N p).eval v‖)*B := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hj v) hB

/-- No numerical estimate is assumed in this reduction for the actual signed
front and the entire independent exterior projection. -/
theorem far_observations (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (C : I → MSExteriorDilation.Table B H) (q : I → Fin (n+m) → QP) (u : I → Fin (1+m) → QP)
    (hq : ∀ i, Injective (q i)) (hu : ∀ i, Injective (u i)) (k : ℕ)
    (hc : ∀ a j,j ≤ k → Ready (fun v i => C i a j v)) :
    ∃ N : ℕ, ∃ A : ℝ,0≤A ∧ ∃ j : ℕ,∀ i v,∀ D : ℝ,0≤D →
      (∀ p ∈ Finset.range N,‖far M R L (C i) p (q i) (u i) k‖ ≤ D) →
      ‖far M R L (C i) v (q i) (u i) k‖ ≤ A*(1+|v|)^j*D :=
  finite_observations (residual_polynomial M R L C q u hq hu k hc)

/-- Reindex a uniform log polynomial by any family of test geometries. -/
theorem reindex {J : Type} {F : ℝ → I → ℂ} (h : Ready F) (g : J → I) :
    Ready (fun v j => F v (g j)) := by
  let A : (I → ℂ) →ₗ[ℝ] (J → ℂ) :=
    { toFun := fun f => f ∘ g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact h.linear A

/-- Any finite prescription of numerical table entries at integer subtraction
scales extends to a single polynomial table on all running scales. -/
def interpolate (N : ℕ) (C : I → MSExteriorDilation.Table B H) (i : I) : MSExteriorDilation.Table B H := fun a k v =>
  evaluate N (fun u i => C i a k u) v i

theorem interpolated (N : ℕ) (C : I → MSExteriorDilation.Table B H) (a : Glyph B H) (k : ℕ) :
    Ready (fun v i => interpolate N C i a k v) := eval_ready N _

theorem at_node (N : ℕ) (C : I → MSExteriorDilation.Table B H) (a : Glyph B H) (k : ℕ) (i : I) {p : ℕ} (hp : p ∈ Finset.range N) :
    interpolate N C i a k p = C i a k p := by
  simp only [interpolate,evaluate,Finset.sum_apply,Pi.smul_apply]
  rw [Finset.sum_eq_single p]
  · rw [plate,Lagrange.eval_basis_self (Nat.cast_injective.injOn) hp,one_smul]
  · intro b _ h
    rw [plate,Lagrange.eval_basis_of_ne h hp,zero_smul]
  · exact fun h => (h hp).elim

abbrev Separated (r : ℕ) := {x : Fin r → QP // Injective x}

/-- The sample count and the amplification bound can be fixed before choosing an
inner compact, an exterior compact, or a specific common separation trajectory. -/
theorem universal (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (C : Separated n → MSExteriorDilation.Table B H) (k : ℕ) (hc : ∀ a j,j ≤ k → Ready (fun v i => C i a j v)) :
    ∃ N : ℕ, ∃ A : ℝ, 0≤A ∧ ∃ j : ℕ,∀ x : Separated n,∀ q : Separated (n+m),∀ u : Separated (1+m),
      ∀ v D : ℝ,0≤D → (∀ p ∈ Finset.range N,‖far M R L (C x) p q.val u.val k‖ ≤ D) →
        ‖far M R L (C x) v q.val u.val k‖ ≤ A*(1+|v|)^j*D := by
  let S := Separated n × Separated (n+m) × Separated (1+m)
  obtain ⟨N,A,hA,j,hr⟩ := far_observations M R L (fun z : S => C z.1)
    (fun z : S => z.2.1.val) (fun z : S => z.2.2.val) (fun z => z.2.1.property) (fun z => z.2.2.property)
    k (fun a k hk => reindex (hc a k hk) (fun z : S => z.1))
  exact ⟨N,A,hA,j,fun x q u => hr (x,q,u)⟩

/-- At all sufficiently large separations it suffices to prove the far decay at
finitely many *fixed integer* subtraction scales. The exterior exponent is
kept exactly, and the running-scale and separation-log powers stay explicit. -/
theorem sampled_rate (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (C : I → MSExteriorDilation.Table B H) (q : ℝ → I → Fin (n+m) → QP) (u : ℝ → I → Fin (1+m) → QP)
    (hsep : ∀ᶠ s : ℝ in atTop, ∀ i,Injective (q s i) ∧ Injective (u s i)) (k : ℕ)
    (hc : ∀ a j,j ≤ k → Ready (fun v i => C i a j v)) :
    ∃ N : ℕ, ∃ A : ℝ,0≤A ∧ ∃ l : ℕ,∀ K : ℝ,0≤K → ∀ j : ℕ,∀ d : ℝ,
      (∀ᶠ s : ℝ in atTop,∀ i,∀ p ∈ Finset.range N,
        ‖far M R L (C i) p (q s i) (u s i) k‖ ≤ K*(1+s)^j*exp (-d*s)) →
      ∀ᶠ s : ℝ in atTop,∀ i v,
        ‖far M R L (C i) v (q s i) (u s i) k‖ ≤ (A*K)*((1+|v|)^l*(1+s)^j*exp (-d*s)) := by
  let S := {t : ℝ × I // Injective (q t.1 t.2) ∧ Injective (u t.1 t.2)}
  obtain ⟨N,A,hA,l,hr⟩ := far_observations M R L (fun z : S => C z.val.2)
    (fun z : S => q z.val.1 z.val.2) (fun z : S => u z.val.1 z.val.2)
    (fun z => z.property.1) (fun z => z.property.2) k
    (fun a j hj => reindex (hc a j hj) (fun z : S => z.val.2))
  refine ⟨N,A,hA,l,fun K hK j d hfixed => ?_⟩
  filter_upwards [hsep,hfixed,eventually_ge_atTop (0:ℝ)] with s hs hf hpos i v
  exact (hr (⟨(s,i),hs i⟩ : S) v (K*(1+s)^j*exp (-d*s)) (by positivity) (hf i)).trans_eq (by ring)

/-- A single simultaneous log-polynomial spectrum for the sampled detector
means that convergence at finitely many fixed scales produces the gains at all
running scales. The resulting coefficient table is itself log-polynomial. -/
theorem limit_from_nodes {J : Type} (l : Filter J) {F : ℝ → I × J → ℂ} (hF : Ready F) :
    ∃ N : ℕ,∀ g : ℝ → I → ℂ,
      (∀ p ∈ Finset.range N,∀ i,Tendsto (fun t => F p (i,t)) l (𝓝 (g p i))) →
      Ready (evaluate N g) ∧ ∀ v i,Tendsto (fun t => F v (i,t)) l (𝓝 (evaluate N g v i)) := by
  obtain ⟨N,hN⟩ := hF
  refine ⟨N,fun g hg => ⟨eval_ready N g,fun v i => ?_⟩⟩
  have ht := tendsto_finsetSum (Finset.range N) (fun p hp => (hg p hp i).const_smul ((plate N p).eval v))
  have eq : (fun t => F v (i,t)) = fun t => ∑ p ∈ Finset.range N, (plate N p).eval v • F p (i,t) :=
    funext fun t => by simpa only [evaluate,Finset.sum_apply,Pi.smul_apply] using congrFun (interpret hN v) (i,t)
  rw [eq]
  simpa only [evaluate,Finset.sum_apply,Pi.smul_apply] using ht

/-- Convergence along a single common finite polynomial family preserves its
logarithmic polynomial law on the entire family of inner configurations. -/
theorem ready_after_limit {J : Type} (l : Filter J) [l.NeBot] {F : ℝ → I × J → ℂ} (hF : Ready F)
    {g : ℝ → I → ℂ} (he : ∀ v i,Tendsto (fun t => F v (i,t)) l (𝓝 (g v i))) : Ready g := by
  obtain ⟨N,h⟩ := limit_from_nodes l hF
  obtain ⟨hp,hlim⟩ := h g (fun p _ i => he p i)
  have hEq : g = evaluate N g := funext fun v => funext fun i => tendsto_nhds_unique (he v i) (hlim v i)
  rwa [←hEq] at hp

/-- Any fixed finite detector assembled from genuine separated MS tours with
arbitrary separation-dependent normalizations has one shared set of subtraction
scales that determines its continuum limit. No candidate coefficient is given. -/
theorem probe_limit {J K : Type} [Fintype K] (l : Filter J) (M : MS_Data G Q)
    (R : K → Fin n → Label B) (order : K → ℕ) (w : K → I × J → ℂ)
    (q : K → I × J → Fin n → QP) (hq : ∀ b t,Injective (q b t)) :
    ∃ N : ℕ,∀ g : ℝ → I → ℂ,
      (∀ p ∈ Finset.range N,∀ i,Tendsto (fun t => ∑ b,w b (i,t) * moment M (R b) p (q b (i,t)) (order b)) l (𝓝 (g p i))) →
      Ready (evaluate N g) ∧ ∀ v i,
        Tendsto (fun t => ∑ b,w b (i,t) * moment M (R b) v (q b (i,t)) (order b)) l (𝓝 (evaluate N g v i)) := by
  apply limit_from_nodes (F := fun v (z : I × J) => ∑ b,w b z * moment M (R b) v (q b z) (order b)) l
  have h (b : K) : Ready (fun v t => w b t * moment M (R b) v (q b t) (order b)) :=
    Ready.pair (LinearMap.mul ℝ (I × J → ℂ)) (Ready.const (w b)) (tour_polynomial M (R b) (q b) (hq b) (order b))
  have hsum := FV2Mod.latSum (E := I × J → ℂ) univ (fun b _ => h b)
  convert hsum using 1
  funext v z
  rw [Finset.sum_apply]

/-- A table at one reference scale determines the homogeneous running table.
The engineering factor is the actual sum of input grades minus the output grade. -/
def normalized (R : Fin n → Label B) (A : (Fin n → QP) → Glyph B H → ℕ → ℂ)
    (x : Fin n → QP) : MSExteriorDilation.Table B H := fun a k v =>
  power ((weight R : ℝ)-a.size) v * A (stretch v x) a k

theorem stretch_zero (x : Fin n → QP) : MSExteriorDilation.stretch 0 x=x := by
  funext i
  simp only [MSExteriorDilation.stretch,Real.exp_zero,one_smul]

theorem reference (R : Fin n → Label B) (A : (Fin n → QP) → Glyph B H → ℕ → ℂ)
    (x : Fin n → QP) (a : Glyph B H) (k : ℕ) : normalized R A x a k 0 = A x a k := by
  simp [normalized,power,stretch_zero]

theorem to_zero (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (A : (Fin n → QP) → Glyph B H → ℕ → ℂ) (x : Fin n → QP) (v : ℝ)
    (q : Fin (n+m) → QP) (u : Fin (1+m) → QP) (hq : Injective q) (hu : Injective u) (k : ℕ) :
    far M R L (normalized R A x) v q u k = power ((weight R : ℝ)+weight L) v *
      far M R L (normalized R A (stretch v x)) 0 (stretch v q) (stretch v u) k := by
  calc
    _ = near M R L (normalized R A (stretch v x)) v v q u k := by
      simp [far,near,normalized,power,stretch_zero]
    _ = _ := by simpa only [sub_self] using scale_residual M R L (normalized R A (stretch v x)) v v q hq u hu k

theorem stretch_commute (v s : ℝ) (y : Fin m → QP) : stretch v (stretch s y) = stretch s (stretch v y) := by
  funext i
  simp only [stretch,smul_smul,mul_comm]

theorem stretch_receding (v s : ℝ) (x : Fin n → QP) (y : Fin m → QP) :
    stretch v (receding s x y) = receding s (stretch v x) (stretch v y) := by
  funext i
  induction i using Fin.addCases with
  | left j => simp only [stretch,receding,Fin.append_left]
  | right j => simp only [stretch,receding,Fin.append_right,smul_smul,mul_comm]

theorem separated_stretch (v : ℝ) {x : Fin n → QP} (h : Injective x) : Injective (stretch v x) := by
  intro i j eq
  apply h
  simpa only [stretch,smul_smul,← Real.exp_add,neg_add_cancel,exp_zero,one_smul] using
    congrArg (fun z : QP => exp (-v) • z) eq

theorem continuous_stretch (v : ℝ) : Continuous (stretch (n := n) v) :=
  continuous_pi fun i => (continuous_apply i : Continuous fun x : Fin n → QP => x i).const_smul (exp v)

/-- The finite union of the dilated shape families at the interpolation nodes. -/
def node_images (N : ℕ) (X : Set (Fin n → QP)) : Set (Fin n → QP) :=
  ⋃ p : Fin N, stretch (p.val : ℝ) '' X

theorem images_compact (N : ℕ) {X : Set (Fin n → QP)} (h : IsCompact X) : IsCompact (node_images N X) :=
  isCompact_iUnion fun p : Fin N => h.image (continuous_stretch (p.val : ℝ))

theorem node_mem (N p : ℕ) (hp : p ∈ Finset.range N) {X : Set (Fin n → QP)} {x : Fin n → QP} (hx : x ∈ X) :
    stretch (p : ℝ) x ∈ node_images N X :=
  Set.mem_iUnion.mpr ⟨⟨p,Finset.mem_range.mp hp⟩,⟨x,hx,rfl⟩⟩

theorem images_inner (N : ℕ) {X : Set (Fin n → QP)} (hx : ∀ x ∈ X,Injective x) :
    ∀ x ∈ node_images N X,Injective x := by
  rintro x h
  rcases Set.mem_iUnion.mp h with ⟨p,z,hz,rfl⟩
  exact separated_stretch _ (hx z hz)

theorem images_exterior (N : ℕ) {Z : Set (Fin m → QP)} (hz : ∀ y ∈ Z,Injective (origin y)) :
    ∀ y ∈ node_images N Z,Injective (origin y) := by
  rintro y h
  rcases Set.mem_iUnion.mp h with ⟨p,z,hmem,rfl⟩
  rw [← anchored]
  exact separated_stretch _ (hz z hmem)

/-- The spatial one-higher estimate on the original independently computed rows
at subtraction scale zero. The same field prescription is used for every
compact separated inner/exterior family. -/
def ReferenceBound (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (A : (Fin n → QP) → Glyph B H → ℕ → ℂ) (k : ℕ) (d : ℝ) : Prop :=
  ∀ (X : Set (Fin n → QP)) (Z : Set (Fin m → QP)), IsCompact X → IsCompact Z →
      (∀ x ∈ X,Injective x) → (∀ y ∈ Z,Injective (origin y)) →
      ∃ K : ℝ,0≤K ∧ ∃ j : ℕ,∀ᶠ s : ℝ in atTop,∀ x ∈ X,∀ y ∈ Z,
        ‖far M R L (normalized R A x) 0 (receding s x y) (origin (stretch s y)) k‖ ≤ K*(1+s)^j*exp (-d*s)

/-- For a log-polynomial normalized table, the spatial far estimate is needed
at the single original MS subtraction scale zero. Its hypothesis is uniform
in the separated inner and exterior compact families, including the full
finite independent physical projection, at that scale alone. -/
theorem fixed_reference (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (A : (Fin n → QP) → Glyph B H → ℕ → ℂ) (k : ℕ) (d : ℝ)
    (hc : ∀ a j,j ≤ k → Ready (fun v (x : Separated n) => normalized R A x.val a j v))
    (hzero : ReferenceBound M R L A k d)
    (X : Set (Fin n → QP)) (Z : Set (Fin m → QP)) (hX : IsCompact X) (hZ : IsCompact Z)
    (hi : ∀ x ∈ X,Injective x) (he : ∀ y ∈ Z,Injective (origin y)) :
    ∃ K : ℝ,0≤K ∧ ∃ l j : ℕ,∀ᶠ s : ℝ in atTop,∀ x ∈ X,∀ y ∈ Z,∀ v : ℝ,
      ‖far M R L (normalized R A x) v (receding s x y) (origin (stretch s y)) k‖ ≤
        K*((1+|v|)^l*(1+s)^j*exp (-d*s)) := by
  obtain ⟨N,F,hF,l,hinterp⟩ := universal M R L (fun x : Separated n => normalized R A x.val) k hc
  obtain ⟨K,hK,j,hnodes⟩ := hzero (node_images N X) (node_images N Z) (images_compact N hX)
    (images_compact N hZ) (images_inner N hi) (images_exterior N he)
  let w : ℝ := (weight R : ℝ)+weight L
  have hw : 0≤w := by dsimp [w]; positivity
  refine ⟨F*(exp (w*N)*K),by positivity,l,j,?_⟩
  filter_upwards [hnodes,MSExteriorCompactTests.compact_separation X Z hX hZ hi he,eventually_ge_atTop (0:ℝ)]
    with s hs hsep hpos x hx y hy v
  have hq : Injective (receding s x y) := by rw [←MSExteriorDilation.position s x y]; exact separated_stretch s (hsep x hx y hy)
  have hu : Injective (origin (stretch s y)) := by rw [←anchored]; exact separated_stretch s (he y hy)
  have hp (p : ℕ) (hn : p ∈ Finset.range N) :
      ‖far M R L (normalized R A x) p (receding s x y) (origin (stretch s y)) k‖ ≤
        exp (w*N)*(K*(1+s)^j*exp (-d*s)) := by
    have hm := hs _ (node_mem N p hn hx) _ (node_mem N p hn hy)
    rw [to_zero M R L A x (p:ℝ) _ _ hq hu k,norm_mul,stretch_receding,anchored,
      stretch_commute (p:ℝ) s,power,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (Finset.mem_range.mp hn).le) hw)) hm (norm_nonneg _) (Real.exp_pos _).le
  exact (hinterp ⟨x,hi x hx⟩ ⟨_,hq⟩ ⟨_,hu⟩ v _ (by positivity) hp).trans_eq (by ring)

/-- A fixed real subtraction log costs only a single dilation of the two
compact families at the reference log. No regularity of the field table is
used here. -/
theorem compact_slice (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (A : (Fin n → QP) → Glyph B H → ℕ → ℂ) (k : ℕ) (d : ℝ)
    (hzero : ReferenceBound M R L A k d) (v : ℝ)
    (X : Set (Fin n → QP)) (Z : Set (Fin m → QP)) (hX : IsCompact X) (hZ : IsCompact Z)
    (hi : ∀ x ∈ X,Injective x) (he : ∀ y ∈ Z,Injective (origin y)) :
    ∃ K : ℝ,0≤K ∧ ∃ j : ℕ,∀ᶠ s : ℝ in atTop,∀ x ∈ X,∀ y ∈ Z,
      ‖far M R L (normalized R A x) v (receding s x y) (origin (stretch s y)) k‖ ≤ K*(1+s)^j*exp (-d*s) := by
  obtain ⟨K,hK,j,h⟩ := hzero (stretch v '' X) (stretch v '' Z) (hX.image (continuous_stretch v))
    (hZ.image (continuous_stretch v)) (by rintro _ ⟨x,hx,rfl⟩; exact separated_stretch v (hi x hx))
    (by rintro _ ⟨y,hy,rfl⟩; rw [←anchored]; exact separated_stretch v (he y hy))
  have hsep := MSExteriorCompactTests.compact_separation X Z hX hZ hi he
  let w : ℝ := (weight R:ℝ)+weight L
  refine ⟨exp (w*v)*K,mul_nonneg (Real.exp_pos _).le hK,j,?_⟩
  filter_upwards [h,hsep] with s hs hq x hx y hy
  have hq' : Injective (receding s x y) := by rw [←MSExteriorDilation.position s x y]; exact separated_stretch s (hq x hx y hy)
  have hu : Injective (origin (stretch s y)) := by rw [←anchored]; exact separated_stretch s (he y hy)
  have hb := hs _ (Set.mem_image_of_mem (stretch v) hx) _ (Set.mem_image_of_mem (stretch v) hy)
  rw [to_zero M R L A x v _ _ hq' hu k,norm_mul,stretch_receding,anchored,stretch_commute v s,
    power,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq (by dsimp only [w];ring)

/-- The original reference-scale bound implies the native spatial rate on every
fixed real log slice, before its field polynomial law is known. -/
theorem fixed_slice (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (A : (Fin n → QP) → Glyph B H → ℕ → ℂ) (k : ℕ) (d : ℝ)
    (hzero : ReferenceBound M R L A k d) {x : Fin n → QP} {y : Fin m → QP}
    (hx : Injective x) (hy : Injective (origin y)) (v : ℝ) :
    (fun s => far M R L (normalized R A x) v (receding s x y) (origin (stretch s y)) k) ∈
      RG11.Grove.individual (-d) := by
  obtain ⟨K,hK,j,h⟩ := compact_slice M R L A k d hzero v {x} {y} isCompact_singleton isCompact_singleton
    (fun z hz => by rcases Set.mem_singleton_iff.mp hz with rfl; exact hx)
    (fun z hz => by rcases Set.mem_singleton_iff.mp hz with rfl; exact hy)
  apply RG11.Grove.personally.mpr
  refine ⟨K,j,hK,?_⟩
  filter_upwards [h,eventually_ge_atTop (0:ℝ)] with s hs hpos
  exact (hs _ (Set.mem_singleton _) _ (Set.mem_singleton _)).trans_eq (by rw [RG11.Grove.sleeve,abs_of_nonneg hpos];ring)

/-- Anti-scaling of a genuine original moment at an expanded configuration,
with its full original positive-order coefficient intact. -/
theorem receding_moment (M : MS_Data G Q) (V : Fin n → Label B) {z : Fin n → QP}
    (hz : Injective z) (v s : ℝ) (k : ℕ) :
    moment M V v (stretch s z) k = power (-(weight V : ℝ)) s * moment M V (v+s) z k := by
  have h := scales M V (v+s) s z hz k
  rw [add_sub_cancel_right] at h
  rw [h,←mul_assoc,←power_add]
  simp [power]

theorem origin_continuous : Continuous (origin (m := m)) := by
  apply continuous_pi
  intro i
  induction i using Fin.addCases with
  | left j => simpa only [origin,Fin.append_left] using (continuous_const : Continuous (fun _ : Fin m → QP => (0:QP)))
  | right j => simpa only [origin,Fin.append_right] using (continuous_apply j : Continuous fun y : Fin m → QP => y j)

theorem running_log (v s : ℝ) (hs : 0 ≤ s) : 1+|v+s| ≤ (1+|v|)*(1+s) := by
  have h := abs_add_le v s
  rw [abs_of_nonneg hs] at h
  nlinarith [mul_nonneg (abs_nonneg v) hs]

/-- All orders of the independently inserted physical output have the full
engineering decay. The same constants control every running subtraction scale
and the entire compact family of separated exterior fields. -/
theorem remote_output (M : MS_Data G Q) (a : Glyph B H) (L : Fin m → Label B)
    (Z : Set (Fin m → QP)) (hZ : IsCompact Z) (he : ∀ y ∈ Z,Injective (origin y)) (k : ℕ) :
    ∃ K : ℝ,0≤K ∧ ∃ j : ℕ,∀ s : ℝ,0≤ s → ∀ v : ℝ,∀ y ∈ Z,
      ‖moment M (centered a L) v (origin (stretch s y)) k‖ ≤
        K*((1+|v|)*(1+s))^j*exp (-((a.size:ℝ)+weight L)*s) := by
  let F (v : ℝ) (y : ↥Z) := moment M (centered a L) v (origin y.val) k
  have hF : Ready F := tour_polynomial M (centered a L) (fun y : ↥Z => origin y.val) (fun y => he y.val y.property) k
  obtain ⟨N,A,hA,j,hj⟩ := finite_observations hF
  have hb (p : ℕ) : ∃ c : ℝ,∀ y ∈ Z,‖moment M (centered a L) p (origin y) k‖ ≤ c := by
    apply hZ.exists_bound_of_continuousOn
    intro y hy
    exact (((FVA2.Poesy.tourSmooth (S := M) univ k (centered a L) (p:ℝ)).continuousOn.continuousAt
      ((FVA2.Poesy.airT (Fin (1+m))).mem_nhds (he y hy))).comp origin_continuous.continuousAt).continuousWithinAt
  choose c hh using hb
  let C : ℝ := ∑ p ∈ Finset.range N,max 0 (c p)
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => le_max_left ..
  have hcap (p : ℕ) (hp : p ∈ Finset.range N) (y : ↥Z) : ‖F p y‖ ≤ C :=
    (hh p _ y.property).trans ((le_max_right 0 (c p)).trans (Finset.single_le_sum (fun _ _ => le_max_left ..) hp))
  refine ⟨A*C,mul_nonneg hA hC,j,fun s hs v y hy => ?_⟩
  have hm := hj (⟨y,hy⟩ : ↥Z) (v+s) C hC (fun p hp => hcap p hp ⟨y,hy⟩)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|v+s|) (running_log v s hs) j
  rw [←anchored,receding_moment M _ (he y hy) v s k,norm_mul,power,Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le,center_weight,Nat.cast_add]
  calc
    _ ≤ exp (-((a.size:ℝ)+weight L)*s) * (A*(1+|v+s|)^j*C) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ ≤ exp (-((a.size:ℝ)+weight L)*s) * (A*((1+|v|)*(1+s))^j*C) := by gcongr
    _ = _ := by ring

/-- The original real subtraction-log law yields a single complex polynomial
on the real line, in the same coefficients as the independent moment. -/
theorem complex_polynomial {F : ℝ → ℂ} (h : Ready F) :
    ∃ P : Polynomial ℂ,∀ v : ℝ,F v = P.eval (v : ℂ) := by
  obtain ⟨N,hN⟩ := h
  let P : Polynomial ℂ := ∑ p ∈ Finset.range N,(plate N p).map Complex.ofRealHom * Polynomial.C (F p)
  refine ⟨P,fun v => ?_⟩
  rw [interpret hN v]
  unfold evaluate P
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Polynomial.eval_mul,Polynomial.eval_C,Complex.real_smul]
  exact congrArg (fun a : ℂ => a * F p) (Polynomial.eval_map_apply (p := plate N p) (f := Complex.ofRealHom) v).symm

/-- Exact named coefficient at the actual running log μ−s, multiplied by its
input/output engineering factor. -/
theorem weighted_scalar {F : ℝ → ℂ} (h : Ready F) (μ w : ℝ) :
    (fun s => power w s * F (μ-s)) ∈ RG11.Grove.season w := by
  obtain ⟨P,hP⟩ := complex_polynomial h
  apply RG11.Grove.season_of.mpr
  refine ⟨P.comp (Polynomial.C (μ : ℂ)-Polynomial.X),fun s => ?_⟩
  rw [hP,Polynomial.eval_comp,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_X,Complex.ofReal_sub]
  rfl

theorem weighted_point {F : ℝ → I → ℂ} (h : Ready F) (μ w : ℝ) (i : I) :
    (fun s => power w s * F (μ-s) i) ∈ RG11.Grove.season w :=
  weighted_scalar (h.linear (LinearMap.proj i)) μ w

/-- Integrating the exact named coefficient preserves its full log law. Only
continuity at the fixed integer subtraction nodes on the test support is used. -/
theorem test_ready (f : Test n) (F : ℝ → Points n → ℂ)
    (h : Ready (fun v (x : ↥(tsupport f)) => F v x.val))
    (hc : ∀ p : ℕ,∀ x ∈ tsupport f,ContinuousAt (F p) x) :
    Ready (fun v => f.applyTo (F v)) := by
  obtain ⟨N,hN⟩ := h
  convert eval_ready N (fun v => f.applyTo (F v)) using 1
  funext v
  let c (p : ℕ) : ℂ := ((plate N p).eval v : ℝ)
  have he (x : Points n) (hx : x ∈ tsupport f) : F v x = ∑ p ∈ Finset.range N,c p * F p x := by
    simpa only [evaluate,Finset.sum_apply,Pi.smul_apply,c,Complex.real_smul] using
      congrFun (interpret hN v) (⟨x,hx⟩ : ↥(tsupport f))
  calc
    f.applyTo (F v) = f.applyTo (fun x => ∑ p ∈ Finset.range N,c p * F p x) := OPETreeTests.on_support f he
    _ = ∑ p ∈ Finset.range N,f.applyTo (fun x => c p * F p x) :=
      OPETreeTests.sum f (Finset.range N) (fun p x => c p * F p x) (fun p _ x hx => continuousAt_const.mul (hc p x hx))
    _ = _ := by
      unfold evaluate
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [OPETreeTests.scalar,Complex.real_smul]

theorem weighted_test (f : Test n) (F : ℝ → Points n → ℂ)
    (h : Ready (fun v (x : ↥(tsupport f)) => F v x.val))
    (hc : ∀ p : ℕ,∀ x ∈ tsupport f,ContinuousAt (F p) x) (μ w : ℝ) :
    (fun s => power w s * f.applyTo (F (μ-s))) ∈ RG11.Grove.season w :=
  weighted_scalar (test_ready f F h hc) μ w

/-- The literal compact profile rate from the genuine distributed integral is
exactly the individual power/log budget used in the original `Snug` rows. -/
theorem individual_of_bound (w : ℝ) (k : ℕ) (F : ℝ → ℂ) {K : ℝ} (hK : 0≤K)
    (h : ∀ᶠ s : ℝ in atTop, ‖F s‖ ≤ K*(exp (w*s)*(1+|s|)^k)) : F ∈ RG11.Grove.individual w :=
  RG11.Grove.personally.mpr ⟨K,k,hK,h⟩

/-- A continuous native field table at subtraction scale zero provides the
running profile continuity on the actual physical configuration space. -/
theorem continuous_table (R : Fin n → Label B) (A : (Fin n → QP) → Glyph B H → ℕ → ℂ)
    {a : Glyph B H} {j : ℕ} (h : ContinuousOn (fun x => A x a j) {x | Injective x}) (v : ℝ) :
    ContinuousOn (fun z : Points n => normalized R A (MSExteriorCompactTests.positions z) a j v) (conf n) := by
  apply continuousOn_const.mul
  exact h.comp ((continuous_stretch v).comp MSExteriorCompactTests.continuous_positions).continuousOn
    (fun _ hz => separated_stretch v (Theater.out.injective.comp hz))

theorem log_envelope (v s : ℝ) (hs : 0 ≤ s) (l j : ℕ) :
    (1+|v|)^l * (1+s)^j ≤ ((1+|v|)*(1+s))^(l+j) := by
  rw [mul_pow]
  apply mul_le_mul (pow_le_pow_right₀ (show (1:ℝ)≤1+|v| from le_add_of_nonneg_right (abs_nonneg v)) (by omega))
    (pow_le_pow_right₀ (show (1:ℝ)≤1+s by linarith) (by omega)) (by positivity) (by positivity)

/-- The fixed-scale spatial input now controls the original measured profile
at every center, with the independently integrated full finite output table.
Only the common compact population of the relative exterior shapes occurs. -/
theorem measured_reference (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)
    (A : (Fin n → QP) → Glyph B H → ℕ → ℂ) (k : ℕ)
    (hc : ∀ a j,j ≤ k → Ready (fun v (x : Separated n) => normalized R A x.val a j v))
    (hA : ∀ a j,j ≤ k → ContinuousOn (fun x => A x a j) {x | Injective x})
    (hzero : ReferenceBound M R L A k ((H:ℝ)+1+weight L)) (f : Test n)
    (Y : Set (RG11.Neighborhood.Tail m)) (hy : IsCompact (MSExteriorOrigins.relative '' Y)) (μ : ℝ) :
    ∃ K : ℝ,0≤K ∧ ∃ J : ℕ,∀ᶠ s : ℝ in atTop, ∀ y ∈ Y,
      ‖MSExteriorTestProjection.difference M R L f (fun x => normalized R A (MSExteriorCompactTests.positions x)) μ s
        (fun x => MSExteriorCompactTests.positions (RG11.Neighborhood.driven (exp (-s)) x y))
        (MSExteriorCompactTests.positions (RG11.Neighborhood.close y)) k‖ ≤
        (∫ x,‖f x‖) * ((K*(1+|μ|)^J)*(exp (((weight R:ℝ)-H-1)*s)*(1+|s|)^(2*J))) := by
  let X := MSExteriorCompactTests.positions '' tsupport f
  have hX : IsCompact X := f.hasCompactSupport.image MSExteriorCompactTests.continuous_positions
  have hi : ∀ z ∈ X,Injective z := fun _ ⟨x,hx,e⟩ => e ▸ Theater.out.injective.comp (f.tsupport_subset hx)
  have he : ∀ z ∈ MSExteriorOrigins.relative '' Y,Injective (origin z) :=
    fun _ ⟨y,_,e⟩ => e ▸ MSExteriorOrigins.remote y
  obtain ⟨K,hK,l,j,hfar⟩ := fixed_reference M R L A k _ hc hzero X (MSExteriorOrigins.relative '' Y) hX hy hi he
  refine ⟨K,hK,l+j,MSExteriorOrigins.tested_original M R L f _ Y hy μ k
    (fun a p hp v => continuous_table R A (hA a p hp) v) hK (l+j) ?_⟩
  filter_upwards [hfar,eventually_ge_atTop (0:ℝ)] with s hs hp x hx y hy v
  exact (hs _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (log_envelope v s hp l j) (Real.exp_pos _).le) hK)

/-- Independent exterior smearing of a genuine compact family costs precisely
the L¹ norm of the second native complex test. The parameterization may vary
the center as well as the separated exterior marks. -/
theorem second_test {r : ℕ} (g : Test r) (Y : Set (RG11.Neighborhood.Tail m))
    (t : Points r → RG11.Neighborhood.Tail m) (ht : ∀ z ∈ tsupport g,t z ∈ Y)
    (F : ℝ → RG11.Neighborhood.Tail m → ℂ) (B : ℝ → ℝ)
    (h : ∀ᶠ s : ℝ in atTop,∀ y ∈ Y,‖F s y‖ ≤ B s) :
    ∀ᶠ s : ℝ in atTop,‖g.applyTo (fun z => F s (t z))‖ ≤ (∫ z,‖g z‖)*B s :=
  h.mono fun _ hs => OPETreeTests.bound g _ _ (fun z hz => hs _ (ht z hz))

end YM.Integration.MSExteriorFiniteScales
