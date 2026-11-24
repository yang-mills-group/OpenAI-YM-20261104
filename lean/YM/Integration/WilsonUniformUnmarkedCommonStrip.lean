import YM.Integration.WilsonUniformUnmarkedTensorRows

/-! The finite action's anchored complete tensor rows in the very same
`Bail` norm used by the infinite-cover comparison. The factor four is
the conversion of the finite maximum metric to the cover's sum metric. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedCommonStrip
open Filter Function Finset PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series Gorge
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery
open RG16 RG16.Literal Pert.Asymptotics WilsonConditionalTaylorCourseAttachment WilsonConditionalTaylorBulkHistory
open WilsonUniformUnmarkedTensorRows
open scoped Classical Topology BigOperators ENNReal
variable {G : Gauge} {n : Side} {r : ℕ}

theorem metric (x y : Site n) : Laurent.size (lift (x-y)) ≤ 4*separation x y := by
  unfold Laurent.size
  calc
    _ ≤ ∑ _z : Axis,pdist (x-y) := Finset.sum_le_sum (fun z _=>component_le (x-y) z)
    _ = _ :=by simp [separation]

theorem diameter (i : wire G n) (t : Fin r→wire G n) :
    wide (lake n _) (Fin.cons i t) ≤ 4*Whisk.extent
      (Whisk.zone (Measuring.chart n G) {Measuring.chart n G ((WilsonMovingGaussianCoordinates.link G n).symm i)}
        (List.ofFn ((WilsonMovingGaussianCoordinates.link G n).symm ∘ t))) := by
  let E:=(WilsonMovingGaussianCoordinates.link G n).symm
  let l:=Measuring.chart n G
  let s:=Whisk.zone l {l (E i)} (List.ofFn (E ∘ t))
  have every (a : Fin (r+1)) : ((Fin.cons i t : Fin (r+1)→wire G n) a).1 ∈ s := by
    refine Fin.cases ?_ (fun z=>?_) a
    · apply Finset.mem_union_left
      exact Finset.mem_singleton_self _
    · apply Finset.mem_union_right
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      exact ⟨E (t z),List.mem_ofFn.mpr ⟨z,rfl⟩,rfl⟩
  apply known_wide
  intro a b
  exact (metric _ _).trans (Nat.mul_le_mul_left 4 (Whisk.curve (every a) (every b)))

theorem exponential (i : wire G n) (t : Fin r→wire G n) {σ : ℝ} (width : 0≤σ) (s : ℕ) :
    Real.exp ((σ/4)*(wide (lake n _) (Fin.cons i t):ℝ)) ≤ weight n G i t σ s := by
  let d:ℕ:=Whisk.extent (Whisk.zone (Measuring.chart n G)
    {Measuring.chart n G ((WilsonMovingGaussianCoordinates.link G n).symm i)}
    (List.ofFn ((WilsonMovingGaussianCoordinates.link G n).symm ∘ t)))
  have room : (wide (lake n _) (Fin.cons i t):ℝ) ≤ 4*(d:ℝ) :=by exact_mod_cast diameter i t
  have expo : Real.exp ((σ/4)*(wide (lake n _) (Fin.cons i t):ℝ)) ≤ Real.exp (σ*(d:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg width (sub_nonneg.mpr room)]
  have extra : 1 ≤ (1+(d:ℝ))^s :=one_le_pow₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) d])
  exact expo.trans (le_mul_of_one_le_left (Real.exp_pos _).le extra)

private theorem wide_perm {V : Type} (D : Reach V) (q : Fin r→V) (π : Equiv.Perm (Fin r)) :
    wide D (q ∘ π)=wide D q :=by
  apply le_antisymm
  · exact known_wide D _ _ (fun a b=>reached D q (π a) (π b))
  · apply known_wide
    intro a b
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using reached D (q ∘ π) (π.symm a) (π.symm b)

theorem render {T : Tile (wire G n) (r+1)} (sym : Agate T) {σ B : ℝ} (width : 0≤σ) (B0 : 0≤B)
    (s : ℕ) (held : ∀ i : wire G n, (∑ t : Fin r→wire G n,
      weight n G i t σ s * |((r+1).factorial:ℝ)*T (Fin.cons i t)|) ≤ B) :
    Bail (lake n _) (σ/4) T B := by
  refine ⟨B0,?_⟩
  intro atSlot i
  let π:=Equiv.swap (0:Fin (r+1)) atSlot
  let f (v : pack atSlot i) := Fin.tail (v.val ∘ π)
  let front (v : pack atSlot i) : Fin (r+1)→wire G n :=Fin.cons i (f v)
  have eq (v : pack atSlot i) : front v=v.val ∘ π :=by
    funext z;refine Fin.cases ?_ (fun j=>?_) z
    · change i=v.val (Equiv.swap 0 atSlot 0)
      rw [Equiv.swap_apply_left,v.property]
    · rfl
  have inject : Injective f :=by
    intro v w e
    have h : front v=front w :=congrArg (fun t : Fin r→wire G n =>(Fin.cons i t : Fin (r+1)→wire G n)) e
    rw [eq,eq] at h
    apply Subtype.ext
    funext z
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using congrFun h (π.symm z)
  let cost (t : Fin r→wire G n):=weight n G i t σ s*|((r+1).factorial:ℝ)*T (Fin.cons i t)|
  have cost0 (t) : 0≤cost t :=mul_nonneg (Whisk.effect ..).le (abs_nonneg _)
  have each (v : pack atSlot i) :
      Real.exp ((σ/4)*(wide (lake n _) v.val:ℝ))*|T v.val| ≤ cost (f v) := by
    have wd : wide (lake n _) (front v)=wide (lake n _) v.val := by rw [eq,wide_perm]
    have same : T (front v)=T v.val :=by rw [eq,sym]
    have val : |T v.val| ≤ |((r+1).factorial:ℝ)*T (front v)| :=by
      rw [same,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ((r+1).factorial:ℝ))]
      exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast Nat.factorial_pos (r+1))
    rw [←wd]
    exact mul_le_mul (exponential i (f v) width s) val (abs_nonneg _) (Whisk.effect ..).le
  have fare : (∑ v : pack atSlot i,Real.exp ((σ/4)*(wide (lake n _) v.val:ℝ))*|T v.val|) ≤ B := by
    calc
      _ ≤ ∑ v : pack atSlot i,cost (f v) :=Finset.sum_le_sum (fun v _=>each v)
      _ = ∑ t ∈ Finset.univ.image f,cost t := (Finset.sum_image (fun a _ b _ e=>inject e)).symm
      _ ≤ ∑ t : Fin r→wire G n,cost t := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun t _ _=>cost0 t)
      _ ≤ B :=held i
  rw [tsum_fintype]
  apply le_trans _ (ENNReal.ofReal_le_ofReal fare)
  rw [ENNReal.ofReal_sum_of_nonneg (fun v _=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
  apply Finset.sum_le_sum;intro v _
  rw [glitter,Gorge.shine,Real.enorm_eq_ofReal_abs,ENNReal.ofReal_mul (Real.exp_pos _).le]

variable (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include simple bought in
theorem purchased (p : ℕ) {η : ℝ} (loss : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ j, k ≤ j → j ≤ N → ∀ e, 0<e → e ≤ p →
      ∀ r, r ≤ e+1 → let n:=R.family.side j per
      let A:=course R u wood tags N j n
      Bail (lake n _) (Alto.candles R.family.path.levels j/4) (rancho A e (r+1))
        ((regulatorRun R.family N per j)^(-η)) := by
  filter_upwards [WilsonUniformUnmarkedTensorRows.bounded R simple u V bought wood tags 6 p le_rfl loss]
    with k cash N per kN j lo hi e pos he r cap n A
  have width : 0≤Alto.candles R.family.path.levels j :=by unfold Alto.candles Alto.cWidth;positivity
  exact render (marble_agate _ _) width (Real.rpow_nonneg (RG16.Literal.g_pos R.makes hi).le _) 6
    (cash N per kN j lo hi e pos he r cap)

end YM.Integration.WilsonUniformUnmarkedCommonStrip
