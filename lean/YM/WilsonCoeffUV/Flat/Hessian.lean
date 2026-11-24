import YM.WilsonCoeffUV.Flat.PoleRate
/-!
# True strip-width (not just periodized) Cauchy rate for the Hessian lift
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Filter Function Lattice RG Laurent Exterior Bloch Metric Matrix Work.F08 Next.Free Extension.UV.Linear
open scoped Topology BigOperators ComplexConjugate

variable {α β : Type*} [Fintype α] [Fintype β] {A η : ℝ}

/-- Real-cube estimate suffices to get a small coefficient, equally at
all displacements. -/
lemma take_one (R : Row α β) (h : R.safe) (hr : ∀ a b p, p ∈ baseCube → ‖R.read p a b‖ ≤ A)
    (a : α) (b : β) (x : Cover) : ‖R a b x‖ ≤ A := by
  let n (i : ℕ) : Side := ⟨i+1, Nat.zero_lt_succ _⟩
  have hn : Tendsto (fun i => (n i).val) atTop atTop := tendsto_atTop_mono (fun i => show i ≤ i+1 by omega) tendsto_id
  apply le_of_tendsto' (entry_limit n hn R h a b x).norm
  intro i
  classical
  let L := n i
  let M := rotations L β
  let Q := wrap L x
  let D := approached (R.acts L)
  let H := R.acts L (0,a) (Q,b)
  let Y := fun p : Site L=> R.read (mon p)
  let V : ℂ := L.val
  have hg : (V^4 • D) (0,a) (Q,b) = ((rotations L α*fiber Y)*star M) (0,a) (Q,b) := by
    have he := congr_arg (· * star M) (circulant L R h)
    rw [Matrix.mul_assoc,rotations_gram,Matrix.mul_smul,Matrix.mul_one] at he
    rw [show V^4 • D = _ from he]
  have hy : (V^4 • D) (0,a) (Q,b)= V^4*(H:ℂ) := rfl
  have he : V^4*(H:ℂ)=∑ j:Site L,Y j a b*star (cell j Q) := by
    rw [← hy,hg, Matrix.mul_apply,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro p _; simp_rw [rot_fiber,Matrix.star_eq_conjTranspose,conjTranspose_apply,M,rotations,Matrix.of_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro k _ hx; simp [Ne.symm hx]
    simp
  have ht := congr_arg norm he
  rw [norm_mul,norm_pow,Complex.norm_real] at ht
  change ‖H‖ ≤ _
  apply le_of_mul_le_mul_left _ (show 0<‖V‖^4 from pow_pos (norm_pos_iff.mpr (side_ne L)) _)
  rw [ht]; apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _j:Site L,A := Finset.sum_le_sum fun j _ => by
      rw [norm_mul,norm_star,show ‖cell j Q‖=1 by change ‖cell j (wrap L x)‖=1; rw [cell_wrap]; exact mode_real _ _ (real_frequency _),mul_one]; exact hr a b (mon j) (mon_mem L j)
    _ = _ := by simp [V,Lattice.Site,Axis]

lemma mix_width {T : Type*} [NormedAddCommGroup T] (U : Cover → T) {η A B:ℝ} (hη : 0<η)
    (hb : 0≤B) (ha : 0≤A) (hv : Width η A U) (hs : ∀ i, 0≤ ‖U i‖ ∧ ‖U i‖ ≤ B) :
    Width (η/4) (Real.sqrt B*Real.sqrt A * ((2*((1+η/4)/(η/4)))^(Fintype.card Axis))) U := by
  set ρ := η/4; have hr : 0<ρ := by unfold ρ; positivity
  let g := fun i : Cover => Real.exp (-ρ*size i)
  have hh (i : Cover) : Real.exp (ρ*size i)*‖U i‖ ≤ Real.sqrt B*Real.sqrt A * g i := by
    let E := Real.exp (ρ*size i); have hp : 0<E := Real.exp_pos _
    have he : E^4 = Real.exp (η*size i) := by unfold E; rw [← Real.exp_nat_mul]; unfold ρ; congr 1; ring
    have hx : g i = E⁻¹ := by unfold g E; rw [neg_mul,Real.exp_neg]
    have ht : E^4*‖U i‖ ≤ A := by rw [he]; exact (hv.2.1.le_tsum i (fun j _ => hv.1 j)).trans hv.2.2
    rw [hx, ← div_eq_mul_inv]
    apply (le_div_iff₀ hp).mpr
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow (Real.sqrt B),Real.sq_sqrt hb,Real.sq_sqrt ha]
    change (E*‖U i‖*E)^2 ≤ _; rw [show (E*‖U i‖*E)^2= ‖U i‖*(E^4*‖U i‖) by ring]
    exact mul_le_mul (hs i).2 ht (mul_nonneg (pow_nonneg hp.le _) (hs i).1) hb
  have hg := Width.compactPay (α:=Axis) ρ hr
  have h (i : Cover) : 0 ≤ Real.exp (ρ*size i)*‖U i‖ := mul_nonneg (Real.exp_pos _).le (hs i).1
  have hm := hg.2.1.mul_left (Real.sqrt B*Real.sqrt A)
  have he := Summable.of_nonneg_of_le h hh hm
  exact ⟨h,he,(he.tsum_le_tsum hh hm).trans (by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hg.2.2 (by positivity))⟩

lemma mass_separation {G:Gauge} (A:Levels G) (m i : ℕ) (h : m ≤ i) :
    A.S.a i * (location A i m).mass.val = A.S.a m := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le h
  induction i generalizing m with
  | zero => simp only [Nat.add_zero,loc_top,Train.mass]; simp
  | succ d ih =>
    rw [loc_land A _ _ (by omega), show (destination A (m+(d+1)) m).land.mass=(A.S.block m)*(location A (m+(d+1)) (m+1)).mass from rfl,
        mul_side_real, mul_comm ((A.S.block m).val:ℝ), ← mul_assoc, show m+(d+1)=m+1+d by omega]
    rw [ih _ (by omega), Schedule.a_step, div_mul_cancel₀ _ (side_pos _).ne']

def freeForms {G : Gauge} (A : Levels G) (n m : ℕ) := record (pulse A.clock.kernel.penalty (location A n m))

/-- One common width before any block lengths, for the J stage. The
metric left *unmodified* at each mesh. No strip statement here on individual
full massless terms without the pole removed. -/
theorem forms_tail (k : ℝ) (hk : 0 < k) (j : ℕ) (hj : 4 ≤ j) : ∃ η C : ℝ, 0<η ∧ 0<C ∧
    ∀ {G:Gauge} (A:Levels G) (m : ℕ), A.clock.J m = j → A.clock.kernel.penalty = k →
    (∀ n, (freeForms A n m).strip η C) ∧
    ∀ i, m ≤ i → ∀ n n', i ≤ n → i ≤ n' → ((freeForms A n m) - freeForms A n' m).strip η
      (C * Real.sqrt (Dcost k (A.clock.J i)*(A.S.a i/A.S.a m))) := by
  obtain ⟨σ,C,hs,hC,H⟩ := heart_banked k hk hj (id : Train j → Train j)
  obtain ⟨D,hD,h⟩ := pulse_tail k hk j hj
  set ρ := σ/4; have hρ : 0<ρ := by unfold ρ; positivity
  let T := Real.sqrt D * Real.sqrt (C+C) * (2*((1+ρ)/ρ))^(Fintype.card Axis)
  set Z := max C T; have hZ := le_max_left C T
  refine ⟨ρ,Z,hρ,hC.trans_le hZ,?_⟩
  intro G A m hJ hK
  subst k
  subst j
  have hg (n : ℕ) : (freeForms A n m).strip σ C := (H _).1
  have hR : ρ ≤ σ := by unfold ρ; linarith
  refine ⟨fun n a b => (hg n a b).mono hR hZ,?_⟩
  intro i hi n n' hn hn'
  let W := minusRows (freeForms A n m) (freeForms A n' m)
  have ht : W.strip σ (C+C) := strip_minus (hg n) (hg n')
  set x := Dcost A.clock.kernel.penalty (A.clock.J i) / (location A i m).mass.val
  have hx : 0<x := div_pos (Dcost_pos ..) (side_pos _)
  have hb a b p (hp : p∈baseCube) : ‖W.read p a b‖ ≤ D*x := by
    have hh n : (freeForms A n m).read p = _ := (heart_true A.clock.kernel.penalty hk hj (location A n m)).1.echo _ hp
    rw [show W.read p=_ from read_less (Row.rights _ _ (hg n) hs.le) (Row.rights _ _ (hg n') hs.le) hp.1, hh n, hh n']; exact h A m i n n' rfl hi hn hn' a b p hp
  intro a b
  rw [← show x = Dcost _ (A.clock.J i)*(A.S.a i/A.S.a m) from ?_]
  · change Width _ _ (W a b)
    refine (mix_width (W a b) hs (mul_nonneg hD.le hx.le) (by positivity) (ht a b) (fun i => ⟨norm_nonneg _, take_one W (Row.rights _ _ ht hs.le) hb _ _ _⟩)).mono le_rfl ?_
    rw [Real.sqrt_mul hD.le]
    apply le_trans (b:=T*Real.sqrt x) (le_of_eq ?_) (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)); unfold T; ring
  unfold x
  rw [← mass_separation A m i hi]; field_simp [(A.S.a_pos i).ne']

end YM.WilsonCoeffUV
