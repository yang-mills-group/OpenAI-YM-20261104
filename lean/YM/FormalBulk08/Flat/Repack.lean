import YM.FormalBulk08.Flat.Doubler

/-!
Convert `slabW` symbol price for the gauge-completed quadratic form
(no depth and no background curvature needed) to a row on parity-free
cover Cells. Keep width BEFORE L, costs after.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08
open Stationary
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {η σ : ℝ}

lemma boundsTile (G : Gauge) (L : Side) (σ : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ x∈Laurent.strip σ, vflux ((slabW G L).tile x) ≤ C := by
  let B:=Real.exp (σ*4)*(Stationary.inch L)⁻¹*Real.exp (σ*4)
  refine ⟨max 1 B, lt_max_of_lt_left one_pos,fun p hp=>?_⟩
  let a:= Loc G 1; let T:=plankTile L a
  refine spade_flux (V:= (1:CompM (Loc G 0) (Loc G 0))) (U:= (altarTile L a).tile p) ?_ (flux_one.trans (le_max_left ..))
  have he : vflux (Matrix.diagonal (spice L a p))≤(Stationary.inch L)⁻¹ := by
    rw [flux_diagonal]; apply (pi_norm_le_iff_of_nonneg (inv_pos.mpr (Stationary.inch_pos _)).le).mpr
    intro i; simp only [spice,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hill_pos _ _)]
    exact inv_le_inv₀ (hill_pos ..) (Stationary.inch_pos ..)|>.2 (hill_inch ..)
  let hT := flux_power (T p) (Matrix.diagonal (spice L a p))
  have hv : vflux (T p*Matrix.diagonal (spice L a p))≤Real.exp (σ*4)*(Stationary.inch L)⁻¹ := hT.trans (mul_le_mul (plank_cap p hp) he (flux_nonneg _) (Real.exp_pos _).le)
  have hx : (0:Momentum) ∈ Laurent.strip σ := fun i=> by simpa using (show 0<σ from (abs_nonneg _).trans_lt (hp i))
  exact ((flux_power _ (T 0)⁻¹).trans (mul_le_mul hv (plank_back 0 hx) (flux_nonneg _) ((flux_nonneg _).trans hv))).trans (le_max_right ..)

lemma freezing (G : Gauge) (P : Patch) (η C : ℝ) (hC : 0≤C) :
    ∃ B : ℝ,0<B ∧ ∀ K : Momentum→CompM (ParcelG G P.L) _,
      Poster η K → Freezer (slabW G P.L|>.dual) (slabW G P.L) K η C →
        ∀ i j, SafeCube η B fun p=> (K p)⁻¹ i j := by
  obtain ⟨D,hD,h⟩:=boundsTile G P.L η
  refine ⟨D*C*D+1,by positivity,fun K hp hF i j=> ?_⟩
  have hx : Poster η (fun p=> (K p)⁻¹):= ⟨fun w=> BillD.take (hp.shape w) (hF.period _ w),fun he w=> congr_arg Inv.inv (hp.shifts he w)⟩
  let S:=slabW G P.L
  refine ⟨fun p w=> hx.shape w.1 _ _,fun p w=>?_⟩
  have ht : vflux ((S.dual.tile p)⁻¹)≤D:= by rw [Slab.inverse_dual,back_flux]; exact h _ (negResident w.1)
  let V:=carryM S S.dual p p (K p)⁻¹
  have hs : (K p)⁻¹ = S.tile p * V * (S.dual.tile p)⁻¹ := by unfold V carryM; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (S.tile _),Matrix.mul_nonsing_inv _ (S.whole _),Matrix.one_mul, Matrix.mul_nonsing_inv _ (S.dual.whole _),Matrix.mul_one]
  apply (flux_tilt _ i j).trans
  rw [hs]
  have hm := (flux_power (S.tile p) V).trans (mul_le_mul (h p w.1) (show vflux V≤_ from hF.price _ w.1) (flux_nonneg _) hD.le)
  exact (flux_power _ _).trans ((mul_le_mul hm ht (flux_nonneg _) ((flux_nonneg _).trans hm)).trans (by linarith))

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

omit [Fintype a] [DecidableEq a] in
lemma arcs_lock (q : Side) {U V : CircM q a b} {F H : Momentum→ CompM a b}
    (h : Jaunt U F 0) (hv : Jaunt V H 0) (hx : ∀ p : Site q, F (mon p)=H (mon p)) : U=V := by
  ext i j
  have hh : U i = V i := by
    apply ray_book
    intro p v
    have hm := congr_fun (h p (mon p) (rolls.refl _) v) i
    rw [hx p] at hm; rw [dotProduct_comm, dotProduct_comm _ (V i)]; exact hm.trans (congr_fun (hv p (mon p) (rolls.refl _) v) i).symm
  rw [hh]

lemma inverse_rows (q : Side) {R : Row a a} (C : Matrix (Co q a) (Co q a) ℝ) {F : Momentum → CompM a a}
    (hv : ∀ p : Site q, IsUnit (F (mon p)).det)
    (h : Jaunt (approached C) F 0) (hh : R.safe) (hp : ∀ p : Site q, R.read (mon p)=(F (mon p))⁻¹) :
    C*R.acts q=1 := by
  classical
  have hP := h.hoist (Jaunt.row R hh)
  apply prom_inj
  rw [prom_mul, show approached (1:Matrix (Co q a) (Co q a) ℝ)=1 from ?_]
  · exact arcs_lock q hP Jaunt.noop (fun p=> by rw [hp]; apply Matrix.mul_nonsing_inv _ (hv p))
  ext i j; by_cases hx : i=j <;> simp [approached,Matrix.one_apply,hx]

lemma delivers (B η : ℝ) (hη : 0<η) (F : Momentum→ CompM a a) (hp : Poster η F)
    (hs : ∀ p∈ Laurent.strip η,IsUnit (F p).det) (h : ∀ i j, SafeCube η B fun p=> (F p)⁻¹ i j)
    (he : ∀ p : Momentum, star p=p → (F (-p))ᵀ=(F p)ᴴ) :
    let s:=η/3
    let Y:=record fun p=> (F p)⁻¹
    Y.strip s (B*(2*((1+s)/s))^4) ∧ ∀ p∈ baseCube, Y.read p=(F p)⁻¹ := by
  let K (p : Momentum) := (F p)⁻¹
  have hk : Poster η K:= ⟨fun w=> BillD.take (hp.shape w) (hs _ w),fun he w=> congr_arg Inv.inv (hp.shifts he w)⟩
  have hr (a b) : Overlaps η fun i=> K i a b := fun p h x _=> congr_fun (congr_fun
    (hk.shifts (show rolls p (p+reciprocal x) from ⟨x,rfl⟩) ((mem_cube_real h hη).1 : p∈Laurent.strip η)).symm a) b
  intro s Y
  have hu : 0<s:= by unfold s; positivity
  constructor
  · intro i j; obtain ⟨hh,hv,_⟩:= hol_on_thickening hη (h i j) (hr _ _)
    exact Work.F07.widthRealPart (hh.issues hv s s hu.le hu (by unfold s; linarith))
  intro p w
  ext a b
  refine RRead_paints hη (h a b) (hr a b) (fun p hp=>?_) _ (base_subset_realCube hη w)
  have hh : (K (-p))ᵀ=(K p)ᴴ := by unfold K; rw [Matrix.transpose_nonsing_inv, he p hp.1, Matrix.conjTranspose_nonsing_inv]
  have hv := congr_fun (congr_fun hh b) a; rw [Matrix.transpose_apply,Matrix.conjTranspose_apply] at hv
  exact (congr_arg star hv).trans (star_star _)
end YM.FormalBulk08.Flat
