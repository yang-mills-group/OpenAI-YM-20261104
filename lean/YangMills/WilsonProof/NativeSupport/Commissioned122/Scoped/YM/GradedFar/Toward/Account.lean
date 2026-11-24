import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Toward.FieldChanges
/-!
# Actual price of applying a finite-horizon detector
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Filter Function Set Scale O.Score O.Enh O.Canon PowerSeries XSpace XSpace.Normalize Dframe
open scoped Topology Classical BigOperators

variable {G : Gauge} {V : Arenas G} {ψ : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    (phys : Physical V ψ B)
    {n m h k p q H : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    {K : Set (Points n)} (kc : IsCompact K) (hk : K ⊆ conf n)
    (u : Appointed122Fields G d)
section
-- Represent actual linear functionals on the horizon h, with norms usable by the physical data.
local notation "L" => Sec G h →ₗ[ℂ] ℂ

def localOp (v : Sec G h →ₗ[ℂ] ℂ) := LinearMap.toContinuousLinearMap (v ∘ₗ (account G h).symm.toLinearMap)
def opCost (v : L) := ‖localOp v‖
lemma local_apply (v : L) (u : Account G h) : localOp v u = v ((account G h).symm u) := rfl
lemma cost_output (v : L) (u : Sec G h) : ‖v u‖ ≤ opCost v * slotNorm u := by
  have H := (localOp v).le_opNorm (account G h u); rw [local_apply,LinearEquiv.symm_apply_apply] at H; exact H
lemma local_of_cost (v : L) {A : ℝ} (hc : 0 ≤ A)
    (h : ∀ x, slotNorm x ≤ 1 → ‖v x‖ ≤ A) : opCost v ≤ A := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc; intro u
  by_cases hu : u=0; · rw [hu,map_zero,norm_zero,norm_zero,mul_zero]
  let y := (account G _).symm u
  let b : ℂ := ‖u‖
  have hx : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have H : ‖b‖= ‖u‖ := by simp [b]
  have hy : slotNorm y= ‖u‖ := by simp [slotNorm,y]
  have hp := h (b⁻¹ • y) (by rw [slotNorm,map_smul,norm_smul,norm_inv,H];
                              change _*slotNorm y ≤ 1; rw [hy, inv_mul_cancel₀ hx.ne'])
  rw [map_smul,norm_smul,norm_inv,H,mul_comm, ← div_eq_mul_inv, div_le_iff₀ hx] at hp
  exact hp

/-- Center operator version of the formal D^X. -/
def filedCenter122 (V : Arenas G) (B : ℝ → Frames G) (η : ℝ) (z : Points (1+m)) (lh : h ≤ H)
    (he : Covered e H) (v : Appointed122Fields G e) (p : ℕ) (t : ℂ) : Sec G h →ₗ[ℂ] ℂ :=
  let f : Sec G h →ₗ[ℂ] Form G e ℂ := (MultilinearMap.ofSubsingleton ℂ _ _ (0 : Fin 1)).symm
    (fittedModel (d := fun _ : Fin 1 => h) (fun _ => lh) he p z t V B η)
  { toFun x := f x v
    map_add' x y := by rw [map_add]; rfl
    map_smul' t x := by rw [map_smul]; rfl }
lemma center_apply (V : Arenas G) (B : ℝ → Frames G) (η : ℝ) (z : Points (1+m)) (lh : h ≤ H)
    (he : Covered e H) (v : Appointed122Fields G e) (p : ℕ) (t : ℂ) (x : Sec G h) :
    filedCenter122 V B η z lh he v p t x = filedCrop122 p t (rowsResponse122 V B η z h lh he v x) := by
  unfold rowsResponse122; rw [← fitted_apply]; rfl
end

include kc hk phys in
theorem vector_bounded (h p : ℕ) (R : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ x ∈ K, ∀ u : Appointed122Fields G d, FieldBudget u R → ∀ z : ℂ, ‖z‖ ≤ 1 → slotNorm (filedVector122 V x h p z u) ≤ C := by
  -- same tariffs; use t-independent bound, and Hausdorff common across detector rows.
  let I := ↥K × {u : Appointed122Fields G d // FieldBudget u R} × UnitDisk
  let a (b : Toon G h) := fun i : I => tariff V i.1.val i.2.1.val (flash b)
  let F (b : Toon G h) i := filedCrop122 p i.2.2.val (a b i)
  have pay (b : Toon G h) := fare_charge phys kc hk (I:=I) (fun i=>i.1.val) (fun i=>i.1.property) (fun i=>i.2.1.val) (fun i=>i.2.1.property) p (flash b)
  have earn (b : Toon G h) : ∃ r : ℝ, 0 < r ∧ ∀ i, ‖F b i‖ ≤ r := by
    obtain ⟨r,hr,k,j⟩ := price_crop (pay b) (fun i => i.2.2.val) (fun i=> i.2.2.property)
    obtain ⟨t, ht, hp⟩ := (j.and (eventually_ge_atTop (0:ℝ))).exists
    exact ⟨_, mul_pos hr (post_at hp), ht⟩
  choose C hC h using earn
  let D := ∑ b, C b
  have hd : 0 ≤ D := Finset.sum_nonneg (fun i _ => (hC i).le)
  refine ⟨D+1, by linarith, fun x hx v hv z hz => ?_⟩
  apply le_trans ?_ (le_add_of_nonneg_right zero_le_one)
  unfold slotNorm; rw [pi_norm_le_iff_of_nonneg hd]; intro i
  rw [account_entry,vector_entry]; exact (h i (⟨x,hx⟩,⟨v,hv⟩,⟨z,hz⟩)).trans
    (Finset.single_le_sum (fun i _=> (hC i).le) (Finset.mem_univ i))

/-- Numerical triangle step assembling (M.3). Call with the same Sec input conversion
on every operand. All the prices are *before* a physical matrix inverse. For precise use
see the MS physical application. -/
lemma earn_triangle (a f : ℂ) (D F : Sec G h→ₗ[ℂ]ℂ) {C X β : ℝ} (hc : 0 ≤ C) (hX : 0 ≤ X)
    (v vW : Sec G h) (hβ : slotNorm v ≤ β)
    (h₁ : ‖a-f‖ + opCost (D-F) ≤ C*X)
    (h₂ : ‖f-F v‖ ≤ C*X) (h₃ : ‖a-D vW‖ ≤ C*X) :
    ‖a-f‖ + opCost (D-F) + ‖a-f-(D-F) v‖ + ‖a-D vW‖ + ‖a-D v‖ ≤ (4+2*max 1 β)*C*X := by
  let b := max 1 β; have hb : 1 ≤ b := le_max_left ..; change _ ≤ (4+2*b)*C*X
  have H : ‖a-f-(D-F) v‖ ≤ b*(C*X) := by
    apply (norm_sub_le ..).trans; apply le_trans (add_le_add le_rfl (cost_output _ _))
    calc
      _ ≤ b*‖a-f‖+b*(opCost (D-F)) := by rw [mul_comm b (opCost _)];
                                             exact add_le_add (le_mul_of_one_le_left (norm_nonneg _) hb)
                                               (mul_le_mul_of_nonneg_left (hβ.trans (le_max_right ..)) (norm_nonneg _))
      _ ≤ _ := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left h₁ (zero_le_one.trans hb)
  have h4 : ‖a-D v‖ ≤ (b+1)*(C*X) := by
    rw [show a-D v= (a-f-(D-F) v) + (f-F v) by rw [LinearMap.sub_apply]; abel, add_mul, one_mul]
    exact (norm_add_le ..).trans (add_le_add H h₂)
  linarith only [h₁,H,h₂,h₃,h4, mul_nonneg hc hX]
end YM.FVA2.GradedFar
