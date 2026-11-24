import YM.RG12.Frames.Payment

/-!
# Compress pricing to the graded physical fibers

Subadditive test costs on all fields induce costs on a grade by using all its realizations
in the grade filtration. Thus no projection (free or interacting) needs to be an isometry.
This uses NO assumption of homogeneity of the (graded) two-point function. In the reflection
application this is a Schur-complement style measurement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Frames
open Function Finset Filter
open scoped Topology BigOperators
variable {d : ℕ} {V : Grade d → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]

structure Tests (g : Col V → ℝ) (K : ℝ) : Prop where
  legal : 1 ≤ K
  upper x : g x ≤ K * ‖x‖
  lower x : ‖x‖ ≤ K * g x
  combine x y : g (x+y) ≤ g x + g y
  scalar (c : ℝ) x (hc : 0 ≤ c) : g ((c:ℂ) • x) = c * g x

variable {g : Col V → ℝ} {K : ℝ}
lemma Tests.nonneg (h : Tests g K) (x : Col V) : 0 ≤ g x := nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (h.lower x)) (zero_lt_one.trans_le h.legal)
lemma Tests.zero (h : Tests g K) : g 0 = 0 := ((h.upper _).trans (by simp)).antisymm (h.nonneg ..)

structure Lives (i : Grade d) (x : V i) (v : Col V) : Prop where
  fitting : v ∈ flag V i
  there : v i = x

abbrev Fiber (i : Grade d) (x : V i) := {v : Col V // Lives i x v}

lemma Lives.here (i : Grade d) (x : V i) : Lives i x (put V i x) :=
  ⟨put_flag _ _ _ le_rfl,Pi.single_eq_same i x⟩

instance (i : Grade d) (x : V i) : Nonempty (Fiber i x) := ⟨put V i x,Lives.here i x⟩

def compress (g : Col V → ℝ) : Currency V := fun i x => ⨅ v : Fiber i x, g v.val

include V
lemma compressed (h : Tests g K) {i : Grade d} (x : V i) (v : Col V) (he : Lives i x v) :
    compress g i x ≤ g v := by
  unfold compress
  exact ciInf_le (f:=fun v:Fiber i x=>g v.val) ⟨0,Set.forall_mem_range.mpr (fun v=> h.nonneg v.val)⟩ (⟨v,he⟩:Fiber i x)

theorem fits_compress (h : Tests g K) : Fits (compress g) K := by
  have ht := zero_lt_one.trans_le h.legal
  refine ⟨h.legal,fun i x=> ?_, fun i x=>?_, fun i x y=> ?_, fun i c hc x=> ?_⟩
  · exact (compressed h x _ (Lives.here i x)).trans ((h.upper _).trans (mul_le_mul_of_nonneg_left (put_norm_le ..) ht.le))
  · rw [mul_comm, ← div_le_iff₀ ht]
    refine le_ciInf fun v => ?_
    have hx : ‖x‖ ≤ ‖v.val‖:= (congr_arg norm v.property.there.symm).trans_le (norm_le_pi_norm v.val i)
    exact (hx.trans (h.lower v.val) |>.trans_eq (mul_comm ..)) |> (div_le_iff₀ ht).mpr
  · have he (v:Fiber i x) (w:Fiber i y): compress g i (x+y) ≤ g v.val + g w.val:=by
      apply le_trans _ (h.combine v.val w.val); exact compressed h (x+y) _ ⟨add_mem v.property.fitting w.property.fitting,
        show v.val i+w.val i=x+y by rw [v.property.there,w.property.there]⟩
    apply sub_le_iff_le_add.mp; apply le_ciInf; intro v
    -- v is which variable?
    rw [sub_le_iff_le_add,add_comm (g v.val)]; apply sub_le_iff_le_add.mp; apply le_ciInf; intro w
    rw [sub_le_iff_le_add]; rw [add_comm _ (g v.val)]; exact he _ _
  rcases hc.eq_or_lt with rfl|hc
  · rw [zero_mul,Complex.ofReal_zero,zero_smul]
    exact ((compressed h _ _ (Lives.here i 0)).trans (by simp [put,h.zero])).antisymm (le_ciInf fun v=> h.nonneg v.val)
  refine le_antisymm ?_ ?_
  · rw [mul_comm, ← div_le_iff₀ hc]
    apply le_ciInf; intro v; rw [div_le_iff₀ hc,mul_comm (g v.val),← h.scalar ..]
    · exact compressed h _ _ ⟨(flag V i).smul_mem (c:ℂ) v.property.fitting,
        congr_arg (fun x:V i=> (c:ℂ) • x) v.property.there⟩
    exact hc.le
  apply le_ciInf; intro v
  have hx := compressed h x ((↑(c⁻¹:ℝ):ℂ) • v.val) (show Lives i x _ from ⟨(flag V i).smul_mem _ v.property.fitting,?_⟩)
  · refine (mul_le_mul_of_nonneg_left hx hc.le).trans_eq ?_; rw [h.scalar _ _ (inv_pos.mpr hc).le, ← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  change (↑(c⁻¹:ℝ):ℂ) • v.val i = _
  rw [v.property.there, smul_smul, ← Complex.ofReal_mul,inv_mul_cancel₀ hc.ne',Complex.ofReal_one,one_smul]

/-- Use a map on the grade from a comparison on full measurements; the image on this
fiber is what matters. -/
lemma compare_fiber {X : BlockMatrix V} (ht : triangular V X) {f : Col V → ℝ} (hf : Tests f K) {r : ℝ} (hr : 0 < r)
    (h : ∀ x, f (X x) ≤ r * g x) (i : Grade d) (x : V i) :
    compress f i (block V X i i x) ≤ r * compress g i x := by
  rw [mul_comm, ← div_le_iff₀ hr]; apply le_ciInf
  intro v; rw [div_le_iff₀ hr,mul_comm (g v.val)]
  apply le_trans _ (h v.val)
  exact compressed hf _ _ ⟨(triangular_iff_stays _ _).mp ht i _ v.property.fitting,
    (same_diag ht v.property.fitting).trans (congr_arg _ v.property.there)⟩
end YM.RG12.Frames
