import YM.MS.TaylorLimit
import YM.Analysis.Homogeneous
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
/-!
# Homogeneous jet comparison on scaled momenta

Ray tests suffice (`Origin h` already exists). Obtain forms `Taylor` with E
finite dimensional charts later. These are real-smooth homogeneous symbols,
complex valued. No implicit Wick factors; there is a factorial from Taylor
coefficient (not from rank derivative positions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Filter Set Koszul MeasureTheory Wire Flux Real Tensor
open scoped Topology ContDiff
variable {ι A P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : Bool} {m : A→ℤ} {w : Wire A E P} {L : Clock ι → Row A P ℂ}
open Domain

@[simp] lemma ray_lift (w : Wire A E P) x : ray (sail w x)=lift w (ContinuousLinearMap.toSpanSingleton ℝ x) := by
   induction w with
   | nil=> rfl
   | cons a w IH=>
       simp only [sail_cons,ray] at *; rw [List.map_cons, IH]
       unfold lift; simp only [List.map_cons]; rw [show ContinuousLinearMap.toSpanSingleton ℝ (a.2 x) = a.2.comp (ContinuousLinearMap.toSpanSingleton ℝ x) by ext; simp]

lemma sail_course {w : Wire A E P} (x:E) (h : Course b w): Course b (sail w x):= fun z=> by rw [sail_net,h z]; rfl
lemma ray_course {w : Legs (Mode A P)} (h: Course b w) : Course b (ray w) := fun z=> by simp [h z]
@[simp] lemma sail_dim (w : Wire A E P) x : fieldDim m (sail w x)=fieldDim m w:= by simp only [fieldDim,← List.map_map,sail_base]
@[simp] lemma ray_len (w : Legs (Mode A P)) : (ray w).length=w.length:= by simp [ray]
@[simp] lemma ray_dim (w : Legs (Mode A P)) : fieldDim m (ray w)=fieldDim m w:= by
   exact (sail_dim (ray w) 1).symm.trans (congr_arg _ (ray_sail w)) -- can infer

variable {j : ℕ}
-- Ray read including factorial.
def fieldVal (f : Row A P ℂ) (w : Wire A E P) : E→ℂ := fun x=>f (sail w x)
def stage (j : ℕ) (f : E→ℂ) := diagonal (coeff f j 0)
def torch (j : ℕ) (f : Row A P ℂ) (w : Legs (Mode A P)) := (stage j (fieldVal f (ray w))) 1
abbrev reading (j : ℕ) (f :ℝ→ℂ) := (Nat.factorial j:ℝ)⁻¹ • iteratedDeriv j f 0
lemma torch_at (j : ℕ) (f : Row A P ℂ) (w : Legs (Mode A P)) : torch j f w=reading j (fun x=> f (sail (ray w) x)) := rfl
lemma lit (f : Row A P ℂ) (w : Wire A E P) (h : ContDiff ℝ ∞ (fieldVal f w)) (x : E): torch j f (sail w x)=stage j (fieldVal f w) x:= by
   unfold torch stage Tensor.diagonal Tensor.coeff; rw [smul_apply, smul_apply]
   let Q:ℝ→L[ℝ] E:=ContinuousLinearMap.toSpanSingleton ℝ x
   have he : fieldVal f (ray (sail w x))= fieldVal f w ∘ Q:= by ext; simp [fieldVal,ray_lift,Q]
   rw [he,Q.iteratedFDeriv_comp_right h 0 (by exact_mod_cast le_top),map_zero]; congr 1; simp [Q]

variable {H : Tensor.T E ℂ j}
lemma origin_symm {f : Clock ι → Row A P ℂ} {i : ι} (h : Origin f w j i H) (hp : ∀ t, ContDiff ℝ ∞ (tape f w i t)) : Tensor.Sym H := by
    intro x v; refine tendsto_nhds_unique (((ContinuousMultilinearMap.apply ℝ _ ℂ (x ∘ v)).continuous.tendsto H).comp h) ?_ -- left or right?
    convert! ((ContinuousMultilinearMap.apply ℝ _ ℂ x).continuous.tendsto H).comp h using 1; ext t; exact Analysis.sym_Jet ((hp t).contDiffAt.of_le (by exact_mod_cast le_top)) x v
lemma origin_test {f : Clock ι → Row A P ℂ} {i : ι} (h : Origin f w j i H) (hp : ∀ t, ContDiff ℝ ∞ (tape f w i t)) x :
    Tendsto (fun t=> torch j (f (i,t)) (sail w x)) atTop (𝓝 ((Nat.factorial j:ℝ)⁻¹ • diagonal H x)) := by
   have hx t : torch j (f (i,t)) (sail w x)=stage j (tape f w i t) x:=lit _ _ (hp t) x
   simp_rw [hx]
   exact Tendsto.const_smul (((ContinuousMultilinearMap.apply ℝ _ ℂ (fun _=>x)).continuous.tendsto H).comp h) _ -- order?
lemma origin_ray_iff {f : Clock ι → Row A P ℂ} {i : ι} (H : ∃ H, Origin f w j i H) (hp : ∀ t, ContDiff ℝ ∞ (tape f w i t)) : Origin f w j i 0 ↔ ∀ (x:E), Tendsto (fun t=> torch j (f (i,t)) (sail w x)) atTop (𝓝 0) := by
   constructor
   · intro h x; simpa [Tensor.diagonal] using origin_test h hp x
   rintro h; obtain ⟨U,H⟩ := H; have he x := tendsto_nhds_unique (origin_test H hp x) (h x)
   have hz := Tensor.ext_diag U 0 (origin_symm H hp) (fun _ _=> rfl) (funext fun x=>?_)
   · rwa [hz] at H
   exact (smul_eq_zero.mp (he x)).resolve_left (by positivity)

/-- polynomial, exact degree; all chart tests. Includes symmetry at each use
  separately, not in `Form`, for splitting through sym projections. -/
structure Shape (f : E→ℂ) (i:ℤ): Prop where
   smooth : ContDiff ℝ ∞ f
   charge : i<0 → f=0
   scale (u:ℝ) x : f (u • x)=u^i • f x

def Form (f : Row A P ℂ) (m : A→ℤ) (g: ℤ) (b : Bool) := ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E], ∀ w : Wire A E P, Course b w→ Shape (fieldVal f w) (g-fieldDim m w)

lemma form_diag (T:Tensor.T E ℂ j) (i:ℤ) (h:i=j) : Shape (diagonal T) i:= by
   subst i; exact ⟨Tensor.diag_smooth ..,fun hx=> by omega, fun u x=> by rw [Tensor.homogeneous]; simp⟩
lemma form_zero (i:ℤ): Shape (0:E→ℂ) i:= ⟨contDiff_const,fun _=>rfl,fun u x=> by simp⟩

end YM.MS.Plane
