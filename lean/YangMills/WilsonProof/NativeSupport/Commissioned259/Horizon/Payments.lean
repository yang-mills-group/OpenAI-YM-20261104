import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Four
import Mathlib.LinearAlgebra.Multilinear.Curry
/-!
# Allowance at compact & moving Flash259HorizonFork layouts. log-price

Use `Log.badge r`, not weaker Rate receipts. These filters below only for uniformity along
all true parameter windows. No NeBot needed (can use `⊥`). Applications explicitly
translate this back to ∀ rooms. Hierarchy, phase & fields estimates NOT statements
about cutoff experiments simultaneous with moving scales.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Filter Set Asymptotics MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open scoped Topology Classical BigOperators
open Node Log
variable {I J E : Type*} [Norm E] {r w u : I → ℝ} {l : Filter I}

def Allowance (l : Filter I) (r w : I→ℝ) (f : I→E) : Prop := ∃ k:ℕ, f =O[l] fun i=> w i*badge (r i)^k
local notation "late" => 𝓝[>] (0:ℝ)
variable (hr : Tendsto r l late)
include hr in
lemma log_pays : ∀ᶠ i in l, 1 ≤ badge (r i) := ((show Tendsto (fun i=>run (r i)) l atTop from (run_towards (r:=fun s:ℝ=>s) tendsto_id).comp hr)|>.eventually_ge_atTop 0).mono (fun i h=>(le_add_of_nonneg_right h))

namespace Allowance
variable {f : I→E}
lemma covers (h : f=O[l] w) : Allowance l r w f := ⟨0,by simpa only [pow_zero,mul_one]⟩
lemma congr (h:Allowance l r w f) {g:I→E} (hg : f=ᶠ[l] g) : Allowance l r w g := by obtain ⟨i,h⟩:=h; exact ⟨i,h.congr' hg (EventuallyEq.refl ..)⟩
lemma transport (h:Allowance l r w f) (hu : w =O[l] u) : Allowance l r u f := by obtain ⟨i,h⟩:=h; exact ⟨i,h.trans (hu.mul (isBigO_refl _ l))⟩
lemma extend (h:Allowance l r w f) (hu:w =ᶠ[l] u) : Allowance l r u f := h.transport ( (isBigO_refl w l).congr' (EventuallyEq.refl ..) hu)
include hr in
lemma overtime (n m : ℕ) (hn : n ≤ m) : (fun i=> w i*badge (r i)^n)=O[l] fun i=> w i*badge (r i)^m := by
  refine IsBigO.of_bound' ?_; filter_upwards [log_pays hr] with i h; simp only [norm_mul,norm_pow]; gcongr; exact h.trans (le_abs_self _)
variable {E : Type*} [NormedAddCommGroup E] {f g:I→E}
lemma travels {E' : Type*} [Norm E'] {f' : I→E'} (h:Allowance l r w f) (hu:f' =O[l] f) : Allowance l r w f' := by obtain ⟨i,h⟩:= h; exact ⟨i,hu.trans h⟩
lemma fixed (f : E) : Allowance l r (fun i=>1) (fun _=> f) := covers (isBigO_const_const (c:=f) one_ne_zero l)
lemma zero (u : I→ℝ) : Allowance l r u (fun _=>(0:E)) := covers (isBigO_zero ..)
lemma norm (h:Allowance l r w f) : Allowance l r w (fun i=> ‖f i‖) := h.travels (isBigO_norm_left.mpr (isBigO_refl _ _))
lemma neg (h:Allowance l r w f) : Allowance l r w (fun i=> -f i) := h.travels (isBigO_neg_left.mpr (isBigO_refl _ _))
include hr
lemma add (h : Allowance l r w f) (u : Allowance l r w g) : Allowance l r w (fun i=> f i+g i) := by obtain ⟨k,h⟩:=h; obtain ⟨m,u⟩:=u; exact ⟨max k m,(h.trans (overtime hr _ _ (le_max_left ..))).add (u.trans (overtime hr _ _ (le_max_right ..)))⟩
lemma sum (s : Finset J) (f : J→I→E) (h : ∀ j∈s,Allowance l r w (f j)) : Allowance l r w (fun i=>∑ j∈s,f j i) := by
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.sum_empty]; exact Allowance.zero _
  | insert j s hj ih => simp_rw [Finset.sum_insert hj]; exact Allowance.add hr (h j (Finset.mem_insert_self ..)) (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
-- universal witnesses permitted by positive price
lemma budget (h : Allowance l r w f) (s : ∀ᶠ i in l, 0 ≤ w i) : ∃ C : ℝ, 0<C ∧ ∃ k:ℕ, ∀ᶠ i in l, ‖f i‖ ≤ C*badge (r i)^k*w i := by
  obtain ⟨k,G⟩:=h; obtain ⟨c,H,v⟩:=G.exists_pos; refine ⟨c,H,k,?_⟩; filter_upwards [v.bound,log_pays hr,s] with i v w h; apply v.trans_eq; rw [Real.norm_of_nonneg (by positivity)]; ring
omit hr
lemma mul {K : Type*}[NormedRing K] {f g:I→K} (h : Allowance l r w f)(v : Allowance l r u g) : Allowance l r (fun i=> w i*u i) (fun i=> f i*g i):=by obtain ⟨k,h⟩:=h; obtain ⟨m,v⟩:=v; exact ⟨k+m,(h.mul v).congr_right (fun i=>by rw [pow_add]; ring)⟩
lemma prod {w:J→I→ℝ}{f:J→I→ℂ} (s : Finset J) (h : ∀ j∈s,Allowance l r (w j) (f j)) : Allowance l r (fun i=>∏ j∈s,w j i) (fun i=>∏ j∈s,f j i) := by
  induction s using Finset.induction_on with
  | empty=> simp_rw [Finset.prod_empty]; exact fixed _
  | insert j s hj ih=> simp_rw [Finset.prod_insert hj]; exact Allowance.mul (h j (Finset.mem_insert_self ..)) (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))

lemma smul {K : Type*}[NormedField K][NormedSpace K E] {f : I→K} (h : Allowance l r w f)(v : Allowance l r u g): Allowance l r (fun i=> w i*u i) (fun i=> f i • g i):=by
  obtain ⟨p,v⟩:=v; obtain ⟨q,h⟩:=h; exact ⟨p+q,(h.smul v).congr_right (fun i=>by rw [pow_add]; ring)⟩
lemma linear {K E' : Type*} [NontriviallyNormedField K] [NormedSpace K E] [NormedAddCommGroup E'][NormedSpace K E'] (L:E→L[K] E')(h : Allowance l r w f) : Allowance l r w (L ∘ f) := by
  exact h.travels (IsBigO.of_bound ‖L‖ (Eventually.of_forall fun i=> L.le_opNorm (f i)))
end Allowance
end YM.OPE.Flash259HorizonFork
