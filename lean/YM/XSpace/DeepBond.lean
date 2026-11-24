import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Depth
import YM.Next.MAXWELL.Steps
/-!
# An orthogonally invariant *complex bilinear*
reflection-axis metric on the **low** horizon four

Here using the existing Maxwell constructive proofs of positivity and change of ray.
Filtration includes the unit. The restriction of a silent equivariant field change is
also skew for this bilinear form; e.g. there's no need to assume it preserves slot number.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Filter Set Maxwell Maxwell.Free Maxwell.Wick
open scoped Topology ContDiff BigOperators
variable {G : Gauge}

lemma move_bond (s : Ortho) {x y : E4} (hx : x≠y) (p q : WickPol G) :
    bond G (Ortho.move s x) (Ortho.move s y) (reflectPol s p) (reflectPol s q)=bond G x y p q:=by
  rw [bond_eval,bond_eval,← moment_rotation _ (pair_ok hx) _ s]
  rw [show Points.move s (pairPoints x y) = pairPoints (Ortho.move s x) (Ortho.move s y) from ?_]
  · exact (congr_arg (moment G (pairPoints (Ortho.move s x) (Ortho.move s y))) (funext fun i=> by fin_cases i <;> rfl))
  ext1 i; rw [Points.move_coord]; fin_cases i <;> rfl
lemma swap_bond {x y : E4} (hx : x ≠ y) (p q : WickPol G) : bond G x y p q=bond G y x q p:= by
  rw [bond_eval,bond_eval,exchangeSites (Equiv.swap 0 1) (pair_ok hx)]
  rw [show points ((pairPoints x y).ofLp ∘ (Equiv.swap 0 1))=pairPoints y x from ?_]
  · exact (congr_arg (moment G (pairPoints y x)) (funext fun i => by fin_cases i <;> simp))
  ext1 i; fin_cases i <;> simp [pairPoints,Points.cons]

def HouseBond (x : E4) : WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ := (bond G x 0) ∘ₗ (reflectPol (house x)).toLinearMap
lemma H_eq (x : E4) (p q : WickPol G) : HouseBond x p q=bond G x 0 (reflectPol (house x) p) q:=rfl
lemma pol_house_twice (x : E4) (p : WickPol G): reflectPol (house x) (reflectPol (house x) p)=p:= by rw [←pol_mul, show house x * house x = 1 by nth_rw 2 [← house_inv]; rw [mul_inv_cancel], pol_one]
lemma reflect_self {x : E4} (hx : x≠0) : Ortho.move (house x) x = -x := by
  change M4.move (houseM x) _ = _
  rw [house_on,real_inner_self_eq_norm_sq]
  have hh : ‖x‖ ≠0:= (norm_pos_iff.mpr hx).ne'; rw [mul_assoc, inv_mul_cancel₀ (by positivity),mul_one,two_smul]; abel
lemma move_zero (s : Ortho) : Ortho.move s 0=0:= map_zero s.motion
lemma house_symmetric {x : E4} (hx : x≠0) (p q : WickPol G) : HouseBond x p q= HouseBond x q p:= by
  rw [H_eq,H_eq, ← move_bond (house x) (y:=0) hx,reflect_self hx,move_zero,pol_house_twice]
  rw [swap_bond (by simpa),← pair_flow 0 (-x) x,zero_add,neg_add_cancel]
lemma orth_H (s : Ortho) {x : E4} (hx : x ≠ 0) (p q : WickPol G) :
    HouseBond (Ortho.move s x) (reflectPol s p) (reflectPol s q)=HouseBond x p q:= by
  rw [H_eq,← pol_mul,house_conjugate,pol_mul,H_eq,← move_bond s (y:=0) hx,move_zero]

lemma orth_four (s : Ortho) {x : E4} (hx : x ≠ 0) (h : G.Simple) {p q : WickPol G} (hp : p∈shellSector G 4) (hq : q∈shellSector G 4):
    HouseBond x (reflectPol s p) (reflectPol s q)=HouseBond x p q:=by
  rw [← orth_H s hx p q]
  let y := Ortho.move s x
  have he : y ≠ 0 := by unfold y; rw [← move_zero s]; exact (Ortho.move_injective _).ne hx
  rw [H_eq,H_eq,corridor h hx he (Ortho.move_norm s x).symm _ _ (closed_sector (closed_sector hp _).1 _).1 (closed_sector hq s).1,pol_mul,pol_house_twice]

def ray : E4 := -basis 3
lemma ray_exists : ray≠0:= by unfold ray; rw [neg_ne_zero]; exact norm_pos_iff.mp (by simp)
lemma houseRay : house ray = (Signed.mirror 3).ortho:= by
  apply Ortho.ext; intro x; apply PiLp.ext; intro i
  change M4.move (houseM ray) x i= Ortho.move (Signed.reflect _) x i
  rw [house_on]; by_cases h : i=3 <;> simp_all [ray]; ring

variable {d : ℕ} {T : Module.End ℂ (WickPol G)} {p q : WickPol G}
def Equivariant (d : ℕ) (T : Module.End ℂ (WickPol G)) := ∀ s : Signed,∀ p∈shellSector G d,T (reflectPol s.ortho p)=reflectPol s.ortho (T p)
def Slot (T : Module.End ℂ (WickPol G)): WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ := (HouseBond ray).comp T
lemma same_slot (S : Signed) (h : G.Simple) (hl : 4≤d) (H : Equivariant d T)
    (ht : T p ∈ shellSector G 4) (hp : p ∈ shellSector G 4) (hq : q∈shellSector G 4) :
    Slot T (reflectPol S.ortho p) (reflectPol S.ortho q)=Slot T p q:=by
  rw [Slot,LinearMap.comp_apply,LinearMap.comp_apply,H S p (chain hl hp)]; exact orth_four _ ray_exists h ht hq
lemma skew_slot (H : Equivariant d T) (h : silence G d T) (hp : p∈shellSector G d) (hq : q∈shellSector G d) :
    Slot T p q+Slot T q p=0:=by
  have hh := two_stat ray_exists h (p:=reflectPol (house ray) p) (closed_sector hp _).1 hq
  rw [houseRay,H (Signed.mirror _) p hp] at hh
  rw [Slot,LinearMap.comp_apply,LinearMap.comp_apply,H_eq,house_symmetric ray_exists (T q), H_eq,houseRay]; exact hh
lemma probe_axis (p : WickPol G) (hp : p∈shellSector G d) (h : ∀ q∈shellSector G d, HouseBond ray p q=0) : p=0:= by
  have hp' : reflectPol (house ray) p=0 := pair_nonzero (r:=1) 3 _ (by norm_num) (closed_sector hp _).1 fun q hq=> by simp only [neg_one_smul]; exact h _ hq
  rw [← pol_house_twice ray p,hp',map_zero]
end YM.XSpace.Normalize
