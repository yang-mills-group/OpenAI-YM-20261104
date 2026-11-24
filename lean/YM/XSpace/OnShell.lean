import YM.XSpace.Compat.MaxwellBidegree
import YM.Next.MAXWELL.Caps
import YM.Next.MAXWELL.Depth

/-!
# A compatible choice of section of the **free** equation ideal

Address-zero, bidegree, real, equivariant. Use invariant-complement freedom in §g0; no
metric fixed for this finite-dimensional lift. (As usual can think of using orthogonal
complements by taking metrics with summands in a real invariant splitting orthogonal.)
Here too choosing an algebra hom (also on the ancillary NON-invariant linear slots) is very
useful. Apply to color-invariant Maxwell Wick labels. Filtration interpreted by inclusions;
no changing the representation with perturbative order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.On
open Function Filter Set Maxwell Maxwell.Free Labels MvPolynomial
open scoped Topology ContDiff BigOperators
variable {G : Gauge}
section legs
variable (G : Gauge) (j : ℕ)
def legmap (s : Signed) := (solutionTurn (F:=G.Color) s.ortho⁻¹) ∘ₗ assign G j ∘ₗ Labels.Taylor.turn s.ortho

def solve : Taylor G j →ₗ[ℝ] Shell G j:= ((Fintype.card Signed : ℝ)⁻¹) • ∑ s:Signed, legmap G j s

variable {G j}
lemma on_shell (x : Shell G j) : solve G j (gaugeJet x) =x:=by
  unfold solve; simp_rw [LinearMap.smul_apply, LinearMap.sum_apply,legmap,LinearMap.comp_apply,gauge_orient,retrieve, ← solution_rep, inv_mul_cancel,solution_id, Finset.sum_const, Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ]
  exact inv_smul_smul₀ (by positivity) _
lemma leg_signed (A : Labels.Taylor G j) (t : Signed) : solve G j (Labels.Taylor.turn t.ortho A) =solutionTurn t.ortho (solve G j A) := by
  have he (s) : legmap G j s (Labels.Taylor.turn t.ortho A)=solutionTurn t.ortho (legmap G j (s*t) A):=by
    unfold legmap; simp only [LinearMap.comp_apply,← Labels.Taylor.turn_mul,← solution_rep,(show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO ..),mul_inv_rev,mul_inv_cancel_left];
  unfold solve; simp_rw [LinearMap.smul_apply, LinearMap.sum_apply,he, ← map_sum,map_smul]; congr 2; exact Equiv.sum_comp (Equiv.mulRight t) (fun s=> legmap G j s A)
lemma leg_color (A : Labels.Taylor G j) (u : G.El) : solve G j (Labels.Taylor.paint u A)= castFace u j (solve G j A):=by
  have ht (t : Ortho) (x : Shell G j) : solutionTurn t (castFace u j x)=castFace u j (solutionTurn t x):=by
    apply (show Injective (gaugeJet (G:=G) (j:=j)) from LeftInverse.injective (f:=gaugeJet (G:=G) (j:=j)) (g:=solve G j) fun _=> on_shell _)
    rw [← gauge_orient,equiv_curl,equiv_curl,gauge_orient t x|>.symm,Labels.Taylor.turn_paint]
  unfold solve; simp only [LinearMap.smul_apply,LinearMap.sum_apply,map_smul, map_sum,legmap,LinearMap.comp_apply,← Labels.Taylor.turn_paint,fit_paint,ht]
end legs

def lifting : WickPol G →ₐ[ℂ] Labels.Pol G:= aeval fun i : Maxwell.Slot G =>
    ∑ j : Fin (Labels.dim G i.1), C (σ:= Labels.Key G) (coordinateLeg i (solve G i.1 (axes G i.1 j)) : ℂ) *
       X (R:=ℂ) (⟨i.1,j⟩ : Labels.Key G)

private lemma lin_test {ι E : Type} [Fintype ι] [AddCommGroup E] [Module ℝ E] (A : Module.Basis ι ℝ E) (L : E →ₗ[ℝ] ℝ) (x : E) :
    ∑ i : ι, ((L (A i):ℝ):ℂ) * (A.repr x i:ℝ) = ↑(L x) := by
  conv_rhs=> rw [← A.sum_repr x,map_sum]
  simp only [map_smul,smul_eq_mul, Complex.ofReal_sum,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _=> mul_comm _ _
lemma lifted (p : WickPol G) (A : Labels.Jet G) : Labels.read A (lifting p) = probe (fun i=> solve G i (A i)) p := by
  suffices H : (Labels.read A).comp lifting=probe (fun i => solve G i (A i)) from DFunLike.congr_fun H p
  ext1 i
  simp only [AlgHom.comp_apply,lifting, MvPolynomial.aeval_X,map_sum,map_mul,Labels.read, MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply,probe] 
  simp only [Labels.coord, Maxwell.coord, Maxwell.coordinateLeg, Module.Basis.coord_apply]
  have h:= lin_test (axes G i.1) ((coordinateLeg i).comp (solve G i.1)) (A i.1)
  simp only [Maxwell.coordinateLeg, LinearMap.comp_apply, Module.Basis.coord_apply] at h
  convert h using 1
lemma lift_recover (p : WickPol G) : reduceEq (lifting p)=p:= equalPol _ _ fun x=>by rw [jet_value,lifted]; simp only [on_shell]
lemma lift_conj (p : WickPol G) : lifting (Free.realForm p)=Labels.conjPol (lifting p):= Labels.eval_ext _ _ fun A=> by rw [lifted,real_eval,conj_value,lifted]
lemma lift_signed (s : Signed) (p : WickPol G) : lifting (reflectPol s.ortho p)=rotated s.ortho (lifting p):=by
  apply Labels.eval_ext; intro A; rw [lifted, reflects_eval,rotated,eval_changed,lifted]
  apply congr_arg (fun x : Maxwell.TaylorTower G => probe x p); ext1 j; rw [changedJet,show s.ortho⁻¹=(s⁻¹).ortho from (map_inv Signed.inclusionO s).symm,leg_signed]
lemma grade {M : Type*} [AddCommMonoid M] (m : ℕ→ M) (i : Maxwell.Slot G) :
    IsWeightedHomogeneous (fun k : Labels.Key G=> m k.1) (lifting (X i)) (m i.1):=by
  rw [lifting,aeval_X]; apply IsWeightedHomogeneous.sum; intro j _; apply IsWeightedHomogeneous.C_mul; exact isWeightedHomogeneous_X ..

variable {d n l : ℕ}
lemma fits (x : shellSector G d) : lifting x.val∈ Labels.localFields G d:=by
  constructor
  · exact transfers _ _ lifting (grade (fun i => i+2)) _ (sector.mp x.property).1
  intro A u; rw [lifted,lifted]; unfold Labels.colored; simp_rw [leg_color]; exact (pigment_action u _ _).symm.trans (congr_arg _ ((sector.mp x.property).2 u))

def sectionMap (d : ℕ) : (shellSector G d) →ₗ[ℂ] Labels.Label G d:= (lifting.toLinearMap ∘ₗ (shellSector G d).subtype).codRestrict _ fits
lemma section_value (v : shellSector G d) : (sectionMap d v).val=lifting v.val:=rfl
theorem recovers (v : shellSector G d): observable G d (sectionMap d v)=v.val:= lift_recover _
theorem raised (h : d≤l) (v : shellSector G d) : raiseLabel G h (sectionMap d v)= sectionMap l (Submodule.inclusion (chain h) v):=rfl
lemma section_turn (s : Signed) (u v : shellSector G d) (h : reflectPol s.ortho u.val=v.val) : sectionMap d v=Labels.tensor s.ortho (sectionMap d u):=Subtype.ext (by rw [section_value,← h,lift_signed]; rfl)
lemma section_real (u v : shellSector G d) (h : Free.realForm u.val=v.val): sectionMap d v=Labels.realBar (sectionMap d u):=Subtype.ext (by rw [section_value,← h,lift_conj]; rfl)
lemma section_grade (x : shellSector G d) (h : MvPolynomial.IsWeightedHomogeneous Free.bwt x.val (l,n)): sectionMap d x ∈ Labels.Grade (l,n):=by
  apply (pure_grade _ _).mpr; change IsWeightedHomogeneous bidegree (lifting x.val) (l,n)
  have he := commuting bwt bidegree lifting (grade (fun i=> (i+2,(1:ℕ)))) x.val (l,n); rw [h.weightedHomogeneousComponent_same] at he
  rw [← he]; exact weightedHomogeneousComponent_mem ..

end YM.XSpace.On
