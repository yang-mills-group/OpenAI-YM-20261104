import YM.XSpace.Compat.GaussInverse
import YM.XSpace.SelfCov
import YM.XSpace.NormalTools

/-!
# W matrix for the top (through field-only letters)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace

open Function Filter Set Lattice Labels Source Source.Drops Wilson Contraction Next.Rank.Normal Finsupp MvPolynomial Top
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {H : Hol G} {d : ℕ}
namespace Survey
variable (A : Survey G H d)

def component (i : Labels.Key G) : Module.Dual ℝ (Snap G d) := Complex.reCLM.toLinearMap ∘ₗ (Work.G05.snapCoord d i).toLinearMap
lemma component_point (i : Labels.Key G) (x : Snap G d) : component (d:=d) i x = (axes G i.1).repr ((expand d x) i.1) i.2:=rfl

def selfCov (z : ℝ := 1) : Cov (Labels.Key G) := ⟨(fun i j=> ↑(z * realCov A (component i) (component j))),by intros; rw [realCov_symm]⟩

section equivariance
variable (T : (i : ℕ) → Module.End ℝ (Labels.Taylor G i))

def coordV (i : Labels.Key G) (j : Fin (dim G i.1)) : ℝ:= (axes G i.1).coord i.2 (T i.1 (axes G i.1 j))
def row (i : Labels.Key G) : Labels.Key G→₀ℂ:= ∑ j, Finsupp.single ⟨i.1,j⟩ (coordV T i j : ℂ)

def snapMove : Module.End ℝ (Snap G d):= LinearMap.pi (fun i=> T i.val ∘ₗ LinearMap.proj i)
lemma coordM (i : Labels.Key G) : component i ∘ₗ snapMove (d:=d) T=∑ j, coordV T i j • component ⟨i.1,j⟩:=by
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply,component_point,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]; unfold expand
  split_ifs with h
  · change (axes _ _).repr (T _ (x ⟨_,h⟩)) _= _
    conv_lhs=> rw [← (axes G i.1).sum_repr (x ⟨_,h⟩)]
    simp only [map_sum, map_smul,Finsupp.finsetSum_apply, Finsupp.smul_apply,smul_eq_mul]; apply Finset.sum_congr rfl; intro j _; rw [mul_comm]; rfl
  simp
lemma equivalent_transform : exchange (row T)= Labels.changed T:=by
  ext1 i; rw [changed,exchange_x,aeval_X,row,map_sum]; apply Finset.sum_congr rfl; intro j _; rw [glyph,linearCombination_single,← MvPolynomial.C_mul']; rfl
lemma keeps_cov (hs : ∀ x y : Module.Dual ℝ (Snap G d), realCov A (x.comp (snapMove T)) (y.comp (snapMove T)) = realCov A x y) (z : ℝ):
    scope (row T) (A.selfCov z)=A.selfCov z:=by
  apply Next.Rank.Normal.Symmetric.ext; funext i j; change treats (A.selfCov z) _ _ = ↑(z * realCov A (component i) (component j))
  unfold row; rw [← hs,coordM,coordM,map_sum (realCov A),LinearMap.sum_apply,Finset.mul_sum,Complex.ofReal_sum,treats_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [map_sum,Finset.mul_sum,Complex.ofReal_sum,treats_comm,treats_sum]
  apply Finset.sum_congr rfl; intro l _
  rw [treats_comm,treats_single,map_smul,map_smul,LinearMap.smul_apply]; simp only [selfCov,smul_eq_mul]; push_cast; ring

lemma transform (p : Labels.Pol G) (z : ℝ) (hs : ∀ x y : Module.Dual ℝ (Snap G d), realCov A (x.comp (snapMove T)) (y.comp (snapMove T)) = realCov A x y) :
    milk (A.selfCov z) (Labels.changed T p)=Labels.changed T (milk (A.selfCov z) p):=by rw [← equivalent_transform,prepared, keeps_cov _ _ hs]
end equivariance

lemma wick_finite (p : Label G d) (z : ℝ) : milk (A.selfCov z) p.val∈localFields G d:=by
  constructor
  · exact wick_bound generation _ p.property.1
  intro J u; change read (changedJet (fun _=>Labels.Taylor.paint u) J) (milk (A.selfCov z) p.val)= _
  have he : changed (fun _=> Labels.Taylor.paint u) p.val=p.val:=by apply Labels.eval_ext; intro J; rw [eval_changed]; exact p.property.2 ..
  rw [← eval_changed, ← A.transform (fun _=>Labels.Taylor.paint u) _ z (fun x y=>realCov_color A u x y),he]

/-- `z=1` gives the prospective top W matrix in the field-only part of the alphabet.
`z=-1` gives the required bare Wick subtraction. -/
def insertW (z : ℝ) : Module.End ℂ (Label G d) :=
  (milk (A.selfCov z) ∘ₗ (localFields G d).subtype).codRestrict _ (fun v=> A.wick_finite v z)
lemma insertW_val (z : ℝ) (p : Label G d) : (A.insertW z p).val=milk (A.selfCov z) p.val := rfl
lemma wick_unit (z : ℝ) : A.insertW z (unit G d)=unit G d:=Subtype.ext (Next.Rank.Normal.pure _)
lemma wick_real (z : ℝ) (p : Label G d): A.insertW z (realBar p)=realBar (A.insertW z p):= by
  apply Subtype.ext; exact Taylor.milk_real (A.selfCov z) (fun i j=>z * realCov A (component i) (component j)) (fun _=>rfl) _
lemma wick_signed (s : Signed) (z : ℝ) (p : Label G d) : A.insertW z (tensor s.ortho p) = tensor s.ortho (A.insertW z p):=Subtype.ext (A.transform (fun _ => Labels.Taylor.turn s.ortho⁻¹) p.val z (fun x y=> realCov_turn A s x y))
lemma inverseCov (z : ℝ) : A.selfCov (-z)= -(A.selfCov z) :=by apply Next.Rank.Normal.Symmetric.ext; funext i j; change ↑(-z * _)= -(↑(z * realCov A (component i) (component j)):ℂ); simp
lemma wick_recovers (z : ℝ) (p : Label G d) : A.insertW (-z) (A.insertW z p)=p:=Subtype.ext (by rw [insertW_val,insertW_val,inverseCov,YM.XSpace.Compat.thaw])
end Survey
end YM.XSpace
