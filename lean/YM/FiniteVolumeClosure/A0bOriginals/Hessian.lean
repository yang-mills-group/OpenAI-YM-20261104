import YM.XSpace.Poincare
import YM.Work.F03.Flat
import YM.Work.F02

/-!
# Wilson action flat Taylor germ on the inversion quotient
The quadratic jet used as precision has the color metric of YM.MergeProof.
With one unoriented plaquette on the quotient the coefficient is 1/2 in the Taylor series;
in our bilinear Hessian formula there is *also* a 1/2 because we sum on the cover,
not on the quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson MeasureTheory
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff

namespace Regulator.Tree
variable {R : Regulator} (T : R.Tree) {G : Gauge}

def expLinks (A : T.Array G) : R.Configuration G := T.place (fun l=> G.lieExp (A l))

theorem expLinks_inject (A : T.Array G) (l : R.Link) : T.expLinks A l = G.lieExp (T.injection G A l) := by
  simp only [expLinks,place,injection,LinearMap.coe_mk,AddHom.coe_mk]; split <;> simp [*]

theorem lift_expLinks (A : T.Array G) : R.Lift (T.expLinks A)= fun e=> G.lieExp (T.periodic G A e) := by
  simpa only [show T.expLinks A = _ from funext (T.expLinks_inject A),one_smul, periodic,LinearMap.comp_apply] using R.Lift_exp (T.injection G A) (1:ℝ)

def action (A : T.Array G) := R.orbitEnergy (T.expLinks A)

lemma action_smooth : ContDiffAt ℝ ω (T.action (G:=G)) 0 := by
  unfold action orbitEnergy energy
  simp_rw [T.lift_expLinks]
  have he (e : R.LEdge) : ContDiffAt ℝ ω (fun A : T.Array G => G.mat (G.lieExp (T.periodic G A e))) 0 := by
    apply ContDiffAt.comp (g:=fun z=>G.mat (G.lieExp z)) _ G.exp_jet.contDiffAt
    exact (contDiffAt_apply ..).comp _ (T.periodic G).toContinuousLinearMap.contDiff.contDiffAt
  refine ContDiffAt.div_const (ContDiffAt.sum fun p _=> Work.F03.price_smooth ?_) _
  simp_rw [faceValue,← Work.F02.stringMat_physical]
  exact ((Work.F02.stringMat_contDiff (G:=G) _ _).restrict_scalars ℝ).contDiffAt.comp _ (Work.F02.physical_contDiffAt he)

lemma cost_zero (A : T.Array G) (w : Walk) (x : R.LSite) : travel (R.Lift (T.expLinks ((0:ℝ) • A))) x w = 1 := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih => rw [travel,ih,mul_one]; unfold Step.read; split <;> simp [lift_expLinks]

lemma line_tangent (A : T.Array G) (x : R.LSite) (w : Walk) :
    HasDerivAt (fun t : ℝ => G.mat (travel (R.Lift (T.expLinks (t • A))) x w))
      (G.colorMat (transport (T.periodic G A) x w)) 0 := by
  have he (e : R.LEdge) : HasDerivAt (fun t : ℝ=> G.mat (R.Lift (T.expLinks (t • A)) e)) (G.colorMat (T.periodic G A e)) 0 := by
    simp only [T.lift_expLinks,map_smul,Pi.smul_apply,G.mat_lieExp]
    simpa using! (hasDerivAt_exp_smul_const (G.colorMat (T.periodic G A e)) (0:ℝ))
  induction w generalizing x with
  | nil=> simpa [transport,travel] using! (hasDerivAt_const (0:ℝ) (1:G.Mat))
  | cons d w ih=>
    have hd : HasDerivAt (fun t : ℝ => G.mat (d.read (R.Lift (T.expLinks (t • A))) x)) (G.colorMat (increment (T.periodic G A) x d)) 0 := by
      rcases d with ⟨i,b|b⟩
      · exact he _
      simp only [Step.read,ite_true,increment,G.mat_inv,map_neg]
      rw [← G.colorMat_skew]; exact (he _).star
    have hz : d.read (R.Lift (T.expLinks ((0:ℝ) • A))) x = 1 := by
      unfold Step.read; split <;> simp [lift_expLinks]
    convert! hd.mul (ih (x+d.vec)) using 1
    simp only [transport,map_add]; rw [hz,cost_zero]; simp

lemma line_face (A : T.Array G) (x : R.LSite) (a b : Axis) :
    transport (T.periodic G A) x (square a b) = curl (T.periodic G A) x a b := by
  simp only [square, curl, transport, Step.vec, increment,Step.used,posDir,negDir,Bool.false_eq_true,↓reduceIte]
  rw [add_sub_right_comm,add_sub_cancel_right]; simp [sub_eq_add_neg, add_assoc]

def Q (G : Gauge) (A B : T.Array G) := (∑ p, inner ℝ (field (T.periodic G A) p) (field (T.periodic G B) p))/2

theorem flat_hessian : T.action (0:T.Array G)=0 ∧ fderiv ℝ T.action (0:T.Array G)=0 ∧
    ∀ (A B : T.Array G), iteratedFDeriv ℝ 2 T.action 0 ![A,B] = T.Q G A B := by
  apply Work.F03.hessian_of_limit (T.action_smooth.of_le le_top)
  · intro A
    unfold Q action orbitEnergy energy
    simp_rw [Finset.sum_div]; refine tendsto_finsetSum _ fun p _=>?_
    have he := T.line_tangent A p.1 (square p.2.val.1 p.2.val.2)
    rw [line_face] at he
    rw [real_inner_self_eq_norm_sq]; refine ((Work.F03.price_limit (V:=fun t => faceValue (R.Lift (T.expLinks (t • A))) p) (T.cost_zero ..) (c:=field _ _) he).div_const 2).congr (fun t => ?_)
    ring
  · intro A B C
    have hf (p) : field (T.periodic G (A+B)) p = field (T.periodic G A) p + field (T.periodic G B) p := by
      simp only [field,map_add,curl,Pi.add_apply]; abel
    unfold Q; simp_rw [hf,inner_add_left]; rw [Finset.sum_add_distrib,add_div]
  intro x y; unfold Q; apply congr_arg (·/2); exact Finset.sum_congr rfl fun i _=>real_inner_comm ..

theorem definite (A : T.Array G) (hA : A ≠ 0) : 0 < T.Q G A A := by
  unfold Q; apply div_pos _ two_pos
  have h : field (T.periodic G A) ≠ 0 := fun he=> hA (T.flat_tree A he)
  obtain ⟨p,hp⟩ := Function.ne_iff.mp h
  exact Finset.sum_pos' (fun q _=> real_inner_self_nonneg) ⟨p,Finset.mem_univ _, real_inner_self_pos.mpr hp⟩
end Regulator.Tree
end YM.XSpace
