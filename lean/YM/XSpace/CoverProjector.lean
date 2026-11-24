import YM.XSpace.Poincare
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Scalar

/-!
# Free cover plaquette covariance

Linear (color-normalized counting metric) identity at every period including
zero-mode convention. Identify with the *same* Fourier coefficient estimates
as used in the baseline. We don't assume our inversion regulator has these
values; calculate its modification below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson MeasureTheory Laurent Bloch Exterior Matrix
open Next.Free Precision PhysicalNext.RankCovariance Further.FreeCovariance.KP
open Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff

variable (G : Gauge) (n : Side)
abbrev FKey := Face (Per n) × G.ColorIndex
abbrev Pot := Edge (Site n) → G.Color
abbrev topScalar := scalarCov 1 (Train.top 4) n

def kernel : Matrix (FKey G n) (FKey G n) ℝ := of fun i j=> (if i.2=j.2 then
  topScalar n (i.1.1,plaquette i.1.2) (j.1.1,plaquette j.1.2) else 0)

-- baseline's projector for the full torus (independent of R even flag)
lemma has_projection :
    (∃ X, topScalar n=Exterior.d 1 n * X) ∧ topScalar n * Exterior.d 1 n=Exterior.d 1 n := by
  obtain ⟨γ,σ,η,C,hγ,hσ,hη,hC,H⟩ := bid_bed (j:=4) 1 0 one_pos le_rfl le_rfl
  let A : RG.Clip := ⟨γ,γ/32,1,hγ,by positivity,by linarith,one_pos⟩
  obtain ⟨M,hM,hB,h,-,hm⟩:= H A le_rfl (Train.top _)
  let D := Exterior.d 1 n
  have ht : Dᵀ * (M.metric.acts n) * D = Dᵀ*D := by
    rw [Matrix.mul_assoc, (show M.metric.acts n * D=_ from (h n).same),hm rfl n,Matrix.one_mul]
  let X := Resolve.field (h n) hη
  have hg : Dᵀ * D * X = Dᵀ := by rw [← ht]; exact Resolve.hinge _ _
  have hp : topScalar n = D*X := scalar_eq_screen (h n) hη hM le_rfl one_pos
  refine ⟨⟨X,hp⟩,?_⟩
  have hv : Dᵀ * topScalar n = Dᵀ := by rw [hp,← Matrix.mul_assoc,hg]
  have hs := congr_arg Matrix.transpose hv
  rw [Matrix.transpose_mul,show (topScalar n)ᵀ = _ from scalar_symm one_pos _ _,transpose_transpose] at hs
  exact hs

lemma kernel_symm : (kernel G n).IsSymm := by
  have he : (topScalar n)ᵀ=topScalar n := scalar_symm one_pos _ _
  ext i j
  by_cases h : i.2=j.2 
  · simp [kernel,h]
    exact congr_fun (congr_fun he _) _
  simp [kernel,h,Ne.symm h]
-- Baselined physical curvature symbol
lemma kernel_formula (i j : FKey G n) :
    (↑(kernel G n i j):ℂ)= if i.2=j.2 then
      Episode.found 1 (Train.top 4) n (plaquette i.1.2) (plaquette j.1.2) (lift i.1.1-lift j.1.1) else 0 := by
  by_cases h : i.2=j.2
  · simp only [kernel,Matrix.of_apply,h,ite_true]; exact scalar_entry one_pos ..
  simp [kernel,h]

def fields : Pot G n →ₗ[ℝ] (FKey G n → ℝ) where
  toFun A i := field A i.1 i.2
  map_add' A B := by ext i; simp only [field,curl,Pi.add_apply,PiLp.add_apply,PiLp.sub_apply]; abel
  map_smul' c A := by ext i; simp only [field,curl,Pi.smul_apply,RingHom.id_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply]; simp only [smul_eq_mul]; ring

def colors (x : FKey G n → ℝ) (c : G.ColorIndex) : Co n (TypeFace 2) → ℝ :=
  fun (i,f)=> x ((i,plaqEquiv.symm f),c)

def flavor (A : Pot G n) (c : G.ColorIndex) : Co n (TypeFace 1) → ℝ := fun (i,a)=> A (i,axisEquiv.symm a) c

theorem colors_equate (A : Pot G n) (c : G.ColorIndex) : colors G n (fields G n A) c = Exterior.d 1 n *ᵥ flavor G n A c := by
  funext (x,p); obtain ⟨p,rfl⟩ := plaqEquiv.surjective p
  rw [show plaqEquiv p=plaquette p from rfl,d_plaquettes, show plaquette p=plaqEquiv p from rfl]
  simp only [colors,flavor,fields, LinearMap.coe_mk, AddHom.coe_mk, field,
    Equiv.symm_apply_apply]
  simp only [show coord = (axisEquiv : Axis → _) from rfl, Equiv.symm_apply_apply,curl,PiLp.add_apply,PiLp.sub_apply]; abel

lemma scalar_action (x : FKey G n → ℝ) (c : G.ColorIndex) : colors G n (kernel G n *ᵥ x) c = topScalar n *ᵥ colors G n x c := by
  funext (v,p)
  obtain ⟨p,rfl⟩ := plaqEquiv.surjective p
  simp only [colors, Equiv.symm_apply_apply, mulVec, dotProduct]
  rw [Fintype.sum_prod_type,← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site n)) plaqEquiv)]
  simp [kernel, -plaq_map]
  rfl

lemma colors_equiv {x y : FKey G n → ℝ} (h : ∀ c, colors G n x c=colors G n y c) : x=y := by
  ext ⟨⟨i,w⟩,v⟩
  simpa only [colors,Equiv.symm_apply_apply] using congr_fun (h v) (i,plaqEquiv w)

theorem project_fixes (A : Pot G n) : kernel G n *ᵥ fields G n A=fields G n A := by
  apply colors_equiv; intro c; rw [scalar_action, colors_equate,Matrix.mulVec_mulVec,(has_projection n).2]

theorem project_into (x : FKey G n → ℝ) : ∃ A : Pot G n, kernel G n *ᵥ x=fields G n A := by
  obtain ⟨X,hX⟩ := (has_projection n).1
  let F (c : G.ColorIndex) := X *ᵥ colors G n x c
  let A : Pot G n := fun e=> WithLp.toLp 2 (fun c=> F c (e.1,axisEquiv e.2))
  refine ⟨A, colors_equiv _ _ fun c=>?_⟩
  have he : flavor G n A c=F c := by ext ⟨i,p⟩; simp [flavor,A]
  rw [scalar_action,hX,colors_equate, he,Matrix.mulVec_mulVec]

theorem projector : kernel G n * kernel G n=kernel G n := by
  apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← Matrix.mulVec_mulVec]
  obtain ⟨a,h⟩:= project_into G n x; rw [h, project_fixes]

theorem row_bounded (i : FKey G n) : ∑ j, |kernel G n i j|^2 ≤ 1 := by
  let K := kernel G n
  have he := congr_fun (congr_fun (projector G n) i) i
  rw [Matrix.mul_apply] at he
  have h (j) : K j i = K i j := (kernel_symm G n).apply ..
  change (∑ j, K i j*K j i)=K i i at he
  simp_rw [h,← sq] at he
  simp_rw [sq_abs]; change ∑ j, K i j ^ 2 ≤ 1
  have ht : K i i ^ 2 ≤ K i i := (Finset.single_le_sum (f:=fun j=> K i j ^ 2) (fun j _=>sq_nonneg _) (Finset.mem_univ _)).trans_eq he
  rw [he]; nlinarith
end YM.XSpace
