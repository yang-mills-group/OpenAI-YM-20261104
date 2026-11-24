import YM.XSpace.CovOrient
/-! # Color preserving contact subtraction -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson MeasureTheory Laurent Bloch Exterior Matrix
open Next.Free Precision Further.CorrectedLift Further.FreeCovariance.KP Next.Rank Normal Spindle
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff
variable (G : Gauge)
abbrev e0 := (EuclideanSpace.basisFun G.ColorIndex ℝ)

def rowC (u : G.El) := Matrix.of fun i j : G.ColorIndex=> (G.adjoint u (e0 G j)) i

lemma col_ortho (u : G.El): rowC G u*(rowC G u).transpose=1 := by
  rw [_root_.mul_eq_one_comm]; ext i j; rw [Matrix.one_apply,Matrix.mul_apply]
  have hx : ⟪G.adjoint u (e0 G j),G.adjoint u (e0 G i)⟫_ℝ= ⟪e0 G j,e0 G i⟫_ℝ:= LinearIsometry.inner_map_map (⟨G.adjoint u,G.norm_adjoint u⟩:G.Color →ₗᵢ[ℝ] G.Color) _ _
  have he : (∑ x : G.ColorIndex, rowC G u x i*rowC G u x j)=⟪G.adjoint u (e0 G j),G.adjoint u (e0 G i)⟫_ℝ:= by simp [PiLp.inner_apply,rowC]
  simp only [Matrix.transpose_apply,he,hx]; by_cases h:i=j <;> simp [h,e0]
  simpa using (e0 G).orthonormal.2 (Ne.symm h)

def colorPull (u:G.El) (A:CoverC G) (e:Edge Cover):= G.adjoint u (A e)
def colorM (u:G.El) (i:AKey G) := ∑ j:G.ColorIndex, Finsupp.single (i.1,i.2.1,j) (↑(rowC G u i.2.2 j):ℂ)

lemma color_line (u:G.El) (v:G.Color) (j:G.ColorIndex): (G.adjoint u v) j = ∑ k:G.ColorIndex, rowC G u j k*v k := by
  conv_lhs=> rw [← (e0 G).toBasis.sum_repr v,map_sum]
  rw [show ∀ p:G.ColorIndex→G.Color,(∑ x,p x).ofLp j=∑ x,(p x).ofLp j from fun p=>map_sum (EuclideanSpace.proj j : G.Color →L[ℝ] ℝ) _ _]; apply Finset.sum_congr rfl; intro k hk; simp [rowC,e0, mul_comm]

lemma reads_color (u:G.El) (A : CoverC G): Normal.reads (colorM G u) (fun i=>(curlC G A i:ℂ))= fun i=>(curlC G (colorPull G u A) i:ℂ) := by
  funext i
  have he (x:Cover) (w:Walk) : linkSum (colorPull G u A) x w=G.adjoint u (linkSum A x w):= by
    induction w generalizing x with
    | nil=>exact (map_zero _).symm
    | cons a w h=> simp_rw [linkSum,map_add,h]; split <;> simp [colorPull]
  simp [Normal.reads,colorM,curlC,he,color_line]

lemma cov_color (u:G.El): scope (colorM G u) (WickK G)=WickK G := by
  apply Normal.Symmetric.ext; funext i j
  let x:= Orb0 (plaquette i.2.1) (plaquette j.2.1) (i.1-j.1)
  have hp:= congr_arg Complex.ofReal (congr_fun (congr_fun (col_ortho G u) j.2.2) i.2.2)
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,Complex.ofReal_mul,Complex.ofReal_sum] at hp
  simp only [scope,treats,colorM,map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply, WickK,local_cov,smul_eq_mul,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [← mul_assoc,← Finset.sum_mul,hp]; by_cases h:i.2.2=j.2.2 <;> simp [*,Ne.symm]
end YM.XSpace
