import YM.Integration.WilsonCoherentFrozenWord

/-! Joint physical stencils with any subset of their intrinsic links held at
independently prescribed compact values. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentFrozenStencil
open Function Lattice Wilson RG
open RGComparison.Core16 RGComparison.Core16.Spool
open scoped Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [Fintype I] (J : I → Lamp G)

def field (A : Finset (Slice J)) (b : (Slice J → G.El)) (z : Slice J → G.Color) :
    (Slice J → G.El) := fun j => if j ∈ A then G.lieExp (z j) else b j

def mark (A : Finset (Slice J)) (b : (Slice J → G.El)) (z : Slice J → G.Color) : ℂ :=
  exhibit J (field J A b z)

def links (A : Finset (Slice J)) (i : I)
    (z : (Slice J → G.Mat) × (Slice J → G.Color)) (e : Edge Cover) : G.Mat :=
  if h : e.1 ∈ (J i).stencil then
    let j : Slice J := ⟨i,⟨e.1,h⟩,e.2⟩
    if j ∈ A then G.mat (G.lieExp (z.2 j)) else z.1 j
  else 1

theorem links_smooth (A : Finset (Slice J)) (i : I) (e : Edge Cover) :
    ContDiff ℝ ω (fun z => links J A i z e) := by
  unfold links
  split
  · dsimp only
    split
    · exact G.exp_jet.comp ((contDiff_apply ℝ G.Color _).comp contDiff_snd)
    · exact (contDiff_apply ℝ G.Mat _).comp contDiff_fst
  · exact contDiff_const

omit [Fintype I] in
theorem entering (A : Finset (Slice J)) (b : (Slice J → G.El)) (z : Slice J → G.Color)
    (i : I) :
    links J A i (fun j => G.mat (b j),z) =
      fun e => G.mat (wind (J i) (fun j => field J A b z ⟨i,j⟩) e) := by
  funext e
  unfold links wind field
  split
  · dsimp only
    split <;> rfl
  · exact G.mat_one.symm

/-- A single ambient analytic function lets us bound Taylor remainders
uniformly on the compact space of every frozen group entry. -/
theorem original (A : Finset (Slice J)) :
    ∃ F : ((Slice J → G.Mat) × (Slice J → G.Color)) → ℂ,
      ContDiff ℝ ω F ∧ ∀ (b : (Slice J → G.El)) (z : Slice J → G.Color),
        F (fun j => G.mat (b j),z) = mark J A b z := by
  classical
  choose k B P eq _ using fun i => (J i).basis
  let tr := fun (i : I) (z : (Slice J → G.Mat) × (Slice J → G.Color)) (j : Fin (k i) × G.ColorIndex) =>
    Complex.ofReal (WilsonCoherentFrozenWord.slot (links J A i z) (B i j.1) j.2)
  let f := fun (i : I) z => MvPolynomial.aeval (tr i z) (P i)
  refine ⟨fun z => ∏ i, f i z,contDiff_prod (fun i _ => ?_),?_⟩
  · have entries (j : Fin (k i) × G.ColorIndex) : ContDiff ℝ ω (fun z => tr i z j) :=
      Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj j.2 : G.Color →L[ℝ] ℝ).contDiff.comp
        (WilsonCoherentFrozenWord.slot_smooth (links_smooth J A i) (B i j.1)))
    unfold f
    induction P i using MvPolynomial.induction_on with
    | C a => simp only [MvPolynomial.aeval_C,Algebra.algebraMap_self_apply]; exact contDiff_const
    | add p q hp hq => simp only [map_add]; exact hp.add hq
    | mul_X p j ih => simp only [map_mul,MvPolynomial.aeval_X]; exact ih.mul (entries j)
  · intro b z
    apply Finset.prod_congr rfl
    intro i _
    unfold f tr
    rw [eq i]
    simp only [Function.comp_apply,Bid.lumin,Bid.mapped,entering,WilsonCoherentFrozenWord.observed]

end YM.Integration.WilsonCoherentFrozenStencil
