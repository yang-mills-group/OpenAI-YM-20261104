import YM.OPE.Sparse.Conclusion

/-!
Exact epsilon-free price result includes arbitrary arities of finite tree when
there is at most one non-unit input, using true hierarchy with the homogeneous
common reader and testing across fixed-clearance configurations. No analogous
singular-slot price assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sparse
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Composite Tracing Nesting.Motion
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
open ExactPrice
structure Quiet:Prop where
   direct(n:ℕ)(f:Fin n→Tree)(v:(fork n f).Leaf→S.Tag)(hV: (∃ p,Circuit.Sparse v p) ∨ IsEmpty (fork n f|>.Leaf))
      (m:ℕ)(c:R.channels m)(D:(fork n f).Inner→ℕ)(M η:ℝ)(_:0≤M)(_ :0<η): ∃ K:ℝ,0<K ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(fork n f).Inner→ℝ,∀ z:(fork n f).Plot,Accept x M η s z →‖Kernel.output U R z v c‖ ≤ K*(toll (wages v) 0 m s) ∧ ‖Kernel.output U R z v c - Kernel.chord U R z v c D‖ ≤ K* bothToll (wages v) 0 m D s
   tested(n:ℕ)(f:Fin n→Tree)(v:(fork n f).Leaf→S.Tag)(hV:(∃ p,Circuit.Sparse v p) ∨ IsEmpty (fork n f|>.Leaf))
      (m:ℕ)(M η δ:ℝ)(_ :0≤M)(_ :0<η)(_ :0<δ){J:Type}[Fintype J](d:J→S.Tag):∃ K:ℝ,0<K ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀ s: (fork n f).Inner→ℝ,∀ z:(fork n f).Plot,∀ y:J→E4, Accept x M η s z → Buffer z y δ → let k:=K* toll (wages v) 0 (m+1:ℕ) s; ‖Kernel.normData U R z v m y d‖ ≤ k ∧ ∀ q:Viewers U, ‖Kernel.pipe U R z v q m y d‖ ≤ k
-- complete after core file
theorem quiet (h:Services C F S): Quiet U R :=by
    constructor
    · intro n f v h' m c D M η hM hη; obtain ⟨j,H⟩ | H:=h'
      · exact ExactPrice.fields U R h (w:=v) (p:=j) (D:=D) H c hM hη
      exact ExactPrice.empty_fields_aux U R h (w:=v) (D:=D) c hM hη fun p=> (H.false p).elim
    intro n f v h' m M η δ hM hη hδ J J_inst w; obtain ⟨j,H⟩ | H := h'
    · exact ExactPrice.match' U R h v j H hM hη m w hδ
    exact ⟨1,one_pos, ExactPrice.no_test U R h (w:=v) hM hη (⟨H⟩) m w hδ⟩

/-- Same-coefficient existence, quantitative arbitrary positive exponent-loss
    trees and an estimate with no inverse power losses on all sparsely occupied
    trees. -/
theorem rooted (G:Gauge)(hG : G.Simple) (f:Extraction.Order) :∃ (C:Family G) (g:Extraction.Order) (S:Table C.book), Services C (f.refine g) S ∧ ∃ (U:Spec.Final C (f.refine g) S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin), Quiet U R ∧ Nesting.Uniform U R ∧ Foundation U R ∧ (∃ X: Climb.Scaling S, Pert.FirstExtension U X ∧ Next.UVStress.Approaches (Next.UVStress.path X) (Next.UVStress.isoPanel X)) :=by
    obtain ⟨C,_,hw,he⟩:=Measuring.simultaneous G hG 1 one_pos
    obtain ⟨g',S,h',U,R,X,h₁,h₂,h₃,h₄⟩:= he f
    exact ⟨C,g',S,h',U,R,quiet U R h',h₂,h₃,X,h₁,h₄⟩
end YM.OPE.Sparse
