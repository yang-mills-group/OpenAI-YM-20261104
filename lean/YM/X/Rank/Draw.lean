import YM.X.Rank.Fog
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Issue.Glyph
/-! Building the color-orbit test without a separate invariant theory axiom. Part 1:
expectations of the free observable polynomial in all Kronecker Gaussian laws. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter Finsupp Maxwell Wick MeasureTheory Matrix
open YM.PhysicalNext.WeightedGaussianMarginal45C.Issue YM.Next.SectorChange.Gaussian
open YM.Next.Rank.Normal MvPolynomial Heat
open scoped Topology BigOperators Classical Kronecker
variable {G : Gauge}
section Gaussian
variable {I J:Type} [DecidableEq I][DecidableEq J][Fintype I][Fintype J]

abbrev Tile (V : Type):= (V×V)→ℝ
abbrev TileK (V : Type):= Matrix V V ℝ
abbrev folio {J:Type} {V:Type} (x:J×V→ℝ) : Matrix J V ℝ := Matrix.of fun i j=>x (i,j)
lemma pushPaid (q : TileK I)(p : poly I)(hp:q.PosDef):
    Integrable (fun x:I→ℝ=> aeval (fun i=>(x i:ℂ)) p) (cloud q) ∧
    (∫ x:I→ℝ, aeval (fun i=>(x i:ℂ)) p ∂cloud q)=blend (realRank q (Matrix.isHermitian_iff_isSymm.mp hp.isHermitian)) 0 p := by
  let h:= fullGlyph q hp.posSemidef (Matrix.isHermitian_iff_isSymm.mp hp.isHermitian)
  refine ⟨h.prices p,?_⟩; have h := (Next.Rank.Tapes.payment (m:=0) h p)
  simp only [Next.Rank.Tapes.carry, zero_add,Pi.zero_apply,Complex.ofReal_zero] at h; exact h
end Gaussian

def ranger (v : Stroke→G.Color)(k:Fiber G) : (G.ColorIndex×G.ColorIndex)→₀ℂ:= ∑ j:G.ColorIndex,Finsupp.single (k.2,j) (↑(v k.1 j))
def lens (A: Stroke→G.Color)(p:Canvas G) := Next.Rank.Normal.exchange (ranger A) p
abbrev foul (x:Tile G.ColorIndex) (p:Canvas G)(A:Stroke→G.Color) : ℂ := aeval (fun k:Fiber G=>((folio x *ᵥ (A k.1).ofLp) k.2:ℂ)) p
lemma lens_v (A:Stroke→G.Color)(p:Canvas G) (x : Tile G.ColorIndex): aeval (fun z=>(x z:ℂ)) (lens A p)=foul x p A:=by
  unfold lens; rw [reads_val]; apply congr_arg (fun x : Fiber G→ℂ=> aeval x p); funext i; simp [reads,ranger,mulVec,dotProduct, mul_comm,folio]
private lemma splitIt (x : Stroke→G.Color)(P : TileK G.ColorIndex) (h:(1 ⊗ₖ P : TileK (G.ColorIndex×G.ColorIndex)).IsSymm) : splitCost (scope (ranger x) (realRank (1 ⊗ₖ P) h)) := by
  let v i j:= ∑ k:G.ColorIndex,∑ l:G.ColorIndex, (x i l:ℂ)*(P l k:ℂ)*(x j k:ℂ); refine ⟨v,fun i=>funext fun j=> ?_⟩
  rcases i with ⟨i,r⟩; rcases j with ⟨j,s⟩; dsimp only
  unfold scope ranger; simp only [treats,map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,realRank, kronecker_apply,Matrix.one_apply]
  by_cases he : s=r
  · simp only [he,↓reduceIte,one_mul]; unfold v; simp_rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=> by ring
  simp [he,Ne.symm he]

theorem color_draw (p : Canvas G) {S: Finset E4}(A : Stroke→ G.Color)(c:G.ColorIndex) (hp: Fits S p) (hv:Silent c p S) (P : TileK G.ColorIndex) (hk:P.PosDef) :
    let μ:= cloud (1 ⊗ₖ P:TileK (G.ColorIndex×G.ColorIndex)); (∫ x, foul x p A ∂μ)=0:= by
  intro μ; have hx: (1 ⊗ₖ P:TileK (G.ColorIndex×G.ColorIndex)).PosDef:=Matrix.PosDef.one.kronecker hk
  unfold μ; simp_rw [← lens_v,pushPaid _ _ hx |>.2, lens,wets, show reads (ranger A) 0=0 from funext fun i=>by unfold reads; simp]
  exact converted c _ (splitIt A P _) hp hv
end YM.PositionX.Rank
