import YM.PertExtension.PaintTop
import YM.PertExtension.CurlSymbol

/-! No loss of symmetry under the full infinite-volume curl heat operator. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.PertExtension.Hue
open Function Filter Set Finset MeasureTheory MvPolynomial Lattice Heat.Top Next.Rank Normal Wilson RG Source Bid Labels Drops LatticePT
open scoped Matrix.Norms.Frobenius Topology Classical BigOperators Real ContDiff RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{α:Type*}

lemma wick_inner (u v: G.Color)(g:G.El) : inner ℝ (G.adjoint g u) (G.adjoint g v)=inner ℝ u v := by
  let F : G.Color →ₗᵢ[ℝ] G.Color:=⟨G.adjoint g, G.norm_adjoint g⟩
  exact F.inner_map_map ..

lemma reformation (g:G.El)(x:G.ColorIndex)(v:G.Color): ∑ i:G.ColorIndex, G.adjoint g (EuclideanSpace.basisFun _ ℝ i) x * v i= G.adjoint g v x:= by
  let B:= (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis
  have h:= congr_arg (fun (w:G.Color)=>(G.adjoint g w) x) (B.sum_repr v)
  dsimp only at h
  rw [map_sum] at h
  have hv(j:G.ColorIndex): B.repr v j=v j:=by unfold B;simp
  rw [show ∀ f:G.ColorIndex→G.Color,(∑ i,f i).ofLp x= ∑ i,(f i).ofLp x from fun f=>map_sum (EuclideanSpace.proj x: G.Color →L[ℝ] ℝ) f _] at h
  refine Eq.trans (Finset.sum_congr rfl fun i hi=>?_) h
  rw [map_smul];change _ = B.repr v i * _ ;rw [hv];exact mul_comm ..
lemma reformed (g:G.El)(x:G.ColorIndex) : WithLp.toLp 2 (fun i=>G.adjoint g (EuclideanSpace.basisFun _ ℝ i) x)=
  G.adjoint g⁻¹ (EuclideanSpace.basisFun _ ℝ x):= by
  let B:=(EuclideanSpace.basisFun G.ColorIndex ℝ)
  ext y
  let a := G.adjoint g⁻¹ (B x); have ha : G.adjoint g a=B x:= (G.adjoint_mul g g⁻¹ _).symm.trans (by simp)
  change ((G.adjoint g (B y)) x)=_
  rw [← show inner ℝ (B x) (G.adjoint g (B y))=(G.adjoint g (B y)) x from EuclideanSpace.basisFun_inner ..]
  calc inner ℝ (B x) _= inner ℝ a (B y):= ha ▸ wick_inner ..
       _ = inner ℝ (B y) a:= real_inner_comm ..
       _ = a y:=EuclideanSpace.basisFun_inner ..

lemma color_delta (u:G.El)(i j:G.ColorIndex) : (∑ a:G.ColorIndex,(G.adjoint u (EuclideanSpace.basisFun _ ℝ a) i : ℂ)*(G.adjoint u (EuclideanSpace.basisFun _ ℝ a) j:ℂ))=(if i=j then 1 else 0):=by
   let B:= (EuclideanSpace.basisFun G.ColorIndex ℝ)
   let v: G.Color:=WithLp.toLp 2 (fun a=>G.adjoint u (EuclideanSpace.basisFun _ ℝ a) j)
   simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum]
   change (((∑ a:G.ColorIndex, G.adjoint u (EuclideanSpace.basisFun _ ℝ a) i*v a):ℝ):ℂ) = _
   simp only [reformation];change ↑(G.adjoint u v i:ℂ)=_; unfold v;rw [reformed (g:=u) j,← G.adjoint_mul,mul_inv_cancel,Gauge.adjoint_one]
   by_cases h:i=j
   · rw [if_pos h,h];simp
   rw [if_neg h];simp [EuclideanSpace.single_apply,h]

lemma dye_scope (u:G.El): scope (rag (α:=RG.Slot) u) (covarianceSymbol G)=covarianceSymbol G:= by
   ext1;funext i j; let Q:=covarianceSymbol G
   change treats _ _ _ = _
   unfold treats rag
   simp only [map_sum,map_smul,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_sum]
   simp [covarianceSymbol, mul_ite,← mul_assoc,← sum_mul];by_cases h:i.2=j.2
   · simp [h]; rw [show (∑ x : G.ColorIndex, ((G.adjoint u (EuclideanSpace.single x 1) j.2:ℝ):ℂ)*((G.adjoint u (EuclideanSpace.single x 1) j.2:ℝ):ℂ))=1 from by simpa using! color_delta u j.2 j.2,one_mul]
   simp [h]; exact Or.inl (by simpa [Ne.symm h] using! color_delta u j.2 i.2)

lemma colored_milk (u:G.El)(p:Poly RG.Slot G) : inked u (milk (covarianceSymbol G) p)= milk (covarianceSymbol G) (inked u p):=by
   have hh := prepared (rag (α:=RG.Slot) u) (covarianceSymbol G) p
   rw [dye_scope] at hh;exact hh.symm

lemma Fixed.heat {p:Poly RG.Slot G}(h:Fixed p): Fixed (milk (covarianceSymbol G) p) := by
   intro u x;rw [hue,colored_milk,h.actual u]

lemma Clear.heat {p:Poly RG.Slot G}(h:Clear p): Clear (milk (covarianceSymbol G) p) := by
   apply promote_clear; rw [← Spindle.flashed,h.actual]; intro i j; dsimp only [covarianceSymbol];split_ifs <;> simp

end YM.PertExtension.Hue
