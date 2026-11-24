import YM.Extra.FREE_DETECTOR_ALGEBRA.Dialog

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F M : Type*} [NormedAddCommGroup F] [NormedAddCommGroup M] {j : ℕ}

lemma dye_dot [InnerProductSpace ℝ F] [InnerProductSpace ℝ M] (L : F→L[ℝ] M) (h : ∀ x y,⟪L x,L y⟫=⟪x,y⟫) (p q : TwoJet F j) :
    dotF (dye L p) (dye L q)=dotF p q := by
  simp_rw [dotF_eval,dotDir_eval]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro i _
  exact h (p a b (dir i)) (q a b (dir i))

variable {G : Gauge}

theorem conjG_inner (u : G.El) (x y : G.Color) : ⟪conjG u x,conjG u y⟫=⟪x,y⟫ := by
  let f : G.Color →ₗᵢ[ℝ] G.Color := ⟨G.adjoint u, G.norm_adjoint u⟩
  exact f.inner_map_map ..

theorem adjointSol (u v : G.El) (p : Sol G.Color j) : actionG (u*v) j p=actionG u j (actionG v j p) := by
  apply Subtype.ext; ext1 i; ext1 m; ext1 w; exact G.adjoint_mul u v (p.val i m w)

theorem move_projection (u : G.El) (A : TwoJet G.Color j) : actionG u j (asSol A) = asSol (dye (conjG u) A) := by
  apply (dualSol G.Color j).injective; ext q
  have ht : q = actionG u j (actionG u⁻¹ j q) := by rw [← adjointSol,mul_inv_cancel,oneSol]
  rw [ht,asSol_duality,dualSol_val]
  let V := actionG u⁻¹ j q
  change dotF (dye (conjG u) (asSol A).val) (dye (conjG u) V.val) = dotF (dye (conjG u) A) (dye (conjG u) V.val)
  rw [dye_dot _ (conjG_inner _),dye_dot _ (conjG_inner _)]
  exact asSol_duality A V

theorem curl_color (u : G.El) (p : Taylor G j) : takeCurl (Taylor.paint u p)=dye (conjG u) (takeCurl p) := by
  ext1 i; ext1 m; ext1 x
  change ((j+1:ℕ):ℝ) • (conjG u _ - conjG u _) = conjG u (((j+1:ℕ):ℝ) • (_-_))
  rw [_root_.map_smul,_root_.map_sub]; rfl

theorem radial_color (u : G.El) (P : Sol G.Color j) : gaugeJet (G:=G) (actionG u j P) = Taylor.paint u (gaugeJet P) := by
  apply potential.injective
  apply Subtype.ext; change takeCurl _ = takeCurl _
  rw [curl_color,match_leg,match_leg]; rfl

theorem send_color (u : G.El) (p : Taylor G j) : sendTo G j (Taylor.paint u p)=actionG u j (sendTo G j p) := by
  change asSol (takeCurl _) = _; rw [curl_color,← move_projection]; rfl

end YM.Extra.FD
