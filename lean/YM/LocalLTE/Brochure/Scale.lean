import YM.LocalLTE.Concert.Fuse
/-! # Dual evacuation of inherited bill. Rebudgeting a given authorization. Exact scaled power preserved on *same* supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay Fan
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B A C:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Push.AbsoluteSums
variable {a b d l x y z:ℝ} (m:ℕ) (hs:Fintype.card V ≤ m)
omit [Fintype V] in
lemma centralBank (h:B.Radial r a b d l)(s:V→ℝ)(hz:∀ i,0<s i)(hK:0 ≤ κ)(hy:κ ≤ 1)(hu:∀ i,s i ≤ κ*r i): B.Radial s (κ*a) (κ*b) (κ*d) l:=by
   have hh:0≤κ:=hK; let S:= κ; have hv:0≤ S:=hh
   have he(i:R.Mode)(j:V)(hn:j∈i.val): Poly.toll s i ≤ S*Poly.toll r i:=by
      refine (prod_le_prod (fun j _=> (hz j).le) (fun j _=> hu j)).trans ?_; rw [prod_mul_distrib,prod_const]; exact mul_le_mul_of_nonneg_right ((pow_le_pow_of_le_one hK hy (Nat.one_le_iff_ne_zero.2 (by exact Nat.ne_of_gt (card_pos.2 ⟨j,hn⟩)))).trans (by rw [pow_one])) (Poly.worth h.pure _).le
   obtain ⟨hR,h0,hL,⟨p,hp,hP⟩,s',hE,hQ⟩:=h
   refine ⟨hz,fun i=> ?_,hL,⟨p,hp,fun i=>?_⟩,s',hE,fun i=>?_⟩
   · apply le_trans (mul_le_mul_of_nonneg_right (hu i) (norm_nonneg _)) _; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h0 i) hh
   · refine budget_mono (budget_scale hv (hP i)) (fun i=> ?_) (fun j=>?_)
     · split; exact mul_nonneg (Poly.worth hz _).le (mul_nonneg (Real.exp_nonneg _) (hp i|>.1)); rfl
     split; next h=>rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (he _ _ h) (mul_nonneg (Real.exp_nonneg _) (hp j|>.1))
     rw [mul_zero]
   rw [mul_assoc]; refine budget_mono (budget_scale hv (hQ i)) (fun j=> ?_) (fun j=>?_)
   · split; exact mul_nonneg (Poly.worth hz _).le (mul_nonneg (Real.exp_nonneg _) (hE j.1 j.2|>.1)); rfl
   split; next h=>rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (he _ _ h) (mul_nonneg (Real.exp_nonneg _) (hE j.1 j.2|>.1))
   rw [mul_zero]
end YM.LocalLTE.Port
