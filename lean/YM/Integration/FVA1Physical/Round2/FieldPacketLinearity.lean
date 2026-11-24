import YM.Integration.FVA1Physical.Round2.FormalFieldTruncation

/-! The independent normalized Wilson step is linear in one marked packet,
including coupling-dependent weighted sums. Its vacuum and its covariance
remain those of the original step. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Matrix MvPolynomial Lattice MSbar MSbar.Cacao MSbar.Duel MSbar.Rolling MSbar.Mosaic
open MSbar.Bakery MSbar.Bakery.Film MSbar.Kelvin Push.Uniform YM.Integration.FVA1Physical.Wilson
open RG YM.Wilson
open scoped Classical BigOperators
variable {σ : Type} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
private theorem wick_eval (P : Pot σ) (y : WickSlot σ → ℝ) :
    eval y (wickStencil P) = eval (fun i=>y (.inl i)) (bowl (fun i j=>y (.inr (i,j))) P) := by
  have h : parameters (fun i=>y (.inl i)) (fun i j=>y (.inr (i,j)))=y := by
    funext i;cases i <;> rfl
  exact h ▸ wickStencil_eval (fun i=>y (.inl i)) (fun i j=>y (.inr (i,j))) P

def wickPacketLinear : Pot σ →ₗ[ℝ] Pot (WickSlot σ) where
  toFun:=wickStencil
  map_add' P Q:=by
    apply MvPolynomial.funext;intro y
    let K:=fun i j:σ=>y (.inr (i,j))
    obtain ⟨T,hT⟩:=branc K
    simp only [_root_.map_add,wick_eval]
    change eval _ (bowl K (P+Q))=eval _ (bowl K P)+eval _ (bowl K Q)
    simp only [←hT,_root_.map_add]
  map_smul' a P:=by
    apply MvPolynomial.funext;intro y
    let K:=fun i j:σ=>y (.inr (i,j))
    obtain ⟨T,hT⟩:=branc K
    simp only [RingHom.id_apply,eval_real_smul,wick_eval]
    change eval _ (bowl K (a • P))=a*eval _ (bowl K P)
    rw [←hT,_root_.map_smul,eval_real_smul,hT]

theorem tilted_packet_sum {ι : Type} (I : Finset ι) (Q : PowerSeries (Pot σ))
    (F : ι→PowerSeries (Pot σ)) (w : ι→ℝ) :
    tiltedStencil Q (∑ i∈I,w i • F i)=∑ i∈I,w i • tiltedStencil Q (F i) := by
  let W:=pulled (wickPacketLinear (σ:=σ))
  have natural (U : PowerSeries (Pot σ)) : wickSeries U=W U := rfl
  simp only [tiltedStencil,Finset.sum_mul,smul_mul_assoc,natural,_root_.map_sum,_root_.map_smul]

theorem grown_packet_sum {τ ι : Type} [Fintype τ] [DecidableEq τ] (A : Matrix σ τ ℝ)
    {D : Matrix τ τ ℝ} (pd : D.PosDef) (Q : PowerSeries (Pot σ)) (kind : Kind Q)
    (p i : ℕ) (hi : i≤p) (I : Finset ι) (F : ι→PowerSeries (Pot σ)) (w : ι→ℝ) :
    PowerSeries.coeff i (growP Q (∑ t∈I,w t • F t) (A*D*A.transpose) (p+1)) =
      ∑ t∈I,w t • PowerSeries.coeff i (growP Q (F t) (A*D*A.transpose) (p+1)) := by
  apply MvPolynomial.funext;intro x
  have price:=fun U=>tiltedStencil_eq_grow A x pd Q U kind (p+1) i (by omega)
  rw [←price,tilted_packet_sum]
  simp only [_root_.map_sum,PowerSeries.coeff_smul,eval_real_smul,price]

end YM.Integration.FVA1Physical.Round2.Curvature
