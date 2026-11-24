import YM.Integration.WilsonIndependentCollarOrdinaryWeak

/-! The finite squarefree logarithm on unsummed angular kernels.  All
constants here precede the spatial scale, its period and its child itinerary. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOrdinaryAlgebra
open Function Finset Lattice RG Wilson Precision
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open scoped BigOperators Classical
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D:ι→ℕ}
variable {e R:ℕ} {U V:Type} [NormedAddCommGroup V]

def Capped (e R:ℕ) (P:Pal V U) (A:ℝ):Prop:= ∀ q≤e,∀r≤R,∀ x,‖P q r x‖≤A

private lemma rotate [NormedSpace ℝ V] {r:ℕ} {P:Ten V U r} {A:ℝ} (bound:∀x,‖P x‖≤A) (x):
    ‖swirl P x‖≤A:=by
  let c:ℝ:=Fintype.card (Equiv.Perm (Fin r))
  have pos:0<c:=by dsimp [c];positivity
  change ‖c⁻¹ • ((∑ θ:Equiv.Perm (Fin r),fun y=>P (y∘θ)) x)‖≤_
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr pos.le),Finset.sum_apply]
  calc
    _ ≤ c⁻¹*∑ _θ:Equiv.Perm (Fin r),A:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le ..).trans (Finset.sum_le_sum fun θ _=> bound (x∘θ))
    _ = A:=by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];exact inv_mul_cancel_left₀ pos.ne' A

omit [Fintype ι] in
/-- Exact disjoint profile product, retaining every rank and coupling split. -/
lemma product {J S:Finset ι} (h:J⊆S) {P:Pal (Pen D J) U} {Q:Pal (Pen D (S\J)) U}
    {A B:ℝ} (ap:0≤A) (bp:0≤B) (p:Capped e R P A) (q:Capped e R Q B):
    Capped e R (foam h P Q) ((((e:ℝ)+1)*((R:ℝ)+1))*(A*B)):=by
  intro i hi r hr x
  simp only [foam,Finset.sum_apply]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _j∈Finset.HasAntidiagonal.antidiagonal i,((R:ℝ)+1)*(A*B):=by
      apply Finset.sum_le_sum; intro j hj
      have je:=Finset.HasAntidiagonal.mem_antidiagonal.mp hj
      apply rotate; intro z; rw [Finset.sum_apply]; apply (norm_sum_le ..).trans
      calc
        _ ≤ ∑ _l∈Finset.HasAntidiagonal.antidiagonal r,A*B:=by
          apply Finset.sum_le_sum; intro l hl
          have eq:=Finset.HasAntidiagonal.mem_antidiagonal.mp hl
          simp only [cobT,dif_pos eq,waveJoy]
          exact (joy_norm ..).trans (mul_le_mul (p _ (by omega) _ (by omega) _) (q _ (by omega) _ (by omega) _)
            (norm_nonneg _) ap)
        _ ≤ ((R:ℝ)+1)*(A*B):=by
          rw [Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg ap bp);exact_mod_cast Nat.succ_le_succ hr
    _ ≤ ((((e:ℝ)+1)*((R:ℝ)+1))*(A*B)):=by
      rw [Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul,mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by positivity);exact_mod_cast Nat.succ_le_succ hi

/-- Finite, numerical coefficient of the ordinary-to-connected conversion. -/
def cost (e R:ℕ) (S:Finset ι):ℝ:=
  1+‖(S.card:ℝ)⁻¹‖*∑ j∈S.powerset, if h:j⊆S∧j≠S then
    (j.card:ℝ)*(((e:ℝ)+1)*((R:ℝ)+1))*cost e R j else 0
termination_by S.card
decreasing_by exact Finset.card_lt_card (lt_of_le_of_ne h.1 h.2)

omit [Fintype ι] in
lemma funded (e R:ℕ) (S:Finset ι):1≤cost e R S:=by
  induction S using Finset.strongInduction with
  | H S ih=>
    rw [cost];apply le_add_of_nonneg_right
    apply mul_nonneg (norm_nonneg _) (Finset.sum_nonneg _)
    intro j _;split
    next h=>have :=ih j (lt_of_le_of_ne h.1 h.2); positivity
    next=>exact le_rfl

omit [Fintype ι] in
theorem original (M:family G D) (cap:ℝ) (hp:0≤cap)
    (board:∀S:Finset ι,S.Nonempty → Capped e R (M S).2 (cap^S.card)) (S:Finset ι):
    Capped e R (reverseO M S).2 (cost e R S*cap^S.card):=by
  induction S using Finset.strongInduction with
  | H S ih=>
    rw [reverseO];split
    next h=>intro q _ r _ x;change ‖(0:Pen D S)‖≤_;rw[norm_zero];exact mul_nonneg (zero_le_one.trans (funded ..)) (by positivity)
    next occupied=>
      intro q hq r hr x
      let P (j:Finset ι):=if h:j⊆S∧j≠S then (j.card:ℝ) • waxV h.1 (reverseO M j) (M (S\j)) else 0
      let bill (j:Finset ι):ℝ:=if _h:j⊆S∧j≠S then (j.card:ℝ)*(((e:ℝ)+1)*((R:ℝ)+1))*cost e R j else 0
      have paid (j:Finset ι):‖(P j).2 q r x‖≤bill j*cap^S.card:=by
        dsimp only [P,bill];split
        next h=>
          have sibling:=ih j (lt_of_le_of_ne h.1 h.2)
          have hj:0≤cost e R j:=zero_le_one.trans (funded ..)
          have live:(S\j).Nonempty:=Finset.sdiff_nonempty.mpr (fun u=>h.2 (Finset.Subset.antisymm h.1 u))
          have hh:=product h.1 (mul_nonneg hj (pow_nonneg hp _)) (pow_nonneg hp _) sibling (board (S\j) live)
            q hq r hr x
          have cards:j.card+(S\j).card=S.card:=by rw [Finset.card_sdiff_of_subset h.1];have :=Finset.card_le_card h.1;omega
          change ‖(j.card:ℝ) • (foam h.1 (reverseO M j).2 (M (S\j)).2 q r x)‖≤_
          rw [norm_smul,Real.norm_of_nonneg (by positivity)]
          apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq
          rw [←cards,pow_add];ring
        next _=>change ‖(0:Pen D S)‖≤_;simp
      change ‖(M S).2 q r x-(S.card:ℝ)⁻¹ • ((∑ j∈S.powerset,P j).2 q r x)‖≤_
      apply (norm_sub_le ..).trans
      rw [norm_smul]
      have gross:‖(∑ j∈S.powerset,P j).2 q r x‖≤(∑j∈S.powerset,bill j)*cap^S.card:=by
        simp only [Prod.snd_sum,Finset.sum_apply,Finset.sum_mul]
        exact (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>paid j)
      apply (add_le_add (board S (Finset.nonempty_iff_ne_empty.mpr occupied) q hq r hr x)
        (mul_le_mul_of_nonneg_left gross (norm_nonneg _))).trans_eq
      rw [cost];dsimp only [bill];ring

end YM.Integration.WilsonIndependentCollarOrdinaryAlgebra
end
