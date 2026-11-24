import YM.Integration.WilsonIndependentCollarOpticalOrdinary
import YM.Integration.WilsonIndependentCollarCompletePrint

/-! Count every angular slot of a disjoint product with the original
tensor norm, before choosing a test or period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarSeedProduct
open Function Finset Lattice RG Wilson Precision Work.F08
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open scoped Classical BigOperators
variable {ι α V:Type} {D:ι→ℕ} {e R:ℕ} [NormedAddCommGroup V]

def Total (e R:ℕ) (P:Pal V (Cloth α)) (A:ℝ):Prop:=∀i≤e,∀r≤R,Fruit 0 0 0 (P i r) A

lemma invoice {i:ℕ} {X:Ten V (Cloth α) i} {A:ℝ} :
    Fruit 0 0 0 X A ↔ SumBudget (fun x=>‖X x‖) A:=by simp only [Fruit,Award,hedge,autumn,pow_zero,one_mul]

lemma branch [DecidableEq ι] {S J:Finset ι}(hj:J⊆S) {i j r:ℕ} (form:i+j=r)
    {P:Ten (Pen D J) (Cloth α) i} {Q:Ten (Pen D (S\J)) (Cloth α) j} {A B:ℝ}
    (p:Fruit 0 0 0 P A) (q:Fruit 0 0 0 Q B):Fruit 0 0 0 (cobT hj P Q r) (A*B):=by
  subst r;apply invoice.mpr
  let W:=weavePair (Cloth α) i j
  let z:=fun x=> ‖P (W x).1‖*‖Q (W x).2‖
  refine budget_minor (cap_walk z _ W.symm (fun _=>by dsimp [z];rw [W.apply_symm_apply])
      (prod_cap (invoice.mp p) (cap_nn (invoice.mp q)) (fun _=>invoice.mp q)))
    (fun _=>norm_nonneg _) ?_
  intro x;simp only [cobT,waveJoy]
  exact joy_norm .. 

/-- Product of the complete rooted input norm budgets before a scalar dual test. -/
lemma product [DecidableEq ι] {J S:Finset ι} (h:J⊆S)
    {P:Pal (Pen D J) (Cloth α)} {Q:Pal (Pen D (S\J)) (Cloth α)}
    {A B:ℝ} (ap:0≤A) (bp:0≤B) (p:Total e R P A) (q:Total e R Q B):
    Total e R (foam h P Q) ((((e:ℝ)+1)*((R:ℝ)+1))*(A*B)):=by
  intro i hi r hr
  change Fruit 0 0 0 ((∑ s∈Finset.HasAntidiagonal.antidiagonal i,cob h (P s.1) (Q s.2)) r) _
  rw [Finset.sum_apply]
  have pieces l (hl:l∈Finset.HasAntidiagonal.antidiagonal i):
      Fruit 0 0 0 (cob h (P l.1) (Q l.2) r) (((R:ℝ)+1)*(A*B)):=by
    have le:=Finset.HasAntidiagonal.mem_antidiagonal.mp hl
    have tile w (hw:w∈Finset.HasAntidiagonal.antidiagonal r):
        Fruit 0 0 0 (cobT h (P l.1 w.1) (Q l.2 w.2) r) (A*B):=by
      have paid:=Finset.HasAntidiagonal.mem_antidiagonal.mp hw
      exact branch h paid (p _ (by omega) _ (by omega)) (q _ (by omega) _ (by omega))
    apply ((Fruit.sum tile (by norm_num)).swirl (by norm_num)).more
    rw [Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hr) (mul_nonneg ap bp)
  apply (Fruit.sum pieces (by norm_num)).more
  rw [Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by positivity);exact_mod_cast Nat.succ_le_succ hi

end YM.Integration.WilsonIndependentCollarSeedProduct
end
