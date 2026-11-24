import YM.Integration.WilsonMacroscopicRichCroppedProbe
import YM.Trace.Physicalv2.Germ

/-! The genuine rooted spatial price when a fitted nonlinear probe is removed outside a finite ball. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichProbeShell
open Function Filter Lattice Wilson Source RG Labels Next.Foundations
open WilsonMacroscopicRichCroppedProbe Push.Local
open scoped Topology Classical ContDiff BigOperators
variable {G:Gauge} {n:Side}

def bonds (B:BudgetPoint) (o:Site n) (L:ℕ) : Finset (Edge (Site n)) :=
  Finset.univ.filter fun e=>separation e.1 o ≤ L*(4*B.B+2)+2*B.B

lemma covers (B:BudgetPoint) (o:Site n) (L:ℕ) (X:Support n) (root:o∈X)
    (small:coverNumber B.B X≤L) (e:Edge (Site n)) (fromRoot:e.1∈X) : e∈bonds B o L := by
  apply Finset.mem_filter.mpr;refine ⟨Finset.mem_univ _,?_⟩
  exact (Corona.extent X B.B fromRoot root).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ small) _)

lemma tail (B:BudgetPoint) (X:Support n) {L:ℕ} (long : L≤coverNumber B.B X) {a:ℝ} (ap:0≤a) :
    a ≤ Real.exp (-(B.supportExponent*L))*B.mass X a := by
  unfold BudgetPoint.mass
  rw [←mul_assoc,←Real.exp_add]
  apply le_mul_of_one_le_left ap (Real.one_le_exp ?_)
  have hn : (L:ℝ)≤coverNumber B.B X := by exact_mod_cast long
  linarith only [mul_le_mul_of_nonneg_left hn B.exponent_pos.le]

/-- A single price before the finite torus, root and cut radius. The norm here is the difference of the two genuine nonlinear jets of the same original source. -/
theorem charged (H:Hol G) (J:Jet G) (d k:ℕ) (hk:k≤d) : ∃ C:ℝ,0≤C ∧
    ∀ (n:Side) (o:Site n) (B:BudgetPoint) (X:Support n) (_:o∈X) (f:Config G n→ℂ) (a:ℝ) (L:ℕ) (A:Finset (Edge (Site n))) (_:bonds B o L⊆A),
    d≤B.order → d≤B.power → B.Regular X f → B.supBounds o X f a →
    ‖iteratedDeriv k (f ∘ H.testLinks d o (B.threshold•J)) 0 -
        iteratedDeriv k (f ∘ fields A H d o (B.threshold•J)) 0‖ ≤
      (C*Real.exp (-(B.supportExponent*L)))*B.mass X a := by
  obtain ⟨c,cp,full⟩ := test_bound H J d k hk
  obtain ⟨v,vp,clipped⟩ := WilsonMacroscopicRichCroppedProbe.price H J d k hk
  refine ⟨c+v,add_nonneg cp vp,?_⟩
  intro n o B X root f a L A sub ho hp hreg due
  by_cases small : coverNumber B.B X≤L
  · rw [(agree hreg.sites A (fun e h _=>sub (covers B o L X root small e h)) H d o (B.threshold•J)).iteratedDeriv_eq,sub_self,norm_zero]
    exact mul_nonneg (mul_nonneg (add_nonneg cp vp) (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le due.1)
  · calc
      _ ≤ c*a+v*a := (norm_sub_le _ _).trans (add_le_add (full n o X B f a ho hp hreg due) (clipped n o X B f a A ho hp hreg due))
      _ = (c+v)*a := (add_mul _ _ _).symm
      _ ≤ (c+v)*(Real.exp (-(B.supportExponent*L))*B.mass X a) := mul_le_mul_of_nonneg_left (tail B X (by omega) due.1) (add_nonneg cp vp)
      _ = _ := (mul_assoc ..).symm

/-- The entire genuine regular part of the registered rooted coefficient, with its original reservation. -/
theorem series (H:Hol G) (J:Jet G) (d k:ℕ) (hk:k≤d) : ∃ C:ℝ,0≤C ∧
    ∀ (F:Labels.Frame G d) (n:Side) (o:Site n) (R:Rep G n) (q:Coefficient F n) {κ z:ℝ} (L:ℕ) (A:Finset (Edge (Site n))) (_:bonds R.p o L⊆A),
    d≤R.p.order → d≤R.p.power → q.Format o H R → q.remBound o R κ z →
      let δ := fun i:ℕ=>iteratedDeriv k (q.regular i ∘ H.testLinks d o (R.p.threshold•J)) 0 -
          iteratedDeriv k (q.regular i ∘ fields A H d o (R.p.threshold•J)) 0
      Summable (fun i=>‖δ i‖) ∧ ‖∑' i,δ i‖ ≤ C*Real.exp (-(R.p.supportExponent*L))*z := by
  obtain ⟨C,Cp,paid⟩ := charged H J d k hk
  refine ⟨C,Cp,?_⟩
  intro F n o R q κ z L A sub ho hp formed funds δ
  obtain ⟨a,b,ap,bp,w,_,⟨e,budget,each⟩,_⟩ := funds
  let K:=C*Real.exp (-(R.p.supportExponent*L))
  have kp : 0≤K := mul_nonneg Cp (Real.exp_pos _).le
  have price : SumBudget (fun i=>‖δ i‖) (K*z) :=
    sumBudget_mono (sumBudget_mul_left budget kp) (fun i=>norm_nonneg _) (fun i=>paid n o R.p (q.support i) (formed.origin i) (q.regular i) (e i) L A sub ho hp (formed.smooth i) (each i))
      (mul_le_mul_of_nonneg_left (by linarith only [w,bp]) kp)
  exact ⟨price.2.1,(norm_tsum_le_tsum_norm price.2.1).trans price.2.2⟩

end YM.Integration.WilsonMacroscopicRichProbeShell
