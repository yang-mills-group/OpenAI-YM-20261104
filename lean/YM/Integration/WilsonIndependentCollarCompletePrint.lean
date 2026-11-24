import YM.Integration.WilsonIndependentCollarQuietIncome

/-! Rooted total variation of every angular coefficient of the complete
independent one-date reset on both the true finite board and its cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCompletePrint
open Finset Function Lattice Laurent Bloch Metric Precision RG Work.F08 Wilson FormalBulk08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open scoped Classical BigOperators
variable {ι U α E : Type} {S:Finset ι} {a:ι} [NormedAddCommGroup E]
variable {n:Side} {r:ℕ} {s t A:ℝ}

def printed (d:Distance U) (p:ι→U) (S:Finset ι) (t:ℝ) {r:ℕ} (F:Ten E (U×α) r)
    (x:dock U α r) := Real.exp (t*Syn d p S x)*‖F x‖

theorem bound {d:Distance U} {p:ι→U} {F:Ten E (U×α) r} (h:Wig d p s A S F)
    (ha:a∈S) (gap:t<s) (pos:0≤t) (x:dock U α r) :
    printed d p S t F x ≤ A*sail ((s-t)/r) d (p a) x := by
  let l:=Syn d p S x
  have pay:Real.exp (-s*l) ≤ Real.exp (-t*l)*sail ((s-t)/r) d (p a) x := by
    cases r with
    | zero =>
      simp only [sail,Finset.univ_eq_empty,prod_empty,mul_one]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg gap.le) (Nat.cast_nonneg _)
    | succ r =>
      apply sail_cut (Nat.le_refl l) pos gap (Nat.zero_lt_succ _) (p a) x
      exact fun j=>leg_le d (foyer p S x) (.inl ⟨a,ha⟩) (.inr j)
  calc
    _ ≤ Real.exp (t*l)*(A*Real.exp (-s*l)) := mul_le_mul_of_nonneg_left (h.2 x) (Real.exp_pos _).le
    _ ≤ Real.exp (t*l)*(A*(Real.exp (-t*l)*sail ((s-t)/r) d (p a) x)) := by gcongr;exact h.1
    _ = _ := by rw [neg_mul,Real.exp_neg];field_simp

theorem finite [Fintype α] {p:ι→Site n} {F:Ten E (Co n α) r} (h:Wig (tor n) p s A S F)
    (ha:a∈S) (gap:t<s) (pos:0≤t) :
    ∑ x,printed (tor n) p S t F x ≤ A*tiePay α r (s-t) := by
  apply (sum_le_sum fun x _=>bound h ha gap pos x).trans
  rw [←mul_sum]
  apply mul_le_mul_of_nonneg_left _ h.1
  cases r with
  | zero => simp [tiePay,sail]
  | succ r => exact train_native (div_pos (sub_pos.mpr gap) (by positivity)) (p a) (r+1)

theorem cover [Fintype α] {p:ι→ Cover} {F:Ten E (Cloth α) r} (h:Wig terrain p s A S F)
    (ha:a∈S) (gap:t<s) (pos:0≤t) :
    SumBudget (printed terrain p S t F) (A*tiePay α r (s-t)) := by
  have nb (x:dock Cover α r) : 0≤printed terrain p S t F x :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have price:SumBudget (fun x:dock Cover α r=>sail ((s-t)/r) terrain (p a) x) (tiePay α r (s-t)) := by
    cases r with
    | zero => simpa [SumBudget,sail,tiePay] using (show Summable (fun _:dock Cover α 0=>(1:ℝ)) from Summable.of_finite)
    | succ r => exact train_pay (div_pos (sub_pos.mpr gap) (by positivity)) (p a) (r+1)
  have old:=price.2.1.mul_left A
  have hs:=Summable.of_nonneg_of_le nb (bound h ha gap pos) old
  refine ⟨nb,hs,(hs.tsum_le_tsum (bound h ha gap pos) old).trans ?_⟩
  simpa only [tsum_mul_left] using mul_le_mul_of_nonneg_left price.2.2 h.1

variable {G:Gauge} {D k:ι→ℕ} [DecidableEq ι]
theorem original (e q r:ℕ) (depth:q≤e) (S Z:Finset ι) (sub:S⊆Z) (front:a∈S) :
    ∃d:ℕ,∀I:Arch G,∃s A:ℝ,0<s ∧ 0≤A ∧ ∀(p:PackOne Z D k e I)(B:Cost),
    let F:=mist p.V.wheel p.V.shadow p.V.H (p.V.T p.V.n) I.R p.V.W' p.K B k S q r
    let K:=Blue.mix B (p.cabinJ S) q r
    let earn:=A*p.V.coin^d*p.A^S.card*rimJ B q r
    MarkU p.w S F K s earn ∧
      (∑ x,printed (tor p.V.n) (wrap p.V.n ∘ p.w) S (s/2) F x ≤
        earn*tiePay (Hooks G) r (s-s/2)) ∧
      SumBudget (printed terrain p.w S (s/2) K) (earn*tiePay (Hooks G) r (s-s/2)) := by
  obtain ⟨d,H⟩:=qLocal_mark (G:=G) (k:=k) (D:=D) e q r depth S Z sub
  refine ⟨d,fun I=>?_⟩
  obtain ⟨A,s,an,hp,both⟩:=H I
  refine ⟨s,A,hp,an,fun p B=>?_⟩
  have h:=both p B
  exact ⟨h,finite h.bill front (by linarith) (by linarith),cover h.access front (by linarith) (by linarith)⟩

end YM.Integration.WilsonIndependentCollarCompletePrint
