import YM.Integration.WilsonEmittedWordFootprint
import YM.Integration.WilsonEmittedProtectedReturn

/-! The authentic armada pays the long group-field words twice in their
respective currencies. The curved regular price is its native tally.
The full-group ticket uses the actual bounded Wilson word and the entire
finite Laurent pole, with no healthy smallness charged to failed fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedGroupWallet
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push.AbsoluteSums Push.Local WilsonEmittedCutGrouping
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (M : ι → Row P Γ G X)
variable (w : V → ℝ) (grades : V → ℕ) {σ b g K θ : ℝ} {p pieces depth : ℕ}
variable (old : Armada M w grades σ b p pieces depth) (B : BudgetPoint)
variable (scope : Invoice.Supports B K (B.supportExponent+2) g σ θ)
local notation "α" => (B.supportExponent+2)

def ceiling (g : ℝ) (p d : ℕ) : ℝ := (g^(d+1))⁻¹*2^(p+d+1)

include old scope in
theorem full (i : ι) (x : X) (U : Config G n) :
    ‖(M i).nominal g x U‖ ≤ ceiling g p depth * (M i).salary := by
  let T:=M i
  obtain ⟨_,wage,rk⟩ := Armada.degreeR grades old.toMinistry (M i) (old.purchases.usable i)
  have grows : -(↑(depth+1):ℤ) ≤ T.lamp.lag := by
    have lr := T.lamp.crest
    unfold Sunrise.Loan.lag
    dsimp [T] at *; omega
  have lag : |g^T.lamp.lag| ≤ (g^(depth+1))⁻¹ := by
    rw [abs_of_pos (zpow_pos scope.1 _)]
    simpa only [zpow_neg,zpow_natCast] using zpow_le_zpow_right_of_le_one₀ scope.1 scope.2.1 grows
  have mag : T.atom.magnitude ≤ 1 :=
    (le_mul_of_one_le_right (Invoice.p_bound _ T.atom) (Real.one_le_exp
      (mul_nonneg scope.2.2.2.2.1 (Nat.cast_nonneg _)))).trans (old.purchases.spend i)
  have atom : |T.atom.unmasked U T.center|≤(2:ℝ)^(p+depth+1) := by
    apply (T.atom.unmasked_bound U T.center).trans
    apply (mul_le_mul_of_nonneg_right mag (by positivity)).trans
    simpa only [one_mul] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) rk
  change ‖T.nominal g x U‖ ≤ _
  simp only [Row.nominal,Row.grain,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact (mul_le_mul (old.honor i x) (mul_le_mul lag atom (abs_nonneg _) (inv_nonneg.mpr (pow_nonneg scope.1.le _)))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) T.sound.le).trans_eq (mul_comm ..)

def stock (B : BudgetPoint) (d t m : ℕ) (b θ : ℝ) :=
  Footprint.payment 1 (B.B+2) 0 θ 1 b (B.supportExponent+2) (Invoice.tax d t)*Real.exp (-θ)^m

private def pay (M : ι → Row P Γ G X) (w : V → ℝ) (B : BudgetPoint)
    (rent : ι → ℝ) (m : ℕ) (o : Site n) (i : ι) :=
  if m ≤ (M i).length then (if o∈(M i).ground B then
    (Poly.toll w (M i).mode * rent i) * Real.exp ((B.supportExponent+2)*coverNumber B.B ((M i).ground B))
    else 0) else 0

include old scope in
private theorem salaries (m : ℕ) (o : Site n) :
    SumBudget (pay M w B (fun i=>(M i).salary) m o) (stock B (p+depth+1) pieces m b θ) := by
  let s := p+depth+1
  let φ i := Poly.toll w (M i).mode * (M i).salary
  let l i := (M i).length
  let z i := (M i).center
  let Xs i := (M i).ground B
  have hφ i : 0 ≤ φ i := mul_nonneg (Poly.worth old.positive _).le (M i).sound.le
  have hz : Footprint.Anchored z φ l σ b := by
    intro x
    convert old.suggests x using 1
    ext i
    unfold φ
    split
    · unfold Row.height l; ring
    · rfl
  apply Footprint.assigned_tail (id : Site n → Site n) 1 (fun i=>by simp) z φ hφ l Xs hz (B.B+2)
    0 B.B (v:=Invoice.tax s pieces) _ _ zero_le_one scope.2.2.2.2.2 φ hφ (fun _=>by simp) m o
  · intro i y hy
    rw [id_eq,separation_comm]
    exact ((M i).near B.B y hy).trans (by unfold Row.radius l; nlinarith)
  · intro i
    have hb : 0 < (B.B:ℝ) := Nat.cast_pos.mpr B.B_pos
    have rank := (Armada.degreeR grades old.toMinistry (M i) (old.purchases.usable i)).2.2
    have tiles : B.B*coverNumber B.B (Xs i) ≤ (1000+s+pieces)*B.B + l i :=
      ((M i).tiles B.B B.B_pos).trans (by unfold s; gcongr; apply old.quota)
    unfold Invoice.tax
    field_simp
    rw [Nat.mul_comm B.B] at tiles
    exact_mod_cast tiles

include old in
private theorem inward (m : ℕ) (s : Γ.Mode) (v : V) (hv : v∈s.val) (rent : ι→ℝ) {E : ℝ}
    (source : SumBudget (pay M w B rent m (P.origin v)) E) :
    SumBudget (fun j : {i // late M s m i} => reservedMass B ((M j.val).ground B) (rent j.val))
      ((Poly.toll w s)⁻¹*E) := by
  have scaled := budget_scale (inv_nonneg.mpr (Poly.worth old.positive s).le) source
  let f := fun i => (Poly.toll w s)⁻¹ * pay M w B rent m (P.origin v) i
  let J := {i // late M s m i}
  have h : SumBudget (f ∘ (Subtype.val : J→ι)) ((Poly.toll w s)⁻¹*E) :=
    ⟨fun j=>scaled.1 j.val,scaled.2.1.comp_injective Subtype.val_injective,
      (tsum_comp_le_tsum_of_inj scaled.2.1 scaled.1 Subtype.val_injective).trans scaled.2.2⟩
  convert h using 1
  ext j
  have mode : s=(M j.val).mode := j.property.1
  have home := (M j.val).heard B.B v (mode ▸ hv) (P.born v)
  simp only [comp_apply,f,pay,if_pos j.property.2,if_pos home,←mode,reservedMass]
  field_simp [(Poly.worth old.positive s).ne']

include old scope in
theorem regular (m : ℕ) (s : Γ.Mode) (v : V) (hv : v∈s.val) :
    SumBudget (fun j : {i // late M s m i} =>
      reservedMass B ((M j.val).ground B) ((M j.val).charge B g))
      ((Poly.toll w s)⁻¹*(Invoice.price B K (p+depth+1) pieces α θ G*b*Real.exp (-θ)^m)) := by
  apply inward M w grades old B m s v hv (fun i=>(M i).charge B g)
  exact Armada.tally M w grades old B scope m (P.origin v)

include old scope in
theorem rough (m : ℕ) (s : Γ.Mode) (v : V) (hv : v∈s.val) :
    SumBudget (fun j : {i // late M s m i} =>
      reservedMass B ((M j.val).ground B) (ceiling g p depth * (M j.val).salary))
      (ceiling g p depth*((Poly.toll w s)⁻¹*stock B (p+depth+1) pieces m b θ)) := by
  have nn : 0 ≤ ceiling g p depth := by unfold ceiling; positivity [scope.1]
  have fee := budget_scale nn (inward M w grades old B m s v hv (fun i=>(M i).salary)
    (salaries M w grades old B scope m (P.origin v)))
  convert fee using 1
  ext i
  unfold reservedMass
  ring

end YM.Integration.WilsonEmittedGroupWallet
