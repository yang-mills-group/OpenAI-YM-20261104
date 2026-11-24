import YM.Integration.WilsonReceivedCanonicalVerseRegister

/-! Total variation of the finite, complex, regulator-dependent portfolio on every
actual occupied face, including the empty product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalVersePortfolio
open Finset Lattice Wilson RG Labels Source WilsonThermometerDeclaredSeeds PhysicalNext.Repeat.Legato
open WilsonReceivedCanonicalVerseBasis (dose restored)
open WilsonReceivedCanonicalVerseRegister (shoulder)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I](R:Run G)(k:I→ℕ)

abbrev Selection (S:Finset I):Type:=(j:S)→Choice R k j
def weight (N p b:ℕ)(v:(j:I)→R.family.label (k j))(S:Finset I)(q:Selection R k S):ℂ:=
  ∏j:S,dose R k N p b v j (q j)

def wallet (M:I→ℝ)(S:Finset I):ℝ:=∏j:S,(∑c:Choice R k j,shoulder R k j c)*M j

omit [DecidableEq I] in
theorem nonneg (j:I)(c:Choice R k j):0 ≤ shoulder R k j c:=by
  cases c with
  | inl => exact zero_le_one
  | inr s =>
    unfold shoulder WilsonOriginalStarLaurentWallet.wallet
    exact sum_nonneg fun i _=>by split <;> positivity

theorem priced (N p b:ℕ)(live:b≤N)(v:(j:I)→R.family.label (k j))(S:Finset I)(M:I→ℝ)
    (cash:∀j∈S,(R.family.labels.level (k j)).coeffSize (v j)≤ M j):
    (∑q:Selection R k S,‖weight R k N p b v S q‖)≤wallet R k M S:=by
  simp only [weight,norm_prod]
  rw [←Fintype.prod_sum (fun (i:S) (c:Choice R k i)=>‖dose R k N p b v i c‖)]
  apply prod_le_prod (fun i _=>sum_nonneg fun _ _=>norm_nonneg _)
  intro j _
  rw [sum_mul]
  apply sum_le_sum
  intro c _
  exact (WilsonReceivedCanonicalVerseRegister.measured R k N p b live v j c).trans
    (mul_le_mul_of_nonneg_left (cash j j.prop) (nonneg R k j c))

theorem signed (N p b:ℕ)(live:b≤N)(v:(j:I)→R.family.label (k j))(S:Finset I)(M:I→ℝ)
    (cash:∀j∈S,(R.family.labels.level (k j)).coeffSize (v j)≤ M j)
    (physical independent:Selection R k S→ℂ){ε:ℝ}(hε:0≤ε)(each:∀q,‖physical q-independent q‖≤ε):
    ‖(∑q,weight R k N p b v S q*physical q)-(∑q,weight R k N p b v S q*independent q)‖≤wallet R k M S*ε:=by
  rw [←sum_sub_distrib]
  simp only [←mul_sub]
  calc
    _≤∑q:Selection R k S,‖weight R k N p b v S q*(physical q-independent q)‖:=norm_sum_le ..
    _≤∑q:Selection R k S,‖weight R k N p b v S q‖*ε:=by
      apply sum_le_sum
      intro q _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each q) (norm_nonneg _)
    _≤_:=by rw [←sum_mul];exact mul_le_mul_of_nonneg_right (priced R k N p b live v S M cash) hε

end YM.Integration.WilsonReceivedCanonicalVersePortfolio
