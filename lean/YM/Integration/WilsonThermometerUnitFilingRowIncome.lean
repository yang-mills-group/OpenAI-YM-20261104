import YM.Integration.WilsonThermometerUnitFilingCoverPieces

/-! The salary of each individual issued row and the countable bill at fixed physical period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRowIncome
open Function Finset Gauge Lattice RG Wilson QuadraticLocal Marker QuadraticLocal.Earn Stationary
open Push Push.Local Push.AbsoluteSums
open scoped Classical BigOperators

variable {G:Gauge}{n:Side}{o:Passport n Unit}{J:Census Unit}{I X:Type}
  (M:I→Row o J G X)(w:Unit→ℝ)(σ:ℝ)

def cash (i:I):ℝ:=Poly.toll w (M i).mode * (M i).height σ

variable {grades:Unit→ℕ}{C:ℝ}{ord cap H:ℕ}

theorem positive (stock:Scene.Armada M w grades σ C ord cap H)(i:I):0 ≤ cash M w σ i:=by
  simpa [cash] using (stock.suggests (M i).center).1 i

theorem single (stock:Scene.Armada M w grades σ C ord cap H)(i:I):
    Scene.Armada (fun _:Unit=>M i) w grades σ (cash M w σ i) ord cap H:=by
  refine ⟨stock.toMinistry,stock.positive,?_,⟨fun _=>stock.purchases.spend i,
    fun _=>stock.purchases.usable i⟩,fun _=>stock.honor i⟩
  intro x
  apply budget_finite
  · intro u;change 0 ≤ if (M i).center=x then cash M w σ i else 0
    split_ifs <;> first | exact positive M w σ stock i | exact le_rfl
  · change (∑ _:Unit,if (M i).center=x then cash M w σ i else 0) ≤ cash M w σ i
    simp only [Fintype.sum_unique]
    split_ifs <;> first | exact le_rfl | exact positive M w σ stock i

theorem summable (stock:Scene.Armada M w grades σ C ord cap H):Summable (cash M w σ):=by
  have hs:Summable (fun i=>∑ x:Site n, if (M i).center=x then cash M w σ i else 0):=
    summable_sum (fun x _=>(stock.suggests x).2.1)
  simpa only [Finset.sum_ite_eq,Finset.mem_univ,if_true] using hs

end YM.Integration.WilsonThermometerUnitFilingRowIncome
