import YM.Integration.WilsonCapturedPrimarySoftProduct

/-! True support and derivative prices of all the original lamp choices in
one squarefree partition. Every block touches the designated physical hull. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySoftRoster
open Function Finset RG Lattice Wilson Marker QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums
open WilsonCenteredCaptureLampRoster WilsonCenteredCaptureRegularAtoms
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {p : BudgetPoint} {k : ℕ}

theorem shared {J : Type} (m : Finset J) (D : J→Support n) (Z : Support n) (B : ℕ)
    (touch : ∀ j∈m,∃ u,u∈Z ∧ u∈D j) :
    coverNumber B (Z ∪ m.biUnion D) ≤ coverNumber B Z + ∑ j∈m,coverNumber B (D j) := by
  induction m using Finset.induction_on with
  | empty => simp
  | @insert j m hj ih =>
    obtain ⟨u,uz,ud⟩:=touch j (mem_insert_self ..)
    have meet:=meets_sum (mem_union_left (m.biUnion D) uz) ud B
    have smaller:=ih (fun i hi=>touch i (mem_insert_of_mem hi))
    rw [biUnion_insert, sum_insert hj]
    calc
      _ = coverNumber B ((Z ∪ m.biUnion D) ∪ D j) := by
        congr 1
        ext u
        simp only [mem_union]
        tauto
      _ ≤ _ := meet
      _ ≤ _ := by omega

abbrev Rows (L : Lamps X ι G p o R) (M : Fin k→R.Mode) := (j : Fin k)→Row L (M j)

private theorem wages (L : Lamps X ι G p o R) (w : V→ℝ) (hw : ∀v,0<w v) {α C : ℝ}
    (paid : L.Paid w p.B α C) :
    ∃ e : ι→ℝ, (∀i,0≤e i) ∧
      (∀ i x y,y∈L.ground i→p.supBounds y (L.ground i) (L.nominal x i) (e i)) ∧
      ∀ (s:R.Mode) (v:V),v∈s.val→SumBudget
        (fun i : Row L s=>e i.val*Real.exp (α*coverNumber p.B (L.ground i.val))) ((Poly.toll w s)⁻¹*C) := by
  obtain ⟨e,pos,cap,spent⟩:=paid.budget
  refine ⟨e,pos,cap,?_⟩
  intro s v hv
  have root (i : Row L s) : o v∈L.ground i.val := L.roots i.val v (by rw [i.property];exact hv)
  let full := fun i : ι=>if o v∈L.ground i then Poly.toll w (L.mode i)*e i*Real.exp (α*coverNumber p.B (L.ground i)) else 0
  have whole : SumBudget full C := spent (o v)
  have sub : SumBudget (fun i : Row L s=>full i.val) C :=
    ⟨fun i=>whole.1 _,whole.2.1.comp_injective Subtype.val_injective,
      (tsum_comp_le_tsum_of_inj whole.2.1 whole.1 Subtype.val_injective).trans whole.2.2⟩
  have win := budget_scale (inv_pos.mpr (Poly.worth hw s)).le sub
  convert win using 1
  funext i
  simp only [full,if_pos (root i),i.property]
  field_simp [(Poly.worth hw s).ne']

theorem original (L : Lamps X ι G p o R) (M : Fin k→R.Mode) (v : Fin k→V)
    (root : ∀ j,v j∈(M j).val) (Z : Support n) (inside : ∀j,o (v j)∈Z)
    (w : V→ℝ) (hw : ∀ i,0<w i) {α C : ℝ} (width : 0≤α) (paid : L.Paid w p.B α C) :
    ∃ e : ι→ℝ, (∀ a,0≤e a) ∧
      (∀ a x y,y∈L.ground a→p.supBounds y (L.ground a) (L.nominal x a) (e a)) ∧
      SumBudget (fun row : Rows L M=>(∏ j,e (row j).val)*
        Real.exp (α*coverNumber p.B (domain L univ (fun j=>(row j).val) Z)))
        (Real.exp (α*coverNumber p.B Z)*∏ j,(Poly.toll w (M j))⁻¹*C) := by
  obtain ⟨e,pos,cap,issued⟩:=wages L w hw paid
  have income j:=issued (M j) (v j) (root j)
  refine ⟨e,pos,cap,?_⟩
  let D j (a : Row L (M j)) := L.ground a.val
  have all:=WilsonCapturedPrimarySoftProduct.budget _ _ income
  apply budget_mono (budget_scale (Real.exp_pos (α*coverNumber p.B Z)).le all)
    (fun row=>mul_nonneg (prod_nonneg fun j _=>pos (row j).val) (Real.exp_pos _).le)
  intro row
  have geo:=shared univ (fun j=>D j (row j)) Z p.B (fun j _=>⟨_,inside j,
    L.roots _ _ (by rw [(row j).property];exact root j)⟩)
  have g : (coverNumber p.B (domain L univ (fun j=>(row j).val) Z) : ℝ) ≤
      coverNumber p.B Z+∑j:Fin k,(coverNumber p.B (D j (row j)):ℝ) := by exact_mod_cast geo
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left g width))
    (prod_nonneg fun j _=>pos (row j).val)).trans_eq ?_
  simp only [mul_add,mul_sum,Real.exp_add,Real.exp_sum,prod_mul_distrib,D]
  ring

theorem complete (L : Lamps X ι G p o R) (x : X) (M : Fin k→R.Mode) (U : Config G n)
    (admitted : Summable (fun i=>L.frame i x U)) :
    HasSum (fun row : Rows L M=>viewed L univ (fun j=>(row j).val) x U)
      (∏ j,(L.log x U).part (M j)) := by
  change HasSum (fun row : (j : Fin k)→Row L (M j)=>∏ j,L.light x (row j).val U) _
  exact WilsonCapturedPrimarySoftProduct.signed (fun j=>Row L (M j))
    (fun j a=>L.light x a.val U) (fun j=>(L.log x U).part (M j))
    (fun j=>published L (M j) x U admitted)

end YM.Integration.WilsonCapturedPrimarySoftRoster
