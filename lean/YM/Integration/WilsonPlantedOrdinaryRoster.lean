import YM.Integration.WilsonPlantedGroupWords

/-! For each partition of the occupied names, sum the complete unmasked
analytic products on their original measured joint support. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPlantedOrdinaryRoster
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Planned.GuardedAtom
open WilsonCapturedPrimarySoftRoster WilsonCenteredCaptureRegularAtoms WilsonCenteredCaptureLampRoster WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {R : Census V}
  {p : BudgetPoint} {o : V → Site n} {k : ℕ}

private theorem wages (L : Lamps X ι G p o R) (w : V→ℝ) (hw : ∀v,0<w v) {α C : ℝ}
    (paid : Gross L w p.B α C) :
    ∃ e : ι→ℝ, (∀i,0≤e i) ∧
      (∀ i x U,‖L.nominal x i U‖≤e i) ∧
      ∀ (s:R.Mode) (v:V),v∈s.val→SumBudget
        (fun i : Row L s=>e i.val*Real.exp (α*coverNumber p.B (L.ground i.val))) ((Poly.toll w s)⁻¹*C) := by
  obtain ⟨e,pos,cap,spent⟩:=paid.before
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
    (w : V→ℝ) (hw : ∀ i,0<w i) {α C : ℝ} (width : 0≤α) (paid : Gross L w p.B α C) :
    ∃ e : ι→ℝ, (∀ a,0≤e a) ∧
      (∀ a x U,‖L.nominal x a U‖≤e a) ∧
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

private theorem reading (L : Lamps X ι G p o R) (s : R.Mode) (w : V→ℝ) (hw : ∀v,0<w v) {a b : ℝ} (apos : 0≤a) (gross : Gross L w p.B a b)
    (t:X) (U:Config G n) :
    HasSum (fun j:Row L s=>L.nominal t j.val U) ((bare L t U).part s) := by
  let f (j:ι):=(Poly.send (L.mode j) (L.nominal t j U)).part s
  have ok:=(WilsonRootedKioskCompleteFiling.sums L hw apos gross t U).1
  have sums : HasSum f ((bare L t U).part s):=by
    rw [WilsonRootedKioskOccupiedSlip.bare,Poly.share ok];exact ((Poly.get s).hasSum ok.hasSum).summable.hasSum
  have off (j:ι) (away:j∉Set.range ((↑):Row L s→ι)) : f j=0:=by
    have miss : s≠L.mode j:=fun yes=>away ⟨⟨j,yes.symm⟩,rfl⟩
    simp [f,Poly.part_send,miss]
  apply ((Subtype.val_injective.hasSum_iff off).2 sums).congr_fun
  intro j
  simp [f,Poly.part_send,j.property]


theorem full (L : Lamps X ι G p o R) (x : X) (M : Fin k→R.Mode) (U : Config G n)
    (w : V→ℝ) (hw : ∀v,0<w v) {a C:ℝ} (h : 0≤a) (gross : Gross L w p.B a C) :
    HasSum (fun row : Rows L M=>nominal L univ (fun j=>(row j).val) x U)
      (∏ j,(bare L x U).part (M j)) := by
  simp only [WilsonCenteredCaptureRegularAtoms.nominal, Finset.prod_apply]
  exact WilsonCapturedPrimarySoftProduct.signed (fun j=>Row L (M j))
    (fun j r=>L.nominal x r.val U) (fun j=>(bare L x U).part (M j))
    (fun j=>reading L (M j) w hw h gross x U)

end YM.Integration.WilsonPlantedOrdinaryRoster
