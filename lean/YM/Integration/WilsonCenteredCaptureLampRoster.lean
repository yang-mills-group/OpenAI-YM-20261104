import YM.Integration.WilsonCenteredCaptureRegularAtoms
import YM.Integration.WilsonCenteredHardEnvelope

/-! The actual addressed signed singleton and pair subseries. The fields'
raw derivative envelopes and rooted incomes are fixed before the centered
test and real configuration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureLampRoster
open Function Finset RG Lattice Wilson Marker QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums
open Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι μ : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {p : BudgetPoint}

abbrev Row (L : Lamps X ι G p o R) (s : R.Mode) := {i : ι // L.mode i=s}

theorem published (L : Lamps X ι G p o R) (s : R.Mode) (x : X) (U : Config G n)
    (admitted : Summable (fun i=>L.frame i x U)) :
    HasSum (fun i : Row L s=>L.light x i.val U) ((L.log x U).part s) := by
  let read i := (L.frame i x U).part s
  have source : HasSum read ((L.log x U).part s) := by
    rw [Lamps.log,Poly.share admitted]
    exact ((Poly.get s).hasSum admitted.hasSum).summable.hasSum
  have off (i : ι) (absent : i ∉ Set.range ((↑) : Row L s→ι)) : read i=0 := by
    have ne : s≠L.mode i := fun he=>absent ⟨⟨i,he.symm⟩,rfl⟩
    simp [read,Lamps.frame,Poly.part_send,ne]
  have same := (Subtype.val_injective.hasSum_iff off).2 source
  apply same.congr_fun
  intro i
  simp [read,Lamps.frame,Poly.part_send,i.property]

theorem inlet (L : Lamps X ι G p o R) (s : R.Mode) (v : V) (hv : v∈s.val)
    (w : V→ℝ) (hw : ∀ i,0<w i) {α C : ℝ} (paid : L.Paid w p.B α C) :
    ∃ e : Row L s→ℝ, (∀ i,0 ≤ e i) ∧
      (∀ i x,p.supBounds (o v) (L.ground i.val) (L.nominal x i.val) (e i)) ∧
      SumBudget (fun i : Row L s=>e i*Real.exp (α*coverNumber p.B (L.ground i.val)))
        ((Poly.toll w s)⁻¹*C) := by
  obtain ⟨e,pos,cap,spent⟩ := paid.budget
  have root (i : Row L s) : o v∈L.ground i.val := L.roots i.val v (by rw [i.property];exact hv)
  let full := fun i : ι=>if o v∈L.ground i then Poly.toll w (L.mode i)*e i*Real.exp (α*coverNumber p.B (L.ground i)) else 0
  have whole : SumBudget full C := spent (o v)
  have sub : SumBudget (fun i : Row L s=>full i.val) C :=
    ⟨fun i=>whole.1 _,whole.2.1.comp_injective Subtype.val_injective,
      (tsum_comp_le_tsum_of_inj whole.2.1 whole.1 Subtype.val_injective).trans whole.2.2⟩
  refine ⟨fun i=>e i.val,fun i=>pos _,fun i x=>cap i.val x _ (root i),?_⟩
  have win := budget_scale (inv_pos.mpr (Poly.worth hw s)).le sub
  convert win using 1
  funext i
  simp only [full,if_pos (root i),i.property]
  field_simp [(Poly.worth hw s).ne']

theorem single (L : Lamps X ι G p o R) (s : R.Mode) (v : V) (hv : v∈s.val)
    (w : V→ℝ) (hw : ∀ i,0<w i) {α C : ℝ} (width : 0≤α) (paid : L.Paid w p.B α C)
    (Z : Support n) (seat : o v∈Z) :
    ∃ e : Row L s→ℝ, (∀ i,0 ≤ e i) ∧ (∀ i x,p.supBounds (o v) (L.ground i.val) (L.nominal x i.val) (e i)) ∧
      SumBudget (fun i : Row L s=>e i*Real.exp (α*coverNumber p.B (Z ∪ L.ground i.val)))
        (Real.exp (α*coverNumber p.B Z)*((Poly.toll w s)⁻¹*C)) := by
  obtain ⟨e,pos,cap,paid⟩ := inlet L s v hv w hw paid
  refine ⟨e,pos,cap,budget_mono (budget_scale (Real.exp_pos (α*coverNumber p.B Z)).le paid)
    (fun i=>mul_nonneg (pos i) (Real.exp_pos _).le) ?_⟩
  intro i
  have root : o v∈L.ground i.val := L.roots _ _ (by rw [i.property];exact hv)
  have bound := meets_sum seat root p.B
  have geo : (coverNumber p.B (Z∪L.ground i.val):ℝ) ≤ (coverNumber p.B Z:ℝ)+coverNumber p.B (L.ground i.val) := by exact_mod_cast bound
  have expL := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left geo width)
  refine (mul_le_mul_of_nonneg_left expL (pos i)).trans_eq ?_
  rw [mul_add,Real.exp_add];ring

theorem pair (L : Lamps X ι G p o R) (D : Lamps X μ G p o R) (a b : V)
    (w : V→ℝ) (hw : ∀ i,0<w i) {α C E : ℝ} (width : 0≤α) (first : L.Paid w p.B α C) (second : D.Paid w p.B α E)
    (Z : Support n) (za : o a∈Z) (zb : o b∈Z) :
    ∃ e : Row L (R.fire a)→ℝ, ∃ k : Row D (R.fire b)→ℝ,
      (∀ i,0≤e i) ∧ (∀ j,0≤k j) ∧
      (∀ i x,p.supBounds (o a) (L.ground i.val) (L.nominal x i.val) (e i)) ∧
      (∀ j x,p.supBounds (o b) (D.ground j.val) (D.nominal x j.val) (k j)) ∧
      SumBudget (fun z : Row L (R.fire a) × Row D (R.fire b)=>e z.1*k z.2*
        Real.exp (α*coverNumber p.B (Z∪L.ground z.1.val∪D.ground z.2.val)))
        (Real.exp (α*coverNumber p.B Z)*(((w a)⁻¹*C)*((w b)⁻¹*E))) := by
  have ida : a∈(R.fire a).val := mem_singleton_self _
  have idb : b∈(R.fire b).val := mem_singleton_self _
  obtain ⟨e,pos,cap,f⟩ := inlet L _ a ida w hw first
  obtain ⟨k,pos',cap',g⟩ := inlet D _ b idb w hw second
  rw [Poly.solo_toll] at f g
  refine ⟨e,k,pos,pos',cap,cap',budget_mono (budget_scale (Real.exp_pos (α*coverNumber p.B Z)).le (budget_prod f g))
    (fun z=>mul_nonneg (mul_nonneg (pos _) (pos' _)) (Real.exp_pos _).le) ?_⟩
  rintro ⟨i,j⟩
  have ha := L.roots i.val a (by rw [i.property];exact ida)
  have hb := D.roots j.val b (by rw [j.property];exact idb)
  have one := meets_sum za ha p.B
  have two := meets_sum (mem_union_left (L.ground i.val) zb) hb p.B
  have geo : (coverNumber p.B (Z∪L.ground i.val∪D.ground j.val):ℝ) ≤
      coverNumber p.B Z + coverNumber p.B (L.ground i.val) + coverNumber p.B (D.ground j.val) := by
    exact_mod_cast two.trans (Nat.add_le_add_right one _)
  have strip := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left geo width)
  refine (mul_le_mul_of_nonneg_left strip (mul_nonneg (pos i) (pos' j))).trans_eq ?_
  simp only [mul_add,Real.exp_add]
  ring

end YM.Integration.WilsonCenteredCaptureLampRoster
