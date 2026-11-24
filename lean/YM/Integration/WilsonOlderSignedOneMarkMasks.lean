import YM.Integration.WilsonCenteredHardFiled
import YM.Integration.WilsonCenteredLampCapture
import YM.Integration.WilsonRootedKioskCompleteFiling

/-! A filed unmasked word differs from its physical lamp only on its recorded
failed support. Attach that signed difference to the complete quiet gas at
the same date, including owners whose recorded flags lie beyond the centre. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkMasks
open Function Finset RG Lattice Wilson Marker QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums
open Source Labels Planned.GuardedAtom Extra.Histories Comparison.RG02.Cumulants
open WilsonCenteredFiledAtoms WilsonCenteredCaptureSlots WilsonCenteredFailedHalo
open WilsonRootedKioskOccupiedSlip WilsonCenteredCaptureLampRoster
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V] [Countable ι]
    {R : Census V} {o : V→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}
    (L : Lamps X ι G P.p o R) (s : R.Mode) (v : V) (hv : v∈s.val)
    (w : V→ℝ) (hw : ∀ i,0<w i) {A : ℝ}
    (gross : Gross L w P.p.B (P.p.supportExponent+2) A)

def fare (p : BudgetPoint) (Z : Support n) (u D full κ : ℝ) :=
  (hitWidth p * u) * (Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*(D⁻¹*full)) / κ

omit [Fintype V] in
include v hv hw gross in
theorem original (x : X) (Z : Support n) (y : Site n) (hy : y∈Z) (seat : o v∈Z) (K : Guard.Keeper P.p P.activities)
    {u κ : ℝ} (div : 0<κ) (pos : 0≤u) (room : hitWidth P.p*u≤1) (quiet : P.activities.KBound P.p u)
    (law : P.activities.ForcedFamily P.p) (S : SectionData F) (Y : Hol G) :
    Store P S Y y κ (fare P.p Z u (Poly.toll w s) A κ)
      (fun U=>(P.eval U:ℂ)*(((L.log x U).part s)-((bare L x U).part s))) := by
  let I:=Row L s
  let T := fun j : I=>Z∪L.ground j.val
  let h := fun (j:I) (U:Config G n)=>((sheet L).soap x j.val U).part s
  let ser:=WilsonCenteredLampCapture.docket (I×Finset ℕ)
  have root (j:I) : o v∈L.ground j.val:=L.roots _ _ (by rw [j.property];exact hv)
  have c (j:I) (U:Config G n) : h j U=gap L x j.val U := by
    change (Poly.send (L.mode j.val) _).part s=_
    rw [Poly.part_send,if_pos j.property.symm]
  have att (j:I) : Attaches P.p.threshold (T j) (h j) := by
    let z := ((sheet L).cost x j.val).widen (Finset.subset_union_right (s₁:=Z))
    refine ⟨fun U U' hg hfl=>congrArg (fun v=>Poly.part v s) (z.reads U U' hg hfl),
      fun k U=>congrArg (fun v=>Poly.part v s) (z.gauge k U),
      (Poly.part_cont _).measurable.comp z.borel,fun U good=>?_⟩
    exact (c j U).trans (healthy L x _ U (good.mono_left Finset.subset_union_right))
  let α := P.p.supportExponent+2
  have ha : 0≤α:=by dsimp [α]; linarith [P.p.exponent_pos]
  obtain ⟨e,ep,cap,hit⟩:=gross.before
  let full:=fun j:ι=>if o v∈L.ground j then Poly.toll w (L.mode j)*e j*Real.exp (α*coverNumber P.p.B (L.ground j)) else 0
  have whole : SumBudget full A:=hit (o v)
  have sub : SumBudget (fun j:I=>full j.val) A:=
    ⟨fun _=>whole.1 _,whole.2.1.comp_injective Subtype.val_injective,
      (tsum_comp_le_tsum_of_inj whole.2.1 whole.1 Subtype.val_injective).trans whole.2.2⟩
  have earn : SumBudget (fun j:I=>e j.val*Real.exp (α*coverNumber P.p.B (L.ground j.val))) ((Poly.toll w s)⁻¹*A) := by
    have earn:=budget_scale (inv_pos.mpr (Poly.worth hw s)).le sub
    convert earn using 1
    funext j
    simp only [full,if_pos (root j),j.property]
    field_simp [(Poly.worth hw s).ne']
  let bill:=Real.exp (α*coverNumber P.p.B Z)*((Poly.toll w s)⁻¹*A)
  have pack : SumBudget (fun j:I=>reservedMass P.p (T j) (e j.val)) bill:=by
    refine budget_mono (budget_scale (Real.exp_pos (α*coverNumber P.p.B Z)).le earn)
      (fun j=>mul_nonneg (Real.exp_pos _).le (ep _)) ?_
    intro j
    change Real.exp (α*coverNumber P.p.B (Z∪L.ground j.val))*e j.val ≤
      Real.exp (α*coverNumber P.p.B Z)*(e j.val*Real.exp (α*coverNumber P.p.B (L.ground j.val)))
    have geo : (coverNumber P.p.B (Z∪L.ground j.val):ℝ) ≤ (coverNumber P.p.B Z:ℝ)+coverNumber P.p.B (L.ground j.val) := by
      exact_mod_cast meets_sum seat (root j) P.p.B
    have bound := Real.exp_monotone (mul_le_mul_of_nonneg_left geo ha)
    refine (mul_le_mul_of_nonneg_right bound (ep _)).trans_eq ?_
    rw [mul_add,Real.exp_add]
    ring
  have price:=WilsonCenteredFailedHalo.cost T K ser h (fun j=>e j.val) quiet pos room (fun j=>ep _) pack
    (fun j U=>by rw [c]; exact (size L x j.val U).trans (cap _ x U))
  let raw:=entered P K T Quiet ser h
  have fit : ForceFormat P.p P.activities y raw :=
    WilsonCenteredCaptureSlots.formed P K T Quiet ser h y law (fun _=>mem_union_left _ hy) att
  obtain ⟨B,format,due,read⟩:=WilsonCenteredHardFiled.source S Y y div raw fit price
  refine ⟨B,format,due,fun U=>?_⟩
  have z:=WilsonRootedKioskCompleteFiling.sums L hw ha gross x U
  let rawrow:=fun j:ι=>((sheet L).soap x j U).part s
  have support : Function.support rawrow ⊆ {j|L.mode j=s}:=by
    intro j hj
    by_contra ne
    have diff : s≠L.mode j := fun eq=>ne eq.symm
    exact hj (by change (Poly.send _ _).part s=0; rw [Poly.part_send,if_neg diff])
  have summed : (∑' j:I,h j U)=((sheet L).log x U).part s:=by
    change (∑' j:I,rawrow j.val)=(∑' j,(sheet L).soap x j U).part s
    rw [Poly.share z.2]
    exact tsum_subtype_eq_of_support_subset support
  have split:=congrArg (fun z=>Poly.part z s) (WilsonRootedKioskCompleteFiling.split L hw ha gross x U)
  change (L.log x U).part s=(bare L x U).part s+((sheet L).log x U).part s at split
  have gapEq : (∑' j:I,h j U)=(L.log x U).part s-(bare L x U).part s:=by rw [summed,split];abel
  rw [read]
  change (Real.exp (P.exponent U):ℂ)*(∑' Q,gasMark P.p P.activities U Q raw)=_
  rw [WilsonCenteredFailedHalo.actual T K ser h att price quiet U,gapEq]
  simp only [Rep.eval,Complex.ofReal_mul]
  ring

end YM.Integration.WilsonOlderSignedOneMarkMasks
