import YM.Integration.WilsonReceivedQuietCrownOwner

/-! Price the absolute signed slips of one physical masked product at its own
original quiet Wilson owner and the same rooted hard divisor. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedQuietAbsolute
open MeasureTheory WilsonReceivedQuietCrownOwner
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Push.Corrected
open Source Labels Planned.GuardedAtom Extra.Histories WilsonCenteredCaptureRegularAtoms WilsonCenteredLampCapture
open WilsonCenteredFiledAtoms WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftRoster
open WilsonRootedKioskOccupiedSlip Comparison.RG02.Cumulants WilsonCenteredCaptureSlots WilsonCenteredFailedHalo
open WilsonMeasuredCoefficientTransport WilsonFullFaceSignedMasks WilsonCenteredHardMount WilsonCenteredHardAnswers WilsonCenteredAbsoluteHard
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {R : Census V}
    {o : V→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}


theorem partition [Countable ι] (L : Lamps X ι G P.p o R) (x : X) (s : R.Mode)
    (q : (parts R).Mode) (admitted : q∈shards R s) (y : Site n) (Z : Support n) (hold : y∈Z)
    (landing : ∀j∈s.val,o j∈Z) (rad : ℕ) (near : ∀j∈s.val,separation (o j) y≤rad)
    (w : V→ℝ) (hw : ∀v,0<w v) {C : ℝ} (paid : L.Paid w P.p.B (P.p.supportExponent+2) C)
    {D : ℝ} (gross : Gross L w P.p.B (P.p.supportExponent+2) D)
    {σ E Λ δ κ v : ℝ} (K : Guard.Keeper P.p P.activities) (law : P.Lawful σ E Λ δ v)
    (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1) (Y : Hol G) :
    ∃ B : Config G n→ℝ, Measurable B ∧
      (∀U, 0 ≤ B U ∧ B U ≤ tariff P.p Z w C q+tariff P.p Z w D q ∧
        ‖(∏ t∈q.val,(L.log x U).part t.val)-(∏ t∈q.val,(bare L x U).part t.val)‖ ≤ B U) ∧
      Owned (F:=F) P Y y κ (charge P.p Z w C D v κ q)
        (fun U => (P.eval U:ℂ)*(B U:ℂ)) := by
  let J := Fin q.val.card
  let A := Rows L (block q)
  let sets (a : A) (j : J) := (a j).val
  let T (a : A) := domain L univ (sets a) Z
  let f (a : A) := nominal L univ (sets a) x
  let h (a : A) := viewed L univ (sets a) x - f a
  let ranks (j : J) := o (root q j)
  have width : 0 ≤ P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
  have head (j:J):o (root q j)∈Z:=landing _ (inside q admitted j)
  obtain ⟨e,ep,caps,book⟩:=WilsonCapturedPrimarySoftRoster.original L (block q) (root q) (seated q) Z head w hw width paid
  obtain ⟨b,bp,capb,raw⟩:=WilsonPlantedOrdinaryRoster.original L (block q) (root q) (seated q) Z head w hw width gross
  let en (a:A):=∏j,e (sets a j)
  let bn (a:A):=∏j,b (sets a j)
  have g (a:A) := WilsonCenteredCaptureRegularAtoms.original L univ (sets a) x Z y ranks rad
    (fun j _=>near _ (inside q admitted j)) e
    (fun j _=>caps _ x (ranks j) (L.roots _ _ ((a j).property.symm ▸ seated q j)))
  have full (a:A) (U:Config G n) : ‖f a U‖ ≤ bn a := by
    simp only [f,nominal,Finset.prod_apply,norm_prod,bn]
    exact prod_le_prod (fun j _=>norm_nonneg _) (fun j _=>capb _ _ _)
  have attaches (a:A) : Attaches P.p.threshold (T a) (h a) :=by
    let f0 := masked P.p.threshold (T a) (f a)
    have hh : Attaches P.p.threshold (T a) (f a-f0) :=
      ⟨fun U W z flags=>congrArg₂ (·-·) ((g a).1.sites U W z) (uses_mask _ (g a).1.sites U W z flags),
        fun k U=>congrArg₂ (·-·) ((g a).1.symmetry k U) (invariant_mask (g a).1.symmetry _ _ k U),
        (g a).1.borel.sub (masked_measurable _ _ _ (g a).1.borel),fun U ok=>sub_eq_zero.mpr (masked_eq _ _ _ _ ok).symm⟩
    have first := (g a).2.2.1
    have eq : h a = WilsonCenteredCaptureRegularAtoms.rebate L univ (sets a) x Z - (f a-f0) := by change _ - f a = (_ - f0) - (f a - f0); abel
    rw [eq]
    refine ⟨fun U W z flags=>congrArg₂ (·-·) (first.sites U W z flags) (hh.sites U W z flags),
      fun k U=>congrArg₂ (·-·) (first.symmetry k U) (hh.symmetry k U),
      first.borel.sub hh.borel,fun U ok=>?_⟩
    simp only [Pi.sub_apply,first.healthy_zero U ok,hh.healthy_zero U ok,sub_self]
  have budget : SumBudget (fun a=>reservedMass P.p (T a) (en a+bn a))
      (tariff P.p Z w C q+tariff P.p Z w D q) :=by
    convert sumBudget_add book raw using 1
    · funext a;dsimp only [reservedMass,en,bn,T,sets];ring
    · rfl
  have pos a : 0≤en a+bn a := add_nonneg (prod_nonneg fun j _=>ep _) (prod_nonneg fun j _=>bp _)
  have cap a U : ‖h a U‖≤en a+bn a :=by
    apply (norm_sub_le ..).trans (add_le_add _ (full a U))
    change ‖∏j,L.light x (sets a j) U‖≤∏j,e (sets a j)
    rw [norm_prod]
    exact prod_le_prod (fun j _=>norm_nonneg _) (fun j _=>L.light_size _ x U (caps _ x _ (L.address _).anchor))
  let mag (a:A) (U:Config G n) : ℂ := ‖h a U‖
  have counted : SumBudget (fun a => en a+bn a) (tariff P.p Z w C q+tariff P.p Z w D q) := by
    apply budget_mono budget pos
    intro a
    exact le_mul_of_one_le_left (pos a) (Real.one_le_exp (mul_nonneg width (Nat.cast_nonneg _)))
  have absolute (U:Config G n) : Summable (fun a => ‖h a U‖) :=
    Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun a=>cap a U) counted.2.1
  have legal (a:A) : Attaches P.p.threshold (T a) (mag a) := by
    let b := attaches a
    exact ⟨fun U W z flags=>congrArg (fun t : ℂ => (‖t‖:ℂ)) (b.sites U W z flags),
      fun k U=>congrArg (fun t : ℂ => (‖t‖:ℂ)) (b.symmetry k U),
      Complex.continuous_ofReal.measurable.comp b.borel.norm,
      fun U ok=>by simp only [mag,b.healthy_zero U ok,norm_zero,Complex.ofReal_zero]⟩
  let serial:=docket (A×Finset ℕ)
  have price:=WilsonCenteredFailedHalo.cost T K serial mag (fun a=>en a+bn a) law.labels.boundK hv room pos budget
    (fun a U=>by simpa [mag] using cap a U)
  have shape:=WilsonCenteredCaptureSlots.formed P K T Quiet serial mag y law.labels.forced (fun _=>mem_union_left _ hold) legal
  obtain ⟨r,fit,bill,entry⟩:=mounted Y y div _ shape price
  refine ⟨fun U=>∑'a,‖h a U‖,Measurable.tsum (fun a=>(attaches a).borel.norm),?_,r,fit,bill,?_⟩
  · intro U
    refine ⟨tsum_nonneg (fun _=>norm_nonneg _),
      ((absolute U).tsum_le_tsum (fun a=>cap a U) counted.2.1).trans counted.2.2,?_⟩
    have physical:=WilsonCapturedPrimarySoftRoster.complete L x (block q) U (paid.sums width hw x U)
    have filed:=WilsonPlantedOrdinaryRoster.full L x (block q) U w hw width gross
    have both : (∑' a,h a U) = (∏ t∈q.val,(L.log x U).part t.val)-(∏t∈q.val,(bare L x U).part t.val) := by
      rw [←enumerate q (fun t=>(L.log x U).part t),←enumerate q (fun t=>(bare L x U).part t)]
      exact (physical.sub filed).tsum_eq
    rw [←both]
    exact norm_tsum_le_tsum_norm (absolute U)
  intro U
  rw [entry]
  change (Real.exp (P.exponent U):ℂ)*(∑' Q,gasMark P.p P.activities U Q (entered P K T Quiet serial mag))=_
  rw [WilsonCenteredFailedHalo.actual T K serial mag legal price law.labels.boundK U]
  simp only [Rep.eval,Complex.ofReal_mul,mag,Complex.ofReal_tsum]
  ring

end YM.Integration.WilsonAddressedQuietAbsolute
