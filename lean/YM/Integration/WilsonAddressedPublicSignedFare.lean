import YM.Integration.WilsonAddressedPublicGuardFare
import YM.Integration.WilsonReflectedOpticalRate
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicSignedFare
open Function Filter Lattice Wilson RG Source Labels
open Extraction Table Spec Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Work.G08
open Next.Foundations OPE.Therm Push.AbsoluteSums.Animals
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonAddressedRestartedColumn WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalMicroscopicGuardedReporters
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramBlockedPublicExperiment WilsonAddressedPublicPool
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {ord : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family ord S) (l : Ultrafilter (ℕ×ℕ))



open WilsonInvariantActionPosition
local notation "a_" => R.family.S.a
local notation "H_" => R.family.path.levels.clock.hatBeta

def amplitude (d f:ℕ)(χ:ℝ):ℂ:= -((χ:ℂ)⁻¹*((a_ f:ℂ)^d)⁻¹)

theorem cost {d K j f:ℕ}{η M χ:ℝ}(positive:0<χ){w:R.family.label d}
    (earned:(R.family.labels.level d).coeffSize w  ≤ 
      stretch R η j K*(2*(R.family.S.a j^d*M))):
    ‖amplitude R d f χ‖*bill R d K f w  ≤ 
     (2*(M/χ))*((a_ j/a_ f)^d*hike R.family K f rate*(1+4*stock R.family K)*stretch R η j K):=by
  have fa:=R.family.S.a_pos f
  have kp:0 ≤ 1+4*stock R.family K:=by
    have h:= (R.family.path.levels.params K).columns_ge
    change 1 ≤ stock R.family K at h
    linarith
  have realFee:‖amplitude R d f χ‖=χ⁻¹*(a_ f^d)⁻¹:=by
    simp only [amplitude,norm_neg,norm_mul,norm_inv,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg positive.le,Real.norm_of_nonneg fa.le]
  rw [realFee,WilsonMeasuredPublicEntranceGridDebit.bill]
  calc
    _  ≤  (χ⁻¹*(a_ f^d)⁻¹)*(hike R.family K f rate*((1+4*stock R.family K)*
          (stretch R η j K*(2*(a_ j^d*M))))):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left earned kp)
        (hike_pos R.family K f rate).le) (mul_nonneg (inv_nonneg.mpr positive.le)
          (inv_nonneg.mpr (pow_nonneg fa.le d)))
    _ = _ :=by rw [div_pow];ring

/-- The same fitted inverse finances both the trial's physical row and its signed
    difference with the true deposited column at the last separated date. -/
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ (R.family.path.levels.budget j).supportExponent)
    (quote:Poetry R.family.path.levels)(D target q B:ℕ){δ:ℝ}(pd:0<δ):
    ∃gate:ℕ,∀ᶠ f:ℕ in atTop,
    let K:=berth R (WilsonReflectedOpticalRate.depth q B D) f
    ∀(I:Type)(d:I→Fin (D+1))(v:(i:I)→S.Field (d i).val)
      (s M:I→ℝ)(L:(i:I)→WilsonMeasuredPublicSlots.Slot F l (d i).val (v i) (s i) (M i))
      (N p:ℕ)(_ :∀i,gate  ≤  (L i).j)(before:∀i,(L i).j  ≤  f)(live:K  ≤  N),
      ∃A:(i:I)→R.family.label (d i).val ≃ₗ[ℂ] R.family.label (d i).val,
        (∀i x,Arrived R (d i).val (L i).j K N p target ((before i).trans
          (WilsonInvariantActionPosition.arrival R _ f).1.le) live (1/32) (A i) x) ∧
        ∀i,let Y:=(L i).arm.source (N,p)
            let w:=(A i).symm (fitted R (d i).val (L i).j N p Y)
            (∀χ:ℝ,0<χ →
              (R.family.labels.level (d i).val).coeffSize (WilsonAddressedPublicGuardFare.word R (d i).val K χ w)  ≤ 
                4*(M i*GapsContact.Ascent.cost F (d i).val (s i) (v i)/χ)*
                  (a_ (L i).j/a_ K)^(((d i).val:ℝ)+1/32)) ∧
            (∀χ:ℝ,0<χ → a_ (L i).j/a_ f ≤ (H_ f)^B →
              ‖amplitude R (d i).val f χ‖*bill R (d i).val K f w  ≤ 
                8*(M i*GapsContact.Ascent.cost F (d i).val (s i) (v i)/χ)*((H_ f)^q)⁻¹) ∧
            ∀o,settled R (d i).val (L i).j f (K-f) N p (by
              rw [Nat.add_sub_of_le (WilsonInvariantActionPosition.arrival R _ f).1.le];exact live) (A i) Y o:=by
  obtain ⟨gate,sales⟩:=WilsonMeasuredPublicEntranceFittedSlots.original R F l simple shop wide quote D target
    (by norm_num : 0<(1/32:ℝ))
  refine ⟨gate,?_⟩
  filter_upwards [WilsonReflectedOpticalRate.original R simple slow q B D pd] with f clock
  let K:=berth R (WilsonReflectedOpticalRate.depth q B D) f
  have fk:f<K:=clock.1
  have kal:f+(K-f)=K:=Nat.add_sub_of_le fk.le
  dsimp only
  intro I d v s M L N p late before live
  obtain ⟨A,invs,earned⟩:=sales I d v s M L f (K-f) N p late before (kal.symm ▸ live)
    (fun i=>(lt_of_le_of_lt (before i) fk).trans_le live)
  refine ⟨A,fun i x=>?_,fun i=>?_⟩
  · simpa only [kal] using invs i x
  · let d':=(d i).val
    let wage:=M i*GapsContact.Ascent.cost F d' (s i) (v i)
    let w:=(A i).symm (fitted R d' (L i).j N p ((L i).arm.source (N,p)))
    have paid:(R.family.labels.level d').coeffSize w ≤ stretch R (1/32) (L i).j K*(2*(a_ (L i).j^d'*wage)):=by
      simpa only [kal] using (earned i).1
    have kp:0 ≤ 1+4*stock R.family K:=by
      have h:= (R.family.path.levels.params K).columns_ge
      change 1 ≤ stock R.family K at h
      linarith
    have h:=hike_pos R.family K f rate
    have width:0<stretch R (1/32) (L i).j K:=by unfold stretch;positivity
    have positive:0 ≤ wage:=by
      have r0:0  ≤  (R.family.labels.level d').coeffSize w:=Finset.sum_nonneg fun _ _=>norm_nonneg _
      have t:0  ≤  (stretch R (1/32) (L i).j K*2*a_ (L i).j^d')*wage:=by
        simpa only [mul_assoc] using r0.trans paid
      exact nonneg_of_mul_nonneg_right t (mul_pos (mul_pos width (by norm_num)) (pow_pos (R.family.S.a_pos _) _))
    refine ⟨fun χ hp=>WilsonAddressedPublicGuardFare.cost R hp paid,fun χ hp close=>?_,(earned i).2⟩
    have one:1 ≤ a_ (L i).j/a_ f:=(one_le_div (R.family.S.a_pos f)).mpr (R.family.S.strictAnti.antitone (before i))
    have active:=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ one (Nat.le_of_lt_succ (d i).isLt)) h.le) kp) width.le).trans (clock.2.2.2 (L i).j close)
    calc
      _  ≤  _:=cost R hp paid
      _  ≤  (2*(wage/χ))*(4*((H_ f)^q)⁻¹):=
        mul_le_mul_of_nonneg_left active (mul_nonneg zero_le_two (div_nonneg positive hp.le))
      _ = _:=by ring

end YM.Integration.WilsonAddressedPublicSignedFare
end
