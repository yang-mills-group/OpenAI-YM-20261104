import YM.Integration.WilsonAddressedPublicGuardFare
import YM.Integration.WilsonAddressedCollarWindow
import YM.Integration.WilsonMeasuredPublicClearance
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicOpticalFare
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



open WilsonInvariantActionPosition WilsonAddressedPublicGuardFare
local notation "a_" => R.family.S.a
local notation "H_" => R.family.path.levels.clock.hatBeta

/-- One public extraction's measured width places each of its actual printing
    stations inside the common physical radius. -/
theorem housed {z:Trace.Terrace.Arch R.family}{D T n:ℕ}{δ r:ℝ}
    (board:WilsonMeasuredPublicClearance.Book F l (z:=z) D T n δ r)
    (d:Fin (D+1))(v:S.Field d.val):
    a_ (((board.bank.department d.val (Nat.le_of_lt_succ d.isLt)).print v).j) ≤ δ*r:=by
  let department:=board.bank.department d.val (Nat.le_of_lt_succ d.isLt)
  let L:=department.print v
  obtain ⟨_,calendar⟩:=department.dated v
  have before:board.micro ≤ L.j:=board.before.trans (by simpa only [L,calendar] using L.fore)
  exact (R.family.S.strictAnti.antitone before).trans board.small.le

theorem quoted {j f K t:ℕ}{δ H s z b:ℝ}(pos:0<H)(power:0 ≤ s)(cost:0 ≤ b)
    (invoice:a_ f / a_ K ≤ H^t*H^δ)(seat:a_ j ≤ z) :
    b*(a_ j/a_ K)^s ≤ b*(z/a_ f)^s*H^(((t:ℝ)+δ)*s):=by
  have ja:=R.family.S.a_pos j
  have fa:=R.family.S.a_pos f
  have ka:=R.family.S.a_pos K
  have zd:=div_nonneg (ja.le.trans seat) fa.le
  have thermal:a_ f/a_ K ≤ H^((t:ℝ)+δ):=by
    rwa [Real.rpow_add pos,Real.rpow_natCast]
  have ratio:a_ j/a_ K ≤ (z/a_ f)*H^((t:ℝ)+δ):=by
    calc
      _ = (a_ j/a_ f)*(a_ f/a_ K):=by field_simp
      _ ≤ _:=mul_le_mul (div_le_div_of_nonneg_right seat fa.le) thermal (div_pos fa ka).le zd
  calc
    _ ≤ b*((z/a_ f)*H^((t:ℝ)+δ))^s:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (div_pos ja ka).le ratio power) cost
    _ = _:=by rw [Real.mul_rpow zd (Real.rpow_pos_of_pos pos _).le, ←Real.rpow_mul pos.le,mul_assoc]

/-- At the authentic optical stop each issued field may be tested with its
    own physical radius, including the measured public extraction radius. -/
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ (R.family.path.levels.budget j).supportExponent)
    (quote:Poetry R.family.path.levels)(D target t:ℕ){η δ:ℝ}(ep:0<η)(pd:0<δ):
    ∃gate:ℕ,∀ᶠ f:ℕ in atTop,
    let K:=berth R t f
    ∀ (I:Type)(d:I→Fin (D+1))(v:(i:I)→S.Field (d i).val)
      (s M:I→ℝ)(L:(i:I)→WilsonMeasuredPublicSlots.Slot F l (d i).val (v i) (s i) (M i))
      (N p:ℕ)(_ :∀i,gate ≤ (L i).j)(before:∀i,(L i).j ≤ f)(live:K ≤ N),
      ∃A:(i:I)→R.family.label (d i).val ≃ₗ[ℂ] R.family.label (d i).val,
        (∀i x,Arrived R (d i).val (L i).j K N p target ((before i).trans (WilsonInvariantActionPosition.arrival R t f).1.le) live η (A i) x) ∧
        ∀i,let Y:=(L i).arm.source (N,p)
            let w:=(A i).symm (fitted R (d i).val (L i).j N p Y)
            (∀χ z:ℝ,0<χ → a_ (L i).j ≤ z →
              (R.family.labels.level (d i).val).coeffSize (word R (d i).val K χ w) ≤
                4*(M i*GapsContact.Ascent.cost F (d i).val (s i) (v i)/χ)*
                  (z/a_ f)^(((d i).val:ℝ)+η)*(H_ f)^(((t:ℝ)+δ)*(((d i).val:ℝ)+η))) ∧
            ∀ o,settled R (d i).val (L i).j f (K-f) N p (by rw [Nat.add_sub_of_le (WilsonInvariantActionPosition.arrival R t f).1.le]; exact live) (A i) Y o:=by
  obtain ⟨gate,sale⟩:=WilsonAddressedPublicGuardFare.original R F l simple shop wide quote D target ep
  refine ⟨gate,?_⟩
  filter_upwards [WilsonAddressedCollarWindow.original R simple slow t pd] with f terms
  let K:=berth R t f
  have fk:f<K:=terms.1
  have clock:f+(K-f)=K:=Nat.add_sub_of_le fk.le
  dsimp only
  intro I d v s M L N p late before live
  obtain ⟨A,arrival,read⟩:=sale I d v s M L f (K-f) N p late before (clock.symm ▸ live)
    (fun i=>(lt_of_le_of_lt (before i) fk).trans_le live)
  refine ⟨A,fun i x=>?_,fun i=>?_⟩
  · simpa only [clock] using arrival i x
  · refine ⟨fun χ z hp seat=>?_,(read i).2⟩
    have receipt:= (read i).1 χ hp
    simp only [clock] at receipt
    let price:=4*(M i*GapsContact.Ascent.cost F (d i).val (s i) (v i)/χ)
    have out:0 ≤ price:=by
      have low:0 ≤ (R.family.labels.level (d i).val).coeffSize (word R (d i).val K χ
          ((A i).symm (fitted R (d i).val (L i).j N p ((L i).arm.source (N,p))))) :=
        Finset.sum_nonneg (fun _ _=>norm_nonneg _)
      exact nonneg_of_mul_nonneg_left (low.trans receipt)
        (Real.rpow_pos_of_pos (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) _)
    exact receipt.trans (quoted R (zero_lt_one.trans (R.family.path.levels.fits.delayed f))
      (add_nonneg (Nat.cast_nonneg _) ep.le) out terms.2.2 seat)

end YM.Integration.WilsonAddressedPublicOpticalFare
end
