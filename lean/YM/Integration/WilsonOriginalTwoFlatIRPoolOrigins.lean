import YM.Integration.WilsonMovingForkHomeIncome
import YM.Integration.WilsonMovingForkSlotDate

noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolOrigins
open Function Filter Finset Set Lattice RG Wilson Source Extraction Table Spec Trace.Pilot
open PhysicalNext.Repeat.Legato GapsContact Climb Maxwell Maxwell.Free
open PhysMS FVA2 FVA2.Register MS.Land
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPositionHomogeneousFrame (homogeneous)
open scoped Classical Topology BigOperators

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {z:Trace.Terrace.Arch R.family}{I:Type}[Fintype I][Nonempty I]
    (Jr:ℝ→tower S)(Z:WilsonPrescription G)

def home {D T:ℕ}{s:ℝ}(B:Book F (l:=l) H z D T s)(d:Fin (D+1))(x:RG17.Free R.family d.val) :=
  WilsonMovingForkSlotDate.slot F B d (homogeneous F Jr Z s d.val x)

/-- Each pooled name carries its issued station and complete numerical quota on the
original cutoff law. The finite roster may have a different reporting home at every index. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (D T h gate:ℕ)(d:I→Fin (D+1))(x:∀i,RG17.Free R.family (d i).val)
    {δ:ℝ}(books:(s:{s:ℝ //0 < s ∧ s < δ})→Book F (l:=l) H z D T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃B:I→ℝ,∃E:I→ℕ,(∀i,1 ≤ B i) ∧ ∀ᶠr in trail,
    ∀ρ:I→{s:ℝ //0 < s ∧ s < δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
    (∃i,(ρ i).val=r) → let f:=reporter F books ρ
    ∀i,let L:=home F Jr Z (books (ρ i)) (d i) (x i)
      let v:=homogeneous F Jr Z (ρ i).val (d i).val (x i)
      let income:=B i*R.family.path.levels.clock.hatBeta f^(E i)
      gate ≤ L.j ∧ L.j ≤ f ∧ R.family.S.a L.j/R.family.S.a f ≤ R.family.path.levels.clock.hatBeta f^(2*T+11+2*h) ∧
      L.arm=((books (ρ i)).rows (d i)).arm false v ∧
      WilsonReflectedPublicStationFare.fee F ((books (ρ i)).rows (d i)) false v ≤ income ∧
      (∀N per,L.j < N → Next.UVStress.quota R.family (d i).val L.j N per (L.arm.source (N,per))
          ≤  R.family.S.a L.j^(d i).val*income) := by
  classical
  obtain ⟨B,E,one,fees⟩:=WilsonMovingForkHomeIncome.original F Jr Z simple bliss slow lead paid D T h d x books window
  refine ⟨B,E,one,?_⟩
  filter_upwards [fees,WilsonMovingForkSlotDate.original F simple bliss slow D T h gate d books] with r cost dates
  intro ρ span near f i L v income
  obtain ⟨cut,live,optical,named⟩:=dates ρ span near (fun i=>homogeneous F Jr Z (ρ i).val (d i).val (x i)) i
  have fare:=((cost ρ span near (fun _=>false) i).2.1)
  refine ⟨cut,live,optical,named,fare,?_⟩
  intro N per active
  exact (L.numerical N per active).trans (mul_le_mul_of_nonneg_left fare (pow_nonneg ((R.family.S.a_pos _).le) _))

end YM.Integration.WilsonOriginalTwoFlatIRPoolOrigins
end
