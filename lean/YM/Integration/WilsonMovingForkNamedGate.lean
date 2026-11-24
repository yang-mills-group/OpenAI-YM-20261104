import YM.Integration.WilsonMovingForkOpticalBook
import YM.Integration.WilsonOriginalTwoFlatPublicMixedNamedRate

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonMovingForkNamedGate
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato GapsContact Climb Maxwell Maxwell.Free Next.Rank Next.Rank.Station
open RG16 RG16.Literal OPE Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters
open WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare WilsonMovingForkRawSeed
open WilsonMovingForkOpticalBook
open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open PhysMS MS MS.Land FVA2 FVA2.Register
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {z:Trace.Terrace.Arch R.family}{I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta

def Columns {D T:ℕ}{δ:ℝ}(book:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (d:I→Fin (D+1))(ρ:I→{s:ℝ // 0<s ∧ s<δ})(aim:ℕ)(τ:ℝ):Prop:=
  let j:=reporter F book ρ
  ∀K:ℕ,∀jk:j ≤ K,∃ A:∀_N _per:ℕ,∀e:Fin (D+1),(C).label e ≃ₗ[ℂ] (C).label e,
    (∀N per:ℕ,∀kn:K<N,∀i:I,∀b:Bool,∀v:S.Field (d i),
      let a:=(book (ρ i)).rows (d i)
      let Y:=(a.arm b v).source (N,per)
      let w:=column R (j:=j) (N:=N) (per:=per) (A N per (d i)) Y
      A N per (d i) w=full R (d i) N per j Y ∧
      Arrived R (d i) j K N per aim jk kn.le τ (A N per (d i)) (full R (d i) N per j Y) ∧
      ((C).labels.level (d i)).coeffSize w  ≤ 
        stretch R τ j K*((1+wrapCost R (d i) j)*(charge F a j b v*(C).S.a j^(d i).val)))

omit [DecidableEq I] [Nonempty I] in
theorem prepared (simple:G.Simple)(bliss:Bliss F l z H)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀j,1 ≤ (R.family.path.levels.budget j).supportExponent)
    {D T:ℕ}{δ:ℝ}(book:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(d:I→Fin (D+1))
    (aim:ℕ){τ:ℝ}(tp:0<τ):∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
      (∃i,(ρ i).val=r) → Columns F book d ρ aim τ:=by
  obtain ⟨start,earned⟩:=eventually_atTop.mp (WilsonMovingForkRawSeed.original R simple shop wide D aim tp)
  have later:=WilsonReflectedPublicStationLate.original F simple bliss T start
  filter_upwards [later] with r late ρ near
  let j:=reporter F book ρ
  obtain ⟨i₀,atNear⟩:=near
  have past:start ≤ j:=by
    have atDate:start ≤ station F ((book (ρ i₀)).rows (d i₀)) false:=by
      rw [←atNear] at late
      exact late _ (book (ρ i₀)).checked (book (ρ i₀)).active false
    exact atDate.trans (station_le F book ρ i₀ (d i₀) false)
  change ∀ K, ∀ jk:j ≤ K, _
  intro K jk
  have maps(N per:ℕ):∃ A:∀e:Fin (D+1),(C).label e ≃ₗ[ℂ] (C).label e,
    ∀kn:K<N,∀e:Fin (D+1),∀Y:(C).label e,
      let w:=column R (j:=j) (N:=N) (per:=per) (A e) Y
      A e w=full R e N per j Y ∧ Arrived R e j K N per aim jk kn.le τ (A e) (full R e N per j Y) ∧
      ((C).labels.level e).coeffSize w ≤ stretch R τ j K*((1+wrapCost R e j)*(Spindle.paid C e j N per Y*(C).S.a j^e.val)):=by
    by_cases kn:K<N
    · obtain ⟨A,all⟩:=earned j past K N per jk kn.le (lt_of_le_of_lt jk kn)
      exact ⟨A,fun _ e Y=>all e Y⟩
    · exact ⟨fun e=>LinearEquiv.refl ℂ ((C).label e),fun hl=>False.elim (kn hl)⟩
  choose A owns using maps
  refine ⟨A,?_⟩
  intro N per kn i b v
  let a:=(book (ρ i)).rows (d i)
  let Y:=(a.arm b v).source (N,per)
  have lift:=owns N per kn (d i) Y
  have cow:=WilsonOriginalTwoFlatPublicFare.issued F a (book (ρ i)).checked b v (station_le F book ρ i (d i) b) (p:=per) (lt_of_le_of_lt jk kn)
  refine ⟨lift.1,lift.2.1,lift.2.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity)
  have fee:0 ≤ WilsonCapturedPrimaryCoreBill.wrapFee ((C).labels.level (d i)) (C).params:=
    mul_nonneg (Nat.cast_nonneg _) (germ_close ((C).labels.level (d i)) (C).params).choose_spec.1.le
  have col:0 ≤ (R.family.path.levels.params j).columns:=zero_le_one.trans (R.family.path.levels.params j).columns_ge
  apply mul_le_mul_of_nonneg_left _ (add_nonneg zero_le_one (mul_nonneg (mul_nonneg fee (Real.exp_pos _).le) col))
  exact mul_le_mul_of_nonneg_right cow (pow_nonneg ((C).S.a_pos j).le _)

theorem original (Jr:ℝ→tower S)(Z:WilsonPrescription G) (fac:Facilities C f S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀j,1 ≤ (R.family.path.levels.budget j).supportExponent)
    (aim:ℕ){τ:ℝ}(tp:0<τ)(D h:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator R.family.book).Field (d i).val)(x:∀i,RG17.Free C (d i).val)
    {M η:ℝ}(one:1  ≤  M)(ep:0<η):
    ∃J u T:ℕ,∃δ:ℝ,∃books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
      0<δ ∧ Stop C 0 J u ∧ ∀p₀:ℕ,∀E:Finset I,E.Nonempty → ∃C₀:ℝ,0<C₀ ∧
      ∀ᶠ r in trail,0<r ∧ outer z h r<δ ∧
      ∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let j:=WilsonInvariantActionPosition.berth R 5 m
      Columns F books d ρ aim τ ∧ ∃uj:u ≤ j,∀N p:ℕ,∀top:j<N,∀o:E → Cover,(∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*outer z h r) →
      (Pairwise fun i i'=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
      ∀weak:E→Bool,
      let v(i:E):=chosen F Jr Z (ρ i).val ((books (ρ i)).V (d i)) (weak i) (y i) (x i)
      let Y:=word R (fun i:E=>(d i).val) j N p top.le o (fun i=>((books (ρ i)).rows (d i)).arm (weak i) (v i) |>.source (N,p))
      let amount:=C₀*(wilson z r)^p₀
      ‖gap R N p u (uj.trans top.le) Y‖ ≤ amount ∧ Heard R fac.simpleGate N p u Y amount :=by
  obtain ⟨J,u,T,δ,books,dp,stop,phases⟩:=WilsonOriginalTwoFlatPublicMixedNamedRate.original F Jr Z fac bliss slow lead paid D h d y x one ep
  have maps:=prepared F fac.simpleGate bliss shop wide books d aim tp
  refine ⟨J,u,T,δ,books,dp,stop,?_⟩
  intro q E ne
  obtain ⟨fee,fp,ph⟩:=phases q E ne
  refine ⟨fee,fp,?_⟩
  filter_upwards [ph,maps] with r sale columns
  refine ⟨sale.1,sale.2.1,?_⟩
  intro ρ bounds near
  exact ⟨columns ρ near,sale.2.2 ρ bounds near⟩

end YM.Integration.WilsonMovingForkNamedGate
