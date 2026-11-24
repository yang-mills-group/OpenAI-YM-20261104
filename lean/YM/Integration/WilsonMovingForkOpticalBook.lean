import YM.Integration.WilsonMovingForkSeededPoint
import YM.Integration.WilsonOriginalTwoFlatPublicMovingSelection

/-! One original field book supplies the optical phase, the normalized mapped public
dose and the wages of all represented arms. All subsets retain the full-roster date. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonMovingForkOpticalBook
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
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {z:Trace.Terrace.Arch R.family}{I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta

def reporter {D T:ℕ}{δ:ℝ}(book:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (ρ:I→{s:ℝ // 0<s ∧ s<δ}):ℕ:=
  WilsonInvariantActionPosition.berth R 5 (univ.sup fun i=>max (book (ρ i)).stock.j (book (ρ i)).W.k)

omit [DecidableEq I] [Nonempty I] in
theorem station_le {D T:ℕ}{δ:ℝ}(book:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (ρ:I→{s:ℝ // 0<s ∧ s<δ})(i:I)(d:Fin (D+1))(b:Bool):
    station F ((book (ρ i)).rows d) b  ≤  reporter F book ρ:=by
  let m:=univ.sup fun k:I=>max (book (ρ k)).stock.j (book (ρ k)).W.k
  have step:max (book (ρ i)).stock.j (book (ρ i)).W.k  ≤  m:=Finset.le_sup (f:=fun k:I=>max (book (ρ k)).stock.j (book (ρ k)).W.k) (mem_univ i)
  have arrive:m  ≤  reporter F book ρ:=(WilsonInvariantActionPosition.arrival R 5 m).1.le
  cases b
  · exact (le_max_left ..).trans (step.trans arrive)
  · exact (le_max_right ..).trans (step.trans arrive)

/-- The original measured inverse at the common station is shared by every arm of each
grade, regardless of the proper face, while the support and phase income use genuine
multi-slot Wilson products. -/
def Gate (simple:G.Simple)(D T q h u aim:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (book:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(M η r τ:ℝ):Prop:=
  ∀ρ:I→{s:ℝ // 0<s ∧ s<δ}, (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
  let j:=reporter F book ρ
  ∀K:ℕ,∀jk:j ≤ K,∃ A:∀_N _per:ℕ,∀e:Fin (D+1),(C).label e ≃ₗ[ℂ] (C).label e,
    (∀N per:ℕ,∀kn:K<N,∀i:I,∀b:Bool,∀v:S.Field (d i),
      let a:=(book (ρ i)).rows (d i)
      let Y:=(a.arm b v).source (N,per)
      let w:=column R (j:=j) (N:=N) (per:=per) (A N per (d i)) Y
      A N per (d i) w=full R (d i) N per j Y ∧
      Arrived R (d i) j K N per aim jk kn.le τ (A N per (d i)) (full R (d i) N per j Y) ∧
      ((C).labels.level (d i)).coeffSize w  ≤ 
        stretch R τ j K*((1+wrapCost R (d i) j)*(charge F a j b v*(C).S.a j^(d i).val))) ∧
    ∀E:Finset I,E.Nonempty → ∃uj:u ≤ j,∀N per:ℕ,∀top:j<N,∀o:E → Cover,
      (∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*outer z h r) →
      (Pairwise fun i i'=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
      ∀b:E→Bool,∀v:∀i:E,S.Field (d i),
      let a(i:E):=(book (ρ i)).rows (d i)
      let Y:=word R (fun i:E=>(d i).val) j N per top.le o (fun i=>((a i).arm (b i) (v i)).source (N,per))
      let fee:=(∏i:E,charge F (a i) j (b i) (v i))*((β j)^q)⁻¹
      ‖gap R N per u (uj.trans top.le) Y‖ ≤ fee ∧ Heard R simple N per u Y fee

theorem original (fac:Facilities C f S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ (R.family.path.levels.budget j).supportExponent)
    (D q h aim:ℕ)(d:I→Fin (D+1)){M η τ:ℝ}(one:1 ≤ M)(ep:0<η)(tp:0<τ):
    ∃J u T:ℕ,∃δ:ℝ,∃book:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
      0<δ ∧ Stop C 0 J u ∧ ∀ᶠr in trail,0<r ∧ r ≤ outer z h r ∧ outer z h r<δ ∧
        Gate F fac.simpleGate D T q h u aim d book M η r τ:=by
  obtain ⟨J,u,T,δ,book,dp,stop,phases⟩:=WilsonOriginalTwoFlatPublicMovingSelection.original F fac bliss slow D q h d one ep
  obtain ⟨start,earned⟩:=eventually_atTop.mp (WilsonMovingForkRawSeed.original R fac.simpleGate shop wide D aim tp)
  have later:=WilsonReflectedPublicStationLate.original F fac.simpleGate bliss T start
  refine ⟨J,u,T,δ,book,dp,stop,?_⟩
  filter_upwards [phases,later] with r paid late
  refine ⟨paid.1,paid.2.1,paid.2.2.1,?_⟩
  intro ρ bounds near
  let j:=reporter F book ρ
  obtain ⟨i₀,atNear⟩:=near
  have past:start ≤ j:=by
    have atDate:start ≤ station F ((book (ρ i₀)).rows (d i₀)) false:=by
      rw [←atNear] at late
      exact late _ (book (ρ i₀)).checked (book (ρ i₀)).active false
    exact atDate.trans (station_le F book ρ i₀ (d i₀) false)
  intro _ K jk
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
  refine ⟨A,?_,fun E ne=>(paid.2.2.2 E ne) ρ bounds ⟨i₀,atNear⟩⟩
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

end YM.Integration.WilsonMovingForkOpticalBook
