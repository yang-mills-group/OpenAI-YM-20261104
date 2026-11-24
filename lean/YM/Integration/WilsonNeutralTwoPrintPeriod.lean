import YM.Integration.WilsonReceivedCanonicalVerseTrial

/-! The independently appointed lower word at its genuine torus and occupied front.
Both signed angular tables are kept before the absolute cost, including the
constant angular coefficient in each occupied source. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPeriod
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Tree Exterior Stationary
open PowerSeries Next.Free FormalBulk08 Flat Reef Jets Series Shore Gorge Lotus Mesa City Cork
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonPointChildPlacedFamily
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations Pose Dawn Kemp Rift
open WilsonMarkedIndependentPhysicalIntake WilsonPointChildFiledPress
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Realm
open WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators


open WilsonReceivedDatedVerseReprint (Issued printed)
open WilsonMarkedIndependentEnrolledPeriod (registered)


open WilsonReceivedDatedVerseReprint (printed Issued)
open WilsonReceivedCanonicalVerseTrial (result)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h:I→ℕ}
variable (R:Run G)(k K:I→ℕ)(κ:(j:I) → Knob (h j))(pt:I → Chamber)

private def charge (r:ℕ)(σ A:ℝ)(J:Finset I)(n:Side):ℝ:=
  ((priceM (Hooks G) r σ+tiePay (Hooks G) r (σ/4)+1)*A^J.card+A^J.card)*catchW (σ/32/16) n

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m<b → ∃σ A:ℝ,0<σ ∧ 1≤A ∧
      ∀J:Finset I,∃t M:ℝ,0<t ∧ t≤σ ∧ 0≤M ∧ ∀c:I,c∈J →
      ∀N,b≤N → ∀q:(j:I)→Choice R k j,∀per,
      let n:=R.family.side m per
      let Y:=result R k K κ pt e N b m q
      ∀z:I→Site n, let y:=PeriodicMarkedWinding.roots n z c
      Issued Y k e J c y t σ M (A^J.card) ∧
      ∀a,a≤e → ∀r,∀w:((Fin r → Woods G n)→ℝ),∀f:Pen h J →L[ℝ] ℝ,
      let difference:=fun x=>f ((Y y J).1 n a r x)-f ((printed Y k e J c y).1 n a r x)
      (∀x,difference x=f ((Y y J).1 n a r x-Carp.plume ((Y y J).2 a r) n x)) ∧
      |∑x,w x*difference x| ≤
        ∑x,|w x| *(‖f‖*(charge (G:=G) r σ A J n*
          Real.exp (-(σ/32/2)*Syn (tor n) z J x))) :=by
  filter_upwards [WilsonReceivedCanonicalVerseTrial.original R k K κ pt simple quiet tags price funded e] with m atDate
  intro b inside
  obtain ⟨σ,A,hs,ha,paid,roster,_⟩:=atDate b inside.le
  refine ⟨σ,A,hs,ha,?_⟩
  intro J
  obtain ⟨t,M,ht,hm,hM,word⟩:=roster J
  refine ⟨t,M,ht,hm,hM,?_⟩
  intro c root N top q per n Y z y
  have issued:=word c root N top q y
  have paired:=((paid N top q).2.2 (Nat.sub_pos_of_lt inside) per).1
  refine ⟨issued,?_⟩
  intro a grade r w f difference
  constructor
  · intro x
    simp only [difference,map_sub]
    exact congrArg (fun v=>f ((Y y J).1 n a r x)-f v) (congrFun ((issued.2.2 a grade).2 n r) x)
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro x _
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    change ‖f ((Y y J).1 n a r x)-f ((printed Y k e J c y).1 n a r x)‖≤_
    rw [←map_sub]
    exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (WilsonReceivedDatedVerseReprint.price Y hs paired J c root z issued a grade r x) (norm_nonneg _))

end YM.Integration.WilsonNeutralTwoPrintPeriod
end
