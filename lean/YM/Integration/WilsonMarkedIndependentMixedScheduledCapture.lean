import YM.Integration.WilsonMarkedIndependentMixedScheduledIntake
import YM.Integration.WilsonMarkedIndependentMixedCapture

/-! Return every paid compact reporter roster at the prescribed physical
clearance to the genuine later finite side before testing the positions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedScheduledCapture
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Layout
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Shard WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Winding WilsonCoeffUV.Blue Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open WilsonMarkedIndependentMixedIntake (full)
open WilsonMarkedIndependentPhysicalIntake (PositiveAt PairedAt)
open WilsonMarkedIndependentMixedHistory (Filed)
open WilsonMarkedIndependentOnePeriod (Course)
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

def Returned (R:Run G)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(T:Credit)(δ:ℝ):Prop:=
  let F:=deck (G:=G) l d h
  let L:=R.family.path.levels
  ∀ᶠb:ℕ in atTop,∀m:ℕ,b ≤ m → ∀X:Herit F,(∀i,fee (F i) (X i) e≤T.buy (zz L m)) →
    ∃s A:ℝ,0<s ∧ 1≤A ∧ ∀M:ℕ,∀ᶠp:ℕ in atTop,∀N,m≤N →
      PairedAt e (Gears L R.metals.O l l N m b (full R l d h X m N M (δ*longLog L m))) (R.family.side b p) s A

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(filed:Filed R l d h e)(T:Credit){δ:ℝ}(hd:0<δ)
    (vac:∀ᶠm:ℕ in atTop,∃s V:ℝ,0<s ∧ 1≤V ∧ ∀N p:ℕ,m≤N →
      PositiveAt R.family.path.levels R.metals.O e N m (R.family.side m p) s V):
    Returned R l d h e T δ:=by
  let L:=R.family.path.levels
  obtain ⟨g,good⟩:=eventually_atTop.mp (WilsonMarkedIndependentMixedScheduledIntake.original R simple v funded l d h e filed T hd)
  obtain ⟨v₀,closed⟩:=eventually_atTop.mp vac
  unfold Returned
  filter_upwards [eventually_ge_atTop g,eventually_ge_atTop v₀,FundedMarkedCoverRows.realm R simple v funded (a+1) l d h e 0 0]
    with b gb vb realm
  obtain ⟨Q,level,scheme,_,anchor,_,_,_,_⟩:=realm
  intro m bm X budget
  let ρ:=δ*longLog L m
  obtain ⟨s,A,hs,hA,marked⟩:=good m (gb.trans bm) X budget ρ le_rfl
  obtain ⟨t,V,ht,hV,quiet⟩:=closed m (vb.trans bm)
  let w:=min t s
  obtain ⟨D,C,r,hC,hr,next⟩:=WilsonMarkedIndependentOnePeriod.original (D:=d) (k:=l) Q l b m anchor.le bm (show 0<w from lt_min ht hs)
  let B:=C*V^D*A
  have hB:1≤B:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hV)) hA
  refine ⟨r,B,hr,hB,?_⟩
  intro M
  filter_upwards [(marked M).2] with p posted
  intro N top
  let H:Course Q.draws:={side i:=R.family.side i p,next i:=by rw [level];exact Subtype.ext (L.clock.op i p).sizes}
  let Z:=full R l d h X m N M ρ
  have v₁:PositiveAt Q.draws Q.paid e N m (H.side m) w V:=by
    change PositiveAt Q.draws Q.paid e N m (R.family.side m p) w V
    rw [level,scheme]
    exact WilsonMarkedIndependentPhysicalIntake.quiet_narrow (quiet N p top) (min_le_left ..) le_rfl
  have a₁:=WilsonMarkedIndependentPhysicalIntake.narrow (posted N top) (min_le_right t s) (zero_le_one.trans hA) le_rfl
  have owned:PairedAt e (Gears Q.draws Q.paid l l N m b Z) (R.family.side b p) r B:=
    (next N top H Z ((marked M).1 N top) V A hV hA v₁ a₁).2
  rwa [level,scheme] at owned

end YM.Integration.WilsonMarkedIndependentMixedScheduledCapture
end
