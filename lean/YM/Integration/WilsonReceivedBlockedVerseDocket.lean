import YM.Integration.WilsonReceivedMicroscopicVerseWallet
import YM.Integration.WilsonMarkedIndependentEnrolledPeriod
import YM.Integration.WilsonReceivedCloseFundedHeat

/-! A predeclared compact independently evolved word at each real date of the joint
new K-local microscopic source. Its tuition is common to every upper vacuum cutoff, placement and period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedBlockedVerseDocket
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
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I]

def family (R:Run G)(u:I → G.ColorIndex)(k h K:I → ℕ)(depth:∀s,k s<h s)
    (N b m:ℕ)(digit:I → ∀j,Site (R.family.S.block j))(v:∀s,Letter (R.family.labels.level (k s))):Outerm G h:=
  Gears R.family.path.levels R.metals.O K k N b m (WilsonOriginalMicroscopicVerseSeed.seed R u k h depth digit b v)

def Docket (R:Run G)(u:I → G.ColorIndex)(k h K:I → ℕ)(depth:∀s,k s<h s)(e b m:ℕ):Prop:=
  ∃ σ A:ℝ,0<σ ∧ 1≤A ∧
    (∀N,b≤N → ∀p digit v,PairedAt e (family R u k h K depth N b m digit v) (R.family.side m p) σ A) ∧
    ∀J:Finset I,∃t M:ℝ,0<t ∧ t≤σ ∧ 0≤M ∧ ∀(c:I),c∈J → ∀N,b≤N → ∀digit v y,
      Issued (family R u k h K depth N b m digit v) k e J c y t σ M (A^J.card)

theorem original (R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (u:I → G.ColorIndex){k h:I → ℕ}(depth:∀s,k s<h s)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(K:I → ℕ)(e:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠm:ℕ in atTop,∀b,m≤b → Docket R u k h K depth e b m:=by
  classical
  have bare:=WilsonReceivedMicroscopicVerseWallet.original R simple booked u depth o tags price funded e pos
  obtain ⟨floor₁,birth⟩:=eventually_atTop.mp bare
  obtain ⟨floor₂,unmarked⟩:=eventually_atTop.mp (quiet e)
  filter_upwards [eventually_ge_atTop floor₁,eventually_ge_atTop floor₂,
    FundedMarkedCoverRows.realm R simple price funded 0 (fun _=>0) (fun _=>1) (fun _=>Nat.zero_lt_succ _) e 0 0] with m born queen realm
  obtain ⟨Q,draws,coins,_,anchor,_⟩:=realm
  intro b before
  obtain ⟨s₀,V,positive,hV,vac⟩:=unmarked b (queen.trans before)
  let s:=min s₀ (width R b/32)
  have hs:0<s:=lt_min positive (div_pos ((Primer.FamilyWindow R.family).pos _) (by norm_num))
  let unit:=(R.family.path.levels.clock.hatBeta b)^η*WilsonPointChildCenteredPortfolio.cap h
  let A:=WilsonReceivedMicroscopicVerseWallet.gross G (mass k univ+e) (width R b) unit
  have hA:1≤A:=WilsonReceivedMicroscopicVerseWallet.one _ _ _ _
  obtain ⟨d,C,σ,hC,hσ,step⟩:=WilsonMarkedIndependentOnePeriod.original (D:=h) (k:=k) Q K m b anchor.le before hs
  rw [draws,coins] at step
  have hB:1 ≤ C*V^d*A:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hV)) hA
  have learned (N:ℕ)(live:b≤N)(p:ℕ)(digit:I → ∀j,Site (R.family.S.block j))(v:∀s,Letter (R.family.labels.level (k s))):
      PairedAt e (family R u k h K depth N b m digit v) (R.family.side m p) σ (C*V^d*A):=by
    let Y:=WilsonOriginalMicroscopicVerseSeed.seed R u k h depth digit b v
    have top:PairedAt e Y (R.family.side b p) (width R b/32) A:=
      (birth b (born.trans before) digit v).2.2 (R.family.side b p)
    exact (step N live (registered R p) Y
      (WilsonOriginalMicroscopicVerseSeed.lawful R u k h depth digit b v simple o) V A hV hA
      (fun a ha he l hl=>(((vac N p live).2 a ha he l hl).mono (min_le_left ..)))
      (fun y J a ha r=>(top y J a ha r).mono (min_le_right ..))).2
  refine ⟨σ,C*V^d*A,hσ,hB,learned,?_⟩
  intro J
  obtain ⟨t,M,hT,small,hM,ready⟩:=planet G J.card (mass k J) (e+1) σ hσ
  refine ⟨t,M,hT,small,hM,?_⟩
  intro c root N live digit v y
  let Y:=family R u k h K depth N b m digit v
  have law:Wellness k Y:=Cog R.family.path.levels R.metals.O live _
    (WilsonOriginalMicroscopicVerseSeed.lawful R u k h depth digit b v simple o) simple R.alloy.B.ratio before
  have cap:0 ≤ (C*V^d*A)^J.card:=pow_nonneg (zero_le_one.trans hB) _
  obtain ⟨rain,rent,jet⟩:=ready _ (Y y J) I J y c _ (law.level' y J) root le_rfl cap
    (fun a ha r=>(learned N live 0 digit v y J a (Nat.le_of_lt_succ ha) r).access) (e+1) le_rfl
  exact ⟨rain,rent,fun a ha=>shineZ (Y y J) y rain hT jet a (Nat.lt_succ_of_le ha)⟩

end YM.Integration.WilsonReceivedBlockedVerseDocket
