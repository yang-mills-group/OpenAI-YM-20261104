import YM.Integration.WilsonOriginalMicroscopicSeedHead
import YM.Integration.WilsonReceivedDatedVerseReprint
import YM.Integration.WilsonOriginalMicroscopicVerseSeed

/-! Original bare marked winding income on all physical periods and for the entire joint roster. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedMicroscopicVerseWallet
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

variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I]

def tariff (G:Gauge)(r:ℕ)(s:ℝ) := priceM (Hooks G) r s+tiePay (Hooks G) r (s/4)+1

def gross (G:Gauge)(l:ℕ)(s A:ℝ) :=
  (1+∑r:Fin (l+1),|tariff G r.val s|)*max 1 A

theorem one (G:Gauge)(l:ℕ)(s A:ℝ):1 ≤ gross G l s A:=
  one_le_mul_of_one_le_of_one_le (by linarith [Finset.sum_nonneg (s:=Finset.univ) (fun (u:Fin (l+1)) _=>abs_nonneg (tariff G u.val s))]) (le_max_left _ _)

theorem buys (G:Gauge){r l:ℕ}(within:r ≤ l)(s:ℝ){A:ℝ}(pos:0 ≤ A):
    tariff G r s*A ≤ gross G l s A:=by
  let z:Fin (l+1):=⟨r,Nat.lt_succ_of_le within⟩
  have p:|tariff G r s| ≤ ∑u:Fin (l+1),|tariff G u.val s|:=
    Finset.single_le_sum (fun t _=>abs_nonneg (tariff G t.val s)) (mem_univ z)
  apply mul_le_mul ((le_abs_self _).trans (p.trans (by linarith))) (le_max_right 1 A) pos
  positivity

omit [DecidableEq I] in
theorem original (R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (u:I → G.ColorIndex){k h:I → ℕ}(depth:∀s,k s<h s)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠN:ℕ in atTop,∀(digit:I → ∀j,Site (R.family.S.block j))(v:∀s,Letter (R.family.labels.level (k s))),
      let s:=width R N
      let A:=(R.family.path.levels.clock.hatBeta N)^η*WilsonPointChildCenteredPortfolio.cap h
      let Y:=WilsonOriginalMicroscopicVerseSeed.seed R u k h depth digit N v
      0<s/32 ∧ 1 ≤ gross G (mass k univ+e) s A ∧
      ∀n:Side,PairedAt e Y n (s/32) (gross G (mass k univ+e) s A):=by
  classical
  have income:=WilsonPointChildCenteredPortfolio.original R simple booked u depth o tags price funded e pos
  filter_upwards [income,(WardBin.bell R.family.path.levels simple).eventually_ge_atTop 1] with N row clock
  intro digit v s A Y
  have ws:0<s:=(Primer.FamilyWindow R.family).pos _
  have positive:0 ≤ A:=mul_nonneg (Real.rpow_nonneg (zero_le_one.trans clock) _) (WilsonPointChildCenteredPortfolio.cap_nonneg h)
  have legal:=WilsonOriginalMicroscopicVerseSeed.lawful R u k h depth digit N v simple o
  refine ⟨by positivity,one _ _ _ _,?_⟩
  intro n y S a ha r
  let Z (c:I):=WilsonPointChildCenteredFunctional.seat R (u c) (k c) h c (depth c) (digit c) N N (v c) (y c)
  have booking:Y y=WilsonPointChildPlacedFamily.roster Z:=rfl
  have enough:0 ≤ gross G (mass k univ+e) s A:=zero_le_one.trans (one _ _ _ _)
  by_cases single:S.card=1
  · obtain ⟨c,rfl⟩:=card_eq_one.mp single
    rw [card_singleton,pow_one]
    by_cases within:r ≤ mass k univ+e
    · have exactHead:(Y y {c}).1 n a r=plume ((Y y {c}).2 a r) n:=by
        rw [booking,WilsonPointChildPlacedFamily.singleton]
        funext x
        exact WilsonOriginalMicroscopicSeedHead.original R simple o (u c) (k c) h c (depth c) (digit c) N (v c) (y c) n a r x
      rw [exactHead]
      have bill:=row N le_rfl digit v y {c} s le_rfl {c} (subset_refl _) a ha r
      rw [card_singleton,pow_one] at bill
      exact (plumeW bill (singleton_nonempty c) ws).more (buys G within s positive)
    · have sub:mass k {c} ≤ mass k univ:=by unfold mass; exact sum_le_sum_of_subset (subset_univ _)
      have high:mass k {c}+a < r:=by omega
      rw [(legal.level' y {c}).span n a r high,(legal.level' y {c}).coverN a r high]
      exact MarkU.zero.more enough
  · have absent:Y y S=0:=by rw [booking,WilsonPointChildPlacedFamily.other Z single]
    rw [absent]
    exact MarkU.zero.more (pow_nonneg enough _)

end YM.Integration.WilsonReceivedMicroscopicVerseWallet
