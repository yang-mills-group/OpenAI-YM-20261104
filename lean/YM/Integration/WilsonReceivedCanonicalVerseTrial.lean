import YM.Integration.WilsonReceivedCanonicalVerseRegister
import YM.Integration.WilsonReceivedReplantedVerseTrail

/-! A whole finite socket selection is entered on the original K-blocked trial with
its full N-quiet history. Each later replant includes its scalar and all mixed
ordinary faces. Its retained widths and incomes precede the regulator limits. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalVerseTrial
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

open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonReceivedMicroscopicVerseWallet (gross)

open WilsonReceivedReplantedVerseTrail (Paid)

open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonReceivedCanonicalVerseRegister (start)
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h:I→ℕ}
variable (R:Run G)(k K:I→ℕ)(κ:(j:I) → Knob (h j))(pt:I → Chamber)

def result (e N b m:ℕ)(q:(j:I)→Choice R k j):Outerm G h:=
  WilsonReceivedReplantedVerseTrail.path R K k e N (b-m) m (start R k κ pt q)

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m ≤ b → ∃σ A:ℝ,0<σ ∧ 1 ≤ A ∧
      (∀N,b ≤ N → ∀q,Paid R k e (b-m) m (result R k K κ pt e N b m q) σ A) ∧
      (∀J:Finset I,∃t M:ℝ,0<t ∧ t ≤ σ ∧ 0 ≤ M ∧ ∀c:I,c∈J → ∀N,b ≤ N → ∀q y,
        Issued (result R k K κ pt e N b m q) k e J c y t σ M (A^J.card)) ∧
      (m<b → ∀N,b ≤ N → ∀q (a:G.ColorIndex)(x:I → Cover)(S:Finset I)(f:Pen h S →L[ℝ] ℝ)(n:Side),
        let Y:=result R k K κ pt e N b m q
        let previous:=result R k K κ pt e N b (m+1) q
        (tuftV f (levelsO (Y x) S)).1 n=WilsonMarkedFiniteIndependentHistory.moments R a tags N K
          (submit previous k e) 1 m x S f n):=by
  classical
  obtain ⟨B,hB,source⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e (s:=1) zero_lt_one
  filter_upwards [WilsonReceivedReplantedVerseTrail.original (h:=h) R simple quiet price funded K k e] with m corridor
  intro b live
  obtain ⟨σ,C,hσ,hC,fees⟩:=corridor (b-m) m le_rfl 1 zero_lt_one
  have paid (N:ℕ)(above:b ≤ N)(q:(j:I)→Choice R k j):
      Paid R k e (b-m) m (result R k K κ pt e N b m q) σ (C*B):=
    fees N (by omega) _ (source q).1 B hB (source q).2.1
  have positive:1 ≤ C*B:=one_le_mul_of_one_le_of_one_le hC hB
  refine ⟨σ,C*B,hσ,positive,paid,?_,?_⟩
  · intro J
    obtain ⟨t,M,hT,small,hM,ready⟩:=planet G J.card (mass k J) (e+1) σ hσ
    refine ⟨t,M,hT,small,hM,?_⟩
    intro c root N above q y
    let Y:=result R k K κ pt e N b m q
    have charges:=paid N above q
    obtain ⟨rain,rent,jet⟩:=ready _ (Y y J) I J y c _ (charges.1.level' y J) root le_rfl
      (pow_nonneg (zero_le_one.trans positive) _) (fun a ha r=>charges.2.1 y J a (Nat.le_of_lt_succ ha) r) (e+1) le_rfl
    exact ⟨rain,rent,fun a ha=>shineZ (Y y J) y rain hT jet a (Nat.lt_succ_of_le ha)⟩
  · intro nonbare N above q a x S f n Y previous
    obtain ⟨t,D,ht,hD,older⟩:=corridor (b-(m+1)) (m+1) (Nat.le_succ _) 1 zero_lt_one
    let initial:=start R k κ pt q
    have charged:Paid R k e (b-(m+1)) (m+1) previous t (D*B):=
      older N (by omega) initial (source q).1 B hB (source q).2.1
    have num:b-m=b-(m+1)+1:=by omega
    have expr:=WilsonReceivedReplantedVerseTrail.ordinary R simple price funded a tags K N (b-(m+1)) m
      (by omega) initial ht (one_le_mul_of_one_le_of_one_le hD hB) charged x S f n
    simpa only [Y,previous,result,num] using expr

end YM.Integration.WilsonReceivedCanonicalVerseTrial
