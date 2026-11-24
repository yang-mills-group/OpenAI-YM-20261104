import YM.Integration.WilsonReceivedCanonicalVerseHearing
import YM.Integration.WilsonReceivedCanonicalVersePosterior
/-! A whole finite socket selection is entered on the original K-blocked trial with
its full N-quiet history. Each later replant includes its scalar and all mixed
ordinary faces. Its retained widths and incomes precede the regulator limits. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalVerseWeighted
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

open WilsonReceivedCanonicalVerseTrial (result)
open WilsonMarkedOrdinaryCaptureGap (tariff)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open WilsonReceivedCanonicalVerseHearing (fee)

def full {S:Finset I}(q:Selection R k S)(j:I):Choice R k j:=if hj:j∈S then q ⟨j,hj⟩ else .inl ()

omit [Fintype I] in
theorem chosen {S:Finset I}(q:Selection R k S)(j:S):full R k q j=q j:=by simp [full]

def wick (u:G.ColorIndex)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (N b m:ℕ)(y:I → Cover)(S:Finset I)(f:Pen h S →L[ℝ] ℝ)(n:Side)(a r:ℕ)(x:Fin r → YForest G)
    (q:Selection R k S):ℂ:=
  ↑(WilsonMarkedFiniteIndependentHistory.moments R u tags N K (start R k κ pt (full R k q))
    (b-m) m y S f n a r (slideC n x))

def filed (e N b m:ℕ)(y:I → Cover)(S:Finset I)(f:Pen h S →L[ℝ] ℝ)(n:Side)(a r:ℕ)(x:Fin r → YForest G)
    (q:Selection R k S):ℂ:=
  let Z:=result R k K κ pt e N b m (full R k q)
  ↑(f ((levelsO (submit Z k e y) S).1 n a r (slideC n x)))

def Measured (e N p b m:ℕ)(σ t A B:ℝ)(v:(j:I)→R.family.label (k j))(M:I→ℝ)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices):Prop:=
  ∀(u:G.ColorIndex)(y:I → Cover)(S:Finset I)(f:Pen h S→L[ℝ]ℝ)(a:ℕ),a ≤ e → ∀(r:ℕ)(x:Fin r → YForest G)
     (c:Cover)(D:ℕ),(∀j∈S,terrain.gap c (y j) ≤ D) → (∀i,terrain.gap c (x i).1 ≤ D) → 8*D < (R.family.side m p).val →
  let w:=weight R k N p b v S
  let n:=R.family.side m p
  ‖(∑q,w q*wick R k K κ pt u tags N b m y S f n a r x q) -
    (∑q,w q*filed R k K κ pt e N b m y S f n a r x q)‖ ≤
    wallet R k M S*(‖f‖*fee (h:=h) e r S n σ t A B)

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m ≤ b → ∃σ t A B:ℝ,0<σ ∧ 0<t ∧ 1 ≤ A ∧ 1 ≤ B ∧
    ∀N,b ≤ N → ∀p (v:(j:I)→R.family.label (k j))(M:I→ℝ),(∀j,(R.family.labels.level (k j)).coeffSize (v j) ≤ M j) →
    Measured R k K κ pt e N p b m σ t A B v M tags:=by
  filter_upwards [WilsonReceivedCanonicalVerseHearing.original R k K κ pt simple quiet tags price funded e] with m offers
  intro b geo
  obtain ⟨σ,t,A,B,hσ,ht,hA,hB,paid⟩:=offers b geo
  refine ⟨σ,t,A,B,hσ,ht,hA,hB,?_⟩
  intro N high p v M cash u y S f a ha r x c D loc hull fits w n
  have nn:0 ≤ fee (h:=h) e r S n σ t A B:=by
    unfold fee
    apply add_nonneg <;> apply mul_nonneg
    · exact mul_nonneg (WilsonMarkedOrdinaryCaptureGap.positive ..) (pow_nonneg (zero_le_one.trans hA) _)
    · exact catch_hot ..
    · exact mul_nonneg (WilsonMarkedOrdinaryCaptureGap.positive ..) (pow_nonneg (zero_le_one.trans hB) _)
    · exact catch_hot ..
  apply WilsonReceivedCanonicalVersePortfolio.signed R k N p b high v S M (fun j _=>cash j)
    (wick R k K κ pt u tags N b m y S f n a r x) (filed R k K κ pt e N b m y S f n a r x) (mul_nonneg (norm_nonneg f) nn)
  intro q
  have bound:=paid N high p (full R k q) u y S f a ha r x c D loc hull fits
  simpa only [wick,filed,←Complex.ofReal_sub,Complex.norm_real] using bound

end YM.Integration.WilsonReceivedCanonicalVerseWeighted
