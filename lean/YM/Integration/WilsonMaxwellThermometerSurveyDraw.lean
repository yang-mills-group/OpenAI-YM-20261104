import YM.Integration.WilsonMaxwellThermometerSurveyHearth
import YM.Integration.WilsonMaxwellThermometerSurveyCohort
import YM.Integration.WilsonMaxwellThermometerSurveyRoot

/-! All registered test sites of the complete surveyed independent input hOn one
inversion. Every slot retains its own translated test, including its unit. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option warningAsError true
namespace YM.Integration.WilsonMaxwellThermometerSurveyDraw
open Function Filter Finset Lattice Wilson RG RG.Supply Precision XSpace PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonMaxwellThermometerSurveyIncome (master prices)
open WilsonMaxwellThermometerReflectedPhysicalColumns (levels)
open WilsonMaxwellThermometerReflectedInverseSection (surveyed)
open WilsonMaxwellThermometerSurveyInversion (tender raw)
open WilsonPositionProgramInvertedStencil (packet)
open WilsonPositionProgramInversionMaterial (ceiling)
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Classical BigOperators
variable {G:Gauge}{D h k u e:ℕ}(R:Run G)(W:Initialize G)(d:Fin 2→ℕ)(fit:∀j,levels j<d j)

abbrev suite (j:Fin 2):SealR G:=BayV (master W) (levels j) (d j) (fit j)
local notation "Q" => suite W d fit
local notation "L" => R.family.path.levels

theorem local_word (m M:ℕ)(X:Herit Q)(φ:Wilt Q)(y:ℝ)(c:CellR)(z:Fin 2 → Cover)(p:Period):
    let θ:=paceT R.family.S m M
    let x:=normalized L R.metals.O Q X m M
    let Y:=(fun j=>centralL L R.metals.O M m M (Q j) (x j))
    let bill:=fun j=>wheelC θ y (z j) (φ j).ψ c
    (∀j,On (levels j) (Y j)) →
      packet (W.tree p) (PowerSeries.X^ceiling R levels*∏j,flash ((locale c
        (shoe (Y j) (φ j) θ y (z j))).1 p.side))=raw R W p z (tender R d fit W X bill m M):=by
  intro θ x Y bill hOn
  apply WilsonMaxwellThermometerSurveyCohort.assembled R W p d fit z
    (fun j=>steep L R.metals.O ((Q j).ans) ((Q j).path) M m (M-m) (x j)) bill
  intro j
  exact WilsonMaxwellThermometerSurveyRoot.root R W (fit j) m M p.side θ y (z j) c (φ j) (X j) (hOn j)

private theorem wage (p:Period)(w:ℝ)(J:Ink (Woods G p.side)):
    Bare.normalized (W.tree p) G (packet (W.tree p) (PowerSeries.X^ceiling R levels*(w • J)))=
      PowerSeries.C (w:ℂ)*Bare.normalized (W.tree p) G (packet (W.tree p) (PowerSeries.X^ceiling R levels*J)):=by
  rw [WilsonPositionProgramInversionAlgebra.smul,←mul_assoc,mul_comm (PowerSeries.X^ceiling R levels) _,mul_assoc,map_mul,
    WilsonPositionProgramInversionAlgebra.scalar]
  change Bare.normalized (W.tree p) G (Bare.scalar (W.tree p) (PowerSeries.map (algebraMap ℝ ℂ) (PowerSeries.C w)) * _) = _
  rw [Bare.normalized_scalar,PowerSeries.map_C]
  rfl

def constant (φ:Wilt Q)(m M:ℕ)(X:Herit Q)(y:ℝ)(c:CellR)(p:Period):PowerSeries ℂ:=
  Bare.normalized (W.tree p) G (packet (W.tree p) (PowerSeries.X^ceiling R levels*
    flash ((locale c (HearthC Q L R.metals.O φ (normalized L R.metals.O Q X m M) m M M y)).1 p.side)))

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:prices W R.kit)(big:h<D)(rails:Rails h k u e)(cap:capP (deck (G:=G) levels d fit) ≤ k):
    ∀ᶠ f:ℕ in atTop,∀m M:ℕ,f ≤ m → m ≤ M → ∀(X:Herit Q)(φ:Wilt Q)(y:ℝ)(c:CellR)(p:Period),
      let θ:=paceT R.family.S m M
      ∀q,PowerSeries.coeff (q+ceiling R levels) (constant R W d fit φ m M X y c p)=
      ∑z∈Fintype.piFinset (fun i=>VisitsT (φ i) θ y c), (∏i,drumB (levels i) θ:ℝ) •
        PowerSeries.coeff q (surveyed R W p z (tender R d fit W X
           (fun j=>wheelC θ y (z j) (φ j).ψ c) m M)):=by
  filter_upwards [WilsonMaxwellThermometerSurveyHearth.original R simple v funded W pub big rails levels d fit cap] with f fired
  intro m M fm mM X φ y c p θ q
  obtain ⟨hOn,spread⟩:=fired (fun _=>true) m M fm mM X φ y c p.side
  unfold constant
  erw [spread,Finset.mul_sum,map_sum,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro z _
  erw [wage,local_word R W d fit m M X φ y c z p hOn,WilsonMaxwellThermometerSurveyInversion.reads,
     PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul]
  rfl

end YM.Integration.WilsonMaxwellThermometerSurveyDraw
end
