import YM.Integration.WilsonMaxwellThermometerReflectedSources
import YM.Integration.WilsonPositionProgramThermometerCoordinates

/-! The two chiral energies, signed reflection, cubic observer and missing
units use their own actual physical inverses on one nominated station.
The full numerical group coordinates can be submitted to the independent
normalized finite programme with a common before-cutoff price. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedPhysicalColumns
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price RG17 XSpace Maxwell Maxwell.Free XSpace.Normalize
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Embroider Source Source.Drops WilsonCoeffUV.Mer
open WilsonPositionProgramReportedField WilsonPositionProgramSubmittedCoordinates
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonPositionThermometerCapStation (Group index)
open WilsonMaxwellThermometerReflectedSources (lower)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}

def height:Fin 2→Fin 7:=Fin.cases 4 fun _=>6
abbrev levels (i:Fin 2):ℕ:=(height i).val
def tag (a:Axis)(b:Sec G 6)(s:Bool)(S:Finset (Fin 2))(i:Fin 2):Sec G (height i):=
  if i∈S then
    Fin.cases (motive:=fun j=>Sec G (height j)) (lower a s)
      (fun j=>by have eq:j=0:=Subsingleton.elim _ _;subst j;exact b) i
  else leaf G (height i)
def active (A:Group R.family 6)(a:Axis)(b:Sec G 6)(s:Bool)(S:Finset (Fin 2))(i:Fin 2):
    (Bel R.family.book).Field (height i):=
  A.change (height i) ((fields R.family.labels _).symm (tag a b s S i))
def atCut (A:Group R.family 6)(a:Axis)(b:Sec G 6)(s:Bool)(S:Finset (Fin 2))
    (N p:ℕ)(i:Fin 2):R.family.label (levels i):=
  A.station.wheel.atCut (N,p) (index A (height i)) (active R A a b s S i)
def currency (A:Group R.family 6)(a:Axis)(b:Sec G 6)(s:Bool)(S:Finset (Fin 2))
    (m N p:ℕ)(i:Fin 2):R.family.label (levels i):=
  entire R (levels i) m (N,p) (awake R.family (levels i) m N p (atCut R A a b s S N p i))
def issued (d:Fin 2→ℕ)(fit:∀i,levels i<d i)(A:Group R.family 6)(a:Axis)(b:Sec G 6)
    (s:Bool)(S:Finset (Fin 2))(m N p:ℕ)(phase:Fin 2→ℂ →L[ℝ] ℝ):Herit (deck (G:=G) levels d fit):=
  submitted R levels d fit (currency R A a b s S m N p) phase

theorem paid (d:Fin 2→ℕ)(fit:∀i,levels i<d i)(A:Group R.family 6)(a:Axis)(b:Sec G 6)
    (s:Bool)(S:Finset (Fin 2))(m N p:ℕ)(phase:Fin 2→ℂ →L[ℝ] ℝ)(i:Fin 2)
    (v:(R.family.labels.level (levels i)).Index):
    issued R d fit A a b s S m N p phase i (plain (R.family.labels.level (levels i)) v)=
      PowerSeries.C (phase i (currency R A a b s S m N p i v)):=
  entry R levels d fit (currency R A a b s S m N p) phase i v

theorem original (simple:G.Simple)(η:ℝ)(pos:0<η)(e:ℕ)(d:Fin 2→ℕ)(fit:∀i,levels i<d i):
    ∀ᶠ m:ℕ in atTop,∀A:Group R.family 6,A.station.k=m → A.station.checked f H A.horizon →
      ∀N p:ℕ,m<N → ∀(a:Axis)(b:Sec G 6)(s:Bool)(S:Finset (Fin 2))
      (phase:Fin 2→ℂ →L[ℝ] ℝ)(i:Fin 2),let F:=R.family.labels.level (levels i)
      fee (issued R d fit A a b s S m N p phase) e i ≤
        (Fintype.card (Alma F)*(e+1:ℕ):ℕ) * (‖phase i‖ *
          ((2:ℝ)^(univ.sup fun v:F.Index=>(F.grades v).2) *
          (R.family.path.levels.clock.hatBeta m)^η*
          (WilsonPositionThermometerStationNorm.cost R.family (levels i)*‖active R A a b s S i‖))):=by
  have funded (i:Fin 2):=WilsonPositionThermometerStationNorm.original
    (f:=f) (H:=H) simple R.makes (levels i) η pos
  filter_upwards [eventually_all.mpr funded] with m bills
  intro A date checked N p future a b s S phase i F
  have cash:=bills i A.station (index A (height i)) rfl date checked (active R A a b s S i) N p future
  have bought: F.coeffSize (currency R A a b s S m N p i) ≤
      (2:ℝ)^(univ.sup fun v:F.Index=>(F.grades v).2)*
      (R.family.path.levels.clock.hatBeta m)^η*
      (WilsonPositionThermometerStationNorm.cost R.family (levels i)*‖active R A a b s S i‖):=by
    rw [mul_assoc]
    exact (WilsonPositionProgramReportedField.purchased R (levels i) m (N,p) future.le _).trans
      (mul_le_mul_of_nonneg_left cash (by positivity))
  simpa only [issued,F,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
    (WilsonPositionProgramSubmittedCoordinates.paid R levels d fit
      (currency R A a b s S m N p) phase e i).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bought (norm_nonneg _)) (by positivity))
end YM.Integration.WilsonMaxwellThermometerReflectedPhysicalColumns
