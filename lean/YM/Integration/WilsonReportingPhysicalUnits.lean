import YM.Integration.WilsonReportingLowRoster
import YM.RG17.Gathers
import YM.PhysMS.Frame.Measured

/-! A fixed unit coefficient has an explicit preimage on the original reporting
layout. Its returned palette is bounded uniformly over all upper cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPhysicalUnits
open Function Filter Lattice Wilson RG Source Labels RG12 RG17 RG05Readout Address
open Trace.Pilot Extraction Spec Next.Extract OPE OPE.Orbits PhysMS Climb WilsonReportingUnitOrbit
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {F:Final C f S}

def entry (L:Layout F) (d:ℕ) (r:ℝ) (z:ℂ) : C.label d :=
  (L.shift d r).symm (z • (C.labels.level d).e0)

theorem physical (L:Layout F) (d:ℕ) (r:ℝ) (age:C.ref d ≤ L.level r) (z:ℂ) :
    master L d r (entry L d r z) = z • S.unit d := by
  letI:L.lens.NeBot:=L.notbot
  have read:=congrArg (S.project d) (L.observes.unit d (L.level r) age)
  have unit:engineering (S:=S) L.charts d (L.level r) (C.labels.level d).e0 = S.unit d := by
    rw [engineering_at]
    change _ = S.project d (C.refUnit d)
    simpa only [unitVec,map_smul,Complex.ofReal_pow] using read
  change engineering L.charts d (L.level r) (L.shift d r ((L.shift d r).symm _)) = _
  rw [LinearEquiv.apply_symm_apply,map_smul,unit]

def price (C:Family G) (d:ℕ) (z:ℂ) : ℝ := ‖phase*z‖/‖phase‖*WilsonReportingUnitPrice.bound C d

theorem paid (L:Layout F) {b d N p:ℕ} (r:ℝ) (z:ℂ) {D:Rail C} {B:ℕ→ℕ→ℝ}
    {V:Sight C d p} {U:Emblems C d} (spine:Spine D B F.room.cutoff b p d N V U)
    (start:b ≤ L.level r) (age:∀i≤d,C.ref i ≤ L.level r) (live:L.level r ≤ N) :
    size (WilsonReportingUpperChartPrice.returned F.room.cutoff (primary d)
      (phase • L.shift d r (entry L d r z)) U (L.level r) N p) ≤ price C d z := by
  let x:C.label d:=phase • (z • (C.labels.level d).e0)
  have atzero:x 0=phase*z := by
    simp only [x,Pi.smul_apply,smul_eq_mul,Frame.e0,Pi.single_eq_same,mul_one]
  have scalar:WilsonReportingPrescribedUnit.scalar C d x=x := by
    rw [WilsonReportingPrescribedUnit.scalar,atzero,mul_smul]
  have fee:=WilsonReportingPrescribedUnit.paid F.room.cutoff spine x start age live
  rw [scalar,atzero] at fee
  simpa only [entry,x,price,LinearEquiv.apply_symm_apply] using fee

theorem generated (simple:G.Simple) {d:ℕ} (low:d<4) (v:Free C d) :
    ∃ z:ℂ, v=z • (Bel C.book).unit d := by
  obtain ⟨x,hx⟩: ∃ x:C.label d,(Bel C.book).project d x=v := (Bel C.book).onto d v
  have unit:(Bel C.book).unit d=(Bel C.book).project d (C.labels.level d).e0 := by
    change (Bel C.book).project d (((1:ℂ)^d) • (C.labels.level d).e0)=_
    rw [one_pow,one_smul]
  have scaled:x=x 0 • (C.labels.level d).e0 := (WilsonReportingLowRoster.whole simple low x).symm
  refine ⟨x 0,?_⟩
  rw [←hx,unit,←map_smul]
  exact congrArg ((Bel C.book).project d) scaled

theorem original (simple:G.Simple) (L:Layout F) (growing:Tendsto L.level trail atTop)
    {J:ℝ→tower S} (leading:Leading F J) {ι:Type} [Fintype ι] (d:ι→ℕ) (low:∀i,d i<4)
    (v:(i:ι)→Free C (d i)) :
    ∃ z:ι→ℂ, ∀ᶠ r in trail, ∀i, let m:=L.level r
      master L (d i) r (entry L (d i) r (z i))=J r (d i) (v i) ∧
      ∀ {b N p:ℕ} {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C (d i) p} {U:Emblems C (d i)},
      Spine D B F.room.cutoff b p (d i) N V U → b ≤ m → m ≤ N →
      size (WilsonReportingUpperChartPrice.returned F.room.cutoff (primary (d i))
        (phase • L.shift (d i) r (entry L (d i) r (z i))) U m N p) ≤ C.path.levels.clock.hatBeta m := by
  choose z coefficient using fun i:ι=>generated simple (low i) (v i)
  refine ⟨z,?_⟩
  have clock := (Next.Rank.Station.hat_rate C.path.levels simple).comp growing
  have ages := Filter.eventually_all.mpr (fun i:ι=>growing.eventually_ge_atTop ((Finset.Iic (d i)).sup C.ref))
  have fees := Filter.eventually_all.mpr (fun i:ι=>clock.eventually_ge_atTop (price C (d i) (z i)))
  filter_upwards [ages,fees,Filter.eventually_all.mpr (fun i:ι=>leading.unit (d i))] with r old funded units
  intro i m
  have age : ∀ e ≤ d i, C.ref e ≤ m := fun e he=>(Finset.le_sup (f:=C.ref) (Finset.mem_Iic.mpr he)).trans (old i)
  refine ⟨?_,fun spine start live=>(paid L r (z i) spine start age live).trans (funded i)⟩
  rw [physical L _ r (age _ le_rfl),coefficient i,map_smul,units i]

end YM.Integration.WilsonReportingPhysicalUnits
