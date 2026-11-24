import YM.Integration.WilsonReflectedPublicChargedRoster
import YM.Integration.WilsonSeparatedPrefixCanonicalCarton
/-! All nonbare dates of the originally served oriented physical programme.
At an actually separated date, both new mixed inventories of this precise
programme can be amplified without altering either of its unary densities. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReflectedPublicOrientedCarton
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Marker Motion PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent RG05Readout RG05Readout.Address RG05Readout.Many
open RG05Readout.Copper RG05Readout.Pantry RG05Readout.Native RG05Readout.Records RG05Readout.Harvest
open Push.Local RG12 Push.GridApprox Bandage Extra.Multi MergeProof.Menu Next.Rank Edition Baler Value Glyph Thirst Alarm
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open WilsonThermometerReflectedTrajectory
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p k j:ℕ} {I:Type} [Fintype I] [DecidableEq I]
variable (d:I → ℕ) (z:I → Site (R.family.side N p)) (turn:I → Motion) (c:I → Site (R.family.side k p))
  (y:(i:I) → Palette R.family (d i)) (V:(i:I) → Sight R.family (d i) p)
  (r:(i:I) → Emblems R.family (d i)) (J:Census I)
local notation "P" => R.family.path.rep N p j
local notation "atRoot" => fun i:I=>point R (z i) (turn i) (c i) j
local notation "home" => WilsonThermometerOwnOffsetJoint.origins R
  (fun i=>WilsonThermometerReflectedRoster.endpoint R (z i) (turn i) (c i)) j
local notation "sng" => fun i:I=>(marked R (z i) (turn i) (c i) (V i) (r i) (y i) j).2.1
local notation "liveK" => fun i:I=>profile (P).activities (marked R (z i) (turn i) (c i) (V i) (r i) (y i) j).2.2

theorem original (start:k≤j) (deep:j<N) (t:ℕ)
    (filed:WilsonThermometerReflectedRoster.filed R d z turn c y V r J (start.trans deep.le) t)
    (wide:5 ≤ (P).p.B) (apart:∀a b:I,a≠b → (P).p.B^2 < separation (atRoot a) (atRoot b)):
    let F:=WilsonThermometerReflectedRoster.density R d z turn c y r J (start.trans deep.le) deep.le
    let w:=fun _:I=>radius R t k j
    ∃ H K, Carton atRoot H K (P).p.threshold ∧ F=restore (P) sng liveK H K ∧
      ∀ u:ℂ, ‖u‖ ≤ Real.exp (((P).p.B/8:ℕ):ℝ) →
        Served (P) sng liveK (restore (P) sng liveK
          (fun Z U=>u • H Z U) (fun b U=>u • K b U)) atRoot w ((P).p.supportExponent-1) 1 := by
  intro F w
  have roots : home = atRoot := funext fun i =>
    WilsonThermometerReflectedRoster.parent R (z i) (turn i) (c i) start deep.le
  have sale:= (filed j start deep.le).2.2
  have bank : (P).p=R.family.path.levels.budget j := (R.makes.wilson.represents N p j deep.le).vac
  change Served (P) sng liveK F home w (topPitch R.family.path N j) 1 at sale
  rw [roots,topPitch,if_neg deep.ne,←bank] at sale
  have got:=WilsonSeparatedPrefixCanonicalCarton.original (P) (o:=atRoot) (e:=(P).p.supportExponent-1)
    (δ:=1) (by simpa only [sub_add_cancel] using sale) (fun _=>radius_pos R t k j start)
    (by norm_num) wide (fun a b e=>apart a b e)
  simpa only [one_mul] using got

end YM.Integration.WilsonReflectedPublicOrientedCarton
end
