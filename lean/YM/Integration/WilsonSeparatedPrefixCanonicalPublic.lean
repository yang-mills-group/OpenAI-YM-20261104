import YM.Integration.WilsonSeparatedPrefixCanonicalCarton
import YM.Integration.WilsonSeparatedPrefixCanonicalSingleton
import YM.Integration.WilsonAddressedPublicGridRoster

/-! Whole basis and scalar tap on the original public reporter, on its actual
physical board and at its originally sold wallet. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalPublic
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Marker Motion PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent RG05Readout RG05Readout.Address RG05Readout.Many
open RG05Readout.Copper RG05Readout.Pantry RG05Readout.Native RG05Readout.Records RG05Readout.Harvest
open Push.Local RG12 Push.GridApprox Bandage Extra.Multi MergeProof.Menu Next.Rank Edition Baler Value Glyph Thirst Alarm
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open WilsonThermometerReflectedTrajectory
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p k:ℕ} {I:Type} [Fintype I] [DecidableEq I]
variable (d:I → ℕ) (z:I → Site (R.family.side N p)) (c:I → Site (R.family.side k p))
  (y:(i:I) → Palette R.family (d i)) (V:(i:I) → Sight R.family (d i) p)
  (r:(i:I) → Emblems R.family (d i)) (J:Census I)
local notation "P" => R.family.path.rep N p k
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "atRoot" => fun i:I=>point R (z i) (1,false) (c i) k
local notation "s0" => fun _:I=>(1,false)
local notation "home" => WilsonThermometerOwnOffsetJoint.origins R (fun i=>WilsonThermometerReflectedRoster.endpoint R (z i) (1,false) (c i)) k
local notation "soft" => fun i:I=> (marked R (z i) (1,false) (c i) (V i) (r i) (y i) k).2.1
local notation "forced" => fun i:I=>profile (P).activities (marked R (z i) (1,false) (c i) (V i) (r i) (y i) k).2.2

theorem original (deep:k<N) (t:ℕ)
    (hi:∀i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i))
    (entered:WilsonThermometerReflectedRoster.filed R d z s0 c y V r J deep.le t)
    (wide:5 ≤ (P).p.B)
    (apart:∀i j:I,i≠j → (P).p.B^2 < separation (atRoot i) (atRoot j)):
    let F:=WilsonThermometerReflectedRoster.density R d z s0 c y r J deep.le deep.le
    let w:=fun _:I=>radius R t k k
    ∃ q:(i:I) → Coefficient (R.family.labels.level (d i)) (R.family.side k p),
      (∀i,(q i).Format (atRoot i) R.family.params (P)) ∧
      (∀i,(q i).remBound (atRoot i) (P) (kappa R.family.path k) (B (d i) k*size (y i))) ∧
      (∀i,Germ.projection (R.family.labels.level (d i)) R.family.params (P).p.threshold
          (atRoot i) (q i)=y i (primaryLetter (d i))) ∧
      (∀i,soft i=(q i).exponentialEntry (atRoot i) (R.family.localSection (d i)) (P)) ∧
      (∀i,forced i=profile (P).activities (q i).forced) ∧
      ∃H K, Carton atRoot H K (P).p.threshold ∧ F=restore (P) soft forced H K ∧
        ∀u:ℂ, ‖u‖ ≤ Real.exp (((P).p.B/8:ℕ):ℝ) →
        Served (P) soft forced (restore (P) soft forced (fun Z U=>u • H Z U) (fun b U=>u • K b U))
          atRoot w ((P).p.supportExponent-1) 1 := by
  intro F w
  choose x good fee proj _tab rays using fun i=> WilsonThermometerWeakReflectedRows.master R (z i) deep.le (y i) (hi i)
  let mv i:=Tour.placard R.family R.makes N p deep.le (atRoot i)
  let q i:=Drift.stamp (atRoot i) (mv i) (x i)
  have mounted i := WilsonSeparatedPrefixCanonicalSingleton.original (R.family.localSection (d i)) (atRoot i) (mv i)
    (x i) (rays i (1,false) (c i)) (good i) (fee i)
  refine ⟨q,fun i=>(mounted i).1,fun i=>(mounted i).2.1,?_,fun i=>(mounted i).2.2.1,fun i=>(mounted i).2.2.2,?_⟩
  · intro i
    rw [←proj i]
    simpa only [zero_add] using WilsonOriginalNullRelocation.page (R.family.labels.level (d i)) R.family.params
      (P).p.threshold 0 (atRoot i) (mv i) (x i)
  · have site : home=atRoot := funext fun i=>WilsonThermometerReflectedRoster.parent R (z i) (1,false) (c i) le_rfl deep.le
    have sale:= (entered k le_rfl deep.le).2.2
    have board: (P).p=R.family.path.levels.budget k := (R.makes.wilson.represents N p k deep.le).vac
    change Served (P) soft forced F home w (topPitch R.family.path N k) 1 at sale
    rw [site,topPitch,if_neg deep.ne,←board] at sale
    have sol:=WilsonSeparatedPrefixCanonicalCarton.original (P) (o:=atRoot) (e:=(P).p.supportExponent-1)
      (δ:=1) (by simpa only [sub_add_cancel] using sale) (fun _=>radius_pos R t k k le_rfl)
      (by norm_num) wide (fun i j e=>apart i j e)
    simpa only [one_mul] using sol

end YM.Integration.WilsonSeparatedPrefixCanonicalPublic
end
