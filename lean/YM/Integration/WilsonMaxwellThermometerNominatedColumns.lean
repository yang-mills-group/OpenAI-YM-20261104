import YM.Integration.WilsonMaxwellThermometerNominatedPupils
import YM.Integration.WilsonAddressedAlignedColumn
import YM.Integration.WilsonThermometerAlignedCells

/-! The cubic is based at the translated common origin. Its full measured
preimage and the two displaced companions are filed on the same Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedColumns
open Filter Lattice Wilson Labels RG Source Extra.Histories PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records Trace.Physical.GermGraph
open RG17 Climb Trace.Pilot Table Spec MergeProof Accent Extra.Multi Menu
open Marker Trace.Physical Next.Rank RG12 ProjectorNext.Equivariance
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonNeutralOffsetCutoff
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "d" => WilsonOriginalThermometerPalette.levels
local notation "C" => R.family
local notation "origins" => WilsonThermometerOwnOffsetJoint.origins
local notation "entry" => WilsonThermometerOffsetLedger.cash
local notation "atOrigin" => WilsonThermometerAlignedCells.atOrigin

def label {k N p:ℕ} {j:Fin 3} (r:Emblems C (d j)) (hk:k≤N) (y:Palette C (d j)) : (C).label (d j) :=
  (((C).S.a k:ℂ)^(d j)) • ((C).factory (d j) N p).terminal (finer r hk y (primaryLetter (d j)))

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) :
    ∃ t≥9,∀ᶠ k:ℕ in atTop,∀ p N (hk:k≤N)
      (o:Site ((C).side N p)×Site ((C).side N p)),
      let z:=atOrigin o
      (∀ i j:Fin 3,i≠j → ((C).path.levels.budget k).B^2 < separation (origins R z k i) (origins R z k j)) →
      ∃ (V:(i:Fin 3)→Sight C (d i) p) (r:(i:Fin 3)→Emblems C (d i)),
        (∀i,Enrolled R.makes R.doors (entry R) k N p (d i) (digits R N p (z i)) (V i) (r i)) ∧
        ∀(A:WilsonPositionThermometerCapStation.Group C 6)
          (low:(i:Fin 3)→Palette C (d i)),
        (∀i:Fin 3,i≠0→label R (j:=i) (p:=p) (r i) hk (low i)=named R A N p i) →
        ∃ y:(i:Fin 3)→Palette C (d i),
          size (y 0)≤2*((C).labels.level 6).coeffSize (Price.awake C 6 k N p (named R A N p 0)) ∧
          (∀i:Fin 3,i≠0→y i=low i) ∧ (∀i, label R (j:=i) (p:=p) (r i) hk (y i)=named R A N p i) ∧
          ∀ names:Census (Fin 3),
            let c:=fun i:Fin 3=>(weight R (y i):ℂ)
            let wallet:=fun i:Fin 3=>c i • y i
            WilsonThermometerIntrinsicRoster.filed R d z wallet V r names hk t ∧
            ∀ j (hn:j≤N),WilsonThermometerIntrinsicRoster.density R d z wallet r names hk hn=
              gust (C).path N p N (Accent.birth names ((C).path.rep N p N)
                (fun i=>c i • (C).O N p (named R A N p i) (z i))) j hn := by
  obtain ⟨t,ht,school⟩:=WilsonThermometerIntrinsicRoster.original R simple shop 6
  refine ⟨t,ht,?_⟩
  filter_upwards [school,open_late C simple 6,eventually_ge_atTop ((Finset.range 7).sup ((C).ref))]
    with k course opened starts p N hk o z gap
  obtain ⟨V,r,enrolled,funds⟩:=course p N hk (Fin 3) d (fun i=>by fin_cases i <;> decide) z gap
  refine ⟨V,r,enrolled,?_⟩
  intro A low solved
  let first:=WilsonAddressedAlignedColumn.offer R (named R A N p 0) (opened p) hk
  let y:=Function.update low 0 first
  have grades:∀e≤6,(C).ref e≤N:=fun e he=>
    (Finset.le_sup (s:=Finset.range 7) (f:=(C).ref) (Finset.mem_range.mpr (by omega : e<7))).trans (starts.trans hk)
  have origin:digits R N p (z 0)=digits R N p 0:=rfl
  have good:=enrolled 0
  rw [origin] at good
  obtain ⟨upper,rent⟩:=WilsonAddressedAlignedColumn.original R good hk le_rfl grades (opened p) (named R A N p 0)
  have rest (i:Fin 3) (hi:i≠0):y i=low i:=Function.update_of_ne hi first low
  have exactSource (i:Fin 3) : label R (j:=i) (p:=p) (r i) hk (y i)=named R A N p i := by
    by_cases hi:i=0
    · subst i;rw [show y 0=first from Function.update_self ..];exact upper
    · rw [rest i hi];exact solved i hi
  refine ⟨y,?_,rest,exactSource,?_⟩
  · rw [show y 0=first from Function.update_self ..];exact rent
  intro names c wallet
  refine ⟨funds names wallet (fun i=>(unit_budget R (y i)).2),?_⟩
  intro j hn
  apply whole R A hk z r y c names _ j hn
  intro i
  let a:ℂ:=((C).S.a k:ℂ)^(d i)
  have nonzero:a≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ((C).S.a_pos k).ne')
  have restore:=congrArg (a⁻¹ • ·) (exactSource i)
  simpa only [label,←show a=((C).S.a k:ℂ)^(d i) from rfl,smul_smul,inv_mul_cancel₀ nonzero,one_smul] using restore

end YM.Integration.WilsonMaxwellThermometerNominatedColumns
