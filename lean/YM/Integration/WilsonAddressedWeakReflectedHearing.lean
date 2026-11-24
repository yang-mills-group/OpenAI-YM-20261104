import YM.Integration.WilsonAddressedWeakCompensatedHearing
import YM.Integration.WilsonThermometerWeakReflectedRows

/-! The finite corrected rank observations on the actual reflected group fields and mixed activity gallery. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakReflectedHearing
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Next.Rank Edition Baler Value Glyph Thirst Alarm
open Trace.Physical Push.Local
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open WilsonThermometerReflectedTrajectory Push.Corrected
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) {χ k N p:ℕ} (gr:χ≤k) (hk:k<N)
local notation "P" => R.family.path.rep N p k
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "T" => Cells.center R.family.S p (gr.trans hk.le) 0
local notation "J0" => Site (R.family.side χ p)
local notation "JJ" => Site (R.family.side χ p) × Fin 2
local notation "Γ" => Stock.census (JJ)
local notation "Z0" => (fun _ : JJ => (1:ℂ))

def motion (i:JJ) : Motion := ((T).omega i.1,decide ((T).hand i.1))
def anchor (i:JJ) := (R.family.S.toDepth gr p).embed i.1
variable (d:Fin 2→ℕ) (z:Fin 2→Site (R.family.side N p)) (y:(i:Fin 2)→Palette R.family (d i))
  (V:(i:Fin 2)→Sight R.family (d i) p) (r:(i:Fin 2)→Emblems R.family (d i))
def origins := WilsonThermometerOwnOffsetJoint.origins R
  (fun i:JJ=>WilsonThermometerReflectedRoster.endpoint R (z i.2) (motion R gr hk i) (anchor R gr i)) k
local notation "O" => origins R gr hk z

/-- The same fitted base coefficients and mixed signed galleries supply every independent scalar subtraction and every packed mode. -/
theorem original (t:ℕ)
    (H:∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i))
    (post:WilsonThermometerReflectedRoster.filed R (fun i:JJ=>d i.2) (fun i=>z i.2)
      (motion R gr hk) (anchor R gr) (fun i:JJ=>y i.2) (fun i=>V i.2) (fun i=>r i.2) Γ hk.le t) :
    ∃ X : (i : Fin 2) → Coefficient (R.family.labels.level (d i)) (R.family.side k p),
      ∃ fmt:∀ i,(X i).Format 0 R.family.params (P),
      (∀ i,Germ.projection (R.family.labels.level (d i)) R.family.params (P).p.threshold 0 (X i)=y i (primaryLetter (d i))) ∧
      (∀ i,(X i).remBound 0 (P) (kappa R.family.path k) (B (d i) k*size (y i))) ∧
      (∀ i,V i k (y i) (line (primaryLetter (d i)))=invoice (X i) 0 (R.family.localSection (d i)) (P)) ∧
      ∃ (vac:Neat (R.family.side k p)→Burst G (R.family.side k p) (P).p.threshold),
      IsoVac (P) vac (R.family.path.levels.clock.forcedAllowance k) ∧
      ∃ (ι κ:Type),∃ (_:Fintype ι) (_:Fintype κ) (A:ι→SourceAt G O) (K:κ→Lifted G O (P).p.threshold),
      Unpacks A (P).p (fun _=>radius R t k k) (P).p.supportExponent 1 ∧
      Unfold (p:=(P).p) K (fun _=>radius R t k k) (P).p.supportExponent 1 ∧
      (∀ i,2≤(A i).fires.val.card) ∧ (∀ i,2≤(K i).fires.val.card) ∧
      ∀ (a:Fin 2→ℂ) (q:ℂ) (s:Finset (Fin 2)),
        let L:=Poly.pass (-WilsonAddressedWeakPackedCertificate.cumulant a q)
        let C : Marker.Poly Γ :=∏ i:J0,Marks.into (Marks.atHand T i L) i
        let Xall:=credsX O (fun i:JJ=>R.family.localSection (d i.2)) (fun i=>X i.2) (fun i=>fmt i.2)
          (fun i=>(motion R gr hk i).1) (fun i=>(motion R gr hk i).2) vac Z0 K A
        WilsonAddressedWeakCompensatedHearing.report R gr hk.le d z y r a q hk.le s =
          (∫ U,Marks.part (C*Xall U) (Marks.packed T s) ∂prior G _)/(partition G (R.family.side N p) (R.family.beta N p):ℂ) := by
  obtain ⟨X,fmt,hx,price,term,rows⟩ := WilsonThermometerWeakReflectedRows.original R d z y V r (I:=JJ) hk H
  obtain ⟨vac,hv,ι,κ,fi,fk,A,K,ha,haK,ma,mk,eqn⟩ :=
    rows (fun i:JJ=>i.2) (motion R gr hk) (anchor R gr) t post
  refine ⟨X,fmt,hx,price,term,vac,hv,ι,κ,fi,fk,A,K,ha,haK,ma,mk,?_⟩
  intro a q s
  dsimp only
  unfold WilsonAddressedWeakCompensatedHearing.report
  congr 1
  apply integral_congr_ae
  filter_upwards [] with U
  exact congrArg (fun f=>Marks.part ((∏ i:J0,Marks.into (Marks.atHand T i
    (Poly.pass (-WilsonAddressedWeakPackedCertificate.cumulant a q))) i)*f U) (Marks.packed T s)) eqn

end YM.Integration.WilsonAddressedWeakReflectedHearing
