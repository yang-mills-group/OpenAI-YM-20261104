import YM.Integration.WilsonAddressedWeakPointCells
import YM.MergeProof.West.Pamu
import YM.MergeProof.Garnet

/-! The complete displaced weak detector on the original Wilson prior and its
corresponding integrated regular and forced coarse-field presentation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakRootedReading
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Next.Rank Edition Baler Value Glyph Thirst Alarm
open Trace.Physical Push.Local
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open WilsonAddressedWeakPointCells
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p k d : ℕ}
local notation "P" => R.family.path.rep N p k
local notation "B" => WilsonThermometerOffsetLedger.cash R

variable (grades : Fin 2 → ℕ)
variable (z : Fin 2 → Site (R.family.side N p)) (y : (i:Fin 2) → Palette R.family (grades i))
  (V : (i:Fin 2) → Sight R.family (grades i) p) (r : (i:Fin 2) → Emblems R.family (grades i))
local notation "O" => WilsonThermometerOwnOffsetJoint.origins R z k
local notation "T" => (fun i=>R.family.localSection (grades i))
local notation "G0" => (fun _ : Fin 2=>(1:Signed))
local notation "F0" => (fun _ : Fin 2=>False)
local notation "Z0" => (fun _ : Fin 2=>(1:ℂ))
local notation "act" => (fun i=>state (k:=k) R (V i) (r i) (y i) (z i) k)

theorem represented {t:ℕ} (hk:k<N)
    (H : ∀ i,Enrolled R.makes R.doors B k N p (grades i) (digits R N p (z i)) (V i) (r i))
    (row : WilsonThermometerIntrinsicRoster.filed R grades z y V r (Stock.census (Fin 2)) hk.le t) :
    ∃ (X : (i:Fin 2) → Coefficient (R.family.labels.level (grades i)) (R.family.side k p)),
      ∃ fmt : ∀ i,(X i).Format 0 R.family.params (P),
      (∀ i,Germ.projection (R.family.labels.level (grades i)) R.family.params (P).p.threshold 0 (X i)=
        (y i) (primaryLetter (grades i))) ∧
      (∀ i,(X i).remBound 0 (P) (kappa R.family.path k) (B (grades i) k*size (y i))) ∧
      ∃ (base : Neat (R.family.side k p) → Burst G (R.family.side k p) (P).p.threshold),
        IsoVac (P) base (R.family.path.levels.clock.forcedAllowance k) ∧
      ∃ (ι κ:Type),∃ (_:Fintype ι) (_:Fintype κ) (A:ι→SourceAt G (O)) (K:κ→Lifted G (O) (P).p.threshold),
        Unpacks A (P).p (fun _=>radius R t k k) (P).p.supportExponent 1 ∧
        Unfold (p:=(P).p) K (fun _=>radius R t k k) (P).p.supportExponent 1 ∧
        (∀ i,2≤(A i).fires.val.card) ∧ (∀ i,2≤(K i).fires.val.card) ∧
        ∀ face : (Stock.census (Fin 2)).Mode,
        reading R grades z y r hk.le face =
        (∫ U : Config G (R.family.side k p), credsX (O) (T) X fmt (G0) (F0) base (Z0) K A U ∂prior G _).part face /
          (partition G (R.family.side N p) (R.family.beta N p) : ℂ) := by
  obtain ⟨X,fmt,proj,price,base,quiet,ι,κ,fι,fκ,A,K,pa,pk,aa,ak,posted⟩ :=
    WilsonThermometerOwnOffsetWeakRows.original R grades z y V r hk H row
  refine ⟨X,fmt,proj,price,base,quiet,ι,κ,fι,fκ,A,K,pa,pk,aa,ak,?_⟩
  intro face
  unfold reading
  rw [posted]

theorem measured (live : k ≤ N) (face : (Stock.census (Fin 2)).Mode) :
    reading R grades z y r live face = R.family.omega N p (fun U =>
      ∏ i ∈ face.val, WilsonThermometerIntrinsicRoster.source R grades z y r live i U) := by
  let joint := WilsonThermometerIntrinsicRoster.source R grades z y r live
  have hc (i : Fin 2) : Continuous (joint i) := by
    change Continuous (fun U => (R.family.S.a k : ℂ)^(grades i) • R.family.O N p _ (z i) U)
    exact (R.family.continuousO N p (grades i) _ (z i)).const_smul ((R.family.S.a k:ℂ)^(grades i))
  have hv : Continuous (R.family.path.rep N p N).eval := by
    rw [(show (R.family.path.rep N p N).eval = _ from (R.makes.wilson.starts N p).2)]
    exact bare_cont _
  let whole := Accent.birth (Stock.census (Fin 2)) (R.family.path.rep N p N) joint
  have ht : Integrable whole (prior G _) :=
    (hatCont R.family N p joint hc hv _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have products : Continuous (fun U => ∏ i ∈ face.val, joint i U) :=
    continuous_finsetProd _ (fun i _ => hc i)
  change reading R grades z y r live face = moment (R.family.beta N p) (fun U => ∏ i ∈ face.val, joint i U)
  rw [conserved,moment_formula _ _ (continuous_integrable _ products),div_eq_mul_inv,mul_comm]
  congr 1
  calc (∫ U, whole U ∂prior G _).part face = ∫ U, (whole U).part face ∂prior G _ :=
      (((Poly.get face).restrictScalars ℝ).integral_comp_comm ht).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with U
      simp only [whole,Accent.birth,Poly.part_smul,Mach,Extra.Trajectories.pass_fire]
      change ((R.family.path.rep N p N).eval U:ℂ) * _ = (bare (R.family.beta N p) U:ℂ) * _
      have start : (R.family.path.rep N p N).eval = bare (R.family.beta N p) := (R.makes.wilson.starts N p).2
      rw [start]

end YM.Integration.WilsonAddressedWeakRootedReading
