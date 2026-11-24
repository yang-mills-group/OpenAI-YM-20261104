import YM.Integration.WilsonThermometerIntrinsicRoster
import YM.Integration.WilsonNeutralGradeFourTransport
import YM.Integration.WilsonPositionThermometerJointFaces

/-! Invert the measured offset circuit on the actual fitted cutoff vector.
All fields, including the sixth-order field, retain the entire cutoff column. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonNeutralOffsetCutoff
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonPositionThermometerCapStation
open WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {k N p : ℕ}
local notation "C" => R.family
local notation "d" => WilsonOriginalThermometerPalette.levels

def named (A : WilsonPositionThermometerCapStation.Group C 6) (N p : ℕ) (i : Fin 3) : R.family.book.Ref (d i) :=
  A.station.wheel.atCut (N,p) (index A (grade i)) (vector A Finset.univ i)

theorem fitted (A : WilsonPositionThermometerCapStation.Group C 6) (i : Fin 3) :
    named R A N p i = ladd C (Next.Rank.Station.mag R.family.path.levels A.station.b A.station.k)
      A.station.k N p (index A (grade i)) (A.station.R N p (index A (grade i)))
      (Further.CorrectedLift.ladder C (index A (grade i)) (vector A Finset.univ i)) := rfl

/-- The physical engineering multiplier is removed before the factory is inverted. -/
def input {h : ℕ} (r : Emblems C h) (hk : k≤N) (x : R.family.book.Ref h) : Palette C h :=
  (finer r hk).symm (Function.update 0 (primaryLetter h)
    ((R.family.factory h N p).terminal.symm (((R.family.S.a k:ℂ)^h)⁻¹ • x)))

theorem launched {h : ℕ} (r : Emblems C h) (hk : k≤N) (x : R.family.book.Ref h) :
    (R.family.factory h N p).terminal (finer r hk (input R (p:=p) r hk x) (primaryLetter h)) =
      ((R.family.S.a k:ℂ)^h)⁻¹ • x := by
  simp [input,Function.update_self]

theorem source_of_primary {h : ℕ} (r : Emblems C h) (hk : k≤N) (x : R.family.book.Ref h)
    (z : Site (R.family.side N p)) (c : ℂ) (y : Palette C h)
    (hit : (R.family.factory h N p).terminal (finer r hk y (primaryLetter h)) =
      ((R.family.S.a k:ℂ)^h)⁻¹ • x) :
    birth R ((R.family.factory h N p).terminal
      (finer r hk (c • y) (primaryLetter h))) k z =
      c • R.family.O N p x z := by
  have a : (R.family.S.a k:ℂ)^h ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos k).ne')
  have read : (R.family.factory h N p).terminal
      (finer r hk (c • y) (primaryLetter h)) =
      c • (((R.family.S.a k:ℂ)^h)⁻¹ • x) := by
    rw [map_smul,Pi.smul_apply]
    exact ((R.family.factory h N p).terminal.map_smul c _).trans
      (congrArg (c • ·) hit)
  rw [WilsonThermometerOwnOffsetNectar.birth,read,(R.family.linearO N p h z).map_smul,(R.family.linearO N p h z).map_smul]
  rw [smul_comm ((R.family.S.a k:ℂ)^h) c]
  simp only [smul_smul,mul_inv_cancel₀ a,mul_one]

theorem source {h : ℕ} (r : Emblems C h) (hk : k≤N) (x : R.family.book.Ref h)
    (z : Site (R.family.side N p)) (c : ℂ) :
    birth R ((R.family.factory h N p).terminal
      (finer r hk (c • input R (p:=p) r hk x) (primaryLetter h))) k z =
      c • R.family.O N p x z :=
  source_of_primary R r hk x z c _ (launched R (p:=p) r hk x)

def weight {h : ℕ} (v : Palette C h) : ℝ := (1+size v)⁻¹

theorem unit_budget {h : ℕ} (v : Palette C h) : 0<weight R v ∧ size ((weight R v:ℂ) • v)≤1 := by
  have pos : 0 < 1+size v := by linarith [size_ge v]
  have wpos : 0 < weight R v := inv_pos.mpr pos
  refine ⟨wpos,?_⟩
  rw [size_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos wpos]
  exact (inv_mul_le_iff₀ pos).mpr (by linarith)

local notation "radii" => WilsonThermometerOwnOffsetRadii.radius
local notation "origins" => WilsonThermometerOwnOffsetJoint.origins
local notation "entered" => WilsonThermometerOffsetLedger.cash

/-- Any calibrated upper companions whose primary is prescribed give
the identical original joint source, down to each proper face. -/
theorem whole (A : WilsonPositionThermometerCapStation.Group C 6) (hk : k≤N)
    (z : Fin 3→Site (R.family.side N p)) (r : (i:Fin 3)→Emblems C (d i))
    (y : (i:Fin 3)→Palette C (d i)) (c:Fin 3→ℂ) (names:Census (Fin 3))
    (hit : ∀ i,(R.family.factory (d i) N p).terminal (finer (r i) hk (y i) (primaryLetter (d i))) =
      ((R.family.S.a k:ℂ)^(d i))⁻¹ • named R A N p i) (j : ℕ) (hn:j≤N) :
    WilsonThermometerIntrinsicRoster.density R d z (fun i=>c i • y i) r names hk hn =
      gust R.family.path N p N (Accent.birth names (R.family.path.rep N p N)
        (fun i=>c i • R.family.O N p (named R A N p i) (z i))) j hn := by
  have eq : WilsonThermometerIntrinsicRoster.source R d z (fun i=>c i • y i) r hk =
      fun i=>c i • R.family.O N p (named R A N p i) (z i) :=
    funext fun i=>source_of_primary R (r i) hk _ (z i) (c i) (y i) (hit i)
  simp only [WilsonThermometerIntrinsicRoster.density,eq]

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) :
    ∃ t ≥ 9, ∀ᶠ k : ℕ in atTop, ∀ p N (hk:k≤N) (z:Fin 3→Site (R.family.side N p)),
      (∀ i j:Fin 3,i≠j → (R.family.path.levels.budget k).B^2 < separation (origins R z k i) (origins R z k j)) →
      ∃ (V:(i:Fin 3)→Sight C (d i) p) (r:(i:Fin 3)→Emblems C (d i)),
        (∀ i,Enrolled R.makes R.doors (entered R) k N p (d i) (digits R N p (z i)) (V i) (r i)) ∧
        ∀ (A : WilsonPositionThermometerCapStation.Group C 6) (names:Census (Fin 3)),
          let x := named R A N p
          let y := fun i=>input R (p:=p) (r i) hk (x i)
          let c := fun i=>(weight R (y i):ℂ)
          let b := fun i=>c i • y i
          WilsonThermometerIntrinsicRoster.filed R d z b V r names hk t ∧
          (∀ i, WilsonThermometerIntrinsicRoster.source R d z y r hk i=R.family.O N p (x i) (z i)) ∧
          ∀ j (hn:j≤N), WilsonThermometerIntrinsicRoster.density R d z b r names hk hn =
            gust R.family.path N p N (Accent.birth names (R.family.path.rep N p N) (fun i=>c i • R.family.O N p (x i) (z i))) j hn := by
  obtain ⟨t,ht,go⟩ := WilsonThermometerIntrinsicRoster.original R simple shop 6
  refine ⟨t,ht,?_⟩
  filter_upwards [go] with k tables p N hk z gap
  obtain ⟨V,r,paid,faces⟩ := tables p N hk (Fin 3) d (fun i=>by fin_cases i <;> decide) z gap
  refine ⟨V,r,paid,?_⟩
  intro A names x y c b
  refine ⟨faces names b (fun i=>(unit_budget R (y i)).2),?_,?_⟩
  · intro i
    unfold WilsonThermometerIntrinsicRoster.source
    dsimp only [y]
    simpa only [one_smul] using source R (r i) hk (x i) (z i) 1
  · intro j hn
    exact whole R A hk z r y c names (fun i=>launched R (p:=p) (r i) hk (x i)) j hn

end YM.Integration.WilsonNeutralOffsetCutoff
