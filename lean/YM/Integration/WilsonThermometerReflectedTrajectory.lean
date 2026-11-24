import YM.Integration.WilsonThermometerWeakTaylor
import YM.RG05Readout.Capture.Room
import YM.MergeProof.West.Lais

/-! Literal reflected copies of one compensated source on its original
hierarchy. The entire forced profile is carried with the two smooth entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerReflectedTrajectory
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p k d:ℕ}
variable (z:Site (R.family.side N p)) (s:Motion) (c:Site (R.family.side k p))

def anchorAt (j:ℕ) := Mix.camp R.family p k j c
def point (j:ℕ) := affine s.1 (anchorAt R c j) (WilsonThermometerOwnOffsetNectar.location R z j)

def marked (V:Sight R.family d p) (r:Emblems R.family d) (y:Palette R.family d) (j:ℕ) :
    Three G (R.family.side j p) :=
  if hj:k≤j ∧ j≤N then
    let π := Classical.choice ((R.makes.wilson.represents N p j hj.2).good.labels.moves s.1 (point R z s c j))
    factor R k j d • View.spin s π (WilsonThermometerOwnOffsetTale.strand R V r hj.1 y)
  else 0

variable {V:Sight R.family d p} {r:Emblems R.family d} (y:Palette R.family d)
variable (H:Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p d (digits R N p z) V r)

theorem transform {j:ℕ} (hj:k≤j) (hn:j≤N) :
    View.Signpost (R.family.path.rep N p j) s (anchorAt R c j) (state (k:=k) R V r y z j) (marked R z s c V r y j) := by
  simp only [state,marked,dif_pos (show k≤j ∧ j≤N from ⟨hj,hn⟩)]
  let y0 := WilsonThermometerOwnOffsetTale.strand R V r hj y
  let o := site R hn z
  let π := Classical.choice ((R.makes.wilson.represents N p j hn).good.labels.moves s.1 (point R z s c j))
  let ρ := Classical.choice ((R.makes.wilson.represents N p j hn).good.labels.moves 1 o)
  have place : point R z s c j=affine s.1 (anchorAt R c j) o := by
    simp only [point,WilsonThermometerOwnOffsetNectar.location,dif_pos hn,o]
  let Q := View.spin s π y0
  have direct : View.Signpost (R.family.path.rep N p j) s (affine s.1 (anchorAt R c j) o) y0 Q := by
    rw [←place]
    exact View.spin_at (P:=y0) s π
  have lower := direct.at_child (View.shift_at (π:=ρ) (P:=y0))
  have real : scalar s (factor R k j d)=factor R k j d := by
    have h : factor R k j d = (((R.family.S.a k)^d*((R.family.S.a j)^d)⁻¹:ℝ):ℂ) := by
      simp [WilsonThermometerOwnOffsetNectar.factor,alto]
    rw [h,scalar_real]
  have both := Address.signpost_scales lower (factor R k j d)
  rw [real] at both
  exact both

include H
theorem live {j:ℕ} (hj:k≤j) (hn:j≤N) :
    Useful (R.family.path.rep N p j) (marked R z s c V r y j) := by
  unfold marked
  rw [dif_pos (show k≤j ∧ j≤N from ⟨hj,hn⟩)]
  apply Useful.smul
  obtain ⟨v,form⟩ := (H.legal j hj hn).capacity0 (finer r hj y)
  exact View.signpost_use R.makes hn s _ (form.useful (R.makes.wilson.represents N p j hn).good _)

theorem upper (simple:G.Simple) (hk:k≤N) (starts:∀e≤d,R.family.ref e≤N)
    {u:ℝ} (test:Cap (d+2) (line (primaryLetter d)) u) :
    Crown (R.family.path.rep N p N) (point R z s c N) (marked R z s c V r y N)
      (‖factor R k N d‖*(u*size (finer r hk y)*pricesTop (fly R.alloy.B.a) (far R.alloy.B.a) N d)) := by
  unfold marked
  rw [dif_pos (show k≤N ∧ N≤N from ⟨hk,le_rfl⟩)]
  apply Crown.sprays
  unfold WilsonThermometerOwnOffsetTale.strand
  rw [H.starts]
  exact arrives R.makes (R.again simple).1.scrim starts test _ s _ _

theorem paid (awake : Awake (C:=R.family) R.doors (WilsonThermometerOffsetLedger.cash R) k d) {j:ℕ} (hj:k≤j) (hn:j<N)
    {u:ℝ} (test:Cap (d+2) (line (primaryLetter d)) u) :
    Ride (R.family.path.levels.clock.op j p) (point R z s c (j+1)) (point R z s c j)
      (R.doors N p j hn) 1 (marked R z s c V r y (j+1)) (marked R z s c V r y j) (charge R r y hj u) := by
  have move : anchorAt R c (j+1)=(R.family.path.levels.clock.op j p).ratio.embed (anchorAt R c j) :=
    (Work.I03.camp_step R.family p hj c).symm
  have finer := transform R z s c (V:=V) (r:=r) y (hj.trans j.le_succ) hn
  rw [move] at finer
  unfold point
  rw [move]
  exact View.paid R.makes hn (sounds R awake hj hn) (show scalar s (1:ℂ)=1 from scalar_real s 1)
    (WilsonThermometerOwnOffsetNectar.paid R H awake hj hn y test)
    (live R z s c y H (hj.trans j.le_succ) hn) (live R z s c y H hj hn.le) finer (transform R z s c y hj hn.le)

theorem written (hk:k≤N) (starts:∀e≤d,R.family.ref e≤N) :
    (marked R z s c V r y N).1 =
      fun U=> ((R.family.path.rep N p N).eval U:ℂ)* stepUp s (anchorAt R c N)
        (WilsonThermometerOwnOffsetNectar.birth R
          ((R.family.factory d N p).terminal (finer r hk y (primaryLetter d))) k z) U := by
  have moved := (transform R z s c (V:=V) (r:=r) y hk le_rfl).trade
  rw [moved,WilsonThermometerOwnOffsetNectar.written R H hk starts y]
  funext U
  unfold stepUp
  rw [scalar_mul,show ((R.family.path.rep N p N).eval (Lattice.pull s.1 (anchorAt R c N) U):ℂ)=
      ((R.family.path.rep N p N).eval U:ℂ) from vac_pull R.family.path N p N R.makes.wilson le_rfl s.1 _ U,
    scalar_real]

end YM.Integration.WilsonThermometerReflectedTrajectory
end
