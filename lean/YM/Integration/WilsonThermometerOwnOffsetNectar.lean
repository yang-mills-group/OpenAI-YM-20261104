import YM.Integration.WilsonThermometerOwnOffsetTale
import YM.RG05Readout.Many.Arrival

/-! The true one-colour input for the separated interacting history. All
adjacent prices arise from its own inverse-calibrated column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetNectar
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage
open WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetTale
open WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p k d : ℕ}

def factor (k j d : ℕ) : ℂ := (R.family.S.a k:ℂ)^d * alto R.family.path j d

def state (V : Sight R.family d p) (r : Emblems R.family d)
    (y : Palette R.family d) (z : Site (R.family.side N p)) (j : ℕ) :
    Three G (R.family.side j p) :=
  if h : k≤j ∧ j≤N then factor R k j d • moved R V r h.1 h.2 y z else 0

def location (z : Site (R.family.side N p)) (j : ℕ) : Site (R.family.side j p) :=
  if h : j≤N then site R h z else 0

def birth (x : R.family.book.Ref d) (k : ℕ) (z : Site (R.family.side N p)) :
    Config G (R.family.side N p) → ℂ := (R.family.S.a k:ℂ)^d • R.family.O N p x z

variable {D : Rail R.family} {B : ℕ→ℕ→ℝ} {V : Sight R.family d p} {r : Emblems R.family d}
    {z : Site (R.family.side N p)} (H : Enrolled R.makes D B k N p d (digits R N p z) V r)

omit H in
theorem sounds (awake : Awake D B k d) {j : ℕ} (hj : k≤j) (hn : j<N) :
    SoundDoor (R.family.path.levels.clock.op j p) (D N p j hn) := by
  obtain ⟨_,_,_,_,_,_,plot,_⟩ := (awake.toll p j N hj hn).author
  exact plot.door

include H
theorem live {j : ℕ} (hj : k≤j) (hn : j≤N) (y : Palette R.family d) :
    Useful (R.family.path.rep N p j) (state (k:=k) R V r y z j) := by
  unfold state
  rw [dif_pos ⟨hj,hn⟩]
  apply Useful.smul
  obtain ⟨v,form⟩ := (H.legal j hj hn).capacity0 (finer r hj y)
  exact View.signpost_use R.makes hn (1,false) _
    (form.useful (R.makes.wilson.represents N p j hn).good _)

theorem upper (simple : G.Simple) (hk : k≤N) (starts : ∀e≤d,R.family.ref e≤N)
    (y : Palette R.family d) {u : ℝ} (test : Cap (d+2) (line (primaryLetter d)) u) :
    Crown (R.family.path.rep N p N) (location R z N) (state (k:=k) R V r y z N)
      (‖factor R k N d‖ * (u * size (finer r hk y) *
        pricesTop (fly R.alloy.B.a) (far R.alloy.B.a) N d)) := by
  unfold state location
  rw [dif_pos (le_refl N),dif_pos (show k≤N ∧ N≤N from ⟨hk,le_rfl⟩)]
  apply Crown.sprays
  unfold moved strand
  rw [H.starts]
  exact arrives R.makes (R.again simple).1.scrim starts test _ (1,false) _ _

theorem written (hk : k≤N) (starts : ∀e≤d,R.family.ref e≤N) (y : Palette R.family d) :
    (state (k:=k) R V r y z N).1 =
      let x := (R.family.factory d N p).terminal (finer r hk y (primaryLetter d))
      fun U => ((R.family.path.rep N p N).eval U:ℂ) * birth R x k z U := by
  let t := primaryLetter d
  let o := site R (le_refl N) z
  let y' := finer r hk y
  let x := (R.family.factory d N p).terminal (finer r (le_refl N) y' t)
  let here := WilsonThermometerOffsetCylinder.address R N p N (digits R N p z) (N-N) (by omega)
  let A := ((R.family.S.a N:ℂ)^d) • R.family.O N p x here
  have seen : (V N y' (line t)).1 = dyes R.family N N p le_rfl A :=
    WilsonThermometerOffsetPrimary.primary R N p N H hk le_rfl starts t rfl y'
  let a := (R.family.S.toDepth (le_refl N) p).embed o
  have addr : here+a=z := located R N p N le_rfl z
  have movedField : A ∘ Lattice.pull 1 a = (R.family.S.a N:ℂ)^d • R.family.O N p x z := by
    funext U;change (R.family.S.a N:ℂ)^d • R.family.O N p x here (Lattice.pull 1 a U)=_
    rw [Lattice.pull_one,R.family.translation,addr];rfl
  have cov := WilsonPositionSeparatedProfileCenteredBranch.covariance R N p (le_refl N) o A
    ((R.family.continuousO ..).const_smul _)
  have movedDensity : (moved R V r hk (le_refl N) y z).1 =
      dyes R.family N N p le_rfl ((R.family.S.a N:ℂ)^d • R.family.O N p x z) :=
    (congrArg (fun f => f ∘ Lattice.pull 1 o) seen).trans
      (cov.symm.trans (congrArg (dyes R.family N N p le_rfl) movedField))
  unfold state
  rw [dif_pos (show k≤N ∧ N≤N from ⟨hk,le_rfl⟩)]
  change factor R k N d • (moved R V r hk le_rfl y z).1 = _
  rw [movedDensity, dyes, gust_base]
  have xx : x=(R.family.factory d N p).terminal (y' t) := by
    unfold x; rw [base_value,LinearEquiv.refl_apply]
  rw [←xx]
  funext U
  change factor R k N d * ((R.family.path.rep N p N).eval U * ((R.family.S.a N:ℂ)^d * R.family.O N p x z U)) =
    (R.family.path.rep N p N).eval U * ((R.family.S.a k:ℂ)^d * R.family.O N p x z U)
  unfold factor alto
  have positive : (R.family.S.a N:ℂ)^d ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne')
  field_simp

def charge (R : Run G) (r : Emblems R.family d) (y : Palette R.family d)
    {j : ℕ} (hj:k≤j) (u : ℝ) : ℝ :=
  max ‖factor R k (j+1) d‖ ‖factor R k j d‖ *
    (ld R.family.path.levels j * size (amplify d R.family (R.family.S.block j)
      (finer r (hj.trans j.le_succ) y)) * u)

theorem paid (awake : Awake D B k d) {j : ℕ} (hj : k≤j) (hn : j<N)
    (y : Palette R.family d) {u : ℝ} (test : Cap (d+2) (line (primaryLetter d)) u) :
    Ride (R.family.path.levels.clock.op j p) (location R z (j+1)) (location R z j)
      (D N p j hn) 1 (state (k:=k) R V r y z (j+1)) (state (k:=k) R V r y z j)
      (charge R r y hj u) := by
  have step := WilsonThermometerOwnOffsetTale.original R H hj hn (sounds R awake hj hn) y test
  unfold state location
  simp only [dif_pos (show j+1≤N by omega),dif_pos hn.le,dif_pos (show k≤j+1 ∧ j+1≤N by omega),
    dif_pos (show k≤j ∧ j≤N by omega)]
  apply step.matchPay
  unfold factor; rw [alto_at]; ring

end YM.Integration.WilsonThermometerOwnOffsetNectar
end
