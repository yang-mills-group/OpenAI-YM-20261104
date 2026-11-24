import YM.Integration.WilsonThermometerOwnOffsetColumn
import YM.RG05Readout.Many.View

/-! One original joint-history receipt at the actual successive ancestors of the
microscopic source. The retained wing set carries both hard profiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetTale
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper
open PhysicalNext.Repeat.Legato MergeProof Accent Motion
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p k d : ℕ}

def site {j : ℕ} (hj : j≤N) (z : Site (R.family.side N p)) : Site (R.family.side j p) :=
  (R.family.S.toDepth hj p).parent z

theorem adjacent {j : ℕ} (hj : j<N) (z : Site (R.family.side N p)) :
    (R.family.path.levels.clock.op j p).ratio.embed (site R hj.le z) +
      child R.family p j (digits R N p z j) = site R hj z := by
  let K := (R.family.path.levels.clock.op j p).ratio
  have nested : site R hj.le z = K.parent (site R hj z) :=
    Next.Rank.Station.parent_nested K _ _ (R.family.S.block_odd _)
      (R.family.S.toDepth_odd hj p) z
  have residue : digits R N p z j = K.residue (site R hj z) := by
    unfold digits; rw [dif_pos (show j+1≤N by omega)]; rfl
  have centered : child R.family p j (digits R N p z j) =
      Lattice.wrap _ (lift (K.residue (site R hj z))) := by
    rw [residue]
    change K.embed 0+_=_
    rw [show K.embed 0=0 from K.root.map_zero,zero_add]
  rw [centered,nested]
  exact K.unpack_at _

def strand (V : Sight R.family d p) (r : Emblems R.family d)
    {j : ℕ} (hj : k≤j) (y : Palette R.family d) : Three G (R.family.side j p) :=
  V j (finer r hj y) (line (primaryLetter d))

def moved (V : Sight R.family d p) (r : Emblems R.family d)
    {j : ℕ} (hj : k≤j) (hn : j≤N) (y : Palette R.family d)
    (z : Site (R.family.side N p)) : Three G (R.family.side j p) :=
  let o := site R hn z
  let π := Classical.choice ((R.makes.wilson.represents N p j hn).good.labels.moves 1 o)
  shiftTape o π (strand R V r hj y)

theorem original {D : Rail R.family} {B : ℕ→ℕ→ℝ}
    {V : Sight R.family d p} {r : Emblems R.family d} {z : Site (R.family.side N p)}
    (H : Enrolled R.makes D B k N p d (digits R N p z) V r)
    {j : ℕ} (hj : k≤j) (hn : j<N) (sound : SoundDoor (R.family.path.levels.clock.op j p) (D N p j hn))
    (y : Palette R.family d) {u : ℝ} (test : Cap (d+2) (line (primaryLetter d)) u) :
    let L := R.family.S.block j
    let x := finer r (hj.trans j.le_succ) y
    Ride (R.family.path.levels.clock.op j p) (site R hn z) (site R hn.le z)
      (D N p j hn) ((L.val:ℂ)^d)
      (moved R V r (hj.trans j.le_succ) hn y z) (moved R V r hj hn.le y z)
      (ld R.family.path.levels j * size (amplify d R.family L x) * u) := by
  intro L x
  let b := digits R N p z j
  let c := child R.family p j b
  let t := primaryLetter d
  let A := strand R V r (hj.trans j.le_succ) y
  let E := strand R V r hj y
  have fixed : headFee R.family p j b (line t)=line t := by
    have h := WilsonThermometerOffsetPrimary.tested R p j (digits R N p z) t rfl 1
    exact h
  have route : (r j) x = finer r hj y := by
    unfold x; rw [finer_next hj,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  have ride := (H.follows j hj hn).travel x (line t) u test
  change Ride _ c 0 _ _ (shiftTape c (keys0 R.makes hn b) (V (j+1) x (headFee R.family p j b (line t)))) (V j (r j x) (line t)) _ at ride
  rw [route,fixed] at ride
  have front : Useful (R.family.path.rep N p (j+1)) A := by
    obtain ⟨v,form⟩ := (H.legal (j+1) (hj.trans j.le_succ) hn).capacity0 x
    exact form.useful (R.makes.wilson.represents N p (j+1) hn).good _
  have take (a : ℕ) (h₀:k≤a) (h₁:a≤N) (hh:Useful (R.family.path.rep N p a) (strand R V r h₀ y)) :
      Useful (R.family.path.rep N p a) (moved R V r h₀ h₁ y z) :=
    View.signpost_use R.makes h₁ (1,false) _ hh
  have childSite : affine (1:Signed) ((R.family.path.levels.clock.op j p).ratio.embed (site R hn.le z)) c =
      site R hn z := by simpa [affine,c,b,add_comm] using adjacent R hn z
  have mature := View.paid (a:=(1,false)) R.makes hn sound (by rfl) ride
    (take (j+1) (hj.trans j.le_succ) hn front) (take j hj hn.le ride.tomorrow)
    (y:=site R hn.le z)
    (View.Signpost.at_child (a:=(1,false))
      (childSite.symm ▸ (View.shift_at (P:=A) (π:=Classical.choice
        ((R.makes.wilson.represents N p (j+1) hn).good.labels.moves 1 (site R hn z)))))
      (View.shift_at (P:=A) (π:=keys0 R.makes hn b)))
    (View.shift_at (P:=E))
  have coarseSite : affine (1:Signed) (site R hn.le z) 0 = site R hn.le z := by simp [affine]
  change Ride _ (affine (1:Signed) ((R.family.path.levels.clock.op j p).ratio.embed (site R hn.le z)) c)
    (affine (1:Signed) (site R hn.le z) 0) _ _ _ _ _ at mature
  rw [childSite,coarseSite] at mature
  exact mature

end YM.Integration.WilsonThermometerOwnOffsetTale
end
