import YM.Integration.WilsonAddressedWeakStationRoom
import YM.Integration.WilsonAddressedWeakPanelIngress

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakPanelSpacing
open Function Filter Set Metric Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Table Spec Extraction XSpace Next.Rank Next.Rank.Station
open WilsonThermometerOffsetTrajectory WilsonThermometerReflectedTrajectory WilsonAddressedWeakReflectedHearing
open WilsonAddressedWeakCalibration WilsonAddressedWeakReflectedArray
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "Lev" => R.family.path.levels

theorem original (simple:G.Simple) (φ:Test 2) (b:ℝ) (positive:0<b):
    ∀ᶠ k:ℕ in atTop,∀ (_:Station.Allowed (Lev) b k) (N p:ℕ) (hk:k<N) (x:Points 2),x∈tsupport φ →
      let χ:=width (Lev) b k;let gr:χ≤k:=(wider ..).trans (before ..)
      let ρ:=gap (Lev) b k;let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
      let T:=Ship.yard R.family b hk.le p
      ∀ (i i':T.Cell×Fin 2),i≠i' →
        ((Lev).budget k).B^2<separation
          (point R (z i.2) (motion R gr hk i) (anchor R (p:=p) gr i) k)
          (point R (z i'.2) (motion R gr hk i') (anchor R (p:=p) gr i') k):=by
  filter_upwards [WilsonAddressedWeakStationRoom.original R simple φ b positive] with k room
  intro ok N p hk x supp χ gr ρ z T
  obtain ⟨Q,hr,span,placed⟩:=room ok N p hk.le
  obtain ⟨apart,inside,roots,_⟩:=placed x supp
  rintro ⟨j,i⟩ ⟨l,h⟩ different
  by_cases e:j=l
  · subst l
    have diff:i≠h:=fun eq=>different (Prod.ext rfl eq)
    change _<separation (point R (z i) (motion R gr hk (j,i)) (anchor R (p:=p) gr (j,i)) k) (point R (z h) (motion R gr hk (j,i)) (anchor R (p:=p) gr (j,i)) k)
    rw [WilsonAddressedWeakDetectorCourse.translated R hk.le z (motion R gr hk (j,i)) (anchor R (p:=p) gr (j,i)) i h]
    have sep:=WilsonAddressedWeakSeparation.original R (p:=p) hk.le ρ hr x (((Lev).budget k).B^2) apart inside
    fin_cases i <;> fin_cases h
    · exact (diff rfl).elim
    · exact sep
    · rw [separation_comm];exact sep
    · exact (diff rfl).elim
  · let c (j:T.Cell):=(R.family.S.toDepth gr p).embed j
    let q:=anchorAt R (c j) k;let q':=anchorAt R (c l) k
    let u':=point R (z i) (motion R gr hk (j,i)) (c j) k
    let v':=point R (z h) (motion R gr hk (l,h)) (c l) k
    have left:separation q u'≤Q:=by
      rw [separation_comm,shifted R hk.le];exact radius R hk.le ρ hr x Q i (roots i)
    have right:separation v' q'≤Q:=by
      rw [shifted R hk.le];exact radius R hk.le ρ hr x Q h (roots h)
    have whole:((Lev).budget k).B^2+2*Q<separation q q':=span.trans_le (WilsonAddressedWeakTiling.spacing R gr j l e)
    have leftTriangle:=separation_triangle q u' q'
    have rightTriangle:=separation_triangle u' v' q'
    change _<separation u' v'
    omega
end YM.Integration.WilsonAddressedWeakPanelSpacing
end
