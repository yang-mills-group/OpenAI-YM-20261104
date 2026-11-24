import YM.Integration.WilsonIndependentConditionedWideBirthWidth
import YM.Integration.WilsonIndependentConditionedWideBirthStart

/-! The charged older horizon for a detector placed farther out than its reporting ruler. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedWideBirthClock
open Filter Set Wilson Lattice RG PhysMS PhysicalNext.Repeat.Legato Next.Rank Pert.Asymptotics
open WilsonPositionProgramReporterBand WilsonReceivedChronologicalFixedCellFee WilsonOriginalTwoFlatIRCapturedCross
open WilsonInvariantActionPosition (berth)
open WilsonAddressedPublicFirstRoseGeometry (Fits)
open WilsonIndependentConditionedGramSpatialHost (date)
open scoped Topology
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "ν" => R.family.path.levels.clock.monitor
local notation "trail" => nhdsWithin (0:ℝ) (Set.Ioi 0)

def span (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(W reserve depth:ℕ):ℕ:=
  (WilsonMovingForkOpticalStops.original R simple slow reserve (W+2+2) depth).choose+2

def Issued {world:XSpace.Run}{stage u depth:ℕ}(run:Band R world stage)
    (v:WilsonIndependentCapturedPages.Stop R world run u depth)(P floor:ℕ){n:ℕ}(φ:Test n)
    (hi lam heat:ℝ)(m f K budget:ℕ):Prop:=
  let c:=capture R φ lam
  ∃w:ℕ,∃_center:c=run.reporter+w,∃uc:u≤c,∃vc:v.date w≤c,
    let first:=v.date w-1
    first+1=v.date w ∧ u≤v.date w ∧ stage≤v.date w ∧ v.date w < c ∧ floor+1≤c ∧
    c < f ∧ v.date w < m ∧ 8*a K < a c ∧ Fits R.family.S hi lam first K ∧
    WilsonAddressedPublicFirstRoseTicket.Receipt R hi (factor R φ) lam heat first f K c budget ∧
    ∀N per:ℕ,c < N → Quote R N per u (v.date w) c P depth uc vc

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels){θ:ℝ→ℝ}(law:Trace.Pilot.Coupling G θ)
    {world:XSpace.Run}{stage u depth:ℕ}(run:Band R world stage)
    (v:WilsonIndependentCapturedPages.Stop R world run u depth)(positive:0 < stage)(deep:0 < depth)
    (cu:R.family.ref 0≤u)(P floor:ℕ){n:ℕ}(φ:Test n){hi:ℝ}(hp:0 < hi)
    (W reserve width:ℕ):
    ∀ᶠr in trail,∀f j:ℕ,a f≤r → 8*a f < min hi (factor R φ)*r → r≤(H f)^W*a f →
      j≤f → ∀lam:ℝ,r≤lam → lam≤r*(ν j)^width →
        Issued R run v P floor φ hi lam (θ r) (date R simple r) f (berth R reserve f)
          (span R simple slow W reserve depth):=by
  let clock:=WilsonMovingForkOpticalStops.original R simple slow reserve (W+2+2) depth
  obtain ⟨old,paid⟩:=eventually_atTop.mp clock.choose_spec
  obtain ⟨hot,rich⟩:=eventually_atTop.mp ((Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (3*factor R φ))
  have lp:=WilsonReceivedChronologicalFixedCellFee.positive R φ
  have appt:=WilsonIndependentConditionedWideBirthStart.original R simple slow ready run v positive deep cu P floor φ hi
  filter_upwards [WilsonIndependentConditionedWideBirthWidth.original R simple W width appt,
    WilsonMovingForkStoppedHeat.original R simple law (W+2+2) depth, Ioc_mem_nhdsGT (R.family.S.a_pos (max old hot))]
    with r widen thermal small
  intro f j near inside posted jf lam wide zoom
  have ofit:max old hot≤f:=le_of_not_gt fun bad=>(R.family.S.strictAnti bad).not_ge (near.trans small.2)
  let c:=capture R φ lam
  let K:=berth R reserve f
  obtain ⟨cap,w,eq,uc,vc,next,uv,sv,vc',fl,openFace,outer,hours,quote⟩:=widen f j near posted jf lam wide zoom
  have lpos:0 < lam:=small.1.trans_le wide
  have high:max hi (factor R φ)*lam≤a (v.date w):=
    (mul_le_mul_of_nonneg_right (le_max_right ..) lpos.le).trans outer.le
  have low:8*a f < min hi (factor R φ)*lam:=inside.trans_le
    (mul_le_mul_of_nonneg_left wide (le_min hp.le lp.le))
  have hiFit:=WilsonAddressedPublicFirstRoseGeometry.original R.family.S hp lp lpos
    (m:=v.date w-1) (f:=f) (by rw [next];exact high) low
  have cf:c≤f:=hiFit.2.finer
  have margin:8*a f < a c:=hiFit.2.margin
  have earlier:c < f:=by
    apply lt_of_le_of_ne cf
    intro equal
    change 8*a f < a c at margin
    rw [equal] at margin
    linarith only [margin,R.family.S.a_pos f]
  have vm:v.date w < date R simple r:=by
    have spaced:r < a (v.date w):=wide.trans_lt ((le_mul_of_one_le_left lpos.le (le_max_left ..)).trans_lt outer)
    by_contra! bad
    exact (not_lt_of_ge (R.family.S.strictAnti.antitone bad)) ((WilsonIndependentConditionedGramSpatialHost.fits R simple small.1).trans_lt spaced)
  have fee:a c/a f≤(H f)^(W+2+2):=WilsonAddressedPublicFirstRoseCaptureWidth.original R simple slow lpos lp cf
    (WilsonCloseCaptureDate.bracket R.family.S (mul_pos lp lpos) openFace).1
    (rich f ((le_max_right ..).trans ofit)) cap
  have receipt:a (v.date w)/a K≤(H (v.date w))^clock.choose:=
    (paid f ((le_max_left ..).trans ofit) c (v.date w) c 0 cf vc le_rfl fee (hours c 0 le_rfl)).1
  have reach:=WilsonAddressedPublicFirstRoseCaptureWidth.previous R simple slow (v.date w-1) K clock.choose
    (by rw [next];exact receipt)
  have kf:= (WilsonInvariantActionPosition.arrival R reserve f).1.le
  have narrow:8*a K≤8*a f:=mul_le_mul_of_nonneg_left (R.family.S.strictAnti.antitone kf) (by norm_num)
  have final:=WilsonAddressedPublicFirstRoseGeometry.original R.family.S hp lp lpos
    (m:=v.date w-1) (f:=K) (by rw [next];exact high) (narrow.trans_lt low)
  refine ⟨w,eq,uc,vc,next,uv,sv,vc',fl,earlier,vm,narrow.trans_lt margin,final.1,?_,quote⟩
  refine ⟨lpos,?_,low,reach,?_⟩
  · rw [next];exact high
  · intro N per live
    rw [next]
    exact thermal f c (v.date w) N per near cf vc live fee (hours N per live)

end YM.Integration.WilsonIndependentConditionedWideBirthClock
