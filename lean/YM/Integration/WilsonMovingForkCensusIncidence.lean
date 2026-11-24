import YM.Integration.WilsonMovingForkOpticalBook
import YM.Integration.WilsonOriginalAlternativeFiniteSource
import YM.Integration.WilsonOriginalJointTrialHearing

/-! The physical census, its complete ordinary components, and the numerical
two-stop recurrence evaluate the same signed density under the original prior. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkCensusIncidence
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker QuadraticLocal Multi
open Extra.Histories Extra.Histories.Relay PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent Extra.Trajectories
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator feeAt)
open WilsonOriginalJointTrialHearing (read)
open WilsonOriginalAlternativeFiniteSource (offer disks fired probe)
open RG05Readout RG05Readout.Records Extra.Trajectories RG16.Literal
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]{N per:ℕ}
local notation "C" => R.family
local notation "vac" i:max => ((C).path.rep N per i)
local notation "X" i:max => Config G ((C).side i per)
local notation "J" => Stock.census I

/-- The paid original public offering, on all its ordinary modes, at its
actual microscopic placement. This includes modes that disappeared in a subpanel. -/
theorem original (d:I→ℕ)(y:∀i,(C).label (d i))(o:I→Site ((C).side N per)):
    offer R d N per y o fired = fun U=>((vac N).eval U : ℂ) •
      (Poly.inject (fun s=>∏a∈s.val,(C).O N per (y a) (o a) U):Poly J):=by
  funext U
  ext s
  unfold offer birth Mach
  simp only [Poly.part_smul,pass_fire,probe,fired,one_mul]
  rfl

theorem history {j:ℕ}(jN:j ≤ N)(d:I→ℕ)(y:∀i,(C).label (d i))(o:I→Site ((C).side N per))(s:(J).Mode):
    (fun U=>(gust (C).path N per N (offer R d N per y o fired) j jN U).part s)=
      credit C N per 0 (fun U=>∏a∈s.val,(C).O N per (y a) (o a) U) j jN:=by
  let source:=fun U=>∏a∈s.val,(C).O N per (y a) (o a) U
  have cont:Continuous source:=continuous_finsetProd _ fun i _=>(C).continuousO N per (d i) _ _
  have cash:=WilsonOriginalAlternativeFiniteSource.paid R d N per y o fired (Nat.le_refl N)
  rw [gust_base] at cash
  have top:(fun U=>(offer R d N per y o fired U).part s)=credit C N per 0 source N le_rfl:=by
    rw [credit_bare C N per 0 R.makes source,pow_zero,one_smul,original]
    funext U
    rfl
  rw [pushpart jN (offer R d N per y o fired) s cash,top]
  exact WilsonThermometerUnitFilingCoarse.cutoff R (Nat.le_refl N) jN source cont

theorem flat {j u:ℕ}(uj:u ≤ j)(Z:X j → Poly (J))(paid:Integrable Z (prior G _))(s:(J).Mode):
    read R N per (1:X u) uj Z s=reading R (N:=N) (fun U=>(Z U).part s) u uj:=by
  unfold WilsonOriginalJointTrialHearing.read reading
  have project:(fun V=>(gust (C).path N per j Z u uj V).part s)=gust (C).path N per j (fun U=>(Z U).part s) u uj:=by
    induction uj using Nat.decreasingInduction with
    | self=>rw [gust_base,gust_base]
    | of_succ k h ih=>
      rw [gust_step (C).path N per j Z h,gust_step (C).path N per j _ h]
      exact (push_get ((C).path.levels.transition_mass k per ((C).path.β N per (k+1)))
        (gust_live (C).path N per j Z paid h) s).trans
        (congrArg (((C).path.levels.clock.op k per).push ((C).path.β N per (k+1))) ih)
  rw [congrFun project 1]

/-- One actual marked Haar defect, including the interaction of a previously
deposited pair with its spectator, is heard at the identical older scalar. -/
theorem dated {u j:ℕ}(uj:u ≤ j)(jn:j<N)(s:(J).Mode)
    (trial:∀i:ℕ,X i → Poly J)(M:∀i:ℕ,X i → ℂ)
    (old:Integrable (trial j) (prior G _))(young:Integrable (trial (j+1)) (prior G _))
    (atOld:(fun U=>(trial j U).part s)=numerator R N per j (M j))
    (atYoung:(fun U=>(trial (j+1) U).part s)=numerator R N per (j+1) (M (j+1))):
    WilsonOriginalJointTrialHearing.fee R N per (1:X u) trial j s=feeAt R N per u M j:=by
  let upper:=gust (C).path N per (j+1) (trial (j+1)) j (Nat.le_succ j)
  have hu:=gust_live (C).path N per (j+1) (trial (j+1)) young (Nat.le_succ j)
  have first:Integrable (numerator R N per j (M j)) (prior G _):=atOld ▸ (Poly.get s).integrable_comp old
  have second:Integrable (numerator R N per (j+1) (M (j+1))) (prior G _):=
    atYoung ▸ (Poly.get s).integrable_comp young
  have both:read R N per (1:X u) uj upper s=read R N per (1:X u) (uj.trans (Nat.le_succ j)) (trial (j+1)) s:=by
    have join:gust (C).path N per j upper u uj=gust (C).path N per (j+1) (trial (j+1)) u (uj.trans (Nat.le_succ j)):=by
      induction uj using Nat.decreasingInduction with
      | self=>rw [gust_base]
      | of_succ k h ih=>rw [gust_step (C).path N per j _ h,gust_step (C).path N per (j+1) _ (h.trans_le (Nat.le_succ j)),ih]
    unfold WilsonOriginalJointTrialHearing.read
    rw [join]
  simp only [WilsonOriginalJointTrialHearing.fee,WilsonOriginalJointTrialHearing.defect,feeAt,dif_pos uj]
  rw [WilsonOriginalJointTrialHearing.difference R N per (1:X u) uj upper (trial j) hu old s,both,
    flat R _ _ young s,flat R uj _ old s,atYoung,atOld]
  exact (WilsonThermometerUnitFilingFlatTelescope.edge R N per uj jn M first second).symm

end YM.Integration.WilsonMovingForkCensusIncidence
