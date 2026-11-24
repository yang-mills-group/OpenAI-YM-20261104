import YM.Integration.WilsonSeparatedOriginalCaptureAtOrigin
import YM.Integration.WilsonAllDateHarvestObservables
import YM.Integration.WilsonPositionSeparatedProfileSlabReceipt

/-! The physical folded three-mark slab at a genuine old observation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
namespace YM.Integration.WilsonSeparatedOriginalSlabFold
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology BigOperators Classical
variable {G:Gauge} (C:Family G){n u m N per:ℕ}
variable (o:Fin 3→Site (C.side n per))(E:Fin 3→Motion)(s:Fin 3→ℕ)(q:ManyStem C o n→Body)
variable (S:(i:Fin 3)→Emblems C (s i))(x:(i:Fin 3)→Palette C (s i))
local notation "J"=>Mine.ward o E (Stock.census (Fin 3))
local notation "Y"=>C.path.rep N per
local notation "f"=>WilsonAllDateHarvestPhysical.columns o E s q S x m N n
local notation "cols"=>WilsonSeparatedOriginalCaptureAtOrigin.clinics o E s q S x m N
local notation "Q"=>Stock.census (Fin 3)
local notation "U!"=>Config G ((C).side u per)

def joint (nN:n ≤ N) (W:Config G ((C).side n per)):ℂ:=
  (baseFold o E Q (gust (C).path N per N (birth (J n) (Y N) f) n nN W)).part entire

theorem current (made:C.Makes)(nN:n ≤ N)(W:Config G ((C).side n per)):
    ((Y n).eval W:ℂ)⁻¹*joint (m:=m) C o E s q S x nN W=
      actualTransport C (N:=N) (fun V=>∏i:Fin 3,cols i V) nN W:=by
  let h:=made
  let A:=Mine.tree o E
  let a:=Mine.remap o E
  have upper:Integrable (birth (J n) (Y N) f) (prior G ((C).side N per)):=
    (hatCont C N per f (fun _=>Records.clinic_cut ..) (show Continuous ((Y N).eval) by
      rw [(h.wilson.starts ..).2];exact bare_cont _) (J n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have equal:Many.combine (A.labelY n) (fun _=>1) f=cols:=by
    funext i;unfold Many.combine
    rw [Finset.sum_eq_single (a.symm i)]
    · rw [if_pos (show A.labelY n (a.symm i)=i from rfl),one_smul]
      exact WilsonSeparatedOriginalCaptureAtOrigin.registered o E s q S x m N i
    · intro z _ nz
      rw [if_neg (show A.labelY n z≠i from fun k=>nz (a.injective (k.trans (a.apply_symm_apply i).symm))),zero_smul]
    · simp
  obtain ⟨fin,branch⟩:=blended f (fun _=>1) (chamber Q (A.labelY n)) nN upper
  rw [equal] at fin branch
  have eq:=WilsonAllDateHarvestObservables.normalized («C»:=C) nN cols (le_refl (Q).choices) fin entire W
  rw [narrow_right] at eq
  rw [show joint (m:=m) C o E s q S x nN W=(gust (C).path N per N (birth Q (Y N) cols) n nN W).part entire from
    congrArg (fun v=> (v W).part entire) branch.symm]
  exact eq

theorem weighted (made:C.Makes)(nN:n ≤ N):
    joint (m:=m) C o E s q S x nN=(fun W=>(Y n).eval W • actualTransport C (N:=N) (fun V=>∏i:Fin 3,cols i V) nN W):=by
  funext W
  have pos:=WardBin.Wheels.gravity (H:=C.path) made.wilson (p:=per) nN W
  rw [Complex.real_smul,←current (m:=m) C o E s q S x made nN W,←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr pos.ne'),one_mul]

theorem paid (made:C.Makes)(nN:n ≤ N):
    Integrable (joint (m:=m) C o E s q S x nN) (prior G (C.side n per)):=by
  let F:ContinuousMap (Config G (C.side N per)) ℂ:=⟨fun V=>∏i:Fin 3,cols i V,continuous_finsetProd _ (fun i _=>Records.clinic_cut ..)⟩
  rw [weighted (m:=m) C o E s q S x made nN]
  exact actualTransport_weighted_integrable C made (le_refl N) F.continuous.aestronglyMeasurable (fun W=>F.norm_coe_le_norm W) nN

private theorem pushed (A:History G) (N p j:ℕ) (X:Config G (A.S.side j p)→ℂ) {k:ℕ} (hk:k≤j):
    gust A N p j X k hk=pushTo A N p hk X:=by
  induction hk using Nat.decreasingInduction with
  | self=>rw [gust_base,pushTo_self]
  | of_succ i hi ih=>rw [gust_step A N p j X hi,Birth.push_first A N p hi,ih]

theorem held (made:C.Makes)(nN:n ≤ N)(un:u ≤ n)(U:U!):
    pushTo (C).path N per un (joint (m:=m) C o E s q S x nN) U/liftVac (C).path N per u U=
      actualTransport C (N:=N) (fun V=>∏i:Fin 3,cols i V) (un.trans nN) U:=by
  let z:=fun W:Config G ((C).side n per)=>actualTransport C (N:=N) (fun V=>∏i:Fin 3,cols i V) nN W
  have field:=weighted (m:=m) C o E s q S x made nN
  rw [field,←actualTransport_tower C made (le_refl N) (fun V=>∏i:Fin 3,cols i V) nN un]
  change _=(((Y u).eval U)⁻¹:ℝ) • gust (C).path N per n (fun W=>(Y n).eval W • z W) u un U
  simp only [pushed (C).path N per n _ un,Complex.real_smul,Complex.ofReal_inv,liftVac,div_eq_inv_mul]
  rfl

end YM.Integration.WilsonSeparatedOriginalSlabFold
