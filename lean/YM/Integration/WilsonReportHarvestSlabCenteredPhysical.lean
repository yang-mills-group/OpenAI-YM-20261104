import YM.Integration.WilsonReportHarvestSlabCenteredSelected
import YM.Integration.WilsonSeparatedOriginalSlabFold

/-! Read the centered physical Wilson product and the corresponding retained
old action under one original held posterior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabCenteredPhysical
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation WilsonReportHarvestSlabCenteredPush
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
local notation "S₀"=>Stock.census (Fin 3)

private theorem source {G:Gauge}{a:Side}(Y:Rep G a)(F:Fin 3→Goods G a)(c:Fin 3→ℂ)(U:Config G a):
    score c (birth S₀ Y F U)=(Y.eval U:ℂ)*(∏i:Fin 3,(c i+F i U)):=by
  change ((Poly.pass (Mach S₀ c))*((Y.eval U:ℂ) • Poly.pass (Mach S₀ (fun i=>F i U)))).part entire=_
  have sum:Mach S₀ c+Mach S₀ (fun i=>F i U)=Mach S₀ (fun i=>c i+F i U):=by
    simp [Mach,send_add,Finset.sum_add_distrib]
  rw [mul_smul_comm,←pass_add (mute S₀ c) (mute S₀ (fun i=>F i U)),sum,Poly.part_smul]
  unfold Mach
  rw [pass_fire]
  rfl

private theorem nested {G:Gauge} (A:History G)(N per:ℕ){u n k:ℕ}(age:u ≤ n)(hi:n ≤ k):
    ∀F:Config G (A.S.side k per)→ℂ,pushTo A N per age (pushTo A N per hi F)=pushTo A N per (age.trans hi) F:=by
  induction k,hi using Nat.le_induction with
  | base=>intro F;rw [pushTo_self]
  | succ k hk ih=>intro F;rw [pushTo_next A N per hk,pushTo_next A N per (age.trans hk)];exact ih _

private theorem pushed {G:Gauge} (A:History G)(N p j:ℕ)(X:Config G (A.S.side j p)→ℂ){k:ℕ}(hk:k ≤ j):
    gust A N p j X k hk=pushTo A N p hk X:=by
  induction hk using Nat.decreasingInduction with
  | self=>rw [gust_base,pushTo_self]
  | of_succ i hi ih=>rw [gust_step A N p j X hi,Birth.push_first A N p hi,ih]

variable {G:Gauge} (C:Family G){u n m N per:ℕ}
    (o:Fin 3→Site (C.side n per))(E:Fin 3→Motion)(s:Fin 3→ℕ)(q:ManyStem C o n→Body)
    (S:(i:Fin 3)→Emblems C (s i))(x:(i:Fin 3)→Palette C (s i))
local notation "J"=>Mine.ward o E (Stock.census (Fin 3))
local notation "Y"=>C.path.rep N per
local notation "F"=>WilsonAllDateHarvestPhysical.columns o E s q S x m N n
local notation "Cₙ"=>WilsonSeparatedOriginalCaptureAtOrigin.clinics o E s q S x m N

theorem original (h:C.Makes)(nN:n ≤ N)(un:u ≤ n)(L:Config G (C.side n per)→Poly S₀)
    (keep:Integrable L (prior G _))(v:Fin 3→ℂ)(V:Config G (C.side u per)):
    let physical:=fun W=>baseFold o E S₀ (gust C.path N per N (birth (J n) (Y N) F) n nN W)
    value C.path N per un physical L v V=
      actualTransport C (N:=N) (fun U=>∏i:Fin 3,(v i+Cₙ i U)) (un.trans nN) V-
        pushTo C.path N per un (fun W=>score v (L W)) V/liftVac C.path N per u V:=by
  intro physical
  let a:=Mine.remap o E
  let A:=Mine.tree o E
  have upper:Integrable (birth (J n) (Y N) F) (prior G (C.side N per)):=
    (hatCont C N per F (fun _=>Records.clinic_cut ..) (show Continuous ((Y N).eval) by
      rw [(h.wilson.starts ..).2];exact bare_cont _) (J n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have equal:Many.combine (A.labelY n) (fun _=>1) F=Cₙ:=by
    funext i;unfold Many.combine
    rw [Finset.sum_eq_single (a.symm i)]
    · rw [if_pos (show A.labelY n (a.symm i)=i from rfl),one_smul]
      exact WilsonSeparatedOriginalCaptureAtOrigin.registered o E s q S x m N i
    · intro z _ nz
      rw [if_neg (show A.labelY n z≠i from fun k=>nz (a.injective (k.trans (a.apply_symm_apply i).symm))),zero_smul]
    · simp
  obtain ⟨fin,branch⟩:=blended F (fun _=>1) (chamber S₀ (A.labelY n)) nN upper
  rw [equal] at fin branch
  have phys:Integrable physical (prior G _):=
    feed_live (chamber S₀ (A.labelY n)) (fun _=>1) (gust_live C.path N per _ _ upper nN)
  have scored:(fun W=>score v (physical W))=pushTo C.path N per nN
      (fun U=>((Y N).eval U:ℂ)*(∏i:Fin 3,(v i+Cₙ i U))):=by
    change (fun W=>score v (baseFold o E S₀ (gust C.path N per N (birth (J n) (Y N) F) n nN W)))=_
    have back:physical=gust C.path N per N (birth S₀ (Y N) Cₙ) n nN:=branch.symm
    change (fun W=>score v (physical W))=_
    rw [back,through C.path N per (birth S₀ (Y N) Cₙ) fin nN (score v)]
    exact congrArg _ (funext (source (Y N) Cₙ v))
  change pushTo C.path N per un (fun W=>score v (physical W)-score v (L W)) V/_=_
  rw [WilsonSeparatedOriginalSlabReturn.difference C.path N per un (fun W=>score v (physical W)) (fun W=>score v (L W))
    ((score v).restrictScalars ℝ|>.integrable_comp phys) ((score v).restrictScalars ℝ|>.integrable_comp keep)]
  change (pushTo C.path N per un (fun W=>score v (physical W)) V-pushTo C.path N per un (fun W=>score v (L W)) V)/_=_
  rw [sub_div,scored,nested C.path N per un nN]
  congr 1
  simp only [actualTransport,pushed C.path N per N _ (un.trans nN),Complex.real_smul,Complex.ofReal_inv,liftVac,div_eq_inv_mul]

end YM.Integration.WilsonReportHarvestSlabCenteredPhysical
