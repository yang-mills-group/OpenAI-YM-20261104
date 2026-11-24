import YM.Integration.WilsonReceivedChronologicalReadout

/-! Process signed source weights through each original Wilson conditional before the connected reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalMixture
open Function Finset MeasureTheory Lattice Wilson RG Source Marker
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato
open WilsonOriginalJointTrialHearing (read fee defect difference)
open private tower from YM.Integration.WilsonOriginalJointTrialHearing
open private summed from YM.Integration.WilsonOriginalOccupiedTransport
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per:ℕ}{V:Type}[DecidableEq V]{J:Census V}
  {I:J.Mode→Type*}[∀s,Fintype (I s)]
local notation "X" i:max => Config G (R.family.side i per)
variable (c:∀s,I s→ℂ)(rows:∀s,I s→∀i:ℕ,Config G (R.family.side i per)→Poly J)

def mix (i:ℕ)(W:X i):Poly J:=fun s=>∑q:I s,c s q*(rows s q i W).part s

theorem live {i:ℕ}(income:∀s q,Integrable (rows s q i) (prior G _)):
    Integrable (mix R c rows i) (prior G _):=by
  apply integrable_pi_iff.mpr
  intro s
  exact integrable_finsetSum _ fun q _=>(((Poly.get s).restrictScalars ℝ).integrable_comp (income s q)).const_mul (c s q)

theorem normalized {b i:ℕ}(bi:b ≤ i)(U:X b)(s:J.Mode)
    (income:∀s q,Integrable (rows s q i) (prior G _)):
    read R N per U bi (mix R c rows i) s=∑q:I s,c s q*read R N per U bi (rows s q i) s:=by
  let F:=fun q:I s=>fun W:X i=>(rows s q i W).part s
  have opened (q:I s):Integrable (F q) (prior G _):=((Poly.get s).restrictScalars ℝ).integrable_comp (income s q)
  have refund:=congrFun (summed R (N:=N) univ (c s) F opened bi).2 U
  have entry:(fun W=>(mix R c rows i W).part s)=∑q:I s,c s q • F q:=by
    funext W
    simp only [mix,Poly.part,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,F]
  have basis (q:I s):gust R.family.path N per i (F q) b bi U=(gust R.family.path N per i (rows s q i) b bi U).part s:=
    (congrFun (WilsonOriginalOccupiedTransport.projected R (N:=N) (rows s q i) (income s q) s bi) U).symm
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,basis] at refund
  have base:=congrFun (WilsonOriginalOccupiedTransport.projected R (N:=N) (mix R c rows i) (live R c rows income) s bi) U
  rw [entry,refund] at base
  unfold WilsonOriginalJointTrialHearing.read
  rw [base,Finset.mul_sum]
  exact sum_congr rfl fun q _=>by ring

theorem difference_at (Z:∀i,X i→Poly J){b i:ℕ}(bi:b ≤ i)(W:X b)(s:J.Mode)
    (next:Integrable (Z (i+1)) (prior G _))(before:Integrable (Z i) (prior G _)):
    fee R N per W Z i s=read R N per W (bi.trans (Nat.le_succ i)) (Z (i+1)) s-read R N per W bi (Z i) s:=by
  unfold WilsonOriginalJointTrialHearing.fee WilsonOriginalJointTrialHearing.defect
  rw [dif_pos bi,difference R N per W bi _ _ (gust_live R.family.path N per (i+1) _ next _) before s]
  unfold WilsonOriginalJointTrialHearing.read
  rw [←tower R N per (Z (i+1)) bi (Nat.le_succ i)]

theorem original {b i:ℕ}(bi:b ≤ i)(W:X b)(s:J.Mode)
    (next:∀s q,Integrable (rows s q (i+1)) (prior G _))(before:∀s q,Integrable (rows s q i) (prior G _)):
    fee R N per W (mix R c rows) i s=∑q:I s,c s q*fee R N per W (rows s q) i s:=by
  rw [difference_at R _ bi W s (live R c rows next) (live R c rows before),
    normalized R c rows _ W s next,normalized R c rows bi W s before,←Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  rw [difference_at R _ bi W s (next s q) (before s q),mul_sub]
end YM.Integration.WilsonReceivedChronologicalMixture
end
