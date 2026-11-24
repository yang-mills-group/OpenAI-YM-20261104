import YM.Integration.WilsonOriginalOccupiedFiledSlice

/-! Exact signed split inside the original two-programme dated hearing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedJointEdge
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N per m k b i:ℕ} {V:Type} [DecidableEq V] [Fintype V] (J:Census V)
variable (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)

def ordinary (bi:b ≤ i)(row:Slice R J (Ψ i))(declared:Config G (R.family.side i per)→Poly J)
    (s:J.Mode)(W:Config G (R.family.side b per)):ℂ:=
  read R N per W bi (fun U=>((Ψ i).eval U:ℂ) • Poly.pass (row.A.E.log row.x U)) s-
    read R N per W bi declared s

include course in
theorem original (mb:m ≤ b)(bi:b ≤ i)(live:i < N)(row:Slice R J (Ψ i))
    (programme:∀j,Config G (R.family.side j per)→Poly J)
    (source:row.A.density row.x=LocalComparison.actualPush R.family N per i (programme (i+1)))
    (upper:Integrable (programme (i+1)) (prior G _))(lower:Integrable (programme i) (prior G _))
    (s:J.Mode)(W:Config G (R.family.side b per)):
    fee R N per W programme i s=credit R J (N:=N) bi Ψ row s W+
      ordinary R J Ψ (N:=N) bi row (programme i) s W:=by
  have one:gust R.family.path N per (i+1) (programme (i+1)) i (Nat.le_succ i)=
      LocalComparison.actualPush R.family N per i (programme (i+1)):=by
    rw [gust_step _ _ _ _ _ (Nat.lt_succ_self i),gust_base];rfl
  have quiet:((Ψ b).eval W:ℂ)=((R.family.path.rep N per b).eval W:ℂ):=by
    exact_mod_cast congrFun (course.1.walk b mb (bi.trans live.le)).view W
  simp only [fee,dif_pos bi,WilsonOriginalJointTrialHearing.defect]
  rw [WilsonOriginalJointTrialHearing.difference R N per W bi _ _
    (gust_live _ _ _ _ _ upper _) lower,one,←source]
  unfold credit ordinary WilsonOriginalJointTrialHearing.read
  rw [quiet,mul_sub];abel

end YM.Integration.WilsonOriginalOccupiedJointEdge
