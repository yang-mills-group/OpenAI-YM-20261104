import YM.Integration.WilsonThermometerUnitFilingPosterior

/-! Linear transport of the signed numerators on a single original law. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRaw
open Function Set Filter MeasureTheory Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingCoarse
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) {N p b:ℕ}
local notation "H" => R.family.path
local notation "W" => R.family.path.rep N p b
local notation "X" => Config G (R.family.side b p)

theorem add (f g:X→ℂ) (hf:Integrable f (prior G _)) (hg:Integrable g (prior G _))
    {j:ℕ} (jb:j≤b) :
    reading R (N:=N) (f+g) j jb=reading R (N:=N) f j jb+reading R (N:=N) g j jb:=by
  have eq:gust H N p b (f+g) j jb=gust H N p b f j jb+gust H N p b g j jb:=by
    induction jb using Nat.decreasingInduction with
    | self => rw [gust_base,gust_base,gust_base]
    | of_succ i ix ih =>
      rw [gust_step H N p b _ ix,ih,StepData.push_add ((H).levels.transition_mass ..) _
        _ (gust_live H N p b f hf ix) (gust_live H N p b g hg ix),
        ←gust_step H N p b f ix,←gust_step H N p b g ix]
  unfold reading
  rw [eq,Pi.add_apply,mul_add]

theorem ratio (live:b≤N) (P:Rep G (R.family.side b p)) (quiet:P.eval=(W).eval)
    (f:X→ℂ) {j:ℕ} (jb:j≤b) :
    reading R (N:=N) f j jb=actualTransport R.family (N:=N) (fun U=>(P.eval U)⁻¹ • f U) jb 1 :=by
  let a:X→ℂ:=fun U=>(P.eval U)⁻¹ • f U
  have h:(fun U=>((W).eval U:ℂ)*a U)=f:=by
    funext U
    have nz:((W).eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
    dsimp only [a];rw [congrFun quiet U,Complex.real_smul,Complex.ofReal_inv]
    field_simp [nz]
  have identity:=WilsonThermometerUnitFilingPosterior.weighted R (N:=N) a jb
  rw [h] at identity
  exact identity

end YM.Integration.WilsonThermometerUnitFilingRaw
