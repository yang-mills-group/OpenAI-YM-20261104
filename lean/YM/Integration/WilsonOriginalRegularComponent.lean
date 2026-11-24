import YM.Integration.WilsonOriginalJointTrialHearing
import YM.Integration.WilsonOriginalSeparatedDecoder
import YM.Integration.WilsonThermometerMixedVacuumReading

/-! Project the original unnormalized signed hearing only after its full
Haar recursion, on the elected actual quiet and any older held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRegularComponent
open Function Finset Filter Lattice Wilson RG Marker QuadraticLocal Multi MeasureTheory
open PhysicalNext PhysicalNext.Repeat Legato Extra.Histories Extra.Histories.Relay
open Extra.Trajectories RG05Readout Records Native Address Many MergeProof MergeProof.Accent
open WilsonOriginalJointTrialHearing
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V]{J:Census V}{N per b i:ℕ}
local notation "H" => R.family.path
local notation "X" t:max => Config G (R.family.side t per)

theorem projected (F:X i→Poly J)(paid:Integrable F (prior G _))(s:J.Mode)(bi:b ≤ i):
    (fun W=>(gust H N per i F b bi W).part s)=gust H N per i (fun U=>(F U).part s) b bi:=by
  induction bi using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base]
  | of_succ j jt ih=>
    rw [gust_step H N per i F jt,gust_step H N per i _ jt]
    have pass:=push_get ((H).levels.transition_mass j per ((H).β N per (j+1)))
      (gust_live H N per i F paid jt) s
    exact pass.trans (congrArg (((H).levels.clock.op j per).push ((H).β N per (j+1))) ih)

theorem original (D:X i→ℝ)(same:D=((H).rep N per i).eval)(F Z:X i→Poly J)
    (hf:Integrable (fun U=>(D U:ℂ) • F U) (prior G _))
    (hz:Integrable (fun U=>(D U:ℂ) • Z U) (prior G _))
    (bi:b ≤ i)(s:J.Mode)(W:X b):
    read R N per W bi (fun U=>(D U:ℂ) • F U) s-
      read R N per W bi (fun U=>(D U:ℂ) • Z U) s=
      actualTransport R.family (N:=N) (fun U=>(F U).part s-(Z U).part s) bi W:=by
  rw [←WilsonOriginalJointTrialHearing.difference R N per W bi _ _ hf hz s]
  unfold WilsonOriginalJointTrialHearing.read actualTransport
  rw [congrFun (projected R _ (hf.sub hz) s bi) W,Complex.real_smul,Complex.ofReal_inv]
  congr 2
  funext U
  change ((D U:ℂ)*(F U).part s-(D U:ℂ)*(Z U).part s)=_
  rw [←mul_sub,same,Complex.real_smul]

end YM.Integration.WilsonOriginalRegularComponent
end
