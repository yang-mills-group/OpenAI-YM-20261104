import YM.FullVolume.Cross
import YM.RGComparison.Core16.Trajectory
import YM.MergeProof.South.Window

/-! The complete positive Wilson joint on its original torus. At every
coarse field the normalized pushed signed fine observable is the actual
Descent conditional on the measured line. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonReportingAbsoluteInletGust
open Lattice RG Wilson PhysicalNext.Repeat.Legato MergeProof.Accent RGComparison.Core16
open scoped Classical
variable {G:Gauge} (R:Run G) {N per m:ℕ}
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem numerator (T:Slices R.family.path.levels per) (live:m≤N) (φ:Config G (R.family.side N per)→E):
    gust R.family.path N per N (fun U=>(R.family.path.rep N per N).eval U • φ U) m live=
      (traversal T live).weighted (line R.family.path per m N) φ := by
  induction live using Nat.decreasingInduction with
  | self =>
    rw [gust_base,traversal_self,Descent.weighted,Descent.output_nil]
    funext U
    exact congrArg (fun x:ℝ=>x • φ U) (congrFun (R.makes.wilson.starts N per).2 U)
  | of_succ k edge ih =>
    rw [gust_step R.family.path N per N _ edge,weighted_step T φ edge,ih]

def physical (live:m≤N) (φ:Config G (R.family.side N per)→E) (V:Config G (R.family.side m per)):E :=
  ((R.family.path.rep N per m).eval V)⁻¹ •
    gust R.family.path N per N (fun U=>(R.family.path.rep N per N).eval U • φ U) m live V

theorem original (T:Slices R.family.path.levels per) (live:m≤N) (φ:Config G (R.family.side N per)→E)
    (V:Config G (R.family.side m per)):
    physical R live φ V=(traversal T live).conditioned (line R.family.path per m N) φ V := by
  unfold physical Descent.conditioned
  rw [numerator R T live φ, vacuum_eq T R.makes.wilson live]
end YM.Integration.WilsonReportingAbsoluteInletGust
