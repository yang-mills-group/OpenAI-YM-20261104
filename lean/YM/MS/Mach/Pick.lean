import YM.MS.Mach.Mark

set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Pilot Garment Color Book Convolve
open Motif Literal Halo Native Detect Lifting Pole
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n h:ℕ} {z:ℂ} {F:ℂ→Mob G}
def Sentence (G:Gauge)(n h:ℕ): Set (ℂ→Mob G):= {F|∃ f:Fin n→Plaq,∃ σ:Grid G n,wage n f=h ∧ F=saint n f σ}
def Gallery (G:Gauge)(n h:ℕ):= Submodule.span ℝ (Sentence G n h)
abbrev Ele (h:ℕ)(n:ℕ)(A:Law G)(X: Box (Mob G)): Prop:= (fun z=> value ( Mob G ) z X)∈ Gallery G n h ∧ X 0 0 = A
lemma lng {X:Box (Mob G)}(c:ℝ)(z:ℂ) : value ( Mob G) z ( c • X )= c • value _ z X:= map_smul ((value _ z).restrictScalars ℝ) c X
end YM.MS.Mach
