import YM.Integration.WilsonTrueProjectedFiledGrades
import YM.Integration.WilsonMeasuredOriginalColumnSigned

/-! Actual adjacent Wilson densities for a graded finite field program. Both
signed receipts use the same incoming word, emitted pupil and outgoing vacuum.
The weights on derivative letters are the submitted numerical coordinates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedFiledSource
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open FormalBulk08 City Pose PhysicalNext Repeat Legato Graces Roost Org
open WilsonTrueProjectedDualHistory WilsonTrueProjectedFiledTransfer
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d D N p i : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
local notation "𝓒" => R.family
local notation "sec" => R.family.localSection d
local notation "lo" => R.family.side i p
local notation "hi" => R.family.side (i+1) p

def edge (fine : Config G hi → ℂ) (coarse : Config G lo → ℂ) : Spaces R p :=
  Function.update (Function.update (fun _ _ => 0) (i+1) fine) i coarse

theorem fine (f : Config G hi → ℂ) (c : Config G lo → ℂ) :
    edge R f c (i+1) = f := by
  unfold edge
  rw [Function.update_of_ne (Nat.succ_ne_self i), Function.update_self]

theorem coarse (f : Config G hi → ℂ) (c : Config G lo → ℂ) :
    edge R f c i = c := Function.update_self ..

theorem with_vacuum (Ψ : ∀ j, RG.Rep G ((𝓒).side j p))
    (book : ι → Config G lo → ℂ) (x : ι → ℂ) (U : Config G lo) :
    submitted R (fun b V => ((Ψ i).eval V : ℂ) * book b V) x U =
      ((Ψ i).eval U : ℂ) * submitted R book x U := by
  unfold submitted weighted
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- A measured deposited pupil and the signed change from that pupil to the
next registered group words, on their shared original Wilson representation. -/
def Paid (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)) (f : Config G hi → ℂ)
    (emitted next : Config G lo → ℂ) (u v : ℝ) : Prop :=
  ∃ e z : GermGraph.store (𝓒) d p i,
    Admitted R Ψ i e u ∧ (R.family.labels.level d).coeffSize e.x ≤ u ∧
    Admitted R Ψ i z v ∧ (R.family.labels.level d).coeffSize z.x ≤ v ∧
    (∀ W, (((Ψ i).eval W : ℂ))⁻¹ * e.density 0 sec (Ψ i) W =
      actualAverage (𝓒) (N:=N) f W - emitted W) ∧
    (∀ W, z.density 0 sec (Ψ i) W = ((Ψ i).eval W : ℂ) * (emitted W-next W))

theorem original (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)) {σ C Λ δ w : ℝ}
    (law : (Ψ i).Lawful σ C Λ δ w) (cut : i ≤ N)
    (fineEq : (Ψ (i+1)).eval = (R.family.path.rep N p (i+1)).eval)
    (lowerEq : (Ψ i).eval = (R.family.path.rep N p i).eval)
    (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D) (q : ℕ) (g : ℝ)
    (upperBook : ι → Config G hi → ℂ) (lowerBook : ι → Config G lo → ℂ)
    (emitted : Fin (q+1) → ι → Config G lo → ℂ)
    (u v : Fin (q+1) → ι → ℝ)
    (paid : ∀ k b, Paid R (d:=d) (N:=N) Ψ (upperBook b) (emitted k b)
      (submitted R lowerBook (fun t => matrix R a wood depth N i (q-k.val) g t b)) (u k b) (v k b))
    (intake : ∀ b, Integrable (WilsonMeasuredOriginalColumnTransition.upper R (d:=d)
      (Ψ (i+1)) (upperBook b)) (prior G _))
    (anchor : ι) (x : Fin (q+1) → ι → ℂ) (F : Spaces R p)
    (enter : F (i+1) = fun W => ∑ k, submitted R
      (fun b => WilsonMeasuredOriginalColumnTransition.upper R (d:=d) (Ψ (i+1)) (upperBook b)) (x k) W)
    (leave : F i = fun W => ((Ψ i).eval W : ℂ) * submitted R lowerBook
      (fun b => ∑ e, WilsonTrueProjectedFiledGrades.layer R a wood depth N i q g x e b) W) :
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F i
      (∑ k : Fin (q+1), ∑ b, ‖x k b‖*(u k b+v k b)) := by
  let fineBank (b : ι) := WilsonMeasuredOriginalColumnTransition.upper R (d:=d) (Ψ (i+1)) (upperBook b)
  let lowerBank (b : ι) (W : Config G lo) := ((Ψ i).eval W : ℂ) * lowerBook b W
  let columns (k : Fin (q+1)) (b : ι) := edge R (fineBank b)
    (submitted R lowerBank (fun t => matrix R a wood depth N i (q-k.val) g t b))
  apply WilsonTrueProjectedFiledGrades.original R Ψ law a wood depth q g columns lowerBank
    (fun k b => u k b+v k b) ?_ ?_ ?_ anchor x F ?_ ?_
  · intro k b
    obtain ⟨e,z,he,pe,hz,pz,hw,hy⟩ := paid k b
    apply WilsonMeasuredOriginalColumnSigned.original R Ψ cut fineEq lowerEq law (columns k b)
      (upperBook b) (emitted k b)
      (submitted R lowerBook (fun t => matrix R a wood depth N i (q-k.val) g t b))
      (fine R ..) ?_ e z he pe hz pz hw hy
    intro W
    rw [show columns k b i = _ from coarse R ..]
    exact with_vacuum R Ψ lowerBook _ W
  · intro k b
    rw [show columns k b (i+1) = _ from fine R ..]
    exact intake b
  · intro k b
    exact coarse R ..
  · simpa only [columns,fine] using enter
  · rw [leave]
    funext W
    exact (with_vacuum R Ψ lowerBook _ W).symm

end YM.Integration.WilsonTrueProjectedFiledSource
