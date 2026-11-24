import YM.Integration.FVA1Physical.Round2.CalibratedVoices
import YM.Integration.FVA1Physical.Wilson.BatchHistory

/-! The true many-step physical conditional moment decomposes into the
same calibrated basis bank. The division uses the one measured vacuum
for the original insertions and all basis choices. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Source Labels
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open LocalLTE.Sail Extra.Histories
open scoped Classical BigOperators ContDiff
variable {J : Type} [Fintype J]
def complexBank (w : J → ℂ) : (J → ℂ) →L[ℝ] ℂ := ∑ i,w i • ContinuousLinearMap.proj i
private theorem complexBank_read (w : J → ℂ) (x : J → ℂ) :
    complexBank w x = ∑ i,w i*x i := by simp [complexBank,smul_eq_mul]

theorem conditioned_complex_bank {G : Gauge} {n c : Side} (d : Descent n c) (h : d.OK G)
    (F : J → Config G n → ℂ) (hc : ∀ i,Continuous (F i)) (β : ℕ → ℝ) (w : J → ℂ) (V : Config G c) :
    d.conditioned β (fun U=>∑ i,w i*F i U) V = ∑ i,w i*d.conditioned β (F i) V := by
  let W := fun U : Config G n=>fun i=>F i U
  have hW : Continuous W := continuous_pi hc
  have each (i : J) : d.conditioned β (F i) V = (d.conditioned β W V) i :=
    measured (ContinuousLinearMap.proj i : (J → ℂ) →L[ℝ] ℂ) β h hW V
  calc
    _ = d.conditioned β (complexBank w ∘ W) V :=
      congrArg (fun O=>d.conditioned β O V) (funext fun U=>(complexBank_read w (W U)).symm)
    _ = complexBank w (d.conditioned β W V) := measured (complexBank w) β h hW V
    _ = _ := by
      rw [complexBank_read]
      exact sum_congr rfl fun i _=>congrArg (w i*·) (each i).symm

variable {G : Gauge} {I : Type} [DecidableEq I] (B : Marker.Census I) {D : ℕ}
    (h : I → Fin (D+1)) (s : B.Mode) (M : I → Motion)
    (v : ∀ i, ((frames G).level (h i).val).Coeff)
    (A : StencilFamily G) {N n m : ℕ} (o : ∀ j,I → Site (A.family.side j n))
    (hm : m ≤ N) (V : Config G (A.family.side m n))

theorem mixed_basis_moment :
    (momentTable B (assignedBatch h M v A N n o) m hm V).part s =
      ∑ t, basisWeight B h s M v t *
        (momentTable B (basisBatch A (choiceLabels B h s A t) N n o) m hm V).part s := by
  let T := someSlices A.path.levels n
  let d := traversal T hm
  let W := fun t : BasisChoice (G:=G) B h s => basisBatch A (choiceLabels B h s A t) N n o
  let F := fun t => fullProduct (W t).wavelengths s.val
  have eqn : fullProduct (assignedBatch h M v A N n o).wavelengths s.val =
      fun x=>∑ t,basisWeight B h s M v t*F t x := funext (mixed_basis_read B h s M v A N n o)
  have e (Y : Batch A.path N n I) : (momentTable B Y m hm V).part s =
      d.conditioned (line A.path n m N) (fullProduct Y.wavelengths s.val) V := by
    rw [Wilson.momentTable_descent B Y T hm A.makes.wilson,moment_part]
  rw [e,eqn]
  exact (conditioned_complex_bank d (traversal_ok T hm) F
    (fun t=>(Wilson.tested_batch B (W t) s Complex.reCLM).1) (line A.path n m N)
    (basisWeight B h s M v) V).trans
    (sum_congr rfl fun t _=>congrArg (basisWeight B h s M v t * ·) (e (W t)).symm)
end YM.Integration.FVA1Physical.Round2
