import YM.PertExtension.RadialCut
import YM.PertExtension.WickColor

/-! The bounded ink polynomial is the true radial label determined by
`joint`, not merely a projection. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.PertExtension.Heat.HueTag
open Function Set Filter Finset RG Wilson Lattice Labels Source Drops Hue MvPolynomial
open Next.Rank Next.Rank.Beamer Next.Rank.Configuration Next.Rank.LiftMark Next.Rank.Normal Next.Rank.Spindle Top Push.CutoffProjectors Next.Foundations Ray Next.Rank.CellsInt MeasureTheory
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{d e:ℕ}{F : Labels.Frame G d} (P : poly (Panel RG.Slot G))

lemma all_turns (A : Snap G d)(u:G.El)(f:RG.Slot) : glow (Cast u A) f = G.adjoint u (glow A f):=by
  have hp x : access (Cast u A) x=G.adjoint u (access A x) := by
    rw [revealed_cell,revealed_cell,map_sum]; apply Finset.sum_congr rfl; intro i hi
    unfold CellsInt.trail
    simp only [expand,dif_pos (Finset.mem_range.mp hi),Function.comp_apply,Cast]
    unfold CellsInt.east; simp_rw [Taylor.paint_value]
    exact (G.adjoint u).toContinuousLinearMap.intervalIntegral_comp_comm (CellsInt.east_int _ _ ((Tensor.diag_smooth _ 1).continuous))
  unfold glow
  have he (w : Walk) (x : Cover) : Exterior.linkSum (access (Cast u A)) x w=G.adjoint u (Exterior.linkSum (access A) x w) := by
    induction w generalizing x with
    | nil => exact (map_zero _).symm
    | cons a w H=> rw [Exterior.linkSum,Exterior.linkSum,map_add,H]; split <;> simp [*]
  exact he ..

lemma original (h : Hue.Fixed P) : print d P∈ invariantSpace G := by
  intro x u; rw [display_jet,display_jet]; unfold colored
  simp_rw [show ∀ i,glow (Drops.trunk d (fun i=>Taylor.paint u (x i))) i=G.adjoint u (glow (Drops.trunk d x) i) from fun _=>all_turns _ u _]
  exact h u (fun i=>glow (Drops.trunk d x) i)

lemma scale_cast (A : Jet G)(u:G.El)(r:ℝ): scaleJet (colored u A) r=colored u (scaleJet A r) := funext fun x=>(map_smul ..).symm
lemma shadow_live (h : Hue.Fixed P): clipped d P∈ invariantSpace G:=by
  have hh:= original (d:=d) P h
  let q:=print d P
  have hT (x:Jet G)(u:G.El)(k): read (colored u x) (tier k q)=read x (tier k q):=by
    apply smul_right_injective ℂ (show (k.factorial:ℝ)≠0 from by positivity)
    dsimp only; rw [← deriv_read,← deriv_read];simp_rw [scale_cast]; congr 1; ext r; exact hh _ _
  change capRead d q ∈ invariantSpace G
  intro x u; unfold capRead; simp [hT]

def shadow (h : Hue.Fixed P) : Label G d:=⟨clipped d P,cap_limited ..,shadow_live P h⟩
lemma shadow_eq (h : Hue.Fixed P): F.coords.symm (joint F P)=shadow P h:= by apply F.coords.injective; rw [LinearEquiv.apply_symm_apply]; exact Ray.collect_normal P rfl

lemma shadow_real (hR : Hue.Clear P) : Labels.conjPol (clipped d P)=clipped d P := by
    have hu: Labels.conjPol (print d P)=print d P:=by apply Labels.eval_ext;intro A; rw [Labels.conj_value, Ray.display_jet];exact hR _
    have ht (q:Pol G): Labels.conjPol (capRead d q)=(capRead d (Labels.conjPol q)):=by ext f; simp only [Labels.conjPol, coeff_map,coeff_capRead]; split_ifs <;> simp
    rw [clipped,ht,hu]
lemma coordinates_real (h:Hue.Fixed P)(hr:Hue.Clear P): star (joint F P)=joint F P:=by
  funext i; change star (joint F P i)= _
  rw [← F.conj_basis]
  have ht : realBar (shadow P h (d:=d))=shadow P h:=Subtype.ext (shadow_real P hr)
  rw [shadow_eq _ h,ht,← show F.coords.symm (joint F P)=_ from shadow_eq P h, LinearEquiv.apply_symm_apply]

end YM.PertExtension.Heat.HueTag
