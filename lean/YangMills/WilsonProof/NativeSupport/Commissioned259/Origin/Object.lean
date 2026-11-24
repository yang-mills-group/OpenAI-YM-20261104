import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Runway
import YM.PhysMS.Frame.Measured
import YM.OPE.Orbits.System

/-! # Operand map for the analytic Near-Far comparison, on the **original** Final reader.

Continuum quantities; no construction of character, installation at a cutoff, or
change of analytic prices here. No use of point-limit hypotheses on a temporary Jordan state.
This chapter is to progress towards the physical comparisons; note their additional *hypotheses*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S)

/-- Identify sources with Sec on the physical H_d used at this radius. -/
def frame (r : ℝ) (k : ℕ) : Sec G k ≃ₗ[ℂ] S.Field k :=
  (Maxwell.Free.fields C.labels k).symm.trans (Z r k)
/-- Keep one frame when returning (commutes with `basis` evaluations on that same sector). -/
def via (Z : ℝ→PhysMS.tower S) : Comparing.Route G := fun r s k=>
  ((frame Z s k).trans (frame Z r k).symm).toLinearMap

variable {n m H h : ℕ} (d : Fin n→ℕ) (e : Fin m→ℕ)
-- Layout explicitly at BOTH homes, true lengths r, s.
abbrev position (o : E4) (r : ℝ) (x : Points n) (i : Fin n) := o+r • x i
abbrev Owner (F : Final C f S) := Viewers F × E4

def measures (d : Fin n→ℕ) (e : Fin m→ℕ) : Sweep (Owner F) G d e := fun p r T x y=>
  let a := beside (position p.2 r x) (position p.2 (r*T) y)
  let Y := (Orbits.moment (S:=S) (d:=Sum.elim d e) (spectator F p.1) a).currySum
  let U : MultilinearMap ℂ (fun i=> S.Field (d i)) (MultilinearMap ℂ (fun i=>S.Field (e i)) ℂ) := Y
  ((MultilinearMap.compLinearMapₗ (fun i : Fin m => (frame Z r (e i)).toLinearMap) : _ →ₗ[ℂ] MLA G e).compMultilinearMap U).compLinearMap (fun i=> (frame Z r (d i)).toLinearMap)

abbrev own {d : Fin n→ℕ} (r : ℝ) (v : Slots G d) : Orbits.Labels S d := fun i=> frame Z r (d i) (v i)

lemma measure_eq (p r T x y u v) : measures F Z d e p r T x y u v =
    whole (spectator F p.1) (position p.2 r x) (own Z r u) (position p.2 (r*T) y) (own Z r v) := by
  let Y := Orbits.moment (S:=S) (d:=Sum.elim d e) (spectator F p.1) (beside (position p.2 r x) (position p.2 (r*T) y))
  change Y.currySum (own Z r u) (own Z r v) = Y (stages _ _)
  rw [MultilinearMap.currySum_apply]; congr 1; funext i; cases i <;> rfl

/-- Mixed-scale exact listener with genuine Far normalization from substitution of actual A_i,
not an order crop. -/
abbrev total (d : Fin n → ℕ) (e : Fin m→ℕ) := Comparing.at_far (measures F Z d e) (via Z)
lemma total_eq (p r T x y u v) : total F Z d e p r T x y u v =
    whole (spectator F p.1) (position p.2 r x) (own Z r u) (position p.2 (r*T) y) (own Z (r*T) v) := by
  unfold total at_far; rw [adjusted_apply, measure_eq]
  congr 1; funext i; unfold own via; simp

def centerD (h : ℕ) (e : Fin m→ℕ) := probed (measures F Z (fun (_:Fin 1)=>h) e) (via Z)
lemma centerD_apply (p r T y v w) : centerD F Z h e p r T y v w =
    whole (spectator F p.1) (fun _ : Fin 1=>p.2) (d:=fun _=>h) (fun _=>frame Z r h w) (position p.2 (r*T) y) (own Z (r*T) v) := by
  change total F Z (d:=fun _=>h) e p r T 0 y (fun _=>w) v=_
  rw [total_eq]; congr 1; ext; simp [position]

lemma beside_separate {x : Points n} {y : Points m} {T : ℝ} (h : forest x (T • y) ∈ conf (n+m)) {r : ℝ} (hr : 0<r) (o : E4) :
    Injective (beside (position o r x) (position o (r*T) y)) := by
  let f : Fin (n+m)→E4 := (forest x (T • y)).ofLp
  have hf : Injective f := h
  let g (x:E4) := o+r • x
  have he : beside (position o r x) (position o (r*T) y) = (g ∘ f) ∘ finSumFinEquiv := by
    ext1 i; cases i with
    | inl i => simp [g,f,position]
    | inr i => simp [g,f,position,mul_smul]
  rw [he]; exact ((fun i j h=> smul_right_injective _ hr.ne' (add_left_cancel h)) |> fun (hinge:Injective g)=> (hinge.comp hf).comp finSumFinEquiv.injective)

lemma center_upon (p : Owner F) {r : ℝ} (hr : 0 < r) {T : ℝ} (hT : 0<T) {y : Points m} (hy : y∈Outside m) (v : Slots G e) :
    centerD F Z h e p r T y v = (upon (S:=S) (spectator F p.1) h p.2 (position p.2 (r*T) y) (own Z (r*T) v)).comp (frame Z r h).toLinearMap := by
  let a : Unit ≃ Fin 1 := Equiv.ofUnique ..
  have hc : forest (0:Points 1) (T • y) ∈ conf (1+m) := squeeze_T T hT y ▸ lives (-Real.log T) hy
  have hp (o:E4) : position o r (0:Points 1) = fun _=> o := by ext; simp [position]
  have hS := beside_separate hc hr p.2; rw [hp] at hS; ext w
  rw [centerD_apply]; exact Eq.symm (whole_perm _ a (Equiv.refl _) (x:=fun (_:Fin 1)=>p.2)
    (d:= fun _=> h) (v:=fun _=>frame Z r h w) (w:=own Z (r*T) v) (spectate F p.1) hS)

variable (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
def coefficients (d : Fin n→ℕ) (h : ℕ) : Comet (Owner F) G d h := fun o r x u=>
  (frame Z r h).symm (Q.packet h (position o.2 r x) (own Z r u) o.2)

/-- exact actual packet tested on these exterior fields. -/
lemma seal_terms (p : Owner F) {r : ℝ} (hr : 0 < r) {T : ℝ} (hT : 0<T)
    (x : Points n) {y : Points m} (hy : y∈Outside m) (u : Slots G d) (v : Slots G e) :
    let z := position p.2 (r*T) y; let w := own Z (r*T) v
    at_far (measures F Z d e) (via Z) p r T x y u v - centerD F Z h e p r T y v (coefficients F Z Q d h p r x u) =
    whole (spectator F p.1) (position p.2 r x) (own Z r u) z w -
      upon (S:=S) (spectator F p.1) h p.2 z w (Q.packet h (position p.2 r x) (own Z r u) p.2) := by
  rw [← total,total_eq,center_upon F Z e p hr hT hy]; simp [coefficients]

end YM.FVA2.GradedFar259.Original
