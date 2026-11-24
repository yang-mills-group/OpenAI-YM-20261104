import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Toward.Account
import YM.OPE.Orbits.System
import YM.PhysMS.Frame.Measured

/-!
# Keep physical layouts and labels throughout M

Sec inputs identified with Bel slots by the project convention, and placed
using exactly the tower specified. Useful without choosing the tower (in the
end theorem will instantiate with the Actual position H of the graded far-field construction).
Use only at the same distinct positions as the formal calls; no inference made
at nonconfigurations. On the final's actual Table. Viewer remains arbitrary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.Compare
open Function Filter Set O.Enh OPE OPE.Orbits PowerSeries XSpace XSpace.Normalize
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {n m p k h H : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (U : Spec.Final C f S) (X : ℝ → PhysMS.tower S)
    (j : Viewers U) -- incl unselected


def place (o : E4) (r : ℝ) (x : Points n) (i : Fin n) := o + r • x i
@[simp] lemma place_null (o : E4) (r : ℝ) : place o r (0 : Points n)= fun _ => o := by
  funext i; change o+r • 0=o; rw [smul_zero,add_zero]
lemma far_place (y : Points m) (o : E4) (r T : ℝ) : place o r (T • y)=place o (r*T) y := by
  funext i; simp only [place, PiLp.smul_apply,mul_smul]

lemma place_distinct (x : Points n) (o : E4) {r : ℝ} (hr : 0 < r) (hx : x ∈ conf n) : Injective (place o r x) :=
  fun _ _ q => hx (smul_right_injective E4 hr.ne' (add_left_cancel q))
lemma beside_place {x : Points n} {y : Points m} (o : E4) {r : ℝ} (hr : 0 < r)
    (hx : forest x y ∈ conf (n+m)) : Injective (beside (place o r x) (place o r y)) := by
  have a : beside (place o r x) (place o r y)= place o r (forest x y) ∘ finSumFinEquiv := by
    funext i; rcases i with i|i <;> simp [place]
  rw [a]; exact (place_distinct _ o hr hx).comp finSumFinEquiv.injective

lemma beside_sole {y : Points m} (o : E4) {r : ℝ} (hr : 0 < r)
    (hy : outgoing y ∈ conf (1+m)) : Injective (beside (sole o) (place o r y)) := by
  have p := beside_distinct.mp (beside_place o hr hy)
  refine beside_distinct.mpr ⟨Function.injective_of_subsingleton _, p.2.1, fun _ l => ?_⟩
  have hp := p.2.2 0 l; rw [place_null] at hp; exact hp

def field (r : ℝ) (d : ℕ) : Sec G d ≃ₗ[ℂ] S.Field d :=
  (Maxwell.Free.fields C.labels d).symm.trans (X r d)
def ratio (r s : ℝ) (k : ℕ) : Sec G k ≃ₗ[ℂ] Sec G k := (field X s k).trans (field X r k).symm
variable (r s T : ℝ) (o : E4) (x : Points n) (y : Points m) (u : Appointed122Fields G d) (v : Appointed122Fields G e)
lemma field_ratio (h : ℕ) (p : Sec G h) : field X r h (ratio X r s h p)= field X s h p := by rw [ratio, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
def labels (X : ℝ → PhysMS.tower S) (r : ℝ) (u : Appointed122Fields G d) : Labels S d := fun i => field X r (d i) (u i)

/-- This is the actual measurement of the original theory in the chosen viewer;
use only on Conf. -/
def measured (U : Spec.Final C f S) (X : ℝ → PhysMS.tower S) (j : Viewers U)
    (r s : ℝ) (o : E4) (x : Points n) (y : Points m) (d : Fin n → ℕ) (e : Fin m → ℕ) :
    Form G d (Form G e ℂ) :=
  (MultilinearMap.compLinearMapₗ (fun i : Fin m => (field X s (e i)).toLinearMap)).compMultilinearMap
    (((moment (d := Sum.elim d e) (spectator U j) (beside (place o r x) (place o r y))).currySum).compLinearMap
      fun i : Fin n => (field X r (d i)).toLinearMap)

theorem measured_whole : measured U X j r s o x y d e u v =
    whole (spectator U j) (place o r x) (labels X r u) (place o r y) (labels X s v) := by
  let L := moment (d := Sum.elim d e) (S:=S) (spectator U j) (beside (place o r x) (place o r y))
  change L.currySum (labels X r u) (labels X s v) = L (stages _ _)
  erw [MultilinearMap.currySum_apply]; apply congr_arg _; funext i; cases i <;> rfl

def actors (r T : ℝ) (e : Fin m → ℕ) : ∀ i, FieldEnd G (e i) := fun i => (ratio X r (r*T) (e i)).toLinearMap
lemma labels_preapply : labels X r (preapply (actors X r T e) v)= labels X (r*T) v := funext (fun i=> field_ratio X r (r*T) (e i) (v i))

def Y (u : Appointed122Fields G d) (v : Appointed122Fields G e) := measured U X j r (r*T) o x (T • y) d e u v
lemma Y_whole : Y U X j r T o x y u v = whole (spectator U j) (place o r x) (labels X r u)
    (place o (r*T) y) (labels X (r*T) v) := by rw [Y,measured_whole, far_place]
lemma measured_raw : measured U X j r r o x (T•y) d e u (preapply (actors X r T e) v) = Y U X j r T o x y u v := by
  rw [measured_whole,Y,measured_whole,labels_preapply]

/-- Original observer D's: sole field x at o, sent through **H_r**, same exterior as in Y. -/
def D (h : ℕ) (v : Appointed122Fields G e) : Sec G h →ₗ[ℂ] ℂ :=
  upon (spectator U j) h o (place o r (T • y)) (labels X (r*T) v) ∘ₗ (field X r h).toLinearMap
lemma D_eval (h : ℕ) (p : Sec G h) : D U X j r T o y h v p =
    upon (spectator U j) h o (place o r (T•y)) (labels X (r*T) v) (field X r h p) := rfl

/-- Index replacement rows by Fin 1 in the Mixed layouts of the formal proof. -/
lemma Y_sole {r0 : ℝ} (p : Sec G h) (hr : 0 < r0) (hy : outgoing (T•y) ∈ conf (1+m)) :
    Y U X j r0 T o (0 : Points 1) y (d:=fun _=>h) (fun _=>p) v = D U X j r0 T o y h v p := by
  rw [Y,measured_whole,D_eval,place_null]
  exact whole_perm _ (Equiv.ofUnique _ _) (Equiv.refl _) (x:=sole o) (d:=fun _:Unit=>h)
    (v:=sole (field X r0 h p)) (w:=labels X (r0*T) v) (spectate U j) (beside_sole o hr hy)

variable (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
/-- c_W^h of (G.6); true same output horizon, using the project's Reader. -/
def cW (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (h : ℕ) : Sec G h :=
  (field X r h).symm (Q.packet h (place o r x) (labels X r u) o)
lemma packet_price (h : ℕ) (hr : 0 < r) (hy : outgoing (T•y) ∈ conf (1+m)) :
    D U X j r T o y h v (cW U X r o x u Q h) =
    Orbits.trunc (spectator U j) U Q h (place o r x) o (labels X r u) (place o (r*T) y) (labels X (r*T) v) := by
  rw [D_eval,cW, LinearEquiv.apply_symm_apply, packet_read U Q _ o _ _ _ j h (beside_sole o hr hy),far_place]
end YM.FVA2.GradedFar.Compare
