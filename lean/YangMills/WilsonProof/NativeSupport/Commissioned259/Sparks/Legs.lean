import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Final
import YM.Work.A04
/-! # Price crossing arbitrary layout inside enlarged Far clearance: derivative of *true*
    scaled point along coordinate = raising in measured sector. (H fixed.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Sparks
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original Matrix Quotes
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e l : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J : ℝ→PhysMS.tower S) (hJ:Leading U J)
    (v : Viewers U) {x:Points n} {r:ℝ} (hr:0<r) (hx:x∈conf n)
local notation "late" => 𝓝[>] (0:ℝ)

def trueK (r:ℝ)(x:Points n)(d:ℕ) : Structure1.Point G d n := (S.classMoment (spectator U v) (fun _=>d) (r•x)).compLinearMap fun _=>(frame J r d).toLinearMap

def upgrade (d:ℕ)(r:ℝ)(a:Axis) : Sec G d→ₗ[ℂ] Sec G (d+1) := (r:ℂ) • ((frame J r (d+1)).symm.toLinearMap ∘ₗ (U.sector.derivatives.deriv d a) ∘ₗ (frame J r d).toLinearMap)
lemma original (r:ℝ)(x:Points n)(d:ℕ) : trueK U J none r x d=Paper.point U J r d n x:= rfl

variable (u:Tags G l n)
local notation "Θ" => spectator U v
local notation "RowHeight" => heights U J r l
include hr hx
lemma regular_at (u:Tags G l n) : ContDiffAt ℝ ∞ (fun x=>trueK U J v r x l u) x := by
  let w j:= (⟨l,frame J r l (u j)⟩: S.Tag); exact ((S.class_smooth Θ (spectate U v).smooth w).contDiffAt ((conf_open _).mem_nhds (Work.A05.smul_conf hr hx))).comp (f:=fun x:Points n=>r • x) x (contDiffAt_id.const_smul r)
lemma rises_on (hd:RowHeight) {D : Fin n→ℕ} (w:Slots G D)(he:∀ i,D i ≤ l):
    trueK U J v r x l (liftSlots he w)= S.classMoment Θ D (r • x) (fun i=>frame J r (D i) (w i)) := by
  change (S.classMoment (spectator U v) (fun _=>l) (r • x)) (fun i=>frame J r l (up (he i) (w i))) = _; simp_rw [hd (D _) (he _)]
  exact AllOrder.Leading.moment_inclusion (a:=D) (d:=fun _=>l) (spectate U v).laws.toSymmetric (spectate_ready U v) he (Work.A05.smul_conf hr hx) _
lemma checked (hd : RowHeight) (h:d≤l) (v':Sec G d) (i:Fin n) :
    trueK U J v r x l (update u i (up h v'))=
      S.useAt Θ (r • x) (update (fun i=> (⟨l,frame J r l (u i)⟩: S.Tag)) i (⟨d,frame J r d v'⟩: S.Tag)) := by
  refine Eq.trans ?_ (U.sector.derivatives.inclusion_slot (spectate_ready U v) (spectate U v).laws.toSymmetric h (Work.A05.smul_conf hr hx) i _ _)
  let u₀:= update u i (up h v');change S.useAt Θ (r • x) (fun i=> (⟨l,frame J r l (u₀ i)⟩:S.Tag))=_; congr 1; funext j; unfold u₀; by_cases hj:j=i
  · subst i; rw [update_self,update_self,hd]
  rw [update_of_ne hj,update_of_ne hj]

lemma entry (hd:RowHeight) (he:d+1≤l)(u:Tags G l n)(b:Sec G d)(a:Axis)(i:Fin n) :
    Points.gradient i a (fun y=> trueK U J v r y l (update u i (up ((Nat.le_succ _).trans he) b))) x =
      trueK U J v r x l (update u i (up he (upgrade U J d r a b))) := by
  let X j:= (⟨l,frame J r l (u j)⟩:S.Tag); let B:=frame J r d b; let w:=update X i (⟨d,B⟩:S.Tag)
  have ht := U.sector.derivatives.derivative_slot (spectate_evolution U v) (spectate U v).laws.toSymmetric (spectate U v).smooth (Work.A05.smul_conf hr hx) i X B a
  let Q (x:Points n):= S.useAt Θ x w
  have hh : ContDiffAt ℝ ∞ Q (r • x) := (S.class_smooth Θ (spectate U v).smooth w).contDiffAt ((conf_open _).mem_nhds (Work.A05.smul_conf hr hx))
  refine Eq.trans (Analysis.GermD (Points.direction i a) (g:=fun x=>Q (r • x)) ?_) ?_
  · filter_upwards [(conf_open _).mem_nhds hx] with y hy; exact checked U J v hr hy u hd _ b i
  let Y:= (frame J r (d+1)).symm (U.sector.derivatives.deriv d a B)
  change Points.gradient i a (fun x:Points n=> Q (r • x)) x=_; rw [Work.A04.gradient_scaled r Q x (hh.differentiableAt (by simp)) i a]; unfold upgrade; change _ = _; rw [LinearMap.smul_apply,map_smul,MultilinearMap.map_update_smul]
  rw [checked U J v hr hx u hd he]; change r • Points.gradient _ _ Q _= (r:ℂ) • S.useAt Θ _ (update X i (⟨d+1,frame J r _ Y⟩: S.Tag))
  unfold Y Q; rw [ LinearEquiv.apply_symm_apply, ← ht ]; exact Complex.real_smul ..

lemma column (hd:heights U J r (d+1))(u:Tags G d n)(a:Axis)(i:Fin n) :
    Points.gradient i a (fun y=> trueK U J v r y d u) x = trueK U J v r x (d+1)
      (update (up (Nat.le_succ _) ∘ u) i (upgrade U J d r a (u i))) := by
  refine Eq.trans (Analysis.GermD (Points.direction i a) ?_) (entry U J v hr hx hd le_rfl (up (Nat.le_succ _) ∘ u) (u i) a i)
  filter_upwards [(conf_open _).mem_nhds hx] with y hy
  rw [show update _ i (up _ _) = up (Nat.le_succ _) ∘ u from update_eq_self i _ ]
  exact Eq.symm (rises_on U J v hr hy hd u (fun _=> Nat.le_succ _))
end YM.FVA2.GradedFar259.Sparks
