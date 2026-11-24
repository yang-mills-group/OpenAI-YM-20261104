import YM.GradedFar.Neighbor
import YM.GradedFar.Vacant
import YM.GradedFar.Segment
import YM.Work.A04
import YM.Work.A05.Window
/-!
# The same compact stage moment with its posted prices; FTC along all shape slots

Used at the bridge from (fixed compact uniform expansion) and (*on grid* signed input)
to the actual moving-T continuum estimates. Do NOT change t along actual lines.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries MeasureTheory
open Climb Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar MS MS.Native MS.Land MS.Fleet
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
   (F:Final C f S)(J:ℝ→tower S){n h p :ℕ}
abbrev Ceiling (n h:ℕ): Fin n→ℕ:= fun _=>h
abbrev ListInput (G:Gauge)(n h:ℕ):= Inputs G (Ceiling n h)
local notation "g"=> strength G
-- true scanned value on whole profiles (never predividing).
def frank (v:Viewers F)(h:ℕ) (r:ℝ)(x:Points n) :=
    (S.classMoment (spectator F v) (Ceiling n h) (r•x)).compLinearMap (fun _ => (assign J r h).toLinearMap)
lemma frank_use (v:Viewers F)(r:ℝ)(x:Points n)(u: ListInput G n h):
    frank F J v h r x u = S.useAt (spectator F v) (r•x) (fun i=>⟨h,assign J r h (u i)⟩):= rfl
lemma kernel_smooth (v:Viewers F){r:ℝ}(hr:0<r)(w:Fin n→S.Tag): ContDiffOn ℝ ∞
    (fun x:Points n=> S.useAt (spectator F v) (r•x) w) (conf n) :=
    (S.class_smooth _ (spectate F v).smooth w).comp (by fun_prop) fun _ hx=>Work.A05.smul_conf hr hx
lemma true_views (v:Viewers F){r:ℝ}(hr:0<r)(u:ListInput G n h): ContDiffOn ℝ ∞ (fun x=> frank F J v h r x u) (conf n):= by simp_rw [frank_use]; exact kernel_smooth F v hr _
lemma transit (v:Viewers F){r:ℝ}(hr:0<r){x:Points n}(hx:x∈conf n)(a:Axis)(i:Fin n)(w:Fin n→S.Tag)(u:S.Field h) :
    Points.gradient i a (fun x=> S.useAt (spectator F v) (r•x) (update w i ⟨h,u⟩)) x = r • S.useAt (spectator F v) (r•x)
        (update w i ⟨h+1,F.sector.derivatives.deriv h a u⟩):= by
    have ha:=Work.A05.smul_conf hr hx; have hS:=spectate F v; have hC: DifferentiableAt ℝ (fun x=>S.useAt (spectator F v) x (update w i ⟨h,u⟩)) (r•x) :=
      ((S.class_smooth _ hS.smooth _).contDiffAt ((conf_open _).mem_nhds ha)).differentiableAt (by simp)
    exact (Work.A04.gradient_scaled r _ x hC i a).trans (congrArg (fun z:ℂ=>r • z) (F.sector.derivatives.derivative_slot
        (spectate_evolution F v) hS.laws.toSymmetric hS.smooth ha i w u a).symm)

def push (d:ℕ) (a:Axis) (r:ℝ): Sec G d→ₗ[ℂ] Sec G (d+1) :=
    (r:ℂ) • ((assign J r (d+1)).symm.toLinearMap.comp ((F.sector.derivatives.deriv d a).comp (assign J r d).toLinearMap))
lemma frank_update (v:Viewers F) (r:ℝ)(x:Points n)(u:ListInput G n h)(i:Fin n)(w:Sec G h):
    frank F J v h r x (update u i w)= S.useAt (spectator F v) (r•x) (update (fun i=>⟨h,assign J r h (u i)⟩) i ⟨h,assign J r h w⟩):=by
    rw [frank_use]; apply congrArg; funext j; by_cases hh:j=i; · subst j; simp
    rw [update_of_ne hh,update_of_ne hh]
-- derivative slot when we planned using through h+1 all slots, that one input from through h
lemma elevate {r:ℝ}(hr:0<r)(v:Viewers F) (hw:∀ u:Sec G h,
    assign J r (h+1) (up (Nat.le_succ h) u)=F.sector.derivatives.rise (Nat.le_succ h) (assign J r h u))
    {x:Points n}(hx:x∈conf n)(a:Axis)(u:ListInput G n (h+1))(i:Fin n)(l:Sec G h):
    Points.gradient i a (fun x=> frank F J v (h+1) r x (update u i (up (Nat.le_succ h) l))) x =
      frank F J v (h+1) r x (update u i (push F J h a r l)):=by
    let θ:=F.sector.derivatives; let k:=spectator F v; let U':=fun i=> (⟨h+1,assign J r (h+1) (u i)⟩:S.Tag)
    let y:=θ.deriv h a (assign J r h l); let w:Sec G (h+1):=(assign J r (h+1)).symm y
    have he : (fun x:Points n=> frank F J v (h+1) r x (update u i (up (Nat.le_succ h) l)))=ᶠ[𝓝 x]
        (fun x=> S.useAt k (r•x) (update U' i ⟨h,assign J r h l⟩)):=by
        filter_upwards [(conf_open _).mem_nhds hx] with b hb; rw [frank_update,hw]; exact θ.inclusion_slot (spectate_ready F v) (spectate F v).laws.toSymmetric _ (Work.A05.smul_conf hr hb) i U' _
    calc
      _ = Points.gradient i a (fun x=> S.useAt k (r•x) (update U' i ⟨h,assign J r h l⟩)) x :=
        DFunLike.congr_fun he.fderiv_eq (Points.direction i a)
      _ = r • S.useAt k (r•x) (update U' i ⟨h+1,y⟩):= transit F v hr hx _ _ _ _
      _ = _ := by
         have hv:push F J h a r l=(r:ℂ) • w:= rfl
         rw [hv,(frank F J v (h+1) r x).map_update_smul,frank_update,show assign J r (h+1) w=y from (assign J r (h+1)).apply_symm_apply _]; rfl
variable (A:Arenas G)
-- common cap form
noncomputable def declared (h:ℕ)(x:Points n)(k:ℕ):MultilinearMap ℂ (fun _ :Fin n=>Sec G h) ℂ := if hv:x∈conf n then A h n ⟨x,hv⟩ k else 0
def sent (h:ℕ)(x:Points n)(u:ListInput G n h): PowerSeries ℂ:= PowerSeries.mk (fun i=> declared A h x i u)
lemma cashed {x:Points n}(u:ListInput G n h)(hx:x∈conf n)(k:ℕ): coeff k (sent A h x u) = A h n ⟨x,hx⟩ k u:= by rw [sent,coeff_mk,declared,dif_pos hx]

variable (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
include H
lemma kernel_continuous (u:ListInput G n h)(k:ℕ):ContinuousOn (fun x=>declared X h x k u) (conf n):=by
    obtain hA:= (H.separatedOPE 0).wilson -- inspect
    have hv (p:Picks G (Ceiling n h))(x:Points n)(hx:x∈conf n) : declared X h x k (basisWord p)=coeff k (install X _ x (indexScan p)):= by
       rw [caring (indexScan p) (boundedByCaps p) hA.dimensions hx,test,Reg.Point.story,coeff_mk,declared,dif_pos hx]
    refine ((show ContinuousOn (fun x=> ∑ p:Picks G (Ceiling n h), multipliers u p • coeff k (install X _ x (indexScan p))) (conf n) from
        continuousOn_finsetSum Finset.univ (fun a _=> (continuousOn_const (c:=multipliers u a)).smul (hA.awake n (indexScan a) k))).congr (fun x hx=> ?_))
    dsimp only; rw [basis_sum (declared X h x k) u]; exact Finset.sum_congr rfl fun i _=> congrArg _ (hv i x hx)
omit H

def ClassExpansion (t:ℝ→ℝ)(n h:ℕ):Prop:= ∀ K:Set (Points n), IsCompact K→ K ⊆ conf n → ∀ u:ListInput G n h,
    Receives t trail (fun r (x:↥K)=> frank F J none h r x.val u) (fun x=> sent A h x.val u)

end YM.Integration.GradedFar.Tariff
