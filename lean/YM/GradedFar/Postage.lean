import YM.GradedFar.Pave
/-!
# The actual derivative field at the committed frame has through-required order coordinates

Assumption: (QScale preceding comparison on n=2 compact stage) and physical frame compatibility.
Needn't assume derivative estimates on either kernel. Proof FTC with nondegenerate detector integrated
along the slot line (same integral length from previous file). Every radius uses same Point stage task.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries MeasureTheory
open Climb Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open Matrix
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable (a:Axis) {h:ℕ}
local notation "Σ0"=> outgoing RootG
local notation "Leg" => Toon G (h+1)
local instance {n:ℕ} : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul

lemma changing{n:ℕ} (B:MultilinearMap ℂ (fun _:Fin n=> Sec G h) ℂ)(u:ListInput G n h)(v:Sec G h)(i:Fin n): B (update u i v)=
    ∑ l:Toon G h, coord l v * B (update u i (theory l)):=by
    let f:=B.toLinearMap u i; have hv:v=∑ j:Toon G h,coord j v • theory j:=(all_sig v).symm
    change f v=∑ l:Toon G h, _ * f _; nth_rw 1 [hv]; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> map_smul ..

local notation "Avenue"=> paving a
lemma vein (B:MultilinearMap ℂ (fun _ :Fin (1+1)=> Sec G h) ℂ) (i:Toon G h)(v:Sec G h):
    B (carpet h v (Bank.detector i)) = ∑ j:Toon G h, coord j v * B (carpet h (theory j) (Bank.detector i)):= by
    -- cannot simp_rw carpet_update (rec)
    rw [carpet_update,changing]; exact Finset.sum_congr rfl fun j _=> congrArg (fun p:(Fin (1+1)→Sec G h)=> coord j v * B p) (carpet_update ..).symm

namespace Docket
def toll (δ r:ℝ)(i j:Leg):= ∫ x in (0:ℝ)..1,frank F J none (h+1) r (paving a δ x) (carpet (h+1) (theory j) (Bank.detector i))
def see (v:Sec G h)(δ r:ℝ) (j:Leg)(x:ℝ):ℂ:=
    frank F J none (h+1) r (paving a δ x) (carpet (h+1) (up (Nat.le_succ h) v) (Bank.detector j))
def tab (δ r:ℝ)(v:Sec G h)(i: Leg) := (δ:ℂ)⁻¹ * (see F J a v δ r i 1-see F J a v δ r i 0)

variable {a}{δ:ℝ}(hv:Paved a δ)(he:0<δ){r:ℝ}
include hv in
lemma records {h:ℕ}(hr:0<r)(u:ListInput G (1+1) h): IntervalIntegrable (fun x=> frank F J none h r (paving a δ x) u) volume 0 1:=
    ((true_views F J none hr u).continuousOn.comp (track a δ).continuousOn fun _ hx=> hv _ hx).intervalIntegrable
include hv he in
lemma draw (hr:0<r)(i:Leg)(v:Sec G h)(hw:∀ u:Sec G h,
    assign J r (h+1) (up (Nat.le_succ h) u)=F.sector.derivatives.rise (Nat.le_succ h) (assign J r h u)):
    ∑ j:Leg,toll F J a δ r i j* coord j (push F J h a r v) = tab F J a δ r v i:=by
    let u:= Bank.detector i; let k:=push F J h a r v; let q(x:ℝ):=frank F J none (h+1) r (Avenue δ x) (carpet (h+1) k u)
    have ha(x:Points (1+1))(hx:x∈conf (1+1)): Points.gradient 0 a (fun x'=>frank F J none (h+1) r x'
        (carpet (h+1) (up (Nat.le_succ h) v) u)) x=frank F J none (h+1) r x (carpet (h+1) k u) := by
       rw [carpet_update (G:=G),elevate F J hr none hw hx,← carpet_update ..];
    have hQ:IntervalIntegrable q volume 0 1:=records F J hv hr _
    have hA(s:ℝ)(hs:s∈ uIcc (0:ℝ) 1): HasDerivAt (see F J a v δ r i) ((δ:ℂ)*q s) s:= by
       let U x:= frank F J none (h+1) r x (carpet (h+1) (up (Nat.le_succ h) v) u)
       have hx : DifferentiableAt ℝ U (paving a δ s):=((true_views F J none hr _).contDiffAt ((conf_open _).mem_nhds (hv s hs))).differentiableAt (by simp)
       refine (slope_chain (f:=U) Σ0 _ s hx).congr_deriv ?_; rw [map_smul]; exact congrArg (δ • ·) (ha _ (hv s hs))
    have hh:= (intervalIntegral.integral_eq_sub_of_hasDerivAt hA (hQ.const_mul (δ:ℂ))); rw [intervalIntegral.integral_const_mul] at hh
    unfold tab; rw [← hh,← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr he.ne'),one_mul]
    dsimp only [q,u]; unfold toll; simp_rw [vein (v:=k)]; rw [intervalIntegral.integral_finsetSum];
    · apply Finset.sum_congr rfl; intro j _; rw [intervalIntegral.integral_const_mul,mul_comm];
    exact fun j _=> (records F J hv hr _).const_mul _

variable {t:ℝ→ℝ}(ht:Coupling G t)(HX:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t (1+1) (h+1))
lemma alongPath {n l:ℕ} {a b:ℝ}(u:ListInput G n l){A:Arenas G}(Xh:ClassExpansion F J A t n l)
    (p:ℝ→Points n)(Hp:Continuous p)(H:MapsTo p (uIcc a b) (conf n)) : Receives t trail (fun r (x:↥(uIcc a b))=>frank F J none l r (p x.val) u)
    (fun x=>sent A l (p x.val) u) := by
    let K:= p '' uIcc a b; obtain hx:= Xh K (isCompact_uIcc.image Hp) H.image_subset u; let e (x:↥(uIcc a b)): ↥K:=⟨p x.val, mem_image_of_mem p x.property⟩
    exact hx.along e

include hv HX
lemma along (u: ListInput G (1+1) (h+1)): Receives t trail
    (fun r (x:↥(uIcc (0:ℝ) 1))=> frank F J none (h+1) r (paving a δ x.val) u) (fun x=> sent X (h+1) (paving a δ x.val) u):=by
    have ho : MapsTo (paving a δ) (uIcc (0:ℝ) 1) (conf (1+1)):= fun _ hh=> hv _ hh
    have he:= alongPath F J (t:=t) (l:=h+1) (n:=1+1) (a:=0) (b:=1) u HX (paving a δ) (track a δ) ho
    exact he
include H in
lemma supplies (i j:Leg): Expansion t trail (fun r=> toll F J a δ r i j) (avenue X (h+1) a δ i j):=by
    let u:= carpet (h+1) (theory j) (Bank.detector i); refine integrates (f:=fun r x=>frank F J none (h+1) r (paving a δ x) u) (along F J Z hv HX u) ?_ (fun k=>?_)
    · filter_upwards [self_mem_nhdsWithin] with r hr; exact records F J hv hr _
    simp_rw [accounted]; simp_rw [sent,coeff_mk]; exact ((kernel_continuous Z M H _ _).comp (track a δ).continuousOn fun _ h=>hv _ h).intervalIntegrable
include ht hG in
lemma earnings (v:Sec G h)(i:Leg):∃ Z, Expansion t trail (fun r=>tab F J a δ r v i) Z:=by
    obtain hr:= along F J Z hv HX (carpet (h+1) (up (Nat.le_succ h) v) (Bank.detector i))
    exact ⟨_, (Receives.fix (δ:ℂ)⁻¹).mul ((hr.along (fun _:Unit=>⟨1,right_mem_uIcc⟩)).sub (hr.along (fun _:Unit=>⟨0,left_mem_uIcc⟩)))
      (Coupling.conforms hG ht)⟩
omit hv
open Neighbor (Included)
include ht H
lemma compactPush (a:Axis) (heard: Included F J h (h+1) (Nat.le_succ h))(u:Sec G h)(i:Leg): ∃ Z, Expansion t trail
    (fun r=> coord i (push F J h a r u)) Z:=by
    obtain ⟨δ,hδ,hp,hκ⟩:= ((show ∀ᶠ δ:ℝ in trail,0<δ from self_mem_nhdsWithin).and ((clear_paving a).and (refunded Z M H (h+1) a))).exists
    let v r (i:Leg):= coord i (push F J h a r u)
    choose P hP using earnings F J Z (a:=a) hp ht HX (hG:=hG) u
    refine ExpSolve (A:=fun r=> Matrix.of (toll F J a δ r)) (f:=v) (Coupling.conforms hG ht)
        (fun j l=> supplies F J Z M H hp HX j l) ?_ hκ hP i
    filter_upwards [self_mem_nhdsWithin, heard] with r (hr:0<r) hx; funext i; exact draw F J hp hδ hr i u hx
end Docket
end YM.Integration.GradedFar.Tariff
