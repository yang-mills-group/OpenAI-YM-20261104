import YM.GradedFar.Postage
/-!
# Receive derivative identity at arbitrary separated line segments

FTC (Shape-direction) variant of the pairing argument in G.9 proof. We only use comparisons
at fixed compacts to get it. Does not require the formal estimates on the *moving* segments
until using this identity to estimate gradients/increments. Avoids needing as a hypothesis or
relying on the higher-order `FormalDemand` smoothness assertion; suffices to compare every
coefficient in FTC with continuous functions on that given line.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries MeasureTheory
open Climb Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {n h:ℕ} {r:ℝ}

-- adapting smaller moment_inclusion proof of AllOrder Leading Solve; keep to actual V
lemma frank_inclusion {d:Fin n→ℕ}(H:Through h d) (hr:0<r)(v:Viewers F)
    (hw:∀ i (u:Sec G (d i)),assign J r h (up (H i) u) =F.sector.derivatives.rise (H i) (assign J r (d i) u))
    (u:Inputs G d) {x:Points n} (hx:x∈conf n): frank F J v h r x (GradedFar.raised H u) = S.classMoment (spectator F v) d (r•x) (labels J r u):=by
    rw [frank_use]; let q i:S.Tag:=⟨d i,assign J r (d i) (u i)⟩; let p i:S.Tag:=⟨h,assign J r h (up (H i) (u i))⟩
    let t(z:Finset (Fin n))(i:Fin n):= if i∈z then p i else q i; let f:= S.useAt (spectator F v) (r•x)
    change f p=f q; suffices H:∀ z, f (t z)=f q from (by simpa only [t,Finset.mem_univ,↓reduceIte] using H Finset.univ)
    intro z; induction z using Finset.induction_on with
    | empty=> simp [t]
    | insert i z hi ih=>
      have hL:f (update (t z) i (p i))= f (update (t z) i (q i)):=by
        dsimp only [p,q,f]; rw [hw]; exact F.sector.derivatives.inclusion_slot (spectate_ready F v)
          (spectate F v).laws.toSymmetric _ (Work.A05.smul_conf hr hx) i _ _
      rw [show t (insert i z)= update (t z) i (p i) from (by funext j; by_cases h:j=i <;> simp [h,t]),hL, show update (t z) i (q i)=t z from
        (by funext j; by_cases h:j=i <;> simp [t,hi,h]), ih]
abbrev Going (d:ℕ) (r:ℝ):Prop:= ∀ u:Sec G d, assign J r (d+1) (up (Nat.le_succ d) u)=F.sector.derivatives.rise (Nat.le_succ d) (assign J r d u)

def climbing (p: ListInput G n h) : ListInput G n (h+1):= fun i=> up (Nat.le_succ h) (p i)
lemma gradients (hr:0<r)(v:Viewers F)(hw:Going F J h r)(u:ListInput G n h){x:Points n}(hx:x∈conf n)(i:Fin n)(a:Axis):
    Points.gradient i a (fun x=> frank F J v h r x u) x =
        frank F J v (h+1) r x (update (climbing u) i (push F J h a r (u i))):=by
    have he: (fun x=> frank F J v h r x u)=ᶠ[𝓝 x] (fun x=> frank F J v (h+1) r x (update (climbing u) i (up (Nat.le_succ h) (u i)))):=by
      filter_upwards [(conf_open _).mem_nhds hx] with x hx
      rw [show update (climbing u) i (up (Nat.le_succ h) (u i))=_ from update_eq_self i (climbing u)]
      exact (frank_inclusion F J (fun _=> Nat.le_succ h) hr v (fun _=>hw) u hx).symm
    exact (DFunLike.congr_fun he.fderiv_eq (Points.direction i a)).trans (elevate F J hr v hw hx a (climbing u) i (u i))

local instance {n:ℕ} : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
-- decompose along actual direction (as in WilsonMacroscopicDirectionalPacket.evaluate)
local notation "D" => Fin n × Axis
def parallel (l:Fin n×Axis)(x: Points n): ℂ:= (x l.1 l.2:ℝ)
lemma evaluate (L:Points n→L[ℝ]ℂ)(x:Points n): L x=∑ i:Fin n×Axis, parallel i x * L (Points.direction i.1 i.2):=by
    have hx:x=∑ i:Fin n×Axis,x i.1 i.2 • Points.direction i.1 i.2:=by
       ext i a; rw [←Finset.univ_product_univ,Finset.sum_product]; simp [Points.direction,Pi.single_apply,apply_ite]
    conv_lhs=> rw [hx];
    simp only [map_sum,map_smul]; rfl
lemma shift_cost (x: Points n)(i:Fin n×Axis): ‖parallel i x‖≤‖x‖:= by
    rw [parallel, Complex.norm_real]; exact (PiLp.norm_apply_le (x i.1) i.2).trans (PiLp.norm_apply_le x i.1)

def stepValue (v:Viewers F)(h:ℕ)(r:ℝ)(x e:Points n)(u:ListInput G n h) := ∑ i:Fin n×Axis, parallel i e *
    frank F J v (h+1) r x (update (climbing u) i.1 (push F J h i.2 r (u i.1)))
lemma income (hr:0<r)(hw:Going F J h r)(x v:Points n)(s:ℝ)(hx:slopePath x v s∈conf n)(z:Viewers F)(u:ListInput G n h):
    HasDerivAt (fun s=>frank F J z h r (slopePath x v s) u) (stepValue F J z h r (slopePath x v s) v u) s:=by
    refine (slope_chain (f:=fun x=> frank F J z h r x u) x v s ((true_views F J z hr u).contDiffAt ((conf_open _).mem_nhds hx)|>.differentiableAt (by simp))).congr_deriv ?_
    rw [evaluate]; exact Finset.sum_congr rfl fun i _=> congrArg (parallel i v*·) (gradients F J hr z hw u hx i.1 i.2)
lemma walking_cont (x v:Points n): Continuous (slopePath x v):= by unfold slopePath; fun_prop
lemma income_cont (z:Viewers F)(hr:0<r)(v:Points n)(u:ListInput G n h): ContinuousOn (fun x=> stepValue F J z h r x v u) (conf n):=
    continuousOn_finsetSum Finset.univ (fun _ _=> continuousOn_const.mul (true_views F J z hr _).continuousOn)

abbrev Walks {n:ℕ}(x v:Points n)(l m:ℝ):= MapsTo (slopePath x v) (uIcc l m) (conf n)
theorem earns (z:Viewers F)(hr:0<r)(hw:Going F J h r)(x v:Points n){l m:ℝ}(hv:Walks x v l m)(u:ListInput G n h):
    frank F J z h r (slopePath x v m) u - frank F J z h r (slopePath x v l) u=
      ∫ s in l..m, stepValue F J z h r (slopePath x v s) v u:=by
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun s=>frank F J z h r (slopePath x v s) u)
       (f':=fun s=>stepValue F J z h r (slopePath x v s) v u) (fun i hi=> income F J hr hw x v i (hv hi) z u)
       (((income_cont F J z hr v u).comp (walking_cont x v).continuousOn hv).intervalIntegrable)).symm

-- now compare on exact line at fixed inputs
local notation "Leg"=> Toon G (h+1)
abbrev Future (G:Gauge)(h:ℕ):= Axis→Sec G h→ Toon G (h+1)→ PowerSeries ℂ
variable (α: Future G h) (A:Arenas G)
def SpecCost (v:Points n)(x:Points n)(u:ListInput G n h):PowerSeries ℂ := ∑ i:Fin n×Axis, PowerSeries.C (parallel i v) *
    ∑ j:Leg, α i.2 (u i.1) j * sent A (h+1) x (update (climbing u) i.1 (theory j))

def PaidFuture (t:ℝ→ℝ):Prop:=∀ i u (j:Leg), Expansion t trail (fun r=> coord j (push F J h i r u)) (α i u j)
include H
lemma Spec_cont (e:Points n)(v:ListInput G n h)(i:ℕ): ContinuousOn (fun x=> coeff i (SpecCost α X e x v)) (conf n):=by
    simp_rw [SpecCost,map_sum,coeff_C_mul,map_sum,coeff_mul,sent,coeff_mk]; refine continuousOn_finsetSum _ (fun _ _=>continuousOn_const.mul ?_)
    exact continuousOn_finsetSum _ fun _ _=> continuousOn_finsetSum _ (fun _ _=>continuousOn_const.mul (kernel_continuous Z M H _ _))
variable {t:ℝ→ℝ}(ht:Coupling G t)(hμ:Neighbor.Included F J h (h+1) (Nat.le_succ h))
include ht hμ in
theorem futureWins (hk: ClassExpansion F J X t 2 (h+1)): ∃ α: Future G h,PaidFuture F J α t:=by
    choose α hv using fun i u j=> Docket.compactPush F J Z M H ht hk i hμ u j
    exact ⟨α,hv⟩
variable (hX: ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n h)
    (hY: ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n (h+1)) (hP:PaidFuture F J α t)
omit H
include ht hP hG hY in
lemma pick (x v:Points n){l m:ℝ}(hx:Walks x v l m)(u:ListInput G n h): Receives t trail
    (fun r (s:↥(uIcc l m))=> stepValue F J none h r (slopePath x v s.val) v u) (fun s=>SpecCost α X v (slopePath x v s.val) u) := by
    have he:= Coupling.conforms hG ht
    let θ(s:↥(uIcc l m)):= slopePath x v s.val
    unfold SpecCost stepValue; refine Receives.sum _ (fun i _=>?_); simp_rw [changing (frank F J none (h+1) _ _) (climbing u) (push F J h i.2 _ (u i.1))]
    refine Receives.mul (Receives.fix _) (Receives.sum _ (fun j _=> ?_)) he
    exact Receives.mul ((hP _ _ _).along (fun _:↥(uIcc l m)=>()))
       (Docket.alongPath F J _ hY _ (walking_cont x v) hx) he
include H ht hP hX hY hμ
lemma fixedLine (x v:Points n){l m:ℝ}(hx: Walks x v l m)(u:ListInput G n h):
    sent X h (slopePath x v m) u - sent X h (slopePath x v l) u= operand l m (fun s=> SpecCost α X v (slopePath x v s) u):=by
    obtain hr:=Docket.alongPath F J u hX (slopePath x v) (walking_cont x v) hx
    have hv(s:ℝ)(hs:s∈uIcc l m): Expansion t trail (fun r=> frank F J none h r (slopePath x v s) u) (sent X h (slopePath x v s) u):=
       Receives.along hr (fun _:Unit=>⟨s,hs⟩)
    obtain he:= Receives.sub (hv m right_mem_uIcc) (hv l left_mem_uIcc)
    have hz:= integrates (f:=fun r s=>stepValue F J none h r (slopePath x v s) v u) (pick F J Z α ht hY hP x v hx u (hG:=hG))
       ( (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin).mono (fun r hr=>
          ((income_cont F J none hr v u).comp (walking_cont x v).continuousOn hx).intervalIntegrable ))
       (fun i=> ((Spec_cont Z M H α v u i).comp (walking_cont x v).continuousOn hx).intervalIntegrable)
    refine Receives.same (Coupling.conforms hG ht) (ht.positive.mono fun x hx=>hx.ne') (F:=fun _=> sent X h (slopePath x v m) u -sent X h (slopePath x v l) u) ?_ hz ()
    exact Receives.congr he (( (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin).and hμ ).mono
        (fun r h=> funext (fun (_:Unit)=>earns F J none h.1 h.2 x v hx u))) (fun _=>rfl)
end YM.Integration.GradedFar.Tariff
