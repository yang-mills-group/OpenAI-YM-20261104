import YM.GradedFar.Glow
/-!
# Differentiable post-arena and iterated shape variations

Using expansions for *all* (finite) installed programs -- includes lifted caps & their
common q price. No differentiation across V or calibration labels or length; just Euclidean shape
of given reading. (Use any word of coordinate direction derivatives.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Sunshine
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open Neighbor (Included)
open scoped Topology BigOperators Classical ContDiff
-- lexical references `Neighbor` names; avoid open parentheses preceding MS.Menus? fix
variable {n h m:ℕ}
open Metric Asymptotics
local notation "Bt"=> Points n
abbrev TraceOrder (n:ℕ) := List (Fin n×Axis)
def δ (L:TraceOrder n)(f:Points n→ℂ): Points n→ℂ := match L with
 | []=> f
 | i::L=> δ L (Points.gradient i.1 i.2 f)
lemma δ_congr {f g:Bt→ℂ} {X:Set Bt}(hX:IsOpen X)(he:EqOn f g X)(L:TraceOrder n) : EqOn (δ L f) (δ L g) X:= by
 induction L generalizing f g with
 | nil=> exact he
 | cons i L ih=> apply ih; intro x hx; have ht:f=ᶠ[𝓝 x] g:= (show ∀ᶠ y in 𝓝 x, y∈X from hX.mem_nhds hx).mono (fun i h=> he h); exact DFunLike.congr_fun ht.fderiv_eq (Points.direction i.1 i.2)
lemma smooth_grad {X:Set Bt}(hX:IsOpen X){f:Bt→ℂ}(hf:ContDiffOn ℝ ∞ f X)(i:Fin n×Axis): ContDiffOn ℝ ∞ (Points.gradient i.1 i.2 f) X:=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hX).1 hf).2.clm_apply contDiffOn_const
lemma smooth_δ {X:Set Bt}(hX:IsOpen X){f:Bt→ℂ}(hf:ContDiffOn ℝ ∞ f X)(L:TraceOrder n): ContDiffOn ℝ ∞ (δ L f) X:= by
 induction L generalizing f with
 | nil=> exact hf
 | cons i L ih=> exact ih (smooth_grad hX hf i)
-- algebra consequences also on OPE program later
lemma δ_sum {X:Set Bt}(hX:IsOpen X){I:Type*}(v:Finset I)(f:I→Bt→ℂ)(hf:∀ i∈v,ContDiffOn ℝ ∞ (f i) X)
    (L:TraceOrder n){x:Bt}(hx:x∈X): δ L (fun y=> ∑ i∈v,f i y) x=∑ i∈v,δ L (f i) x:= by
 induction L generalizing f x with
 | nil=> rfl
 | cons a L ih=>
   change δ L (Points.gradient _ _ _) x = _; rw [δ_congr hX (f:=Points.gradient a.1 a.2 (fun y=>∑ i∈v,f i y)) (g:=fun y=> ∑ i∈v,Points.gradient a.1 a.2 (f i) y) ?_ L hx]; · exact ih (fun i => Points.gradient a.1 a.2 (f i)) (fun i hi=> smooth_grad hX (hf i hi) a) hx
   intro y hy; change (fderiv ℝ _ _) _ = _; rw [fderiv_fun_sum (fun i hi=>((hf i hi).contDiffAt (hX.mem_nhds hy)).differentiableAt (by simp)),_root_.sum_apply]; rfl
lemma δ_const_mul {X:Set Bt}(hX:IsOpen X){f:Bt→ℂ}(hf:ContDiffOn ℝ ∞ f X) (z:ℂ)(L:TraceOrder n){x:Bt}(hx:x∈X):
    δ L (fun y=> z*f y) x=z*δ L f x:= by
 induction L generalizing f x with
 | nil=> rfl
 | cons i L ih=>
   change δ L (Points.gradient _ _ _) x = _; rw [δ_congr hX (f:=Points.gradient i.1 i.2 (fun y=>z*f y)) (g:=fun y=>z*Points.gradient i.1 i.2 f y) ?_ L hx]; · exact ih (smooth_grad hX hf i) hx
   intro y hy; change (fderiv ℝ _ _) _ = _; rw [fderiv_const_mul ((hf.contDiffAt (hX.mem_nhds hy)).differentiableAt (by simp))]; rfl

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
variable (Z: WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H: Main.Match Z hG M σ true)
local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {t:ℝ→ℝ}(ht:Coupling G t)(hμ: ∀ h, Included F J h (h+1) (Nat.le_succ h))(hX:∀ h, ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n h)
    (A:∀ h,Future G h) (hA:∀ h,PaidFuture F J (A h) t)
include ht H hμ hX hA
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
set_option maxHeartbeats 550000 in
lemma cents (i:ℕ)(v:ListInput G n h)(k:ℕ) : ContDiffOn ℝ i (fun x=> coeff k (sent X h x v)) (conf n):=by
 induction i generalizing h k with
 | zero=> rw [Nat.cast_zero, contDiffOn_zero]; simp_rw [sent,coeff_mk]; exact kernel_continuous Z M H v k
 | succ i ih=>
    let L:=specTariff (A h) X v k
    have hh(x:Points n)(hx:x∈ conf n) := glow_at (A h) F J Z M H ht (hμ h) (hX h) (hX (h+1)) (hA h) hx v k
    have he:ContDiffOn ℝ i L (conf n):= by
       unfold L specTariff; refine ContDiffOn.sum (fun a (_:a∈Finset.univ)=>?_)
       have hf:ContDiffOn ℝ i (fun x=> coeff k (iris_one (A h) X a v x)) (conf n):= by
         simp_rw [iris_one,map_sum,coeff_mul]; refine ContDiffOn.sum (fun a (_:a∈Finset.univ)=>?_); exact ContDiffOn.sum (fun t _=> contDiffOn_const.mul (ih _ t.2))
       exact hf.smul contDiffOn_const
    rw [Nat.cast_add_one]; exact (contDiffOn_succ_iff_fderiv_of_isOpen (conf_open _)).2 ⟨fun x hx=> (hh x hx).differentiableAt.differentiableWithinAt, (by simp), he.congr (fun _ hx=> (hh _ hx).fderiv)⟩
lemma Air (v:ListInput G n h)(k:ℕ): ContDiffOn ℝ ∞ (fun x=> coeff k (sent X h x v)) (conf n):=
 contDiffOn_infty.mpr fun i=> cents F J Z M H ht hμ hX A hA i v k
-- differentiate that formal read, apply α replacement to one slot. This identity already implies higher formal rotations by iteration.
variable {y:Points n}(hy:y∈conf n)
local notation "leg"=> Toon G (h+1)
local notation "α"=> A h
-- perturbative expression for shape derivative on compact status
-- operator norms eventually on any fixed compact program. not iterated-fderiv wording.
def jetCost (L:TraceOrder n)(V:Arenas G)(h:ℕ)(v:ListInput G n h)(x:Points n): PowerSeries ℂ:= PowerSeries.mk
    (fun k=> δ L (fun y=> coeff k (sent V h y v)) x)
omit ht H hμ hX hA in
lemma jetCost_zero {V:Arenas G}(v:ListInput G n h)(x:Bt): jetCost [] V h v x=sent V h x v:= by ext1 k; rw [jetCost,coeff_mk]; rfl
include hy
lemma jetCost_cons (L:TraceOrder n)(q:Fin n×Axis)(v:ListInput G n h): jetCost (q::L) X h v y=
    ∑ j:leg, α q.2 (v q.1) j* jetCost L X (h+1) (update (climbing v) q.1 (theory j)) y:= by
 ext1 k; let Y(j:Toon G (h+1)):= update (climbing v) q.1 (theory j); let f(j:Toon G (h+1))(x:Bt):=sent X (h+1) x (Y j); let a:=α q.2 (v q.1)
 have he : EqOn (Points.gradient q.1 q.2 (fun x=> coeff k (sent X h x v))) (fun x=> coeff k (∑ j,a j*f j x)) (conf n):=
    fun x hx=> exposed (A h) F J Z M H ht (hμ h) (hX h) (hX (h+1)) (hA h) hx v k q
 simp_rw [jetCost,map_sum,coeff_mul,coeff_mk]; rw [δ,δ_congr (conf_open _) he L hy]; simp_rw [map_sum (coeff k),coeff_mul]
 let p:= Finset.HasAntidiagonal.antidiagonal k; have ho (i:leg)(u:ℕ×ℕ) : ContDiffOn ℝ ∞ (fun x=> coeff u.1 (a i)*coeff u.2 (f i x)) (conf n):= contDiffOn_const.mul (Air F J Z M H ht hμ hX A hA (Y i) _)
 rw [δ_sum (conf_open _) _ _ (fun i _=>ContDiffOn.sum (fun u _=> ho i u)) L hy]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [δ_sum (conf_open _) p _ (fun u _=>ho j u) L hy]; exact Finset.sum_congr rfl fun t _=> δ_const_mul (conf_open _) (Air F J Z M H ht hμ hX A hA (Y j) _) _ L hy
omit ht H hμ hX hA in
lemma physical_cons {r:ℝ}(hr:0<r)(H: Going F J h r)(P:Viewers F)(L:TraceOrder n)(q:Fin n×Axis)(v:ListInput G n h):
    δ (q::L) (fun x=> frank F J P h r x v) y = ∑ j:leg, coord j (push F J h q.2 r (v q.1))*δ L (fun x=>frank F J P (h+1) r x (update (climbing v) q.1 (theory j))) y := by
 let Y(j:leg):=update (climbing v) q.1 (theory j); let f(j:leg)(x:Bt):= frank F J P (h+1) r x (Y j); let c(j:leg):=coord j (push F J h q.2 r (v q.1))
 have he : EqOn (Points.gradient q.1 q.2 (fun x=> frank F J P h r x v)) (fun x=> ∑ i,c i*f i x) (conf n):= fun x hx=> (gradients F J hr P H v hx ..).trans (changing ..)
 rw [δ,δ_congr (conf_open _) he L hy,δ_sum (conf_open _) _ _ (fun i _=> contDiffOn_const.mul (true_views F J P hr (Y i))) L hy]; exact Finset.sum_congr rfl fun i _=> δ_const_mul (conf_open _) (true_views F J P hr (Y i)) _ L hy
end YM.Integration.GradedFar.Tariff.Sunshine
