import YM.AllOrder.Wheel.Budget
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Wheel
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Catch Catch.Clock Floe StateE Pace Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{L n f : Side}{ι:Type*}{T:Clock ι} {K:KernelChoices}{P:Patch}{σ C b a D η κ:ℝ}{k l p j M:ℕ}
open ConnectedActivityE6.Coat Shellac Work.G05
variable (S:Stage) (R:ι→PathData G) (hG:G.Simple) {n:ι→Side} {f Λ a' b':ι→ℝ} {U:ι→ Age→ℕ} (h:∀ᶠ i in T.rail,(R i).Bounds S.clip S.width S.paths (Λ i))
    (x: ∀ i,Apex (n i) G) {β:ι→ℝ} (ht:Epoch T β) (hp:T.Meter Λ 0) (hq:T.Meter (fun i=> (Fintype.card (Primary (n i) G):ℝ)) 0) (ha:T.Meter f (-(1/2)))(hv:∀ᶠ i in T.rail,0<f i ∧ ‖x i‖≤ f i)(hj:k+3 ≤ j)
local notation "A"=> T.Meter
local notation "V"=> fun i=> Apex (n i) G
local notation "H"=> (fun i=> (f i)⁻¹)
local notation "u"=>fun i=> gStep (β i)
local notation "M'"=> fun i=> staff S.clip (R i) (n i)
local notation "Q"=> fun (i:ι)=> BareRates.pre G S.width S.paths j
local notation "L"=> fun i=> Precision.loop (R i) ∘ Desk.night (c:=n i)
local notation "F'"=> Shellac.off
local notation "τ"=> Estate («V»:=V) T j k (H) u x
variable (z:Age) (s:∀ i:ι, Packet G z.r)(Q':ι→ Coin)
local notation "e"=> Age.e z
local notation "r"=> Age.r z
local notation "s₀"=> (fun i=>speak (s i) (n i))
structure Atlas (z:Age)(s:∀ i:ι,Packet G z.r)(T:Clock ι): Prop where
    pays : ∃ (σ:ℝ)(a:ι→ℝ), 0<σ ∧ T.Meter a 0∧ ∀ᶠ i in T.rail,Charged (s i) σ (a i)
namespace Atlas
variable (hσ:Atlas z s T)
local notation "T₁"=> T.book (fun i=> Metric.closedBall (0: Apex (n i) G) (f i))
set_option quotPrecheck false
local notation "I"=>fun i:ι=> (Fintype.card (Primary (n i) G):ℝ)
lemma space (h:∀ᶠ i in T.rail, Charged (s i) a (Λ i))(ht:0<a) (hp:A Λ η)(ha:T.Meter f (-(1/2))) (hq:T.Meter I 0)(hx:1≤j) : Catch.Cover («V»:=fun i=> Apex (n i.1) G) (U:=fun _=>ℝ) (T₁) j η (fun _=>1) (fun i=> F' (s₀ i.1)) (fun i=>i.2.1):= by
 obtain ⟨B,hB⟩:= paint_supply G j; let Z i:=1+I i; let v i:= tollS (Z i) j (Λ i * Plateau.amt G r j a B)*2
 have he:T.Meter v η:= ((((Meter.const T 1).add hq).pow j).unitPay (by simp) (hp.rscale _)).rscale _
 let H':= T.bookF (fun i=> Metric.closedBall (0:Apex (n i) G) (f i)); apply Catch.Cover.has (he.pays _ H'); filter_upwards [H'.tends.eventually (ha.low (by norm_num) zero_lt_one),H'.tends.eventually h] with i hI ht'; have hh:i.2.1∈ Metric.ball (0: Apex (n i.1) G) 1:=mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp i.2.2).trans_lt ((le_abs_self _).trans_lt hI)); exact speaking (s i.1) ht ht' hB hx (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_add_of_nonneg_left zero_le_one) _ hh
local notation "C'"=> fun i=> ratioW (u i) e r • s₀ i
include hq ha hv hj hσ ht
lemma fare_v (hk:z.e ≤ k) : Catch.Cover T j (graded e) H (fun i=>F' (C' i)) x:= by
 obtain ⟨σ,Λ,hp,hL,h⟩:= hσ.pays; have hR:z.r=z.slots+1+1:=rfl; have hx:∀ᶠ i in T.rail,0<f i∧ f i ≤1:= (hv.and (ha.low (by norm_num) zero_lt_one)).mono fun i hi=> ⟨hi.1.1, ((le_abs_self _).trans_lt hi.2).le⟩
 let u':= (fun i=> F' (s₀ i)); refine (((Catch.Cover.certainly (f:=u') ha hx (hv.mono fun i hi=>hi.2) (space z s h hp hL ha hq (by omega :1≤ j)) (n:=z.slots+1) (by have h:=z.pricey; omega)).caliber (ht.hours z)).weak (by dsimp only [graded]; rw [← hR]; linarith)).home ?_; filter_upwards [h] with i H' ;
 have hb:(s₀ i)=u' i:= by unfold u'; let f:=s₀ i; have hz:f 0=0:=staid_zero (s i) hp H' (by omega); unfold Shellac.off; exact funext (fun k=>by change f k=f k-f 0; rw [hz,sub_zero])
 rw [off_sc, ← hb, show blockTaylor (z.slots+1) (s₀ i)=0 from ?_,sub_zero,hb]
 ext1 v; unfold blockTaylor; rw [Finset.sum_apply]; apply sum_eq_zero; intro j hj; have hx:= mem_range.mp hj; unfold Tensor.coeff Tensor.diagonal; rw [staid (s i) hp H' j (by omega),smul_zero]; rfl
lemma setup (hk:z.e≤k): τ (fun i=>(ratioW (u i) e r) • s₀ i) (fun i=> adjective (Haiku.Coat.trade e (s i)) (n i) (β i)):= by
 refine ⟨fun k' hv'=>?_⟩; obtain ⟨σ,Λ,hp,hL,h⟩:=hσ.pays; by_cases he:z.e≤k'; swap;
 · refine Catch.Cover.home ((fare_v x ht hq ha hv hj z s hσ hk).weak ?_) ?_; · unfold graded; nlinarith only [Nat.cast_le (α:=ℝ)|>.mpr (show k'+1≤z.e from (by omega))]
   apply Eventually.of_forall; intro i; rw [show delay (adjective (Haiku.Coat.trade e (s i)) (n i) (β i)) k' (u i) =0 from ?_, sub_zero]; refine Finset.sum_eq_zero fun j hj=>?_ ; rw [show adjective (Haiku.Coat.trade e (s i)) (n i) (β i) j=0 from (by ext1 x; unfold adjective Haiku.Coat.trade; rw [if_neg (show ¬e ≤j from (by have hh:=mem_range.mp hj;omega))]; rfl),smul_zero]
 have hx:∀ᶠ i in T.rail,0<f i∧ f i≤1:= (hv.and (ha.low (by norm_num) zero_lt_one)).mono fun i hi=> ⟨hi.1.1,((le_abs_self _).trans_lt hi.2).le⟩
 let u':=fun i=> F' (s₀ i); let a':= k'-z.e+z.r; have ha':a'<j:=by unfold a'; have hp:= z.pricey; omega
 refine (((Catch.Cover.certainly (f:=u') ha hx (hv.mono fun i hi=> hi.2) (space z s h hp hL ha hq (by omega : 1 ≤ j)) ha').caliber (ht.hours z)).weak ?_).home ?_; · unfold a'; unfold graded; simp only [Nat.cast_add,Nat.cast_sub he]; push_cast; linarith
 filter_upwards [h,ht.one] with i hi hw; have h' : delay (adjective (Haiku.Coat.trade e (s i)) (n i) (β i)) k' (u i)= ratioW (u i) e r • blockTaylor a' (s₀ i):= by ext1 v; unfold delay; rw [Finset.sum_apply]; exact sail_full _ hp hi _ (Fare.gS _ hw).1 _ _ he v;
 obtain ⟨B,hB⟩:= paint_supply G j; rw [h',skirt, off_sc, off_sc, ← smul_sub, ← taylor_off _ a' ((signal _ hp hi hB _ (mem_ball_self zero_lt_one)).1.of_le le_top)] -- eta
end Atlas
end YM.AllOrder.Wheel
