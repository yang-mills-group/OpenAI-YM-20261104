import YM.AllOrder.Wheel.Berth
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
set_option quotPrecheck false
local notation "I"=> (fun i=>(Fintype.card (Primary (n i) G):ℝ))
local notation "Z"=> (fun i=> 1 + I i)
structure Civil (S:Stage)(T:Clock ι)(R:ι→PathData G):Prop where
 cost:∃ f:ι→ℝ,T.Meter f 0∧∀ᶠ i in T.rail,(R i).Bounds S.clip S.width S.paths (f i)
namespace Civil
variable (hC:Civil S T R) (j)
local notation "z"=>F'
local notation "T₁"=> T.book (fun i=> Metric.closedBall (0: Apex (n i) G) (f i))
include hq hC ha
variable (hS:1≤ j)
include hS
lemma valueU : Catch.Cover («V»:=fun i=> Apex (n i.1) G) (U:=fun _=>ℝ) (T₁) j 0 (fun _=>1) (fun i=> z (M' i.1)) (fun i=> i.2.1) ∧ Catch.Cover («V»:=fun i=> Apex (n i.1) G) (U:=fun _=>ℝ) (T₁) j 0 (fun _=>1) (fun i=>z (L i.1)) (fun i=> i.2.1) :=by
 obtain ⟨Λ,hΛ,hν⟩:= hC.cost; let B':= Classical.choice (BareRates.offered G S.width S.paths j); let v:=BareRates.bill B' S.clip
 let L' i:=tollS (Z i) j v*(1+1); let u' i:=tollS (Z i) j ((1+|(0:ℝ)| +Λ i)*v)*(1+1); have h := T.bookF (fun i=> Metric.closedBall (0: Apex (n i) G) (f i));
 have hX:A Z 0:= (Meter.const T 1).add hq; let hh:= (hX.pow j|>.weak (by simp : (0:ℝ)*j≤0)); have hx:T.Meter L' 0:= (hh.rscale _).rscale _; have hp:T.Meter u' 0:= (hh.unitPay le_rfl (((Meter.const T _).add hΛ).rscale _)).rscale _ -- addition wrong order
 let X:= (Σ i:ι,{x:Apex (n i) G// x∈Metric.closedBall 0 (f i)}); have hc :∀ᶠ i:X in (T₁).rail, Brush j (L' i.1) 1 (z (M' i.1)) i.2.1∧ Brush j (u' i.1) 1 (z (L i.1)) i.2.1:= by
   filter_upwards [h.tends.eventually (hν.and (ha.low (by norm_num) zero_lt_one))] with i hi; let Y₀:= i.2.1; let v i:=V i; let c:=n i.1; let a:= R i.1
   have hz:Y₀∈ Metric.ball 0 1:= mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp i.2.2).trans_lt ((le_abs_self _).trans_lt hi.2));
   let w(b:v i.1)(hb:b∈Metric.ball 0 1):= bareSocket _ B' (R:=a) hi.1 hb 0
   obtain ⟨hA,hj',hV,H0,h0,h'⟩:= w _ hz; have h':0≤ Λ i.1:= hasInheritance hi.1; have hk: Z i.1 ≥1:=le_add_of_nonneg_right (Nat.cast_nonneg _); have hr(h:ℕ) :0≤ |(0:ℝ)|:=by positivity; -- hr unused
   let hx:= le_add_of_nonneg_left (b:=1) (a:=I i.1) zero_le_one; change _ ∧ Brush j _ _ (z (Precision.loop (R i.1) ∘ Desk.night (c:=n i.1))) i.2.1; erw [← driftW S (R i.1) hi.1 (n:=n i.1)]; exact ⟨(horizonB hk hx H0.le hV zero_lt_one hS hz (fun i hi=> ⟨(w i hi).2.2.2.2.1,(w i hi).1⟩)).2, (horizonB hk hx (by positivity) hV zero_lt_one hS hz (fun i hi=> ⟨(w i hi).2.2.2.2.2,(w i hi).2.1⟩)).2⟩
 exact ⟨Catch.Cover.has (hx.pays _ h) (hc.mono fun _ hi=> hi.1),Catch.Cover.has (hp.pays _ h) (hc.mono fun _ hi=> hi.2)⟩
omit hS
include hv hj hG ht
lemma firstC : Catch.Cover T j 0 H (fun i=>F' (β i • M' i)) x:=by
 obtain ⟨Λ,hΛ,hν⟩:=hC.cost; let G₁ i:= z (M' i); have hh: ∀ᶠ i in T.rail, 0<f i∧ f i≤1:= (hv.and (ha.low (by norm_num) zero_lt_one)).mono fun i hi=> ⟨hi.1.1, ((le_abs_self _).trans_lt hi.2).le⟩
 have h:= ((Catch.Cover.certainly (f:=G₁) ha hh (hv.mono fun i hi=>hi.2) (valueU j S R hq ha hC (by omega)).1 (by omega : 1<j)).caliber ht.price); refine (h.weak (by norm_num)).home ?_; filter_upwards [hν] with i hi; rw [show blockTaylor 1 (G₁ i)=0 from oracleX S _ hG hi,sub_zero,off_sc] -- parentheses
lemma footprint : τ (fun i=>β i • M' i) (fun i=> adjective (base S.clip (R i)) (n i) (β i)) ∧ τ L (fun i=> adjective (Haiku.Coat.clerk (fun _=> Precision.loop (R i)) 0) (n i) (β i)) := by
 obtain ⟨Λ,hΛ,hν⟩:= hC.cost; let G₁ i:= z (M' i); let G₂ i:= z (L i); obtain ⟨h₁,h₂⟩:= valueU j S R hq ha hC (by omega); have hh: ∀ᶠ i in T.rail, 0<f i∧ f i≤1:= (hv.and (ha.low (by norm_num) zero_lt_one)).mono fun i hi=> ⟨hi.1.1, ((le_abs_self _).trans_lt hi.2).le⟩; let hν':= hv.mono (p:=fun i=> 0<f i∧ ‖x i‖≤ f i) (q:=fun i=> ‖x i‖ ≤ f i) fun _ hi=>hi.2
 constructor
 · refine ⟨fun l hl=>?_⟩; let h:= (Catch.Cover.certainly (f:=G₁) ha hh hν' h₁ (by omega : l+2<j)); refine ((h.caliber ht.price).weak (by unfold graded; push_cast; linarith)).home ?_; filter_upwards [hν,ht.one] with i hi he; let hp: ContDiffAt ℝ ω (M' i) 0:= (cursor S.clip (R i) 0 hi (Classical.choice (BareRates.offered G S.width S.paths j)) _ (mem_ball_self zero_lt_one)).1; rw [skirt,oracleA S _ hG hi he, off_sc, off_sc, ← smul_sub, ← taylor_off (M' i) _ (hp.of_le le_top)] -- off affects denominator scope?
 refine ⟨fun l hl=>?_⟩; refine ((Catch.Cover.certainly (f:=G₂) ha hh hν' h₂ (by omega : l < j)).weak (by unfold graded; push_cast; linarith)).home ?_; filter_upwards [hν,ht.one] with i hi he; rw [skirt,oracleB S (R i) hi he]; apply congr_arg (F' (L i) - ·); -- need show hp definitional
 apply taylor_off; exact (driftW S (R i) hi (n:=n i) ▸ (cursor S.clip (R i) 0 hi (Classical.choice (BareRates.offered G S.width S.paths j)) _ (mem_ball_self zero_lt_one)).2).of_le le_top
end Civil
end YM.AllOrder.Wheel
