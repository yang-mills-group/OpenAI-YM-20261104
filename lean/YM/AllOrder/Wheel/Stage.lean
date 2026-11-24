import YM.AllOrder.Wheel.Vent
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
variable {x} {Y:ι→Scene G} (F:∀ i,Book (Apex (n i) G))(R':ι→ Scene G)
-- Exact relative under SnapPred.Factor for any era.
lemma bill_transfer {V0:Type}{q U:V0→ℝ}{h':ι→V0}(hg:Ink.Money.Grade q U)(h:A (q∘h') 0) : A (U∘h') 0:= by
 obtain ⟨v,t,hv,hg⟩:=hg; refine (((( (Meter.const T 1).add h.ab).pow t).lscale v).weak (by simp)).smaller (Eventually.of_forall (fun i=>?_)); have he:=hg (h' i); unfold Function.comp; rw [abs_of_nonneg he.1]; exact he.2.trans (le_abs_self _)
lemma pay_transfer {V0:Type}{q:V0→ℝ}{U:V0→Side→ℝ}{s':ι→V0}(hg:Ink.Money.Pay q U)(h:A (q∘s') 0)(he:A (fun i=>( (n i).val:ℝ)) 0) : A (fun i=> U (s' i) (n i)) 0:= by
 obtain ⟨v,hv,r,hg⟩:=hg; refine (((bill_transfer hv h).mul (he.pow r)).weak (by simp)).smaller (Eventually.of_forall (fun i=>?_)); have hh:=hg (s' i) (n i); rw [abs_of_nonneg hh.1]; exact hh.2.trans (le_abs_self _)
structure Wire (T:Clock ι)(n:ι→Side)(k:ℕ)(u₁:∀ i,Book (Apex (n i) G))(R:ι→ Scene G):Prop where
 price {j:ℕ} : j≤k → ∃ (p r:ι→ℝ), (∀ s,T.Meter p s) ∧ ∀ᶠ i in T.rail, Prices (j+2) (p i) ((u₁ i j∘ Kinetic.Port.exteriorL G (n i)) -(R i j (n i))-(fun _=> r i))
-- β & near order. Use PricesB `.Price`. 
namespace Wire
variable (hW:Wire T n k F Y)
include hW hq hv ha ht
local notation "Z"=> fun i:Apex _ _ => i -- remove
set_option quotPrecheck false
local notation "F₁"=> fun i k x => F i k ((gStep (β i))⁻¹ • x)
local notation "V₁"=> fun i => F i
lemma receipt (η:ℝ)(n':ℕ)(h:n'≤k): Catch.Cover T j η H (fun i=> F' (F₁ i n' - adjective (Y i) (n i) (β i) n')) x:= by
 obtain ⟨p,r,H',hr⟩:=hW.price h; let E i:= Kinetic.Port.exteriorL G (n i); let P i:=(F i n' ∘ E i)-Y i n' (n i)-fun _=> r i; let hq':=ht.starts
 let f' i:= bend (n:=n i) (G:=G) (u i); let A' i:=p i*(1+(u i)⁻¹)^(n'+2); let t:=n'+2;
 let X i:ℝ:=1+ (Fintype.card (Primary (n i) G):ℝ); let B i:=tollS (X i) j (A' i*Rail.mantle j t *2^t); have hb:T.Meter B η:= by
    unfold B tollS A'; let hP:=(Meter.const T 1).add hq; refine (hP.pow j).unitPay (by simp) (((((H' (η-1/2*t)).mul (b:=1/2*t) ?_).weak ?_).rscale _).rscale _);
    · exact ((((Meter.const T 1).weak (by norm_num : (0:ℝ)≤1/2)).add hq').pow _)
    linarith
 apply Catch.Cover.has («g'»:=fun i=>B i+B i) (hb.add hb); filter_upwards [ht.one,hv,ha.low (by norm_num) zero_lt_one,hr] with i hi hx he hU
 let Vx := E i; let η:= (f i); let m':= P i ∘ f' i; have hy:η<1:= (le_abs_self _).trans_lt he; have hv:Prices t (A' i) m':= pricedBend (p:=P i) hU (gS _ hi).1; have hu(z: Apex (n i) G)(hz:‖z‖≤η): Brush j (B i) 1 m' z:= brushLens hv z hz hy (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_add_of_nonneg_left zero_le_one) j; have hf: F' m'=F' (F₁ i n'-adjective (Y i) (n i) (β i) n'):= by
    ext1 x; unfold m' adjective P f' bend Shellac.off; simp only [Pi.sub_apply,Function.comp_apply,E,ContinuousLinearEquiv.apply_symm_apply]; abel
 rw [← hf]; exact (((hu  (x i) hx.2).separating ((Brush.certified zero_le_one _).climb (hu 0 (norm_zero.trans_le hx.1.le)|>.bound) le_rfl)).climb le_rfl ((one_le_inv₀ hx.1).2 hy.le))
lemma sick (η:ℝ) : Catch.Cover T j η H (fun i=> F' (delay (F₁ i) k (u i) - delay (adjective (Y i) (n i) (β i)) k (u i))) x:= by
 let X(i:ι)n' :=F₁ i n'; let P i:= adjective (Y i) (n i) (β i); let L' i(z:ℕ):= F' (X i z -P i z); refine (Catch.Cover.home (Catch.Cover.booking (range (k+1)) (F:=fun v i=> (u i)^v • L' i v) (fun z hz=> ?_) (hv.mono fun i hi=>inv_nonneg.mpr hi.1.le)) ?_);
 · exact (((receipt ht hq ha hv F hW η z (by have he:= mem_range.mp hz; omega)).caliber (ht.stepI.pow z)).weak (by linarith [Nat.cast_nonneg (α:=ℝ) z])) -- args
 refine Eventually.of_forall fun i=>?_ ; ext1 x; unfold delay Shellac.off L' X P; simp only [Shellac.off, Finset.sum_apply,Pi.smul_apply,Pi.sub_apply]; simp_rw [← sum_sub_distrib, smul_sub]
end Wire
end YM.AllOrder.Wheel
