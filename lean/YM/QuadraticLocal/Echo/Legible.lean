import YM.QuadraticLocal.Echo.Hole
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Echo
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {ι:Type*} {V:Type}[Fintype V][DecidableEq V]{G:Gauge} {k j e d Nℓ:ℕ} {a σ Z τ A:ℝ} {n:Side}
open Aperture Poetry Work.G05 Toggle Aux Aux.Name
open Spot Trace
namespace Wake
variable {P:Patch}{K:KernelChoices}{T:Catch.Clock ι}{r:Stage}{N p m M':ℕ}{q:ℝ→ℝ} {U:Push.Uniform.Before G r.width r.paths P.J K ((k+3)+3)}
variable (W:ι→ Aux.Name G P K q p r (k+3) U) (M:V→Sunrise.Loan)(S:∀ i, Page (W i) M) (h:Aux.Name.Proper W T)
variable (R: ι→ ℕ→ Poetry.Roll G V) (v:V)
variable (s:∀ i j, Finset (R i j).Ty)
set_option quotPrecheck false
local notation "Ω₁" => (fun i=> (W i).Θ)
local notation "q'"=> (fun i=>(S i).root)
local notation "Pt"=> Focus.onto (univ:Finset V)
local notation "Tt"=> T.rail
variable (n₀:ℕ)(hx:0<σ) (u:ι→ℝ) (hu:T.Meter u 0)
-- one supply.Record.Stalled.Include Light Anther paths scope *outside* x predictor. This certificate on weak-curvature expenditure, internal estimates require ModelLens Kernel.P. Keep actual τ.Well width.Support.Becomes next.The L→P reader commitments. Include immersion dearth.R.
variable (hX : ∀ᶠ i in T.rail,(R i e|>.Faith (univ:Finset V) v n₀ σ (u i)))
variable (hs:∀ᶠ i in T.rail,∀ k∈s i e,Spot.Entails (R i e|>.leg k) v (S i).root)
local notation "Bx"=> bendSlot W M S R v s
local notation "Lx"=> life W M S R v
local notation "Mx"=> mere W M S R v s
variable (b:ι→ℝ)(x:∀ i,(W i).X) (hb:T.Meter b (-(1/2:ℝ)))(hp:∀ᶠ i in T.rail,0<b i)(hx':∀ᶠ i in T.rail,‖x i‖≤ b i)
variable (he:e≤j)
local notation "ζ"=> (fun i=> (b i)⁻¹)
local notation "m₀" i:max a:max=> (R i e).price σ a
local notation "A₁"=> (fun i=> (b i)⁻¹)
-- Support/cut treasury. Expect full sums! Infinite.Ty.Leg.N.Engine.Sold.
variable {f:ι→ℝ}
variable {O:ChartRatio G}(hO:LocalRatio O)
open Comparison.RG02 Bulk
variable (K':∀ i,Bulk.Kernel (W i).data (W i).tube.high (W i).tube.up O)
set_option quotPrecheck false
local notation "H"=> Fintype.card V
local notation "Θ"=> T.Meter
local notation "Qs"=> (fun i=> Page.portrait (W i) M (S i) (K' i))
local notation "λ₀"=> (fun i=> (W i).Θ)
local notation "v₁"=> (fun i d j=> Page.prognosis (W i) M (S i) (K' i) d j)
-- Step.Asset supply before applying local estimator, resolved later from Ink heat + Card stanzas. Statement expects **only value** and price weight to evaluate the finite polynomial discrepancy on halo.Y.Time.
structure Supply (T:Catch.Clock ι)(k P:ℕ)(b:ℝ): Prop where
 grant (i:ℕ)(hi:i≤k) : ∃ f:ι→ℝ, T.Meter f 0 ∧ ∀ᶠ a in T.rail,(R a i).Faith (univ:Finset V) v P b (f a)
 step (d:ℕ) (hd:d≤k): ∃ n:ℕ,∃ f:ι→ℝ,(∀ a:ℝ,T.Meter f a) ∧ ∀ᶠ i in T.rail,∀ x:(W i).X,
   |Page.prognosis (W i) M (S i) (K' i) d k x-Sunrise.Aviary.production (R i) k d (W i).c (Plateau.bend (W i).Θ x) (Bunch.mapC (S i).root)| ≤ f i*(1+‖(W i).tulip x‖)^n
structure Kind (T:Catch.Clock ι)(k:ℕ)(b:ℝ): Prop where
    rows e (he:e≤k): ∃ f, (∀ a:ℝ,T.Meter f a) ∧ Charity («T»:=T) (σ:=b) W M S R v s f e ∧ ∀ᶠ i in T.rail,∀ x∈s i e, Spot.Entails (R i e |>.leg x) v (S i).root
-- need repl []. aperture requires rank.L; follow projection Hp from w proof.
variable (Vd:Supply W M S R v K' T j n₀ σ)(hK:Kind W M S R v s T j σ)(hxZ: T.Meter (fun i=>‖x i‖) (-(1/2:ℝ)))
include hx Vd hK
-- price on any.Land decide projection Root.Site.We. below choose berty
local notation "J'"=> range (j+1)
local notation "YL" i:max j:max=> (W i).Θ^j
local notation "κ"=> (fun i d=> (Sunrise.Aviary.production (R i) j d (W i).c (Plateau.bend (W i).Θ (x i)) (Bunch.mapC (S i).root)))
def receiver (j:ℕ) (A:ι): (W A).X→ℝ:= ∑ i∈Finset.range (j+1), mere W M S R v s j i A
def voice (j:ℕ)(A:ι): Config G (W A).c →ℝ:= ∑ i ∈ Finset.range (j+1), bendSlot W M S R v s i A
local notation "F"=> receiver W M S R v s
local notation "A"=> voice W M S R v s
include hxZ h
lemma scale_m (a:ℝ): T.Meter (fun i=> Qs i j (x i) - F j i (x i)) a:= by
 let f i:= ∑ e∈ J',Lx j e i (x i); let z i:= Qs i j (x i); let t i:=(F j i) (x i)
 have he: Θ (fun i=> f i-t i) a:= by
    unfold f t; simp_rw [receiver, Finset.sum_apply, ← Finset.sum_sub_distrib]; apply Clock.Meter.sum; intro e he; have he:= Nat.le_of_lt_succ (mem_range.mp he); obtain ⟨c,hC,hB⟩:= Vd.grant e he; obtain ⟨u,hu,hh,-⟩:= hK.rows e he; exact alms W M S h R v s n₀ hx c hB x he hu hh hxZ a
 let Q i:=∑ d∈J', YL i d * κ i d; have hA: f=ᶠ[T.rail] Q:=by
     let n₁:=j+n₀; obtain ⟨Z,hZ⟩:=paint_supply G n₁
     have hb:∀ t:Fin (j+1),∀ᶠ i in T.rail, Lx j t.val i (x i)=∑ d ∈ J', YL i d * ∑ x':Site _,∑' v, Poetry.Lantern.gleam (R i t.val|>.leg v) x' (Bunch.mapC (S i).root) t.val d (Plateau.bend (W i).Θ (x i)):=by
         intro t; have ht:t.val ≤ j:=Nat.le_of_lt_succ t.prop; obtain ⟨f,hf,hL⟩:= Vd.grant t ht; exact hL.mono fun i hi=> (telescopeE v (q' i) (R i t.val) hi _ hZ _ (Name.Θp _) hx ht (by unfold n₁; omega)).symm
     filter_upwards [eventually_all.mpr hb] with i hi; unfold f Q Sunrise.Aviary.production; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; apply sum_congr rfl fun j₁ hj₁=> (by simpa only [Finset.mul_sum] using hi (⟨_,mem_range.mp hj₁⟩))
 have ht : Θ (z-Q) a:= by
    change Θ (fun i=> z i-Q i) a; unfold z Q Page.portrait delay; simp_rw [← Finset.sum_sub_distrib]; apply Meter.sum; intro d hD; obtain ⟨n,p,hp,hW⟩:= Vd.step d (Nat.le_of_lt_succ (mem_range.mp hD)); let b i:=(W i).Θ; let v'(i:ι):=‖(W i).tulip (x i)‖; let u i:=v₁ i d j (x i)-κ i d; have hz:= Name.Proper.meter W h; have he : T.Meter v' 0:=by unfold v' Name.tulip; simp_rw [norm_smul]; exact (hz.2.ab.mul hxZ).weak (by linarith)
    have h' : T.Meter u a:= (((hp a).mul (((Meter.const T 1).add he).pow n)).weak (by simp)).smaller (hW.mono fun i hi=> (hi (x i)).trans (le_abs_self _)); simp_rw [smul_eq_mul,← mul_sub]; exact (hz.1.pow d).unitPay (by nlinarith only [Nat.cast_nonneg (α:=ℝ) d]) h'
 exact (ht.add he).eq_mem (hA.mono fun i hi=>by change z i-Q i+(f i-t i)= z i-t i; rw [hi]; ring)
end Wake
end YM.QuadraticLocal.Echo
