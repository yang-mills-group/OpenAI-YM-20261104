import YM.QuadraticLocal.Echo.Evil
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
abbrev Charity (f:ι→ℝ) (e:ℕ): Prop := ∀ᶠ i in T.rail,SumBudget (Trace.rent v ((S i).root) (R i e) (s i e) σ) (f i)
variable (hf:∀ a:ℝ,T.Meter f a)(hC:∀ᶠ i in T.rail,SumBudget (Trace.rent v ((S i).root) (R i e) (s i e) σ) (f i))
variable (hw:T.Meter (fun i=> ‖x i‖) (-(1/2:ℝ)))
local notation "Hℓ"=> T.Meter
include h hX he hx
include hw hf hC
lemma alms (v':ℝ): T.Meter (fun i=>Lx j e i (x i) - Mx j e i (x i)) v':= by
 let c:=j+n₀; obtain ⟨Z,hZ⟩:= paint_supply G c; let L:=(∑ v'∈ Finset.range (n₀+1), Trace.branch G Z σ c v'); let z i:= ‖(W i).Θ⁻¹ • x i‖; let Kx i:= Trace.upper G Z σ ((W i).Θ) c n₀ (z i); let p i:=(↑(j+1):ℝ)*(1+|(W i).Θ|)^j*Kx i
 have he': Hℓ z 0:= by unfold z; simp_rw [norm_smul]; exact (((Proper.meter W h).2.ab).mul hw).weak (by norm_num)
 have hq : Hℓ p 0:= by
    let h:= ((Meter.const T 1).add ((Proper.meter W h).1.ab.weak (b:=0) (by norm_num))).pow j; unfold p Kx Trace.upper; exact (((h.weak (by simp : _≤(0:ℝ))).lscale (↑(j+1):ℝ)).mul (((Meter.const T 1).add he').pow c |>.lscale L)).weak (by simp)
 apply ((hf v'|>.mul hq).weak (by simp : v'+0≤v')).smaller; filter_upwards [hX,hC] with i hi hx'; unfold mere; rw [Finset.sum_apply]; apply (financing v ((S i).root) (R i e) hi _ hZ _ ((W i).Θp) hx he (by unfold c; omega) (s i e) _ hx').trans ; exact le_abs_self (f i*p i)
omit hw hf hC
-- up rank budget during reorientation, budget R through all moments at fixed κ
omit h hX he hx
lemma cred (i:ι)(h: (R i e).Faith (univ:Finset V) v n₀ σ (u i)): Rank (W i).X (j-e+n₀) (Mx j e i):=by -- edit rank keyword X
 refine Rank.sum ?_; intro k h'; let V:=(R i e|>.leg k); let s:=Trace.setX V.atom ((q' i) v); let t:=Plateau.ratioW (Ω₁ i) e V.r
 by_cases he: Spot.Entails V v (S i).root; swap; · rw [show Trace.castable v _ _ _ _ _ k=(fun _=>0) from funext fun i=> if_neg he]; exact Rank.nil _ _
 rw [show Trace.castable v (q' i) (R i e) j e (Ω₁ i) k=Trace.palette v (q' i) V (Ω₁ i) j e from funext fun i=> if_pos he]; let a:=j-e+V.r; suffices h': Rank (W i).X a (blockTaylor a s) from (h'.scal t).up (by unfold a; have ht:V.r≤n₀:= (V.card_le (h.pinned k).tall).1; omega)
 unfold blockTaylor; apply Rank.sum; intro ℓ hℓ
 apply (Project.maturity s ℓ).up; exact Nat.le_of_lt_succ (mem_range.mp hℓ)
end Wake
end YM.QuadraticLocal.Echo
