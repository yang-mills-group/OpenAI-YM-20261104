import YM.QuadraticLocal.Echo.Wallet
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
abbrev Pupil := ∀ᶠ i in T.rail,(R i e|>.Faith (univ:Finset V) v n₀ σ (u i))
variable (hX : ∀ᶠ i in T.rail,(R i e|>.Faith (univ:Finset V) v n₀ σ (u i)))
variable (hs:∀ᶠ i in T.rail,∀ k∈s i e,Spot.Entails (R i e|>.leg k) v (S i).root)
def bendSlot (e:ℕ)(i:ι): Config G (W i).c→ℝ:= ∑ a∈ s i e, Trace.offered v ((S i).root) (R i e|>.leg a) (W i).Θ e
def mere (k e:ℕ)(i:ι): (W i).X→ℝ:= ∑ a∈ s i e, Trace.castable v (q' i) (R i e) k e (Ω₁ i) a
abbrev life (j e:ℕ) (i:ι) (x:(W i).X):= ∑' a,Trace.castable v (q' i) (R i e) j e (Ω₁ i) a x
local notation "Bx"=> bendSlot W M S R v s
local notation "Lx"=> life W M S R v
local notation "Mx"=> mere W M S R v s
variable (b:ι→ℝ)(x:∀ i,(W i).X) (hb:T.Meter b (-(1/2:ℝ)))(hp:∀ᶠ i in T.rail,0<b i)(hx':∀ᶠ i in T.rail,‖x i‖≤ b i)
variable (he:e≤j)
local notation "ζ"=> (fun i=> (b i)⁻¹)
local notation "m₀" i:max a:max=> (R i e).price σ a
local notation "A₁"=> (fun i=> (b i)⁻¹)
include h hb hu hp hx he hX
-- θ*(1+Λ)^e budget growth.
lemma salary (N:ℕ) (hr: e ≤ j) (hI:j-e+n₀< N): ∃ f:ι→ℕ→ℝ,(∀ n≤ n₀, T.Meter (fun i=> f i n) (graded (j+1))) ∧ ∀ᶠ i in T.rail, ‖x i‖≤ b i→ b i≤ 1 → ∀ A:Poetry.Lantern G V,A.r≤ n₀ → Brush N (f i A.r*A.money σ) ((b i)⁻¹) ((Trace.offered v (q' i) A (Ω₁ i) e ∘ Desk.night)-Trace.palette v (q' i) A (Ω₁ i) j e) (x i) := by -- uses hb
 obtain ⟨Z,hZ⟩:= paint_supply G N; let f i r:=branch G Z σ N r * Plateau.ratioW (Ω₁ i) e r*(b i)^(j-e+r+1); refine ⟨f,fun n hn=> ?_,?_⟩;
 · let ht:= (Proper.meter W h); have he': T.Meter (fun i=>Plateau.ratioW (Ω₁ i) e n) (graded e+n/2):= by unfold Plateau.ratioW; simp_rw [← inv_pow]; exact ((ht.1.pow e).mul (ht.2.pow n)).weak (by unfold graded; linarith)
   refine (((he'.lscale _).mul (hb.pow (j-e+n+1))).weak ?_); unfold graded; push_cast; rw [Nat.cast_sub he]; linarith
 apply hp.mono; intro i hi hx₁ hx₂ A hA; refine Brush.climb (Trace.weather j e v _ _ _ _ hx hZ hi hx₂ (Name.Θp _) hx₁ (by omega : j-e+A.r< N)) ?_ le_rfl; apply le_of_eq; unfold f; ring -- verify binder order
include hx' hs
lemma pours (n:ℕ): Catch.Cover T n (graded (j+1)) ζ (fun i=> (Mx j e i)- Bx e i ∘ Desk.night) x := by
 let N:= n+(j-e+n₀+1); let Z:= Bx e; let L:= Mx j e; obtain ⟨f',hf,hF⟩:= salary W M S h R v n₀ hx u hu hX b x hb hp he N he (by unfold N; omega) -- hb, s params
 let f r i:= f' i r; let Fθ i:= ∑ n∈ range (n₀+1), |f n i|; let g i:= Fθ i*u i; let vv(i:ι)(y : (R i e).Ty):=Fθ i* m₀ i y
 have h : T.Meter g (graded (j+1)) := ((Clock.Meter.sum _ (fun n (h:n∈range (n₀+1)) => (hf n (Nat.le_of_lt_succ (mem_range.mp h))).ab)).mul hu).weak (by simp)
 apply Catch.Cover.has h; filter_upwards [hp,hb.low (by norm_num) zero_lt_one,hx',hF,hX,hs] with i hi hq hG hH hX hs;
 let u':= (q' i); -- typing
 let Y0 a:= Trace.offered (V:=V) v u' ((R i e).leg a) (Ω₁ i) e ∘ Desk.night; let X0 a:= Trace.castable v u' (R i e) j e (Ω₁ i) a; let A0:= s i e; let g₁ i:= ∑ k∈A0, (X0 k i - Y0 k i); have hr(a)(ha:a ∈ A0): Brush n (Fθ i*m₀ i a) ((b i)⁻¹) (X0 a -Y0 a) (x i):= by
    have ht:= ((R i e).leg a).card_le (hX.pinned a).tall; let s:=((R i e).leg a).r; have hm:= (R i e).leg a |>.fee_nn σ; have hq₁:b i≤1:= (le_abs_self _).trans hq.le; let U(x:(W i).X):= Trace.palette v u' ((R i e).leg a) (Ω₁ i) j e x; rw [show X0 a=U from funext fun _=> if_pos (hs _ ha), ← neg_sub]; refine (((hH hG hq₁ _ ht.1).opposite).smaller (show n≤N by unfold N; omega)).climb (mul_le_mul_of_nonneg_right (?_) hm) le_rfl; exact (le_abs_self (f s i)).trans (Finset.single_le_sum (f:=fun j=> |f j i|) (fun _ _=> abs_nonneg _) (Finset.mem_range.mpr (by omega : ((R i e).leg a).r < n₀+1)))
    -- `omega` error context. later
 refine (((Brush.spree (A0) (fun i x=>X0 i x-Y0 i x) (vv i) (inv_nonneg.mpr hi.le) hr).climb ?_ le_rfl).shimmy ?_); · unfold vv; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (budget_sum hX.price A0) (sum_nonneg fun i _=>abs_nonneg _)
 exact Eventually.of_forall fun y=>by rw [Pi.sub_apply,Function.comp_apply]; unfold mere bendSlot; simp_rw [Finset.sum_apply,Finset.sum_sub_distrib]; rfl

end Wake
end YM.QuadraticLocal.Echo

