import YM.AllOrder.Burn.Scent
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Burn
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Floe Floe.Pace Floe.Aero Floe.StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω α:ℝ}{k r m n N l:ℕ}{j:Side}
open Till Tilt Floe.Step Floe.Step.PlanV Plateau
-- L=1 for receipts on either.Housing z support paid. R.Space β recognition. factor 2*sqrt or 4..
section lyrics
variable (P:RG.Rep G j)(s:Locale G)(V:Config G j)
local notation "p"=>P.p
local notation "X"=>P.activities
local notation "K'"=> keys j
abbrev rise : RG.Rep G j:= { P with activities:= press (p) (X) s }
local notation "W"=> rise P s
lemma brand (hp: Plateau.gardenfold (P.p.B) s): Nonempty (Burn.Seed (rise P s) s):= ⟨pivot j,(fun i=> ⟨(congr_arg RegularAddress.support (earns p X s i|>.1)).trans rfl,(congr_arg RegularAddress.site (earns p X s i|>.1)).trans rfl⟩), (fun i=> (earns p X s i).2), hp⟩
def seed (hp:Plateau.gardenfold P.p.B s): Burn.Seed (rise P s) s:= ⟨pivot j,(fun i=> ⟨(congr_arg RegularAddress.support (earns p X s i|>.1)).trans rfl,(congr_arg RegularAddress.site (earns p X s i|>.1)).trans rfl⟩),(fun i=> (earns p X s i).2),hp⟩
variable (h:P.activities.Valid P.p C Ω)
include h
lemma grain : (rise P s).activities.additive P.p V=∑ i,masked P.p.threshold (court i P.p.B) (s j i) V + (X).additive p V := by -- parentheses syntax sum extends; test
 let f (i:Site j):= masked P.p.threshold (court i P.p.B) (s j i) V; let g i:= (X).regularOccurrence p i V; let k:= Sum.elim f g; have hh i:(rise P s|>.activities.regularOccurrence (p) i V)=k (K' i):= by unfold rise press Activities.regularOccurrence; simp only [Function.comp_apply]; cases K' i <;> rfl
 unfold Activities.additive at *; simp_rw [hh]; rw [(K').tsum_eq k,Summable.tsum_sum (f:=k) Summable.of_finite (((X).ESeries h).summable V), tsum_fintype]; rfl
lemma point_reads : (rise P s).eval V=P.eval V*Real.exp (-(∑ i, masked P.p.threshold (court i P.p.B) (s j i) V)) := by
 unfold RG.Rep.eval; rw [show (W).exponent V=P.exponent V-(∑ i, masked (P.p).threshold (court i P.p.B) (s j i) V) from ?_,sub_eq_add_neg,Real.exp_add,mul_right_comm]; rfl
 change _*_ - _ - (W).activities.additive p V = (_*_ - _ - (X).additive p V)-_; rw [grain P s V h]; change P.v*_ -P.path.inChannels .. -_= _; abel
end lyrics
open Pane
variable (G) {j f:Side}(D:StepData j f) (T:Tube G D) (β:ℝ) (B:BudgetPoint)
local notation "A"=> Pane.virgin T B β
variable (s:Layout G) (k:ℕ)
open Tilt Floe.Step.PlanV Floe.Step.Rent
abbrev offerS (G:Gauge)(B:BudgetPoint)(s:Layout G)(X:Finset Age)(t:ℝ):Locale G:= fun f o=> Tilt.patch G B.B f o X s t
open ConnectedActivityE6.Coat
local notation "F"=> offerS G B s (Age.scope (horizon k+2)) (gStep β)
local notation "Ξ"=> Burn.rise A F
-- operates real Level.El.NO Actors. actual Life.*. expression injection near all good for later estimates. require poses.
structure Capacity (G:Gauge)(B:BudgetPoint)(Z:ℝ)(k:ℕ):Prop where
 cuts : 4*(horizon k+4) ≤ B.B
 near v : Near Z v → Real.exp B.supportExponent*Tilt.price B G (horizon k) B.B (strengthP Z) (gStep v) (Age.scope (horizon k+2)) ≤ silver Z
 paid : PostFuel Z k (silver Z) ∧ young Z k ≤ (Real.sqrt Z)⁻¹ ^ (11/5:ℝ)
-- eventual claim .after pre. x shift covers top and bottom
lemma worth (P:RG.Stage): ∀ᶠ x:ℝ in atTop,∀ B:BudgetPoint, B.threshold=temp x→ B.B=radiusB x→ B.supportExponent=P.supportExponent→B.order=P.order→ B.power=P.power → Capacity G B x k:= by
 let U:=Age.scope (horizon k+2); filter_upwards [fueling G k,Work.E01.radiusB_tendsto.eventually_ge_atTop (4*(horizon k+4)),budgets_x ((Burn.stop (G:=G) U P 0 (horizon k)).l_scale (Real.exp P.supportExponent)) (by norm_num : -(3/2:ℝ)< -(7/5:ℝ))] with x hv he hx B ht hp he' ho hk; refine ⟨hp.symm ▸ he,fun i hi=>?_, hv⟩; rw [Tilt.sameprice,he',hk,ht,ho,hp]; exact (le_abs_self _).trans (hx i hi)
variable (V:Locale G) (P:Teller G) (m:ℝ)
variable (S':Step.Fees) (h : ∀ i∈ Age.scope (Burn.horizon k+2), Quoted (s i) (S' i) (authority (Burn.horizon k) i (strengthP m))) (hm:∀ i,0<S' i) (hf: m>1) (hi: Near m β) (hn:4≤f.val) (g:G.Simple)
include hm h hi hf hn g
lemma E_pivot (hc:Capacity G B m k) : Nonempty (Burn.Seed (Ξ) F)∧ (Ξ).activities.Valid B (silver m) 0∧ Candor B (Ξ).activities (Set.range (pivot f)) (silver m) 0 ∧ ∀ i ∉ Set.range (pivot f),(Ξ).activities.E i=0:= by
 have hC:= hc.near β hi; let V f o:= F f o;
 obtain ⟨he,hB⟩:= remit B (pale f G) (F) (whey f G B) (fun i:Site f=> Tilt.paint _ _ _ S' h g _ _ hn i B hm fun i hi=> Nat.mul_le_mul_left 4 (i.pricey.trans (Nat.add_le_add_right (Age.in_scope.mp hi) 2))|>.trans hc.cuts) (signed _ _ _ _ f)
 refine ⟨brand _ _ ?_,{he with boundE:=VerifiedReset.Time.E_rises he.boundE (le_trans (add_zero _).le hC)}, ?_,fun i hi=>?_⟩; exact Tilt.regional _ _ _ _
 · exact (show Candor (Ξ).p (Ξ).activities (Set.range (pivot f)) _ _ from hB).loosen (R:=Ξ) hC le_rfl
 have he' :(Ξ).activities.E i=(Sum.elim ((F) f) (pale f G|>.E) (keys f i)):=rfl; rw [he']; cases H:keys f i with | inl v=> exact (hi ((rolled i).2 ⟨v,H⟩)).elim | inr j=> rfl
-- eval simplified
omit hm h hi hf hn g
lemma glowing (V:Config G f): (Ξ).eval V=(A).eval V*Real.exp (-(∑ i,(F) f i V)):= by
 rw [Burn.point_reads A F V (whey f G B)]; by_cases h : flags B.threshold V=∅; · simp_rw [show ∀ i:Site f, masked (A).p.threshold (court i (A).p.B) (F f i) V= F f i V from fun i=> masked_eq _ _ _ _ (show Healthy B.threshold _ V from by unfold Healthy; rw [h]; simp)]
 rw [Pane.sparkling, if_neg h]; ring
end YM.AllOrder.Burn
