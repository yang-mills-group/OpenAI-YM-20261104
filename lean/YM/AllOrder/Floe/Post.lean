import YM.AllOrder.Floe.Clocks
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
namespace Pace
open Aero Bloch Stationary
variable {μ B C' Λ a:ℝ} {ι:Type} {Q L : ι→ℝ} {l:ℕ} {U K:ι→Ink.Money.Bills (Coarse G)}
abbrev money (Γ:ι→ℝ)(T:ι→Ink.Money.Bills (Coarse G))(k l:ℕ)(u:ℝ):= ∃ (X:ι→Picture G k)(f:ι→ℝ), CreditF Γ l f ∧ (∀ n i, Recorded (X i) (T i n) 0) ∧ ∀ i j w, Firm u (f i) (X i j w)
abbrev mental (T:ι→Ink.Money.Bills (Coarse G)):= ∀ i n,AnalyticAt ℝ (T i n) 0
namespace money
lemma adapt (h:money Q U k l μ)(he :∀ i n,iteratedFDeriv ℝ (k+1) (U i n) 0=iteratedFDeriv ℝ (k+1) (K i n) 0) : money Q K k l μ:= by obtain ⟨p,a,h,hV,hP⟩:= h; exact ⟨p,a,h,fun n i=> Coat.remake _ _ (he i n) (hV n i),hP⟩
lemma squeeze (h:money Q U k l μ)(he:a≤μ)(hp:0<a)(hk:l≤j): money Q U k j a:= by obtain ⟨p,t,h,H,X⟩:=h; exact ⟨p,t,h.up hk,H,fun i k v=> (X i k v).mono hp he le_rfl⟩
lemma zipper (h:money Q U k l μ)(H:money Q K k l μ)(hp:mental U)(hv:mental K): money Q (U+K) k l μ∧ money Q (U-K) k l μ := by
 obtain ⟨p,a,h,hL,hρ⟩:=h; obtain ⟨q,b,H,hK,hξ⟩:=H; exact ⟨⟨p+q,_,h.add H,fun n i=>(hL n i).both (hp i n) (hv i n) (hK n i),fun i j k=>(hρ i j k).add (hξ i j k)⟩,⟨p-q,_,h.add H,fun n i=>(hL n i).less (hp i n) (hv i n) (hK n i),fun i j k=>(hρ i j k).sub (hξ i j k)⟩⟩
lemma scale (h:money Q U k l μ)(he:mental U)(hf: Pace.Cost Q j L)(hp:0<μ): money Q (fun i=> L i • U i) k (j+l) μ := by
 obtain ⟨p,a,h,hV,X⟩:=h; refine ⟨fun i=>(L i:ℂ) • p i,_,CreditF.mul hf h,fun n i=>(hV n i).weigh (L i) (he i n),fun i j t=>?_⟩; have hh := Firm.const (α:=Keys k) hp (L i:ℂ) -- inspect level
 simpa only [Complex.norm_real,Real.norm_eq_abs] using! (hh.mul (X i j t))
lemma void (hf:∀ i n,iteratedFDeriv ℝ (k+1) (U i n) 0=0)(ha:0<μ):money Q U k l μ:= ⟨0,0,(freeC _ le_rfl).up (Nat.zero_le _),fun n i=>Haiku.Coat.no_charge _ (hf i n),fun _ _ _=>Firm.zero ha⟩
lemma total {α:Type*}{F:α→ι→ Ink.Money.Bills (Coarse G)}(s:Finset α)(h:∀ i∈s,money Q (F i) k l μ)(hx:∀ i∈s,mental (F i))(hp:0<μ): money Q (fun v n=>∑ i∈s,F i v n) k l μ:= by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact void (fun i n=>by simp) hp
 | insert i s he ih=>
    let f v (n:Side):=∑ i∈s,F i v n; have hh (i h'):= h i (mem_insert_of_mem h'); have H i hi:= hx i (mem_insert_of_mem hi); have ht:mental f:= by intro i n; rw [show f i n= _ from (show f i n=(fun v=>∑ j∈s,F j i n v) from funext (fun z=>(Finset.sum_apply ..)))]; exact (show ContDiffAt ℝ ω (fun x:rule (Coarse G) n=>∑ j∈s, F j i n x) 0 from ContDiffAt.sum (fun j hj=> (H j hj i n).contDiffAt)).analyticAt -- name
    simp_rw [sum_insert he]; exact zipper (h i (mem_insert_self ..)) (ih hh H) (hx i (mem_insert_self ..)) ht|>.1
-- special explicit widths via `bottoms` finite.Loop. purely estimation.
lemma species {f:ι→Ink.Field (Coarse G)}(h:∀ i,(f i).Good μ (L i) N)(ha:0<μ)(hL:CreditF Q l L): let x:= weaker (k+1) (Rail.widthG μ (k+1)); money Q (fun i n=>(f i).table n) k l (small_a x):= by
 intro s; choose p hp h' using fun i => Haiku.Revenue.rent_coin (f i) (h i) ha (N:=k); refine ⟨p,_,?_,fun n i=>h' i n,hp⟩
 have hx:0<s:= by unfold s weaker; apply div_pos (Rail.widthG_pos ha); positivity
 have hσ := boltC_pos k hx; apply CreditF.up (l:=l) ((freeC _ (norm_nonneg _)).mul ((((freeC _ (Rail.mantle_pos (k+1) N).le).mul hL).mul (freeC _ (count_pos (half_pos (Rail.widthG_pos (k:=k+1) ha))).le)).mul (freeC _ hσ.le))); omega
end money
end Pace
end YM.AllOrder.Floe
