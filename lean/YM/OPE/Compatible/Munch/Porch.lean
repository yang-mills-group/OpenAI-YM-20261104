import YM.OPE.Compatible.Munch.Macro
/-! # localization of full untruncated thermostats. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m Z:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}(x:Site L.f){q:Sender L}
variable {B: Law (Bid.Dir G L.c)}(μ:Measure (Bid.Dir G L.c))[μ.IsAddHaarMeasure] {X:Seats L.ForestQ}
variable {N: ChartRatio G}(hN:LocalRatio N)
variable (hp:Funded L X q a k)(H:StackP N r R β)
set_option quotPrecheck false
local notation "W'"=> Bid.Dir G L.c
local notation "χ"=> wallet3 G k s c v u C
local notation "g!"=> Gov s u
local notation "Π!"=> quart B μ
variable (η:Phase)(hs:G.Simple)(hw:L.b=0)(h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:0≤v)(hX:(X.card:ℝ) ≤ z)(hφ:PerSeat (L:=L) B A)(hA:0≤A)
variable (hS:∀ t z a:ℝ,‖wallet3 G k s c v u C t z a β‖≤ D*(1+(‖t‖+(‖z‖+‖a‖)))^Z)(hD:0≤ D)
include H hs hw h ht hc he hv hX hφ hA hS hD hp hN
noncomputable abbrev Noble (G:Gauge)(Z:ℕ)(b:ℝ){s:ℝ}(h:0 < s):price:=fun i=> (ΘVar h G b Z i).choose
lemma harvest_M (i:ℕ)(hK:Training L x X i): Cane (quart B μ) (Censor L q N η x i-skry (GPY L q N) η) ((Ywall (Gov s u/2) z a D Z i*(1-Real.exp (-(Gov s u/2)))⁻¹) • Noble G Z A (Gov_price ht h.vein.warmth).1):=by
         obtain ⟨n,hN'⟩:= eventually_atTop.1 (SoarQ L x); let f:= Censor L q N η x; let p:= lamp_B G Z; let V:= Noble G Z A (Gov_price ht h.vein.warmth).1; let g:= Ywall g! z a D Z; let b:= g!/2; let t:price:= (Ywall b z a D Z i*(1-Real.exp (-b))⁻¹) • V
         have hv' (j:ℕ): Cane Π! (f (i+j)-f (i+j+1)) (g (i+j) • p (i+j) A):=pineM x μ hN hp H η hs hw h ht hc he hv hX hφ hA hS hD (i+j) (fun u hu=> (hK u hu).trans (by exact_mod_cast (show i≤ i+j from by omega)))
         let q':= skry (GPY L q N) η; have hu:f (i+n)=q':=by unfold f Censor; rw [hN' _ (by omega)];rfl
         let T':ℕ→price:= fun j=>g (i+j) • p (i+j) A; let Y:= ∑ j ∈ Finset.range n,T' j; have hK(m:ℕ): f i-f (i+m)=∑ j∈ Finset.range m,(f (i+j)-f (i+j+1)):=by induction m with | zero=> simp| succ m ih=>rw [sum_range_succ,←ih]; simp only [← _root_.add_assoc]; abel
         rw [show Censor L q N η x i-q'= ∑ j∈Finset.range n,_ from (by rw[← hu,hK n])]
         apply (Cane.sum (Finset.range n) (fun j=> f (i+j)-f (i+j+1)) T' (fun j _=>hv' j)).grow; intro j hj; obtain ⟨hh,hφ'⟩:= (ΘVar (Gov_price ht h.vein.warmth).1 G A Z j).choose_spec; rw[Finset.sum_apply]; let B':=(D*Ωθ z a Z); have hB:0 ≤ B':=mul_nonneg hD (by unfold Ωθ; positivity); change ∑ j'∈ Finset.range n,T' j' j≤ _; apply le_trans (sum_le_sum (g:=fun k:ℕ=>(B'* V j)* burst b (i+k:ℕ)) (fun k _=>?_)) _; swap
         · apply le_trans _ (show B'*(V j* _)≤ (B'*V j)*burst b (i+k:ℕ) from le_of_eq ((mul_assoc ..).symm)); unfold T'; rw [Pi.smul_apply,smul_eq_mul]; change (burst _ _*_ * Ωθ z a Z)* _≤ _; rw [show (burst g! (i+k:ℕ)*D*Ωθ z a Z)* p (i+k) A j= B'*(burst g! (i+k:ℕ)*p (i+k) A j) from (by unfold p B'; ring)]; exact mul_le_mul_of_nonneg_left (hφ' _) hB -- inspect
         rw[← Finset.mul_sum]; apply (mul_le_mul_of_nonneg_left (Bsum (half_pos (Gov_price ht h.vein.warmth).1) n i) (mul_nonneg hB hh)).trans; apply le_of_eq; change _= (Ywall b z a D Z i* (1-Real.exp (-b))⁻¹)*V j; unfold B' Ywall b; ring
end
end YM.OPE.Borealis.Galea
