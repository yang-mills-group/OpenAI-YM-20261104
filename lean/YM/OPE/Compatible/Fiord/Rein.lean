import YM.OPE.Compatible.Fiord.Part
/-!
# Tilt calculus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {I:Type}{s t c:ℝ}{X Y:I→Type}[∀ i,MeasurableSpace (X i)][∀ i,MeasurableSpace (Y i)] {φ:Filter I}{Z:I→ℝ} {μ:(i:I)→Measure (X i)} {ν:(i:I)→Measure (Y i)}
open PertExtension Series Libra GaussianScore Jargon JetS
variable [∀ i, IsProbabilityMeasure (μ i)][∀ i,IsProbabilityMeasure (ν i)]
variable {p q f g:Hang X}(ht:Tendsto Z φ atTop)
-- Fees all Stages stable
omit [∀ i,IsProbabilityMeasure (μ i)] in abbrev Pine (μ:(i:I)→Measure (X i))(φ:Filter I)(Z:I→ℝ)(p:Hang X)(s:ℝ):Prop:= ∀ i:Fin 3,Grain μ φ Z (run_H p i.val) s
include ht
lemma PineInv (he:Pine μ φ Z p 0)(hv:∀ i x,(p i x).s=1): Pine μ φ Z (fun i x=>(p i x)⁻¹) 0:=by
       intro i; fin_cases i
       · apply (Grain.const (μ:=μ) (RateLE.const 1 ht)).shift; filter_upwards with i; funext x; exact ((sp_s _).trans (by rw [hv,inv_one])).symm
       · apply ((Grain.const (μ:=μ) (RateLE.const 0 ht)).sub (he 1) ht).shift; filter_upwards with i; funext x; change 0-(p i x).l=_; rw[zero_sub]; exact ((sp_l _).trans (by rw[hv];simp)).symm
       apply (((he 1).pow ht 2).sub (he 2) ht).shift; filter_upwards with i; funext x; exact ((sp_h _).trans (by rw[hv];simp;rfl)).symm -- calc dsimp
omit [∀ i, IsProbabilityMeasure (μ i)]
lemma PineM (he:Pine μ φ Z p s)(hp:Pine μ φ Z q t): Pine μ φ Z (p*q) (s+t):=by
       have h0:=he 0; have h1:=he 1; have h2:=he 2; have p0:=hp 0; have p1:=hp 1; have p2:=hp 2; intro i; fin_cases i; · exact h0.mul p0
       · exact (h0.mul p1).add (h1.mul p0) ht
       exact ((h0.mul p2).add (h1.mul p1) ht).add (h2.mul p0) ht
lemma PineC (he:Pine μ φ Z (p-q) s)(h:Pine μ φ Z p 0)(hv:Pine μ φ Z (f-g) s)(hG:Pine μ φ Z g 0):Pine μ φ Z (p*f-q*g) s:=by
       rw [show p*f-q*g=p*(f-g)+(p-q)*g by ring]; intro i; let z:= (PineM ht h hv i).mint (le_of_eq (zero_add _)); let V:=(PineM ht he hG i).mint (le_of_eq (add_zero _)); fin_cases i<;>exact z.add V ht
-- Beacon Δ inv when exact positives. Unit solves Lips.Elementwise
end YM.OPE.Cinders

namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {I:Type}{s t c:ℝ}{X Y:I→Type}[∀ i,MeasurableSpace (X i)][∀ i,MeasurableSpace (Y i)] {φ:Filter I}{Z:I→ℝ} {μ:(i:I)→Measure (X i)} {ν:(i:I)→Measure (Y i)}
open PertExtension Series Libra GaussianScore Jargon JetS
variable [∀ i, IsProbabilityMeasure (μ i)][∀ i,IsProbabilityMeasure (ν i)]
variable {p q f g:Hang X}(ht:Tendsto Z φ atTop)
include ht
noncomputable abbrev Trek (p: Hang X)(i:I)(x:X i):= (p i x)⁻¹
lemma PerV (he:Pine μ φ Z p 0)(hp:Pine μ φ Z q 0)(ha: Pine μ φ Z (p-q) s)(hf:∀ i x,(p i x).s=1)(hq:∀ i x,(q i x).s=1): Pine μ φ Z (Trek p-Trek q) s:=by
       have hx : Trek p*p=1:=funext fun i=>funext fun x=> JetS.uniting (p:=p i x) (by rw[hf]; exact one_ne_zero); have ht' : Trek q*q=1:=funext fun i=> funext fun x=> JetS.uniting (p:=q i x) (by rw[hq];exact one_ne_zero)
       rw [show Trek p-Trek q=(fun i x=> -(Trek p i x))*(Trek q)*(p-q) from ?_]; swap
       · symm; calc
             _ = Trek p*(Trek q*q)- Trek q*(Trek p*p):=by rw[show (fun i x=> -(Trek p i x))=-(Trek p) from rfl]; ring
             _ = _:=by rw[hx,ht',mul_one,mul_one]
       let b:= PineInv ht he hf; let hp':= PineInv ht hp hq; let g(i:I)(x:X i):= -(Trek p i x); have hg: Pine μ φ Z g 0:=by
             intro i; apply ((Grain.const (μ:=μ) (p:=0) (RateLE.zero φ Z _)).sub (b i) ht).shift; filter_upwards with j; funext x; change (0:ℝ)-_= _; rw[zero_sub]; fin_cases i<;>rfl
       exact fun i=> (PineM ht (PineM ht hg hp') ha i).mint (by simp)
lemma beaconP (p:Hang X)(d:I→ℝ)(h:Pine μ φ Z p s)(hd:RateLE φ Z d 0): Grain μ φ Z (aftD p d) s:=by
       exact ((h 0).add (((Grain.const hd).mul (h 1)).mint (by simp)) ht).add (((Grain.const (hd.pow 2 ht)).mul (h 2)).mint (by simp)) ht
lemma BeaconΔ (p q:Hang X)(d:I→ℝ)(h:Pine μ φ Z (p-q) s)(hd:RateLE φ Z d 0): Grain μ φ Z (aftD p d-aftD q d) s:=by
       apply Grain.shift (beaconP ht _ _ h hd); filter_upwards with i; ext1 x; let v:=p i x; let s:=q i x; let t:= d i; change (v.s - s.s) + t * (v.l-s.l) + t^2*(v.h-s.h)= v.atK t-s.atK t; simp only [atK, smul_eq_mul];ring -- atK power type maybe v.s-s not defeq
end YM.OPE.Cinders
