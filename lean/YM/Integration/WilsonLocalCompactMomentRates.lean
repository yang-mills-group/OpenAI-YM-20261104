import YM.Integration.WilsonLocalCompactMoments
import YM.Integration.WilsonLocalCompactConnectedHistory

/-! Separate conditional cubic budgets suffice to price both cumulants of the
retained law. The constants are independent of the torus and the old history. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactMomentRates
open MeasureTheory Lattice RG Wilson
open WilsonLocalCompactProbability WilsonLocalCompactMoments WilsonLocalCompactConnectedHistory
open scoped Classical Topology
variable {G:Gauge} {n:Side} (P:Signal (G:=G) (n:=n)→ₗ[ℝ]ℝ) (pos:Positive P) (one:P 1=1)

def Admitted (F:Signal (G:=G) (n:=n)) (a:ℝ):Prop:=P ((absolute (center P F))^3)≤a^3

include pos in
private theorem lower (X:Signal (G:=G) (n:=n)):0 ≤ spread P X:=by
  exact pos (absolute (center P X)) (fun _=>abs_nonneg _)

include pos one in
theorem pair (F H:Signal (G:=G) (n:=n)) {a b τ:ℝ} (ap:0<a) (bp:0<b) (tn:0≤τ)
    (fm:Admitted P F a) (hm:Admitted P H b):pairPrice P τ F H≤(2*τ+τ^2)*a*b:=by
  have f:spread P F≤a:=single P pos one _ ap fm
  have h:spread P H≤b:=single P pos one _ bp hm
  have prod:=two P pos one _ _ ap bp fm hm
  have m:=deviation P pos one (center P F*center P H)
  unfold pairPrice
  calc _≤τ*(2*(a*b))+(τ*a)*(τ*b):=by
         exact add_le_add (mul_le_mul_of_nonneg_left (m.trans (by linarith only [prod])) tn)
           (mul_le_mul (mul_le_mul_of_nonneg_left f tn) (mul_le_mul_of_nonneg_left h tn)
             (mul_nonneg tn (lower P pos H)) (mul_nonneg tn ap.le))
       _=_:=by ring

include pos one in
private theorem two_cap (F H:Signal (G:=G) (n:=n)) {a b τ:ℝ} (ap:0<a) (bp:0<b) (tn:0≤τ)
    (fm:Admitted P F a) (hm:Admitted P H b):
    let m:=center P F*center P H
    |P m|+τ*spread P m≤(1+2*τ)*(a*b):=by
  intro m
  have raw:P (absolute m)≤a*b:=two P pos one _ _ ap bp fm hm
  have mean:=signed P pos m
  have delta:=deviation P pos one m
  calc _≤a*b+τ*(2*(a*b)):=add_le_add (mean.trans raw)
         (mul_le_mul_of_nonneg_left (delta.trans (by linarith only [raw])) tn)
       _=_:=by ring

include pos one in
theorem triple (F H J:Signal (G:=G) (n:=n)) {a b c τ:ℝ} (ap:0<a) (bp:0<b) (cp:0<c) (tn:0≤τ)
    (fm:Admitted P F a) (hm:Admitted P H b) (jm:Admitted P J c):
    triplePrice P τ F H J≤(5*τ+6*τ^2+2*τ^3)*a*b*c:=by
  let f:=center P F;let h:=center P H;let j:=center P J
  let cut:=fun X=>τ*spread P X;let cap:=fun X=>|P X|+cut X
  have non (X):0≤cut X:=mul_nonneg tn (lower P pos X)
  have cost (X) {z:ℝ} (zp:0<z) (xm:Admitted P X z):cut X≤τ*z:=
    mul_le_mul_of_nonneg_left (single P pos one _ zp xm) tn
  have capped (X Y Z) {x y z:ℝ} (xp:0<x) (yp:0<y) (zp:0<z)
      (xm:Admitted P X x) (ym:Admitted P Y y) (zm:Admitted P Z z):
      cut X*cap (center P Y*center P Z)≤(τ*x)*((1+2*τ)*(y*z)):=
    mul_le_mul (cost _ xp xm) (two_cap P pos one Y Z yp zp tn ym zm)
      (add_nonneg (abs_nonneg _) (non _)) (mul_nonneg tn xp.le)
  have three_:P (absolute (f*h*j))≤a*b*c:=three P pos f h j ap bp cp fm hm jm
  have joint:cut (f*h*j)≤τ*(2*(a*b*c)):=
    mul_le_mul_of_nonneg_left ((deviation P pos one _).trans (by linarith only [three_])) tn
  have singles:2*cut F*cut H*cut J≤2*(τ*a)*(τ*b)*(τ*c):=
    mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (cost _ ap fm) (by norm_num)) (cost _ bp hm)
      (non _) (by positivity)) (cost _ cp jm) (non _) (by positivity)
  change cut (f*h*j)+cut F*cap (h*j)+cut H*cap (f*j)+cut J*cap (f*h)+2*cut F*cut H*cut J≤_
  exact (add_le_add (add_le_add (add_le_add (add_le_add joint (capped F H J ap bp cp fm hm jm))
    (capped H F J bp ap cp hm fm jm)) (capped J F H cp ap bp jm fm hm)) singles).trans_eq (by ring)

end YM.Integration.WilsonLocalCompactMomentRates
