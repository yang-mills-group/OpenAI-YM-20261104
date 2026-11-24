import YM.Integration.WilsonLocalCompactProbability

/-! Three-factor Hölder and mean deviation on the actual positive conditional
functional. Each moment can be bought separately on its own source. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactMoments
open MeasureTheory Lattice RG Wilson
open WilsonLocalCompactProbability
open scoped Classical Topology
variable {G:Gauge} {n:Side} (P:Signal (G:=G) (n:=n)→ₗ[ℝ]ℝ)

def Positive:Prop:=∀F:Signal (G:=G) (n:=n),(∀U,0≤F.1 U)→0≤P F

theorem mono (pos:Positive P) {F H:Signal (G:=G) (n:=n)} (ordered:∀x,F.1 x≤H.1 x):P F≤P H:=by
  have test:=pos (H-F) (fun x=>sub_nonneg.mpr (ordered x))
  simpa only [map_sub,sub_nonneg] using test

theorem signed (pos:Positive P) (F:Signal (G:=G) (n:=n)):|P F|≤P (absolute F):=by
  apply abs_le.mpr
  have lo:=mono P pos (F:=-F) (H:=absolute F) (fun x=>neg_le_abs (F.1 x))
  rw [map_neg] at lo
  exact ⟨by linarith only [lo],mono P pos (F:=F) (H:=absolute F) (fun x=>le_abs_self (F.1 x))⟩

theorem deviation (pos:Positive P) (one:P 1=1) (F:Signal (G:=G) (n:=n)):
    spread P F≤2*P (absolute F):=by
  have charge:=mono P pos (F:=absolute (center P F)) (H:=absolute F+|P F| • 1) (fun x=>by
    change |F.1 x-P F*1|≤|F.1 x|+|P F| * 1;simp only [mul_one];exact abs_sub ..)
  rw [map_add,map_smul,one,smul_eq_mul,mul_one] at charge
  change P (absolute (center P F))≤_
  linarith only [charge,signed P pos F]

private theorem agm (x y z:ℝ) (hx:0≤x) (hy:0≤y) (hz:0≤z):
    3*(x*y*z)≤x^3+y^3+z^3:=by
  nlinarith only [mul_nonneg (add_nonneg (add_nonneg hx hy) hz)
    (add_nonneg (add_nonneg (sq_nonneg (x-y)) (sq_nonneg (y-z))) (sq_nonneg (z-x)))]

private theorem unit_bound (pos:Positive P) (f h j:Signal (G:=G) (n:=n))
    (fnn:∀U,0≤f.1 U) (hnn:∀U,0≤h.1 U) (jnn:∀U,0≤j.1 U)
    (fm:P (f^3)≤1) (hm:P (h^3)≤1) (jm:P (j^3)≤1):P (f*h*j)≤1:=by
  have bound:=mono P pos (F:=(3:ℝ)•(f*h*j)) (H:=f^3+h^3+j^3) (fun U=>agm _ _ _ (fnn U) (hnn U) (jnn U))
  rw [map_smul,smul_eq_mul,map_add,map_add] at bound
  linarith only [bound,fm,hm,jm]

private theorem normalized (F:Signal (G:=G) (n:=n)) {a:ℝ} (ap:0<a)
    (fm:P ((absolute F)^3)≤a^3):P ((a⁻¹•absolute F)^3)≤1:=by
  have eq:(a⁻¹•absolute F)^3= (a⁻¹)^3•(absolute F)^3:=by
    ext x;change (a⁻¹*|F.1 x|)^3=(a⁻¹)^3*|F.1 x|^3;ring
  rw [eq,map_smul,smul_eq_mul]
  calc (a⁻¹)^3*P ((absolute F)^3)≤(a⁻¹)^3*a^3:=mul_le_mul_of_nonneg_left fm (by positivity)
       _=1:=by field_simp

theorem three (pos:Positive P) (F H J:Signal (G:=G) (n:=n)) {a b c:ℝ} (ap:0<a) (bp:0<b) (cp:0<c)
    (fm:P ((absolute F)^3)≤a^3) (hm:P ((absolute H)^3)≤b^3) (jm:P ((absolute J)^3)≤c^3):
    P (absolute (F*H*J))≤a*b*c:=by
  have bound:=unit_bound P pos (a⁻¹•absolute F) (b⁻¹•absolute H) (c⁻¹•absolute J)
    (fun x=>mul_nonneg (inv_nonneg.mpr ap.le) (abs_nonneg (F.1 x)))
    (fun x=>mul_nonneg (inv_nonneg.mpr bp.le) (abs_nonneg (H.1 x)))
    (fun x=>mul_nonneg (inv_nonneg.mpr cp.le) (abs_nonneg (J.1 x)))
    (normalized P F ap fm) (normalized P H bp hm) (normalized P J cp jm)
  have eq:(a⁻¹•absolute F)*(b⁻¹•absolute H)*(c⁻¹•absolute J)=
      (a⁻¹*b⁻¹*c⁻¹)•absolute (F*H*J):=by
    ext x
    change (a⁻¹*|F.1 x|)*(b⁻¹*|H.1 x|)*(c⁻¹*|J.1 x|)=(a⁻¹*b⁻¹*c⁻¹)*|F.1 x*H.1 x*J.1 x|
    rw [abs_mul,abs_mul];ring
  rw [eq,map_smul,smul_eq_mul] at bound
  have paid:=mul_le_mul_of_nonneg_left bound (mul_nonneg (mul_nonneg ap.le bp.le) cp.le)
  calc P (absolute (F*H*J))=(a*b*c)*((a⁻¹*b⁻¹*c⁻¹)*P (absolute (F*H*J))):=by
         field_simp [ap.ne',bp.ne',cp.ne']
       _≤(a*b*c)*1:=paid
       _=a*b*c:=mul_one _

theorem one_abs:absolute (1:Signal (G:=G) (n:=n))=1:=by ext U;exact abs_one

theorem two (pos:Positive P) (one:P 1=1) (F H:Signal (G:=G) (n:=n)) {a b:ℝ} (ap:0<a) (bp:0<b)
    (fm:P ((absolute F)^3)≤a^3) (hm:P ((absolute H)^3)≤b^3):P (absolute (F*H))≤a*b:=by
  simpa only [mul_one] using three P pos F H 1 ap bp zero_lt_one fm hm (by simp [one_abs,one])

theorem single (pos:Positive P) (one:P 1=1) (F:Signal (G:=G) (n:=n)) {a:ℝ} (ap:0<a)
    (fm:P ((absolute F)^3)≤a^3):P (absolute F)≤a:=by
  simpa only [mul_one] using two P pos one F 1 ap zero_lt_one fm (by simp [one_abs,one])

end YM.Integration.WilsonLocalCompactMoments
