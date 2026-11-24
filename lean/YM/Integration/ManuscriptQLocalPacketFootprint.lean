import YM.Integration.LocalComparisonPackets
import YM.Comparison.Density.RenderM.Inflect
import YM.Next.SCHEDULE.TensorCost

/-! Held mark tariffs for every positive requested support exponent. The change
of origin uses the genuine purchased cover and path reserve. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalPacketFootprint
open Finset Lattice RG Wilson Marker Comparison.Density.RenderM Next.Scheduling
open Comparison.Density.RenderM.Token LocalComparison Push.AbsoluteSums
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {B : Census V}
  {D : V → ComparisonDensity.Address.Orbit} {P : MarkedPackets D G n B} {q : BudgetPoint}
  {address : V→Support n} {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
  {w : V→ℝ} {g width budget : ℝ} {off slope : ℕ}
  (H : P.Paid q address region w g width budget off slope)
  {i : ℕ} {T : Token G n (fun v => (D v).Mood) (P.rank i)} (hT : P.packet i=some T)

/-- The radius and ensuing finite scalar bill agree definitionally with
the original ActualWilsonPacketRegularWeight prices. -/
def radius (ω : ℝ) := min 1 (ω/4)

def geometry (b : ℝ) (m k : ℕ) (ω : ℝ) :=
  Real.exp 3*(24*(1+b))^m*((m.factorial:ℝ)^2)*((k.factorial:ℝ)/(radius ω)^k)

def purchase (G : Gauge) (p : BudgetPoint) (cap : ℕ) (ω : ℝ) :=
  geometry p.B (p.power*p.order) (Wages.grade cap p.power p.order) ω *
    (∑ r∈range (cap+1),2*Wages.startup G r p.power p.order)

theorem geometry_nonnegative (b : ℝ) (m k : ℕ) {ω : ℝ} (hb : 0≤b) (hω : 0<ω) :
    0≤geometry b m k ω := by
  have hr : 0<radius ω := lt_min zero_lt_one (by positivity)
  unfold geometry
  positivity


private theorem power {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) (n : ℕ) :
    x^n ≤ ((n.factorial:ℝ)/h^n) * Real.exp (h*x) := by
  have hf : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have ht := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (h*x) (mul_nonneg hh.le hx) n)
  calc
    _ ≤ Real.exp (h*x)*(n.factorial:ℝ)/h^n := (le_div_iff₀ (pow_pos hh n)).mpr (by
      simpa only [mul_pow, mul_comm (x^n)] using ht)
    _ = _ := by ring

private theorem polynomial {b f a ω : ℝ} (hb : 0≤b) (hf : 0≤f) (ha : 0≤a) (hω : 0<ω) (m k : ℕ) :
    (6*(1+b)*(1+a)*(1+ω*f))^m*(1+f)^k ≤
      geometry b m k ω*Real.exp a*Real.exp ((ω/2)*f) := by
  let h := radius ω
  have hh : 0<h := lt_min zero_lt_one (by positivity)
  have h1 : h≤1 := min_le_left .. 
  have h4 : h≤ω/4 := min_le_right ..
  have hA : (1+a)^m≤(m.factorial:ℝ)*Real.exp (1+a) := by
    simpa using power (show 0≤1+a by linarith) zero_lt_one m
  have hF' := power (show 0≤1+ω*f by positivity) (show (0:ℝ)<1/4 by norm_num) m
  have hF : (1+ω*f)^m ≤ ((m.factorial:ℝ)*4^m)*Real.exp ((1/4)*(1+ω*f)) := by
    apply hF'.trans_eq
    have hi : ((1/4:ℝ)^m)⁻¹=4^m := by rw [←inv_pow,show (1/4:ℝ)⁻¹=4 by norm_num]
    rw [div_eq_mul_inv,hi]
  have hV := power (show 0≤1+f by linarith) hh k
  have he : Real.exp (1+a)*Real.exp ((1/4)*(1+ω*f))*Real.exp (h*(1+f)) ≤
      Real.exp 3*Real.exp a*Real.exp ((ω/2)*f) := by
    simp only [←Real.exp_add]
    apply Real.exp_monotone
    nlinarith only [h1,mul_le_mul_of_nonneg_right h4 hf]
  let C := (6*(1+b))^m*(m.factorial:ℝ)*((m.factorial:ℝ)*4^m)*((k.factorial:ℝ)/h^k)
  have hC : 0≤C := by unfold C;positivity
  calc
    _ = (6*(1+b))^m*(((1+a)^m*(1+ω*f)^m)*(1+f)^k) := by simp only [mul_pow];ring
    _ ≤ (6*(1+b))^m*((((m.factorial:ℝ)*Real.exp (1+a))*
        (((m.factorial:ℝ)*4^m)*Real.exp ((1/4)*(1+ω*f))))*
        (((k.factorial:ℝ)/h^k)*Real.exp (h*(1+f)))) := by gcongr
    _ = C*(Real.exp (1+a)*Real.exp ((1/4)*(1+ω*f))*Real.exp (h*(1+f))) := by unfold C;ring
    _ ≤ C*(Real.exp 3*Real.exp a*Real.exp ((ω/2)*f)) := mul_le_mul_of_nonneg_left he hC
    _ = _ := by
      unfold C geometry h
      rw [show 24*(1+b)=(6*(1+b))*4 by ring]
      simp only [mul_pow]
      ring


include H in
private theorem weighted_cover_at (s z : ℝ) (hs : 0 ≤ s) (hwidth : s*(slope:ℝ)≤z*(q.B:ℝ))
    (i : ℕ) (T : Token G n (fun v => (D v).Mood) (P.rank i)) (hT : P.packet i=some T) :
    Real.exp ((s)*(coverNumber q.B T.plot:ℝ)) ≤
      Real.exp ((s)*off)*Real.exp (z*T.fall) := by
  have hb : 0<(q.B:ℝ) := Nat.cast_pos.mpr q.B_pos
  have hq := H.cover i T hT
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  apply (le_of_mul_le_mul_right _ hb)
  calc
    _ = (s)*(q.B*(coverNumber q.B T.plot:ℝ)) := by ring
    _ ≤ (s)*(off*q.B+slope*T.fall) :=
      mul_le_mul_of_nonneg_left hq hs
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg T.fall)]


def surcharge (σ : ℝ) := max 1 (4*σ)⁻¹

def fee (G : Gauge) (σ : ℝ) (p : BudgetPoint) (cap : ℕ) (ω : ℝ) :=
  surcharge σ^(p.power*p.order) * purchase G p cap ω

include H hT in
private theorem span (p : BudgetPoint) (hB : p.B=q.B) :
    1+(Comparison.Density.RenderM.Token.span p T:ℝ) ≤
      surcharge q.supportExponent*(6*(1+(p.B:ℝ))*(1+(off:ℝ))*(1+width*T.fall)) := by
  let k : ℝ := coverNumber q.B T.plot
  let b : ℝ := q.B
  let f : ℝ := T.fall
  have hb : 0<b := Nat.cast_pos.mpr q.B_pos
  have hf : 0≤f := Nat.cast_nonneg _
  have ho : 0≤(off:ℝ) := Nat.cast_nonneg _
  have hF : 0≤width*f := mul_nonneg H.width_pos.le hf
  let V := surcharge q.supportExponent
  have hv : 1≤V := le_max_left _ _
  have hpos : 0<4*q.supportExponent := mul_pos (by norm_num) q.exponent_pos
  have hsl : (slope:ℝ)≤V*(width*b) := by
    have w := (div_le_iff₀ hb).mp H.width_reserved
    have v : (slope:ℝ)≤(width*b)/(4*q.supportExponent) := by
      apply (le_div_iff₀ hpos).2
      nlinarith only [w]
    rw [div_eq_mul_inv,mul_comm (width*b) ((4*q.supportExponent)⁻¹)] at v
    exact v.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg H.width_pos.le hb.le))
  have hcov : k≤off+V*(width*f) := by
    apply le_of_mul_le_mul_left _ hb
    have qcov := H.cover i T hT
    change b*k≤off*b+slope*f at qcov
    nlinarith only [qcov,mul_le_mul_of_nonneg_right hsl hf]
  unfold Comparison.Density.RenderM.Token.span
  rw [hB]
  push_cast
  calc
    _ ≤ (6*(1+b))*(1+k) := by
      change 1+(k*(4*b+2)+2*b)≤_
      nlinarith only [hb.le,(show 0≤k from Nat.cast_nonneg _),mul_nonneg hb.le (show 0≤k from Nat.cast_nonneg _)]
    _ ≤ (6*(1+b))*((1+(off:ℝ))*(1+V*(width*f))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [hcov,mul_nonneg ho (mul_nonneg (zero_le_one.trans hv) hF)]
    _ ≤ (6*(1+b))*((1+(off:ℝ))*(V*(1+width*f))) := by
      gcongr
      linarith
    _ = _ := by ring

include H hT in
theorem token (p : BudgetPoint) (hB : p.B=q.B)
    (hr : p.supportExponent≤2*q.supportExponent)
    (c cap : ℕ) (hc : c≤P.rank i) (hcap : P.rankCap≤cap) :
    p.mass T.plot (touched p T) ≤
      fee G q.supportExponent p cap width*p.threshold^c*Real.exp ((p.supportExponent+1)*off)*
        (T.coin*Real.exp (width*T.fall)) := by
  let m := p.power*p.order
  let k := Wages.grade cap p.power p.order
  let f : ℝ := T.fall
  let S := ∑r∈range (cap+1),2*Wages.startup G r p.power p.order
  have hh := H.width_reserved
  have hb : 0<(q.B:ℝ) := Nat.cast_pos.mpr q.B_pos
  have hwidth : p.supportExponent*(slope:ℝ)≤(width/2)*(q.B:ℝ) := by
    have h' := (div_le_iff₀ hb).mp hh
    nlinarith only [h',mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg slope)]
  have cover := weighted_cover_at H p.supportExponent (width/2) p.exponent_pos.le hwidth i T hT
  have hspan := span H hT p hB
  have hP := pow_le_pow_left₀ (show 0≤1+(Comparison.Density.RenderM.Token.span p T:ℝ) by positivity) hspan m
  rw [mul_pow] at hP
  have hv : 0 ≤ surcharge q.supportExponent := zero_le_one.trans (le_max_left _ _)
  have hrc := (P.rank_bounded i T hT).trans hcap
  have hf : 0≤f := Nat.cast_nonneg _
  have hω := H.width_pos
  have hgrade : Wages.grade (P.rank i) p.power p.order ≤ k := Nat.mul_le_mul_left _ hrc
  have hTpow := pow_le_pow_right₀ (show (1:ℝ)≤1+f from le_add_of_nonneg_right hf) hgrade
  have hpoly := polynomial (Nat.cast_nonneg p.B) (Nat.cast_nonneg T.fall) (Nat.cast_nonneg off) H.width_pos m k
  have hlength : (1+(Comparison.Density.RenderM.Token.span p T:ℝ))^m*(1+f)^(Wages.grade (P.rank i) p.power p.order) ≤
      surcharge q.supportExponent^m*(geometry p.B m k width*Real.exp (off:ℝ)*Real.exp ((width/2)*f)) := by
    calc
      _ ≤ (surcharge q.supportExponent^m*(6*(1+(p.B:ℝ))*(1+(off:ℝ))*(1+width*f))^m)*(1+f)^k :=
        mul_le_mul hP hTpow (by positivity) (by positivity)
      _ = surcharge q.supportExponent^m*((6*(1+(p.B:ℝ))*(1+(off:ℝ))*(1+width*f))^m*(1+f)^k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (pow_nonneg hv _)
  have ht : p.threshold^(P.rank i)≤p.threshold^c := pow_le_pow_of_le_one p.threshold_pos.le p.threshold_le hc
  have hs0 (r : ℕ) : 0≤2*Wages.startup G r p.power p.order :=
    mul_nonneg (by norm_num) (start_safe (t:=r) p G)
  have hS : 2*Wages.startup G (P.rank i) p.power p.order≤S :=
    single_le_sum (fun r _ => hs0 r) (mem_range.mpr (by omega))
  have hSa : 0≤S := sum_nonneg fun r _ => hs0 r
  have hcoin := (H.coefficient i T hT).1
  have hθ := p.threshold_pos.le
  have hstart := hs0 (P.rank i)
  have hG := geometry_nonnegative (p.B:ℝ) m k (Nat.cast_nonneg _) H.width_pos
  change Real.exp (p.supportExponent*(coverNumber p.B T.plot:ℝ))*
      ((1+(Comparison.Density.RenderM.Token.span p T:ℝ))^m*
        ((2*Wages.startup G (P.rank i) p.power p.order)*p.threshold^(P.rank i)*T.coin*
          ((T.fall:ℝ)+1)^(Wages.grade (P.rank i) p.power p.order))) ≤ _
  rw [hB,add_comm (T.fall:ℝ) 1]
  calc
    _ = Real.exp (p.supportExponent*(coverNumber q.B T.plot:ℝ))*
        ((2*Wages.startup G (P.rank i) p.power p.order)*p.threshold^(P.rank i)*T.coin)*
        ((1+(Comparison.Density.RenderM.Token.span p T:ℝ))^m*(1+f)^(Wages.grade (P.rank i) p.power p.order)) := by ring
    _ ≤ (Real.exp (p.supportExponent*off)*Real.exp ((width/2)*f))*(S*p.threshold^c*T.coin)*
        (surcharge q.supportExponent^m*(geometry p.B m k width*Real.exp (off:ℝ)*Real.exp ((width/2)*f))) := by gcongr
    _ = _ := by
      unfold fee purchase
      rw [show (p.supportExponent+1)*(off:ℝ)=p.supportExponent*off+off by ring,Real.exp_add,
        show width*f=(width/2)*f+(width/2)*f by ring,Real.exp_add]
      ring

end YM.Integration.ManuscriptQLocalPacketFootprint
