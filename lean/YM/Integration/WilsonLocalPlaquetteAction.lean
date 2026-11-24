import YM.Integration.WilsonLocalPlaquetteField

/-! Measured inverse-coupling order and local finite-field remainder of the
original Wilson Boltzmann weight. Uniform in compact pivots and torus side. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteAction
open Finset Lattice Wilson RG WilsonLocalPlaquetteTaylor WilsonLocalPlaquetteField
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
def polynomial (p:ℕ) (b:Pivots G) (z:Angles G) (t:ℝ) : ℝ :=
  ∑i∈range (p+1),t^i*row b z i

def booked (p:ℕ) (S:Finset (Bonds n)) (outside L R:Config G n) (X Y:Angular G n) (t:ℝ) : ℝ :=
  ∑q∈set S,(polynomial p (pivot S outside L R q) (angles S X q) t-
    polynomial p (pivot S outside L R q) (angles S Y q) t)

def load (k:ℕ) (S:Finset (Bonds n)) (X Y:Angular G n) : ℝ :=
  ∑q∈set S,(‖angles S X q‖^k + ‖angles S Y q‖^k)

theorem energy_price (G:Gauge) (p:ℕ) : ∃C:ℝ,0≤C ∧ ∀ (n:Side) (S:Finset (Bonds n))
    (outside L R:Config G n) (X Y:Angular G n) (t:ℝ),0<t→(∀e∈S,t*‖X e‖<1 ∧ t*‖Y e‖<1)→
    |energy (field S outside L R X t)-energy (field S outside L R Y t)-booked p S outside L R X Y t|≤
      C*t^(p+1)*load (p+1) S X Y := by
  obtain ⟨C,hC,bill⟩:=WilsonLocalPlaquetteTaylor.purchased G p
  refine ⟨C,hC,?_⟩;intro n S outside L R X Y t ht room
  let value q (Z:Angular G n):=G.price (loop (placed (pivot S outside L R q) (t•angles S Z q)))
  let approximation q (Z:Angular G n):=polynomial p (pivot S outside L R q) (angles S Z q) t
  have price (q:Face (Per n)) (Z:Angular G n) (hz:∀e∈S,t*‖Z e‖<1) :
      |value q Z-approximation q Z|≤C*t^(p+1)*‖angles S Z q‖^(p+1) := by
    simpa only [value,approximation,polynomial,mul_pow,←mul_assoc] using
      bill (pivot S outside L R q) (angles S Z q) t ht (collar S Z ht hz q)
  rw [difference,booked,←Finset.sum_sub_distrib,load,Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _=>?_ )
  change |(value q X-value q Y)-(approximation q X-approximation q Y)|≤_
  calc
    _ = |(value q X-approximation q X)-(value q Y-approximation q Y)| := by congr 1;ring
    _ ≤ |value q X-approximation q X|+|value q Y-approximation q Y| := abs_sub _ _
    _ ≤ _ := by
      rw [mul_add];apply add_le_add
      · exact price q X (fun e he=>(room e he).1)
      · exact price q Y (fun e he=>(room e he).2)

theorem original (G:Gauge) (p:ℕ) : ∃C:ℝ,0≤C ∧ ∀ (n:Side) (S:Finset (Bonds n))
    (outside L R:Config G n) (X Y:Angular G n) (β g:ℝ),0≤β→0<g→β*g^2=1→
    (∀e∈S,g*‖X e‖<1 ∧ g*‖Y e‖<1)→
    |Real.log (bare β (field S outside L R X g)/bare β (field S outside L R Y g))+
      β*booked (p+2) S outside L R X Y g|≤C*g^(p+1)*load (p+3) S X Y := by
  obtain ⟨C,hC,bill⟩:=energy_price G (p+2)
  refine ⟨C,hC,?_⟩;intro n S outside L R X Y β g hβ hg clock room
  let x:=field S outside L R X g
  let y:=field S outside L R Y g
  let a:=booked (p+2) S outside L R X Y g
  have log : Real.log (bare β x/bare β y)+β*a= -β*(energy x-energy y-a) := by
    rw [bare,bare,Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp];ring
  change |Real.log (bare β x/bare β y)+β*a|≤_
  rw [log,abs_mul,abs_neg,abs_of_nonneg hβ]
  refine (mul_le_mul_of_nonneg_left (bill n S outside L R X Y g hg room) hβ).trans_eq ?_
  have power : g^(p+2+1)=g^2*g^(p+1) := by rw [←pow_add];congr 1;omega
  rw [power]; change β*(C*(g^2*g^(p+1))*load (p+3) S X Y)=_
  calc
    _=(β*g^2)*(C*g^(p+1)*load (p+3) S X Y) := by ring
    _=_ := by rw [clock,one_mul]

theorem measured (G:Gauge) (p:ℕ) : ∃C:ℝ,0≤C ∧ ∀ (n:Side) (S:Finset (Bonds n))
    (outside L R:Config G n) (X Y:Angular G n) (β:ℝ),0<β→
    let g:=(Real.sqrt β)⁻¹
    (∀e∈S,g*‖X e‖<1 ∧ g*‖Y e‖<1)→
    |Real.log (bare β (field S outside L R X g)/bare β (field S outside L R Y g))+
      β*booked (p+2) S outside L R X Y g|≤C*g^(p+1)*load (p+3) S X Y := by
  obtain ⟨C,hC,bill⟩:=original G p
  refine ⟨C,hC,?_⟩;intro n S outside L R X Y β hβ
  apply bill n S outside L R X Y β _ hβ.le (inv_pos.mpr (Real.sqrt_pos.mpr hβ))
  rw [inv_pow,Real.sq_sqrt hβ.le,mul_inv_cancel₀ hβ.ne']

end YM.Integration.WilsonLocalPlaquetteAction
