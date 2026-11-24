import YM.AllOrder.Laplace.Mercy
import YM.AllOrder.Laplace.Desk
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested MeasureTheory ProbabilityTheory Function Set Metric Filter PositionX.Jet
open scoped Topology ENNReal ContDiff Classical
open Matrix Lattice Wilson RG Gauge Precision Tree Push Push.Uniform
open PhysicalNext Repeat Lapis Lantern Fare Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat Local Vote
open scoped BigOperators Matrix.Norms.Frobenius MatrixOrder
section accent
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {ι:Type} [Fintype ι][DecidableEq ι]
local notation "Y"=> Body ι
variable {A B:X×Poll.Body ι→ℝ}{m:X→Matrix ι ι ℝ}{ρ:X→Poll.Body ι}
    (h:Accent A B m ρ) (R:ℝ)
local notation "F"=> (A ∘ Prod.snd)
set_option quotPrecheck false

local notation "H"=> fun p : ℝ×(X×Y)=> R*Real.exp (-B p.2)
local notation "μ"=> sweep (m 0)⁻¹
-- constant paths
variable (v:X)(z:Poll.Body ι)
def munit (n:Matrix ι ι ℝ):= ((Real.sqrt (2*Real.pi))^Fintype.card ι * Real.exp (- Real.log n.det/2))
lemma munit_pos (n:Matrix ι ι ℝ): 0< munit n:= by unfold munit; positivity
def course {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](v:E)(t:ℝ):= t• v
local notation "Y₀"=> ρ ∘ course v
include h
lemma sip_read : munit (m 0)*Shield.lens₀ (m 0)⁻¹ z= Real.exp (-vote A ρ z (0,0)):= Function.const _ (by
   obtain ⟨hp,hh⟩:= h.station.self_of_nhds
   have he:= hp.det_pos
   have hx : ((m 0)⁻¹)⁻¹ = m 0:= Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr he.ne')
   rw [roll, Shield.lens₀,hx, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv,(hh z).2]; unfold munit; let r:= Real.log (m 0).det/2; rw [show -(-Real.log (m 0).det)/2=r from (by unfold r; ring), Real.exp_sub,Real.exp_neg]; field_simp; ring_nf; rw [←Real.exp_add,show Real.log (m 0).det*(-1/2)+r=0 from (by unfold r; ring), Real.exp_zero]
  ) (inferInstance : FiniteDimensional ℝ X)
lemma tripped : Treaty A ρ (A ∘ Prod.snd) (fun p:ℝ × (X×Poll.Body ι)=> R*Real.exp (- B p.2)):= Function.const _ (by
 have h₀ : ContDiffAt ℝ ω (fun p:ℝ×(X×Y)=> B p.2) 0 := h.poly.comp (f:=Prod.snd) 0 contDiffAt_snd
 exact ⟨h.steer,h.steer.hard.comp (f:=Prod.snd) 0 contDiffAt_snd, fun _ _=> rfl, contDiffAt_const.mul h₀.neg.exp⟩
  ) (inferInstance : FiniteDimensional ℝ X)
lemma course_claim : NextTo ρ (course v) (ρ ∘ course v):= Function.const _ (belong h.steer (zero_smul ..) (contDiffAt_id.smul contDiffAt_const)) (inferInstance : FiniteDimensional ℝ X)
variable (r:ℝ) (hr:0< Laplace.curvature A (fderiv ℝ (course v) 0 1) (fderiv ℝ (ρ ∘ course v) 0 1)+r)
include hr
local notation "Q"=> prepare F (course v) Y₀ r
local notation "Ψ"=> (H) ∘ tone (course v) Y₀
local notation "g"=> glowP (course v) A B m ρ
local notation "S"=> Real.exp ∘ slopeP (course v) A B m ρ
local notation "α"=> Real.exp (-r)* R* munit (m 0)
local notation "J"=> Shield.lens₀ (m 0)⁻¹
lemma mint : (fun n=> normTerm (Ψ) (Q) n (onLane z))= fun i=> α * J z * plus (someJ (S)) (someJ (g z)) i:= by
 let L':= Q; let c':=α*J z; let f t:= c'*(S t*g z t); have hk:= approved (tripped h R) (course_claim h v) hr ; let hP:= (course_claim h v).cont; let hp:=(course_claim h v).p0
 have hm:= nice_glow h (course v) hP hp z; have hS:ContDiffAt ℝ ω S 0:=(nice_slope h _ hP hp).exp
 rw [coined hk.revenue hk.income («g»:=f) (contDiffAt_const.mul (hS.mul hm))]
 · rw [show f= (fun (_:ℝ)=> c')*((S)*(g z)) from rfl, some_mul contDiffAt_const (show ContDiffAt ℝ ω ((S)*(g z)) 0 from hS.mul hm),some_mul hS hm, show someJ (fun (_:ℝ)=> c')=just c' from funext (fun i=> (Act.static c' (n:=i)).writes i le_rfl),exact_scale]; rfl
 filter_upwards [cost_shift h _ hP hp z,Tested.eventually_pos] with t ht h₁
 rw [projection_eq]; have hc : tone (course v) (ρ ∘ course v) (t • onLane z)= (t,course v t,ρ (course v t)+t • z):=by simp [tone,onLane]
 unfold prepare; simp only [Pi.add_apply, Function.comp_apply,hc ]; simp only [onLane,Prod.smul_mk,smul_eq_mul, mul_one]
 let y:= (course v t,ρ (course v t)+ t• z); let q:= slopeP (course v) A B m ρ t; let a:= grace A B ρ m z (t, course v t); let i:= vote A ρ z (0,0); change -(A y)/t^2-B y=q+a-i at ht
 change R*Real.exp (-B y)*Real.exp (-(A y+r*t^2)/t^2)=(Real.exp (-r)*R*munit (m 0)*J z)*(Real.exp q*Real.exp a)
 rw [show -(A y+r*t^2)/t^2= -r+ -(A y)/t^2 from (by field_simp; ring), show -A y/t^2=q+a-i+B y from (by linarith),mul_assoc R, ← Real.exp_add,mul_assoc _ (munit _), sip_read h z, show -B y+(-r+(q+a-i+B y))=-r+ -i +(q+a) from (by ring)]
 rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
end accent
end YM.AllOrder.Laplace.SigmaP
