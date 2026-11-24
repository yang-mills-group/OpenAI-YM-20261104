import YM.Integration.WilsonOlderFreshGraphPainter
import YM.QuadraticLocal.Earn.Payload

/-! Issue each paid term of the independently normalized unary column at the
true physical binder. The signed Laurent monomial and its actual group
function are exact. Its salary uses the word's own paths before any test. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphMount
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn AllOrder AllOrder.Ink
open scoped Classical BigOperators

variable {G:Gauge}{n:Side}{V α:Type}[DecidableEq V]
variable {P:Earn.Passport n V}{H:Marker.Census V}(S:Earn.Binder P H)
variable (Y:Poetry.Lantern G Unit) (e d:ℕ) (h:0<d)
    (held:Y.Bears {()} () (e+d+2)) (law:Y.atom.Invariant)
    (seen:0<Y.atom.magnitude) (σ:ℝ) (weight:α→ℂ)

def fare:ℝ:=Y.atom.budget σ

include seen in
private lemma positive :0<fare Y σ:=mul_pos seen (Real.exp_pos _)

def loan :Loan:=⟨e,Y.r,d,h,by
  have whole:Y.r+Y.roots.length ≤ e+d+2:=held.tall
  have marked:0<Y.roots.length:=List.length_pos_of_mem held.owns
  omega⟩

def ballot:Earn.Row P H G α where
  binder:=S
  lamp:=loan Y e d h held
  atom:=Bloom.letdown Y.atom (fare Y σ)⁻¹
  lawful:=Bloom.claim _ _ law
  clear:=Y.r=0
  salary:=fare Y σ
  sound:=positive Y seen σ
  paint:=fun t=>(fare Y σ:ℂ)*weight t
  rank:=id

include seen in
theorem enrolled (cap:∀t,‖weight t‖≤1):
    let M:=ballot S Y e d h held law seen σ weight
    M.Budget ∧ M.Graceful σ ∧ M.lamp.e=e ∧ M.lamp.toll=d ∧ M.lamp.r=Y.r ∧
      M.center=S.center ∧ M.binder=S := by
  intro M
  refine ⟨fun t=>?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · change ‖(fare Y σ:ℂ)*weight t‖≤fare Y σ
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positive Y seen σ)]
    exact mul_le_of_le_one_right (positive Y seen σ).le (cap t)
  · change (Bloom.letdown Y.atom (fare Y σ)⁻¹).budget σ≤1
    rw [Bloom.reduce_charge,abs_of_pos (inv_pos.mpr (positive Y seen σ))]
    change (fare Y σ)⁻¹*fare Y σ≤1
    rw [inv_mul_cancel₀ (positive Y seen σ).ne']

theorem literal (t:α) (g:ℝ) (U:Config G n):
    (ballot S Y e d h held law seen σ weight).nominal g t U =
      weight t*(g^((e:ℤ)-(Y.r:ℤ))*Y.atom.unmasked U S.center:ℝ) := by
  change (fare Y σ:ℂ)*weight t*(g^((e:ℤ)-(Y.r:ℤ)) *
    (Bloom.letdown Y.atom (fare Y σ)⁻¹).unmasked U S.center:ℝ)=_
  rw [Bloom.grant]
  push_cast
  have nz : (fare Y σ:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (positive Y seen σ).ne'
  field_simp [nz]

theorem hearing {b:ℝ} (hb:2*σ≤b) (pos:0≤σ):
    (ballot S Y e d h held law seen σ weight).height σ ≤
      Real.exp (σ*S.length) *Y.money b := by
  change Y.atom.magnitude*Real.exp (σ*(Y.atom.length:ℝ)) *
    Real.exp (σ*((S.length+Y.atom.length:ℕ):ℝ)) ≤
    Real.exp (σ*(S.length:ℝ))*(Y.atom.magnitude*Real.exp (b*(Y.length:ℝ)))
  have leg:Y.atom.length≤Y.length := Nat.le_add_left _ _
  have tail : σ*(Y.atom.length:ℝ)+σ*((S.length+Y.atom.length:ℕ):ℝ)
       ≤ σ*(S.length:ℝ)+b*(Y.length:ℝ):=by
    have h₁:=mul_le_mul_of_nonneg_right hb (show 0≤(Y.atom.length:ℝ) from by positivity)
    have h₂:=mul_le_mul_of_nonneg_left (show (Y.atom.length:ℝ)≤(Y.length:ℝ) by exact_mod_cast leg)
      ((by linarith : 0≤b))
    push_cast;linarith
  rw [mul_assoc,←Real.exp_add,mul_left_comm (Real.exp _),←Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr tail) seen.le

end YM.Integration.WilsonOlderFreshGraphMount
end
