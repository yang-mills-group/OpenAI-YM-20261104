import YM.FVAAlt2.Commuting
/-! Exponential in formal coupling. Use on positive valuation. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Finset Function MS MS.Koszul MS.Native MS.Book MS.Cylinder MS.Puff MS.Puff.Actors
open MS.Swirl MS.Puff.Mom MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open Filter Topology
open scoped PowerSeries
section general
variable {R T: Type*}[CommRing R][CommRing T] [Algebra ℂ R][Algebra ℂ T]
local notation "R₀" => PowerSeries R
local notation "cf" => PowerSeries.coeff (R:=R)
set_option quotPrecheck false
local notation "ε" => fun (l:ℕ)=>(l.factorial:ℂ)⁻¹

def formExp (f: PowerSeries R): PowerSeries R:= PowerSeries.mk fun i=> ∑ l∈range (i+1), ε l • cf i (f^l)
lemma formExp_coeff (f:R₀)(i:ℕ): cf i (formExp f) = ∑ l∈range (i+1), ε l • cf i (f^l) := PowerSeries.coeff_mk ..
lemma formExp_map (h:R→ₐ[ℂ] T)(f:R₀): formExp (PowerSeries.map h.toRingHom f) = PowerSeries.map h.toRingHom (formExp f):= by ext i; simp only [formExp_coeff,PowerSeries.coeff_map,map_sum,←map_pow, AlgHom.toRingHom_eq_coe,RingHom.coe_coe]; simp
lemma formExp_sq {f:R₀} (H:cf 0 f=0)(h:f*f=0): formExp f=1+f:=by
  ext i; by_cases he:i=0
  · rw [he,formExp_coeff]; rw [PowerSeries.coeff_zero_eq_constantCoeff] at H; simp [H]
  rw [formExp_coeff,sum_range_succ']; rw [Finset.sum_eq_single 0]
  · simp [PowerSeries.coeff_one,he]
  · intro j _ hj; obtain ⟨k,rfl⟩:= Nat.exists_eq_succ_of_ne_zero hj; simp [pow_succ',← mul_assoc,h]; -- wrong
  intro hu; simp at hu; omega
end general

namespace Com
open MS.Puff.SplitP
variable {A W : Type} {p:Sector A}
local notation "cf" => (PowerSeries.coeff (R:=Com p))
local notation "f!" => forget p

lemma forget_pow (x:PowerSeries (Com p))(n:ℕ): f! (x^n)=(PermV p).power (f! x) n:= by
  induction n with
  | zero=> rw [pow_zero]; exact forget_one
  | succ i ih=> rw [pow_succ',forget_mul,power,ih]

lemma forget_exp (x:PowerSeries (Com p)): f! (formExp x)=exp0 p (f! x):= by
  funext i; unfold exp0 Actors.Cheer Actors.cheers; rw [Finset.sum_apply,forget_at,formExp_coeff,Submodule.coe_sum]
  simp_rw [ Actors.wages, Pi.smul_apply ]; exact sum_congr (show Finset.range (i+1)=_ from rfl) fun j _=> congrArg ((↑(j.factorial):ℂ)⁻¹ • ·) (congrFun (forget_pow x j) i)

lemma isProper{f:PowerSeries (Com p)} (hp: cf 0 f=0): Happy useN (forget p f):= by unfold Happy; rw [forget_at,show useN.origin=0 from rfl,hp]; rfl

lemma exponent_add {f g:PowerSeries (Com p)} (hf: cf 0 f=0)(hg: cf 0 g=0): formExp (f+g)=formExp f*formExp g:= forget_inj (by rw [forget_exp,map_add,forget_mul,forget_exp,forget_exp]; exact cheer_a (kept f) (kept g) (isProper hf) (isProper hg))
lemma exp_sum (X: Finset W) {f : W→ PowerSeries (Com p)} (h:∀ i∈ X, cf 0 (f i)=0) : formExp (∑ i∈X,f i)=∏ i∈X,formExp (f i):= by
  classical
  induction X using Finset.induction_on with
  | empty=>rw [Finset.sum_empty, Finset.prod_empty, formExp_sq (map_zero (cf 0)) (by simp),add_zero]
  | insert a s ha ih=>
    have he:=fun i hi=>h i (Finset.mem_insert_of_mem hi); rw [Finset.sum_insert ha, Finset.prod_insert ha, exponent_add (h a (Finset.mem_insert_self a s)) (Eq.trans (map_sum ..) (Finset.sum_eq_zero he)), ih he]
end Com
end YM.FVAAlt2
