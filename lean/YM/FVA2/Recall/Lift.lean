import YM.FVA2.Hearth.Term
import Mathlib.RingTheory.PowerSeries.Substitution
/-!
 # X-adic extension with no topology demands on the (nonlocal) coefficient polynomials

 Used for joint field & formal coupling re-expression. The coefficient images
 are themselves allowed to be non-constant series. Use X-adic rules,
 with through-order whenever applying (even for non-Arch gauges).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries
open scoped Classical Topology BigOperators
variable {R S : Type*} [CommRing R][CommRing S]

abbrev Neat (φ:PowerSeries R→PowerSeries S) := ∀ {a b i},Through i a b→ Through i (φ a) (φ b)
lemma neatC (s:R→+*S) : Neat (map s : PowerSeries R →+* PowerSeries S):= fun _ i hi=> by rw [coeff_map,coeff_map]; congr 1; exact ‹Through ..› i hi

lemma coin_m (m:ℕ)(p:R): PowerSeries.monomial m p= X^m * C p:= PowerSeries.ext (fun i=>by rw [mul_comm,coeff_monomial,coeff_C_mul_X_pow])
-- uniqueness. prove equality only on monomials.
lemma recruit (a b:PowerSeries R→+ PowerSeries S)(p:Neat a)(q:Neat b) (h:∀ k:ℕ,∀ x:R,a ( X^k * C x ) = b ( X^k * C x )) (f: PowerSeries R) : a f=b f:= by
 have he (v:Polynomial R) : a v=b v:= by
    induction v using Polynomial.induction_on' with
    | monomial k x=> rw [Polynomial.coe_monomial,coin_m]; exact h k x
    | add x y hx hy=> rw [Polynomial.coe_add,a.map_add,b.map_add,hx,hy]
 apply PowerSeries.ext; intro i
 let f': PowerSeries R:= ↑(trunc (i+1) f); have hx: Through i f f':= Through.symm Through.through_trunc; rw [p hx i le_rfl,q hx i le_rfl]; exact congr_arg (coeff i) (he _)

namespace Porch
variable (Γ:R→+* PowerSeries S) (y:PowerSeries S)
local notation "θ"=> ( X*y )
private lemma shoots {i k:ℕ}(h:i<k)(v:PowerSeries S): coeff i (θ^k * v)=0:= by rw [mul_pow,mul_assoc,coeff_X_pow_mul', if_neg h.not_ge]

def run : PowerSeries R→+ PowerSeries S where
 toFun v:= mk (fun i=> ∑ j∈range (i+1), coeff i ( θ^j * Γ (coeff j v) ) )
 map_zero':= PowerSeries.ext fun i=> by simp
 map_add' x y:= PowerSeries.ext fun i=> by simp only [coeff_mk,map_add,mul_add,Finset.sum_add_distrib]

private lemma rate (v: PowerSeries R)(i:ℕ): coeff i (run Γ y v) = ∑ j∈range (i+1), coeff i (θ^j* Γ ( coeff j v )):= by simp [run]
lemma runway : Neat (run Γ y):= by
 intro a b i h j hj; rw [rate,rate]; apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_range] at hk; rw [h k (by omega)]
lemma arrives (f:R)(k): run Γ y ( X^k * C f ) = θ^k * Γ f:= by
 rw [ ←coin_m ]; apply PowerSeries.ext; intro i; rw [rate]; by_cases hx:k ≤ i
 · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (by omega)),coeff_monomial_same]; intro j _ h; rw [coeff_monomial,if_neg h,map_zero,mul_zero,map_zero]
 rw [shoots y (by omega), Finset.sum_eq_zero (fun j h=> ?_) ]; rw [Finset.mem_range] at h; rw [coeff_monomial,if_neg (by omega),map_zero,mul_zero,map_zero]
lemma rider (p:Polynomial R): run Γ y p= Polynomial.eval₂RingHom Γ θ p:= by
 induction p using Polynomial.induction_on' with
 | monomial k f=> rw [Polynomial.coe_monomial,coin_m, arrives,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_monomial,mul_comm (θ^k)]
 | add x y hx hy=> rw [Polynomial.coe_add,map_add,map_add,hx,hy]

def trip : PowerSeries R →+* PowerSeries S where
 __:= run Γ y
 map_one':= by change run Γ y 1=1; rw [ ←Polynomial.coe_one (R:=R),rider, RingHom.map_one]
 map_mul' f g:= by
    apply PowerSeries.ext; intro i; let x:= trunc (i+1) f; let z:= trunc (i+1) g
    have h:Through i f (↑x):= Through.symm Through.through_trunc; have k:Through i g (↑z):= Through.symm Through.through_trunc
    let v:= run Γ y; change coeff i (run Γ y (f*g)) = coeff i (run Γ y f*run Γ y g); rw [runway Γ y (h.mul k) i le_rfl, ((runway Γ y h).mul (runway Γ y k)) i le_rfl, ←Polynomial.coe_mul,rider,rider,rider,map_mul]
lemma trip_neat : Neat (trip Γ y):= runway Γ y
@[simp] lemma fromC (c:R) : trip Γ y (C c)= Γ c:= by change run Γ y _=_; simpa only [pow_zero,one_mul] using arrives Γ y c 0
@[simp] lemma source : trip Γ y X=X * y:= by change run Γ y _=_; simpa only [pow_one,map_one,mul_one] using arrives Γ y 1 1
end Porch
end YM.FVA2.Recall
