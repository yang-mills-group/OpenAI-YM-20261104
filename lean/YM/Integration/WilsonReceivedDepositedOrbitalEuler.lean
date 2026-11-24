import YM.Integration.WilsonReceivedDepositedOrbitalMode

/-! Counting only the occupied source names in a marked thermal board is a
derivation. Its finite exponential is the same pass used in the paid post. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalEuler
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators
variable {V:Type}[DecidableEq V]{J:Census V}

def count (w:V→ℂ)(s:J.Mode):ℂ:=∑ j∈s.val,w j

def scale (w:V→ℂ)(P:Poly J):Poly J:=Poly.inject fun s=>count w s * P.part s

private theorem counted (w:V→ℂ)(a b:Poly J):scale w (a*b)=a*scale w b+b*scale w a:=by
  rw [mul_comm b (scale w a)]
  apply Marker.Poly.ext
  intro s
  change count w s*(a*b).part s=(a*scale w b).part s+(scale w a*b).part s
  simp_rw [Poly.part_mul,Finset.mul_sum,←Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>?_
  by_cases h:Poly.merges j k s
  · simp only [h,if_true]
    change count w s*(a.part j*b.part k)=a.part j*(count w k*b.part k)+(count w j*a.part j)*b.part k
    have hsum:count w s=count w j+count w k:=by rw [count,←h.2,sum_union h.1];rfl
    rw [hsum];ring
  · simp [h]

def euler (w:V→ℂ):Derivation ℂ (Poly J) (Poly J) where
  toFun:=scale w
  map_add' a b:=Marker.Poly.ext fun s=>mul_add (count w s) (a.part s) (b.part s)
  map_smul' c a:=by
    apply Marker.Poly.ext
    intro s
    change count w s*(c*a.part s)=c*(count w s*a.part s)
    ring
  map_one_eq_zero' :=by
    apply Marker.Poly.ext
    intro s
    change count w s*(1:Poly J).part s=0
    by_cases h:s=J.quiet
    · subst s;simp [count,Census.quiet]
    · simp [Poly.one_part,h]
  leibniz' :=counted w

variable [Fintype V]

theorem pass (D:Derivation ℂ (Poly J) (Poly J))(a:Poly J)(quiet:a.part J.quiet=0):
    D a.pass=D a*a.pass:=by
  let n:=Fintype.card V
  have vanish:a^(n+1)=0:=Poly.stops a quiet _ (Nat.lt_succ_self _)
  have last:(n+1) • (a^n*D a)=0:=by
    have h:=congrArg D vanish
    rw [D.leibniz_pow, map_zero, Nat.add_sub_cancel] at h
    simpa only [smul_eq_mul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul,mul_assoc] using h
  have vanished:a^n*D a=0:=by
    letI : IsAddTorsionFree (Poly J):=.of_isTorsionFree ℂ (Poly J)
    exact (smul_right_inj (M:=Poly J) (Nat.succ_ne_zero n)).mp (last.trans (smul_zero _).symm)
  change D (∑j∈range (n+1),(j.factorial:ℂ)⁻¹ • a^j)=D a*∑j∈range (n+1),(j.factorial:ℂ)⁻¹ • a^j
  rw [map_sum,Finset.mul_sum,Finset.sum_range_succ' _ n,Finset.sum_range_succ _ n]
  have tail:D a*((n.factorial:ℂ)⁻¹ • a^n)=0:=by rw [mul_smul_comm,mul_comm,vanished,smul_zero]
  rw [tail,add_zero,pow_zero]
  simp only [Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,Derivation.map_one_eq_zero,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [D.map_smul,D.leibniz_pow,Nat.add_sub_cancel,mul_smul_comm]
  change ((j+1).factorial:ℂ)⁻¹ • ((j+1) • (a^j * D a))=(j.factorial:ℂ)⁻¹ • (D a*a^j)
  rw [←Nat.cast_smul_eq_nsmul ℂ,smul_smul,mul_comm (D a)]
  congr 1
  push_cast [Nat.factorial_succ]
  have ha:(j.factorial:ℂ)≠0:=by exact_mod_cast Nat.factorial_ne_zero j
  have hb:(j:ℂ)+1≠0:=by exact_mod_cast Nat.succ_ne_zero j
  field_simp

end YM.Integration.WilsonReceivedDepositedOrbitalEuler
end
