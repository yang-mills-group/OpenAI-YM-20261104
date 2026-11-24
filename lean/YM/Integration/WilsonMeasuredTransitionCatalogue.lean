import YM.Integration.WilsonMeasuredOriginalPeriodRead

/-! Coefficients of the difference between all emitted children and the filed
lower transition. Every occupied power has one original lower basis label. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredTransitionCatalogue
open scoped Classical BigOperators
variable {C V:Type} [Fintype C] [Fintype V] {D:ℕ}

abbrev Names (C V:Type) (D:ℕ) := C ⊕ (V × Fin (D+1))
def weight (r:ℝ)(c:V→ℕ→ℝ) : Names C V D → ℝ
  | .inl _ => r
  | .inr (v,k) => -c v k
def lag : Names C V D → ℕ
  | .inl _ => 0
  | .inr (_,k) => k
def value (X:C→ℕ→ℂ)(Y:V→ℕ→ℂ) : Names C V D → ℕ → ℂ
  | .inl z => X z
  | .inr (v,_) => Y v

def slice (pole i ν:ℕ) (X:ℕ→ℂ) := if ν + pole≤ i then X (i-ν-pole) else 0

theorem antidiagonal (e:ℕ) (he:e≤D) (g:ℕ→ℕ→ℂ) :
    (∑k:Fin (D+1),if k.val≤e then g k.val (e-k.val) else 0)=
      ∑b∈(Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),g b.1 b.2 := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun k=>if k≤e then g k (e-k) else 0),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ = ∑k∈Finset.range (e+1),if k≤e then g k (e-k) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k _ absent
      have hk:¬k≤e:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using absent
      simp [hk]
    _ = _ := Finset.sum_congr rfl fun k hk=>if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem signed (r:ℝ) (c:V→ℕ→ℝ) (X:C→ℕ→ℂ) (Y:V→ℕ→ℂ)
    (reads:∀e≤D, (r:ℂ)*(∑ z,X z e)=∑v,∑b∈(Finset.HasAntidiagonal.antidiagonal e:
      Finset (ℕ×ℕ)),(c v b.1:ℂ)*Y v b.2) (pole i:ℕ) (hi:i <pole+D+1) :
    (∑a:Names C V D, weight r c a • slice pole i (lag a) (value X Y a))=0 := by
  classical
  by_cases low:i <pole
  · have zero(a:Names C V D):slice pole i (lag a) (value X Y a)=0:=if_neg (by omega)
    simp only [zero,smul_zero,Finset.sum_const_zero]
  have enough:pole≤ i:=by omega
  let e:=i-pole
  have hd:e≤D:=by dsimp [e];omega
  have out(z:C): weight r c (D:=D) (.inl z) • slice pole i (lag (V:=V) (D:=D) (.inl z)) (X z)
      = (r:ℂ)*X z e :=by simp [weight,lag,slice,enough,Complex.real_smul,e]
  have back (v:V)(k:Fin (D+1)):
      (-c v k) • slice pole i k.val (Y v) =
      -(if k.val≤e then (c v k:ℂ)*Y v (e-k.val) else 0):=by
    by_cases h:k.val≤e
    · have ok:k.val+pole≤ i:=by dsimp [e] at h;omega
      have addr:i-k.val-pole=e-k.val:=by dsimp [e];omega
      simp [slice,h,ok,addr,Complex.real_smul]
    · have skip:¬k.val+pole≤ i:=by dsimp [e] at h;omega
      simp [slice,h,skip]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [value,weight,lag] at out ⊢
  simp_rw [out,back]
  simp only [Finset.sum_neg_distrib, ←Finset.mul_sum]
  have counted(v:V):=antidiagonal e hd (fun i j=>(c v i:ℂ)*Y v j)
  simp_rw [counted]
  rw [reads e hd]
  abel

end YM.Integration.WilsonMeasuredTransitionCatalogue
end
