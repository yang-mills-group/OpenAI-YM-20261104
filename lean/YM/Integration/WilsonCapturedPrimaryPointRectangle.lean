import YM.Integration.WilsonCapturedPrimaryPointPeriodic

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPointRectangle
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp Pose
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations
open WilsonCapturedPrimaryPointBasis WilsonCapturedPrimaryPointWindow
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}

def rectangle (F:Frame G d)(Z:Pot G)(row:F.Index)(p:ℕ)(g:ℝ):ℝ:=
  ∑r∈range ((F.grades row).2+1),∑e∈range (p+1),pearlJ F (Z e r) row*g^((F.grades row).2-r+e)

def finite (F:Frame G d)(n:Side)(B:ℕ)(Z:Pot G)(row:F.Index)(p:ℕ)(g:ℝ):ℝ:=
  ∑r∈range ((F.grades row).2+1),∑e∈range (p+1),
    quote F B (sieve n (Z e r)) (axis F row)*g^((F.grades row).2-r+e)

def tail (F:Frame G d)(Z:Pot G)(row:F.Index)(p:ℕ):ℝ:=
  ∑r∈range ((F.grades row).2+1),∑e∈(range (p+1)).filter (fun e=>p<(F.grades row).2-r+e),
    |pearlJ F (Z e r) row|

theorem acoustic (F:Frame G d)(Z:Pot G)(row:F.Index)(k:ℕ):
    coeff k (coordinate F Z row)=∑r∈range ((F.grades row).2+1),
      if (F.grades row).2-r≤k then pearlJ F (Z (k-((F.grades row).2-r)) r) row else 0:=by
  simp only [coordinate,map_sum,coeff_mul_X_pow',coeff_mk]

private theorem offset (a p:ℕ) (f:ℕ→ℝ) (g:ℝ):
    (∑k∈range (p+1),(if a≤k then f (k-a) else 0)*g^k)=
      ∑e∈(range (p+1)).filter (fun n=>a+n≤p),f e*g^(a+e):=by
  simp_rw [ite_mul,zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun k _=>k-a) (fun e _=>a+e) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [mem_filter,mem_range] at hk ⊢;omega
  · intro e he; simp only [mem_filter,mem_range] at he ⊢;omega
  · intro k hk;simp only [mem_filter] at hk;omega
  · intro e he;omega
  · intro k hk;simp only [mem_filter] at hk
    rw [Nat.add_sub_of_le hk.2]

private theorem low (F:Frame G d)(Z:Pot G)(row:F.Index)(p:ℕ)(g:ℝ):
    (∑k∈range (p+1),coeff k (coordinate F Z row)*g^k)=
      ∑r∈range ((F.grades row).2+1),∑e∈(range (p+1)).filter (fun e=>(F.grades row).2-r+e≤p),
        pearlJ F (Z e r) row*g^((F.grades row).2-r+e):=by
  simp_rw [acoustic,Finset.sum_mul];rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _=>offset ((F.grades row).2-r) p (fun e=>pearlJ F (Z e r) row) g

theorem calibrated (F:Frame G d)(Z:Pot G)(row col:F.Index)(p:ℕ){g:ℝ}(g0:0≤g)(small:g≤1)
    (paid:coordinate F Z row=if row=col then 1 else 0):
    |rectangle F Z row p g-(if row=col then 1 else 0)|≤g^(p+1)*tail F Z row p:=by
  let v (r e:ℕ):=pearlJ F (Z e r) row
  let expn (r e:ℕ):=(F.grades row).2-r+e
  have known:=low F Z row p g
  rw [paid] at known
  have installed:(if row=col then (1:ℝ) else 0)=
      ∑r∈range ((F.grades row).2+1),∑e∈(range (p+1)).filter (fun e=>expn r e≤p),v r e*g^(expn r e):=by
    apply Eq.trans _ known
    by_cases yes:row=col <;> simp [yes,PowerSeries.coeff_one]
  have balance (r:ℕ): (∑e∈range (p+1),v r e*g^(expn r e))=
      (∑e∈(range (p+1)).filter (fun e=>expn r e≤p),v r e*g^(expn r e))+
      ∑e∈(range (p+1)).filter (fun e=>p<expn r e),v r e*g^(expn r e):=by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not (range (p+1))
      (fun e=>expn r e≤p) (fun e=>v r e*g^(expn r e))).symm
  have difference:rectangle F Z row p g-(if row=col then 1 else 0)=
      ∑r∈range ((F.grades row).2+1),∑e∈(range (p+1)).filter (fun e=>p<expn r e),v r e*g^(expn r e):=by
    change (∑r∈range ((F.grades row).2+1),∑e∈range (p+1),v r e*g^(expn r e)) - _=_
    rw [installed];simp_rw [balance];rw [Finset.sum_add_distrib];ring
  rw [difference]
  unfold tail
  simp_rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _=>?_ )
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e present=>?_ )
  have rank:p+1≤expn r e:=(Finset.mem_filter.mp present).2
  rw [abs_mul,abs_of_nonneg (pow_nonneg g0 _),mul_comm (g^(p+1))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one g0 small rank) (abs_nonneg _)

theorem seam (F:Frame G d)(n:Side)(B:ℕ)(Z:Pot G)(row:F.Index)(q:ℕ)
    {g ε:ℝ}(g0:0≤g)(small:g≤1)(rent:0≤ε)
    (measured:∀r≤(F.grades row).2,∀e≤q,|quote F B (sieve n (Z e r)) (axis F row)-pearlJ F (Z e r) row|≤ε):
    |finite F n B Z row q g-rectangle F Z row q g|≤((F.grades row).2+1:ℕ)*(q+1:ℕ)*ε:=by
  unfold finite rectangle
  simp_rw [←Finset.sum_sub_distrib,←sub_mul]
  calc
    _ ≤ ∑r∈range ((F.grades row).2+1),∑e∈range (q+1),ε:=by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr=>?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he=>?_)
      rw [abs_mul,abs_of_nonneg (pow_nonneg g0 _)]
      have price:=measured r (by simpa [Nat.lt_succ_iff] using hr) e (by simpa [Nat.lt_succ_iff] using he)
      exact (mul_le_mul price (pow_le_one₀ g0 small) (pow_nonneg g0 _) rent).trans (mul_one ε).le
    _ = _ := by simp [nsmul_eq_mul];ring

end YM.Integration.WilsonCapturedPrimaryPointRectangle
