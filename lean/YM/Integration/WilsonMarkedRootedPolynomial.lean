import YM.FormalBulk08.Rift.Glory
import YM.FormalBulk08.Lava.Splash
import YM.AllOrder.Fire.PriceR

/-! A rooted absolute invoice on every homogeneous tensor controls the
entire original polynomial at every field, with no factor for the volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedRootedPolynomial
open Function Finset MvPolynomial AllOrder.Fire FormalBulk08 Lava Gorge Rift
open scoped Topology BigOperators Classical ENNReal

variable {V:Type} [Fintype V] {r:ℕ}

def leaf (v:chain V r) (x:V→ℝ):ℝ:=∏i:Fin r,x (v i)
def layer (T:Tile V r) (x:V→ℝ):ℝ:=∑v:chain V r,T v*leaf v x

theorem form (T:Tile V r) (x:V→ℝ) : eval x (facade r T)=layer T x:=by
  simp [facade_eq,cards,layer,leaf]

theorem monomial (v:chain V r) : Rank (V→ℝ) r (leaf v) := by
  induction r with
  | zero =>
    have rest : leaf v=fun _=>1 := by funext x;simp [leaf]
    rw [rest]; exact Rank.nil 0 1
  | succ r recur =>
    let L:(V→ℝ)→L[ℝ]ℝ:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:V=>ℝ) (v 0)
    have split:leaf v=(L:((V→ℝ)→ℝ))*leaf (fun a:Fin r=>v a.succ):=by
      funext x;exact Fin.prod_univ_succ _
    rw [split];exact Rank.dot L r (recur _)

theorem grade (T:Tile V r) : Rank (V→ℝ) r (layer T):=by
  have sum:layer T=∑v:chain V r,T v • leaf v:=by funext x;simp [layer,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [sum];exact Rank.sum fun v _=>(monomial v).scal (T v)

theorem unweighted {D:Reach V} {a:V} {σ b:ℝ} {T:Tile V r}
    (hs:0≤σ) (h:Knoxville D σ a T b) : ∑v:chain V r,‖T v‖≤b := by
  have billed: (∑v:chain V r, Real.exp (σ*wide D (Fin.cons a v))*‖T v‖)≤b:=by
    apply (ENNReal.ofReal_le_ofReal_iff h.1).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun v _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    have rows:=h.2
    rw [tsum_fintype] at rows
    simpa only [Gorge.shine,←ofReal_norm,←ENNReal.ofReal_mul (Real.exp_pos _).le] using rows
  apply le_trans (sum_le_sum (fun v _=>?_)) billed
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg hs (Nat.cast_nonneg _)))

theorem priced (T:Tile V r) (b:ℝ) (nn:0≤b) (paid:∑v:chain V r,‖T v‖≤b) :
    Prices r b (layer T) := by
  refine ⟨nn,grade T,fun z=>?_⟩
  have mul (v:chain V r):|leaf v z|≤(1+‖z‖)^r:=by
    unfold leaf;rw [Finset.abs_prod]
    calc ∏i:Fin r,|z (v i)| ≤ ∏_:Fin r,(1+‖z‖):=prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>
          (norm_le_pi_norm z (v i)).trans (le_add_of_nonneg_left zero_le_one))
         _ = _:=by simp
  unfold layer
  calc |∑v:chain V r,T v*leaf v z| ≤ ∑v:chain V r,|T v*leaf v z|:=abs_sum_le_sum_abs ..
       _ ≤ ∑v:chain V r,‖T v‖*(1+‖z‖)^r:=sum_le_sum fun v _=>by
         rw [abs_mul];exact mul_le_mul_of_nonneg_left (mul v) (abs_nonneg _)
       _ = (∑v:chain V r,‖T v‖)*(1+‖z‖)^r:=by rw [sum_mul]
       _ ≤ _:=mul_le_mul_of_nonneg_right paid (by positivity)

theorem levels (P:MvPolynomial V ℝ) (d:ℕ) (tail:∀r,d<r→marble r P=0) :
    (∑r∈range (d+1),facade r (marble r P))=P := by
  simp_rw [marble_grade]
  by_cases ok:P.totalDegree≤d
  · refine ((sum_subset (range_mono (Nat.succ_le_succ ok)) (fun i _ notin=>?_)).symm).trans (sum_homogeneousComponent P)
    exact homogeneousComponent_eq_zero i P (by simpa only [mem_range,Nat.lt_succ_iff,not_le] using notin)
  · refine (sum_subset (range_mono (by omega : d+1≤P.totalDegree+1)) (fun i _ notin=>?_)).trans (sum_homogeneousComponent P)
    exact (marble_eq_zero_iff i P).mp (tail i (by simpa only [mem_range,Nat.lt_succ_iff,not_le] using notin))

theorem total (P:MvPolynomial V ℝ) (d:ℕ) (tail:∀r,d<r→marble r P=0) (C:ℕ→ℝ)
    (bill:∀r≤d,Prices r (C r) (layer (marble r P))) :
    Prices d (∑r∈range (d+1),C r) (fun z=>eval z P) := by
  let A (r:ℕ):=(layer (marble r P))
  have full:(fun z=>eval z P)=∑r∈range (d+1),A r:=by
    funext z
    conv_lhs=> rw [← levels P d tail,map_sum]
    simp only [Finset.sum_apply,form,A]
  rw [full]
  refine ⟨sum_nonneg (fun r hr=>(bill r (by simpa using hr)).1),
    Rank.sum (fun r hr=>(bill r (by simpa using hr)).2.1.up (by simpa using hr)),fun z=>?_⟩
  rw [Finset.sum_apply,sum_mul]
  calc |∑r∈range (d+1),A r z| ≤ ∑r∈range (d+1),|A r z|:=abs_sum_le_sum_abs ..
       _ ≤ _:=sum_le_sum fun r hr=>by
         have le:r≤d:=by simpa using hr
         exact ((bill r le).2.2 z).trans (mul_le_mul_of_nonneg_left
           (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg z)) le) (bill r le).1)

end YM.Integration.WilsonMarkedRootedPolynomial
end
