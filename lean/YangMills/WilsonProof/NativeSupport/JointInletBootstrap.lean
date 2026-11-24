import YangMills.WilsonProof.NativeSupport.JointPrefixScale
/-! Multiply the linear tariffs on the actual schedule. The accumulated
loss is a power of its total block scale. The quadratic and newborn
expenses form an additive error on that same full inlet. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Finset Lattice Wilson RG RGComparison.Core16 PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}

theorem original_bootstrap {A:Levels G} {p:ℕ} (T:Slices A p) {t N:ℕ} (tN:t ≤ N)
    (ν:ℕ) {k r:ℝ} (k0:0 ≤ k) (r0:0 < r) (u:ℕ→ℝ) (positive:∀ j,0 ≤ u j) (start:u N=0)
    (bill:2*((N-t:ℕ):ℝ)*(scale (traversal T tN):ℝ)^ν*k*r ≤ 1)
    (step:∀ j,t ≤ j → j < N → u (j+1) ≤ r →
      u j ≤ ((A.S.block j).val:ℝ)^ν*u (j+1)+k*(u (j+1)^2+r^2)) :
    ∀ j (_tJ:t ≤ j) (jN:j ≤ N),u j ≤ 2*((N-j:ℕ):ℝ)*(scale (traversal T jN):ℝ)^ν*k*r^2  ∧  u j ≤ r := by
  intro j tj jn
  induction jn using Nat.decreasingInduction with
  | self => simp [start,r0.le]
  | of_succ j hj ih =>
    have next:=ih (tj.trans (Nat.le_succ j))
    have nonlinear : u (j+1)^2 ≤ r^2 := pow_le_pow_left₀ (positive _) next.2 _
    have front : scale (traversal T hj.le)=(A.S.block j).val*scale (traversal T hj) := by
      rw [traversal_push T hj,scale]
      rfl
    let D : ℝ := scale (traversal T hj.le)
    let d : ℝ := scale (traversal T hj)
    let L : ℝ := (A.S.block j).val
    have split : D^ν=L^ν*d^ν := by dsimp only [D,d,L];rw [front,Nat.cast_mul,mul_pow]
    have count : ((N-j:ℕ):ℝ)=((N-(j+1):ℕ):ℝ)+1 := by exact_mod_cast (by omega : N-j=N-(j+1)+1)
    have mass : 1 ≤ D^ν := by
      apply one_le_pow₀
      dsimp only [D]
      have v:=prefix_monotone T hj.le (le_rfl : N ≤ N)
      rw [traversal_self,scale] at v
      exact_mod_cast v
    have fixed : u j ≤ 2*((N-j:ℕ):ℝ)*D^ν*k*r^2 := by
      calc
        _  ≤  L^ν*u (j+1)+k*(u (j+1)^2+r^2) := step j tj hj next.2
        _  ≤  L^ν*(2*((N-(j+1):ℕ):ℝ)*d^ν*k*r^2)+k*(r^2+r^2) := by gcongr; exact next.1
        _  ≤  2*((N-j:ℕ):ℝ)*D^ν*k*r^2 := by
          rw [count]
          nlinarith only [congrArg (fun z:ℝ=>2*((N-(j+1):ℕ):ℝ)*z*k*r^2) split,
            mul_nonneg (sub_nonneg.mpr mass) (mul_nonneg k0 (sq_nonneg r))]
    refine ⟨fixed,fixed.trans ?_⟩
    have duration : ((N-j:ℕ):ℝ) ≤ ((N-t:ℕ):ℝ) := by exact_mod_cast Nat.sub_le_sub_left tj N
    have scope : D ≤ (scale (traversal T tN):ℝ) := by
      dsimp only [D]
      exact_mod_cast prefix_monotone T tj hj.le
    calc
      2*((N-j:ℕ):ℝ)*D^ν*k*r^2  ≤  2*((N-t:ℕ):ℝ)*(scale (traversal T tN):ℝ)^ν*k*r^2 := by gcongr
      _ = (2*((N-t:ℕ):ℝ)*(scale (traversal T tN):ℝ)^ν*k*r)*r := by ring
      _  ≤  r := mul_le_of_le_one_left r0.le bill

end YM.Integration.InletSusceptibility.Packet
