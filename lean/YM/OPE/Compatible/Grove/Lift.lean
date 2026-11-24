import YM.OPE.Compatible.Grove.Opine
/-! Evaluate rank reads before normalization. No vanishing in a particular camera used. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Work.G05 WardBin Tensor
open scoped Topology BigOperators Classical ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
variable [Fintype I]
def summitX (P: (r:ℕ)→Script W r)(x:I→fieldX W)(k:I→ℕ)(v:ℕ):ℝ:=∑ i∈ range (v+1), slopeX x k v i (P i)
variable {A:J→Chant G n}{y:J→ℝ}
lemma chorusX (h:saturate A y s U)(hx:∀ i,moderateX (A i) D)(hs:0<s)(hd:0≤D)(x:I→fieldX (Shade G))(k:I→ℕ)(p:∀ i,Quiet (x i) (k i))(v n':ℕ):
   HasSum (fun j=> y j * slopeX x k v n' (coff (A j) n')) (slopeX x k v n' (timbre A y n')):=by
      let g(q: Fin n'→I)(z: Script (Shade G) n'):= if (∑ i,(k (q i)+1))=v then wholeX z (x ∘ q) else 0; have ht (q: Fin n'→I): HasSum (fun i=> y i*g q (coff (A i) n')) (g q (timbre A y n')):=by
         unfold g; by_cases he:(∑ i,(k (q i)+1))=v; simp only [if_pos he]; exact everyone h hx hs hd _ _ (fun i=>p (q i))
         simp [he,hasSum_zero]
      unfold slopeX -- maybe instead mul_sum
      convert! hasSum_sum (s:=univ) (f:=fun q i=> y i*g q (coff (A i) n')) (a:=fun q=> g q (timbre A y n')) (fun q _=>ht q) using 1; ext i; simp only [mul_sum,g]
lemma accompaniment (h:saturate A y s U)(hx:∀ i,moderateX (A i) D)(hs:0<s)(hd:0≤ D)(x:I→fieldX (Shade G))(k:I→ℕ)(p:∀ i,Quiet (x i) (k i))(v:ℕ): HasSum (fun i=> y i * leading v (fun t:ℝ=>verseX (A i) (lotU (spout x k t)))) (summitX (timbre A y) x k v):=by
     simp_rw [pulses]; let f(j:ℕ)(i:J):= y i*slopeX x k v j (coff (A i) j); have hs := hasSum_sum (s:=range (v+1)) (fun j _=> show HasSum (f j) _ from chorusX h hx hs hd x k p v j)
     convert! hs using 1; ext i; simp [f,mul_sum]
lemma keyAdd (X Y : (r:ℕ)→Script W r)(x:I→fieldX W)(k:I→ℕ)(v:ℕ)(h:∀ i,Quiet (x i) (k i)) (ha:∀ i m, ∃ b, soot m (X i) b)(hb:∀ i m,∃ b,soot m (Y i) b): summitX (X+Y) x k v=summitX X x k v+summitX Y x k v:=by
   unfold summitX slopeX; rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; rw [← sum_add_distrib]; apply sum_congr rfl; intro p _; by_cases hp:(∑ j,(k (p j)+1))=v; swap; · rw [if_neg hp, if_neg hp,if_neg hp, add_zero]
   rw [if_pos hp,if_pos hp,if_pos hp]; exact manyX (ha i (∑ j,k (p j))).choose_spec (hb ..).choose_spec (fun j:Fin i=>h (p j)) le_rfl
lemma keyScale (X:(r:ℕ)→Script W r)(x:I→fieldX W)(k:I→ℕ)(v:ℕ)(t:ℝ): summitX (t • X) x k v=t*summitX X x k v:=by
    unfold summitX slopeX; simp_rw [mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro p _; split
    next h=>exact scaleX (X i) _ _ --
    next h=> simp
end Script
end YM.OPE.Flume
