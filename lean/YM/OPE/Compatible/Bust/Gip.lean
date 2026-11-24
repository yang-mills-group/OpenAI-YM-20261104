import YM.OPE.Compatible.Bust.Oct
/-!
# Wick and unwinding in seats. cap powers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra RG Work.F08 Matrix
open scoped Topology BigOperators Classical
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
variable {I K E F X:Type}{m r i j n k:ℕ}{C D:ℝ}{N c:Side}{v:Train r}{G:Gauge} {L:KernelChoices}
abbrev boostS (A:RowB I)(t:ℝ)(m k:ℕ): End ℝ (Seat k m I):= fixExp (lapD A m k).toLinearMap t k
lemma lockS (K:KernelChoices)(v:Train r)(h:4 ≤ r)(t:ℝ){p:Seat k (m+1) (Shade G)}(hp:p∈ bed G k (m+1)): boostS (atlasF G v h K) t (m+1) k p∈ bed G k (m+1):=by
     let X:= atlasF G v h K; have he(i:ℕ):( (lapD X (m+1) k).toLinearMap^i ) p∈ bed G k (m+1):=by induction i with | zero=>simpa| succ i ih=>rw [pow_succ',End.mul_apply]; exact scopeX v h ih
     rw [boostS, Hflow]; apply Submodule.sum_mem; exact fun i _=> (bed G k (m+1)).smul_mem _ (he i)
def rooft (I:Type)(k m n:ℕ) : Submodule ℝ (Seat k m I) where
     carrier := setOf fun x => ∀ i > n,lilies m k I x i=0
     zero_mem' :=by intro i h; rw [map_zero];rfl
     add_mem':= by intro a b (h:∀i > n,_) (hp:∀i > n,_) i hi; rw [map_add, Pi.add_apply,h _ hi,hp _ hi,add_zero]
     smul_mem':= by intro a b (h:∀i > n,_) i hi; rw [map_smul,Pi.smul_apply,h _ hi,smul_zero]
lemma lap_deb (A:RowB I)(p:ℝ)(k m:ℕ): reduces (rooft I k m) (p • (lapD A m k).toLinearMap):=by
     rintro i x (h:∀ j > i, _); have ht(j:ℕ)(hv:j+2>i): lilies m k I ((p •(lapD A m k).toLinearMap) x) j=0:= by rw [LinearMap.smul_apply,map_smul,Pi.smul_apply,ContinuousLinearMap.coe_coe,pulse_i,h (j+2) hv]; ext1 x; simp [pad,tunnel,Sack.rope]
     refine ⟨fun hk=>lilies_inj _ _ _ (funext fun j=> by rw [ht j (by omega),map_zero];rfl), fun j hj=>ht j (by omega)⟩
lemma switchingF (A:End ℝ (Seat k m I))(n:ℕ)(t:ℝ): fixExp A (-t) n= fixExp (-A) t n:=by
     unfold fixExp; apply Finset.sum_congr rfl; intro i _; symm
     cases i.even_or_odd with
     | inl h=> rw [h.neg_pow t, h.neg_pow A]
     | inr h=> rw [h.neg_pow t,h.neg_pow A,smul_neg, neg_div]; exact (neg_smul _ _).symm
lemma sustain (p:ℝ)(A:RowB I)(m k:ℕ)(x:Seat k m I): boostS A p m k (boostS A (-p) m k x)=x:=by
     have hp:x∈rooft I k m k:=(show ∀ i> k,lilies m k I x i=0 from (sproutV m k x).1)
     rw [boostS,boostS,switchingF]; exact negatives (by simpa only [one_smul] using lap_deb A 1 k m) x hp p k le_rfl
lemma bootPrice (I:Type)(m k:ℕ)(u:ℝ){A:ℝ} (ha:0≤A):∃ C:ℝ,0 ≤ C∧∀ p: RowB I,p.fare ≤ A→∀ x:Seat k m I,‖boostS p u m k x‖ ≤ C*‖x‖:=by
      let a:= wind k*A; have he:0≤a:=mul_nonneg (by unfold wind; positivity) ha; let c(i:ℕ):= ‖u^i/(i.factorial:ℝ)‖*a^i; refine ⟨∑ i∈range (k+1),c i,sum_nonneg (fun i _=>by unfold c; positivity),fun p hp x=>?_⟩
      rw [boostS,Hflow,sum_mul]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i hb; rw [norm_smul]; unfold c; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); have ht:‖lapD p m k‖≤a:=(lapE p).trans (mul_le_mul_of_nonneg_left hp (by unfold wind; positivity)); let f:= lapD p m k; induction i with
      | zero=>simp
      | succ i ih=> -- ih with hi
          rw [pow_succ',pow_succ',End.mul_apply, mul_assoc]; change ‖f _‖ ≤ _; exact (f.le_opNorm _).trans (mul_le_mul ht (ih (Finset.mem_range.mpr ((Nat.lt_add_one i).trans (Finset.mem_range.mp hb)))) (norm_nonneg _) he)
end YM.OPE.Silt.Float
