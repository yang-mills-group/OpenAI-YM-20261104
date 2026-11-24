import YM.RGComparison.Core16.Astage.Axle

/-!
# Payload for the measured() **spatial** estimate

Log-rate with gap > outcome horizon. At the far detectors, chosen by the ACTUAL Reader of
Exhibit, it suffices for the producer to bound the grouped moment residual. It needn't check
that the Gram approximate predicts some other Reader in some other scheme. We recover the actual
*exact* continuum OPE packet in the fixed horizon frame at that spatial precision (before WilsonX
report reindexing). Uses qru from the Quota port of Axle and no logarithmic tightening.
The geometric & phase occurrence scopes (power-small spatial claims only!) all from Services
on THIS calibration. Consumer for grouped/moment estimates. Adapters from group-root labs/sample
pairs still have to reach these residuals. Not replacing them with estimates after the large
measurement/frame/mass normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage.Panel
open Function Filter Real Metric Set MeasureTheory OPE Labels Table Orbits Axle
open Ward Extraction Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
section
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book}
    (T:Final C f S) (H:Services C f S) (R:Reader T.sector.derivatives T.sector.turns T.room.kernel.spin)
    {φ:Filter (ℕ×ℕ)}[φ.NeBot](hf:φ≤ f.fuse)
    {I J K:Type}[Fintype I][Fintype J]{ι:Type}{l:Filter ι}[l.NeBot]
    {m:ι→ℕ} (ht:Tendsto m l atTop)
    (u:ℕ) {d:I→ℕ} {e:J→ℕ}
    (A:ι→ Labels S d) (hA:∀ j, Crew φ (κ:=l) (m:=m) (fun i=>A i j))
    (w:Labels S e)
local notation "D"=> T.sector.derivatives
local notation "t"=> ruler C m
set_option quotPrecheck false
include R H hf ht hA
-- composition argument of Levy/Conversion/Evaluated on these actual frames with their own chart
omit [l.NeBot] in
set_option maxHeartbeats 780000 in
lemma moving (M:ι→∀ d:I→ℕ,MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ){b:ℝ}
     (hr:∀ (g:I→ℕ)(he:g≤d),∀ᶠ k in l,∀ v:(i:I)→S.Field (g i), M k g v=M k d (fun i=>(D).rise (he i) (v i)))
     (he:∀ (g:I→ℕ)(_:g≤d)(v:(i:I)→S.Field (g i)),RateLE l t (fun k=>M k g v) (weight g+b)): RateLE l t (fun i=>M i d (A i)) b:=by
    let J:= fun i=>Fin (d i+1); let P(i:ι)(j:I)(k:J j):S.Field (k.val):= R.cutTest k.val (d j) (A i j); let e' (j:(i:I)→J i):I→ℕ:=fun i=>(j i).val
    have hh:= large_s C ht
    have hEq (k): A k=fun i=>∑ j:J i,(D).rise (Nat.le_of_lt_succ j.isLt) (P k i j):=by
       funext i; exact ((D|>.arrival R.continuum.laws.toSymmetric R.lifts (A k i)).symm).trans (R.reconstruct (d i) (d i) (le_refl _) (A k i)).symm
    let F (j:(i:I)→J i)(k:ι):= M k (e' j) (fun i =>P k i (j i))
    have heq: ∀ᶠ i in l,(∀ j:(i:I)→J i, ∀ v:(i:I)→S.Field (e' j i), M i (e' j) v=M i d (fun s=>(D).rise (Nat.le_of_lt_succ (j s).isLt) (v s))) := eventually_all.mpr fun j=>hr (e' j) (fun i=> Nat.le_of_lt_succ (j i).isLt)
    apply (RateLE.sum (S:=Finset.univ) (f:=F) hh ?_).congr <| heq.mono (fun i h=>by
       nth_rw 1 [hEq i]; rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl (fun j _=> h j (fun k=>P i k (j k))))
    intro j _; refine (Orbits.contract (φ:=l) hh (fun k=> M k (e' j)) (he (e' j) (fun i=>Nat.le_of_lt_succ (j i).isLt)) (fun k i=>P k i (j i)) (fun i=> -((j i).val:ℝ)) (fun i=> crew_budget T _ hf R H ht _ (hA _) _ (Nat.le_of_lt_succ (j i).isLt))).mono ?_
    unfold weight e'; rw [Finset.sum_neg_distrib]; linarith

set_option maxHeartbeats 800000 in
lemma keeps_balance {x:ι→ I→ E4}{o:ι→ E4} (z:ι→Viewers T) {y:ι→J→ E4}
     (hx:enveloped l t 1 x o)(hk:Kept l t 1 x)
     (hb:Intervals l t 0 (sole ∘ o) y)(hy:Kept l t 0 y): RateLE l t
       (fun i=> Orbits.balance T (spectator T (z i)) R u (x i) (o i) (A i) (y i) w) (-(u+1:ℝ)):=by
    let M:ι→∀ e:I→ℕ,MultilinearMap ℂ (fun i=>S.Field (e i)) ℂ:= fun i _=>Levy.invoice T R (o i) w (z i) u (x i) (y i)
    have he:= clearance_both (large_s C ht) (o:=o) hx hk (y:=y) hb hy zero_lt_one le_rfl
    apply (moving (R:=R) T H hf ht _ hA M ?_ ?_).congr <| Eventually.of_forall fun i=> (Levy.invoice_paid ..).symm
    · -- ordering
      intro t' hq; filter_upwards [he.2] with k hh v
      unfold M; rw [← Levy.invoice_paid,← Levy.invoice_paid]; unfold balance whole
      let e0:=Sum.elim t' e; let e':=Sum.elim d e; let hz :e0 ≤ e':=fun i=> by cases i; apply hq; exact le_rfl
      refine congr_arg₂ HSub.hSub ?_ ?_
      · apply Eq.trans (Levy.inclusionMoment T e0 e' hz (stages v w) _ (z k) hh); apply DFunLike.congr_arg; funext i; cases i; rfl; rename_i i; exact ((D).arrival R.continuum.laws.toSymmetric R.lifts _)
      exact Finset.sum_congr rfl (fun i _=> congr_arg _ (R.fresh_inclusions ..).symm)
    intro _ ht' v
    have h':=balance_rate T R H (large_s C ht) v hx hk zero_lt_one z w hb hy le_rfl le_rfl u zero_lt_one
    rw [mul_zero,sub_zero,add_zero,mul_one,mul_one] at h'
    exact h'.congr (Eventually.of_forall fun i=>Levy.invoice_paid ..)
-- package actual moving profile operands.
def sampled {K:Type}[MeasurableSpace K](μ:Measure K)(w:K→ℂ)(X:K→I→E4)(o:E4)(P:Labels S d):=
    ∫ i,w i • R.packet u (X i) P o ∂μ

def sales {K:Type}[MeasurableSpace K](μ:Measure K)(w:K→ℂ)(X:K→I→E4)(T:Table C.book)(A:Labels S d)(v:J→E4)(z:Labels S e):= ∫ i, w i * Orbits.whole T (X i) A v z ∂μ

variable [MeasurableSpace K] [Nonempty K] {x:ι→K→I→E4}{o:ι→ E4}{α:ι→ K→ℂ}{y:ι→J→ E4}{μ:ι→ Measure K}
    (hx:∀ v:ι→ K, enveloped l t 1 (fun i=>x i (v i)) o ∧ Kept l t 1 (fun i=>x i (v i)))
    (hs: RateLE l t (fun i=>∫ j, ‖α i j‖ ∂μ i) 0)(ha:∀ᶠ i in l, Integrable (α i) (μ i))
    (hv:∀ᶠ i in l, Integrable (fun j=> α i j • R.packet u (x i j) (A i) (o i)) (μ i))
    (z:ι→Viewers T)
local notation "P!"=>fun i=> sampled T R u (μ i) (α i) (x i) (o i) (A i)
omit H hf ht hA
omit [Nonempty K] in
set_option maxHeartbeats 620000 in
lemma sampled_capture (A: Labels S d)(x:K→I→E4)(o:E4)(p:Viewers T) (y:J→E4)(μ:Measure K)(α:K→ℂ)
    (hi:Injective (beside (sole o) y))
    (h: Integrable (fun j=> α j * Orbits.whole (spectator T p) (x j) A y w) μ)
    (hs: Integrable (fun j=> α j • R.packet u (x j) A o) μ):
       sales μ α x (spectator T p) A y w - upon (spectator T p) u o y w (sampled T R u μ α x o A)=
          ∫ j, α j * Orbits.balance T (spectator T p) R u (x j) o A y w∂μ:=by
    let L':= LinearMap.toContinuousLinearMap (upon (spectator T p) u o y w); let f j:= L' (α j • R.packet u (x j) A o)
    have hu(k:K): α k* Orbits.balance T (spectator T p) R u (x k) o A y w= α k * Orbits.whole (spectator T p) (x k) A y w - f k:=by
       rw [Orbits.tested_fields,← packet_read T R (x k) o A y w p u hi,mul_sub]; exact congr_arg (α k * Orbits.whole (spectator T p) (x k) A y w - ·) (show α k * L' _ = f k from (map_smul L' (α k) _).symm)
    have hg: Integrable f μ:= L'.integrable_comp hs
    simp_rw [hu]; rw [integral_sub h hg]; exact congr_arg (sales μ α x (spectator T p) A y w - ·) (L'.integral_comp_comm (μ:=μ) hs).symm
omit R [l.NeBot] in
lemma tally_error (A:ι→K→ℂ)(p:ι→ℝ)(hA:∀ f:ι→K,RateLE l p (fun i=>A i (f i)) (-(u+1:ℝ)))
    (ha:RateLE l p (fun i=>∫ j, ‖α i j‖ ∂μ i) 0)(hh:∀ᶠ i in l, Integrable (α i) (μ i)):
       RateLE l p (fun i=>∫ j, α i j * A i j ∂μ i) (-(u+1:ℝ)):=by
    intro b h; obtain ⟨a,ha',hb⟩:=exists_between h; filter_upwards [hh, ha (b-a) (sub_pos.mpr hb),universalize (p:=fun i j=> ‖A i j‖ ≤ exp (a*p i)) (fun f=> hA f a ha')] with i ih ht hf
    calc _ ≤ ∫ j, ‖α i j‖ * exp (a*p i) ∂μ i:= norm_integral_le_of_norm_le ((ih.norm).mul_const _) (Eventually.of_forall fun j=> by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hf j) (norm_nonneg _))
         _ ≤ exp ((b-a)* p i)* exp (a*p i):= by rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans ht) (exp_nonneg _)
         _ = _:=by rw [←Real.exp_add]; ring_nf
end
set_option maxHeartbeats 440000 in
lemma true_balance {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book}
    (T:Final C f S) (H:Services C f S) (R:Reader T.sector.derivatives T.sector.turns T.room.kernel.spin)
    {φ:Filter (ℕ×ℕ)}[φ.NeBot](hf:φ≤ f.fuse)
    {I J K:Type}[Fintype I][Fintype J]{ι:Type}{l:Filter ι}[l.NeBot]
    {m:ι→ℕ} (ht:Tendsto m l atTop) (u:ℕ){d:I→ℕ}{e:J→ℕ}(A:ι→ Labels S d) (hA:∀ j, Axle.Crew φ (κ:=l) (m:=m) (fun i=>A i j))
    (w:Labels S e) [MeasurableSpace K][Nonempty K] {x:ι→K→I→E4}{o:ι→ E4} {p:ι→K→ℂ} {μ:ι→Measure K} {y:ι→J→E4}(z:ι→Viewers T)
    (hx:∀ v:ι→ K, enveloped l (ruler C m) 1 (fun i=>x i (v i)) o ∧ Kept l (ruler C m) 1 (fun i=>x i (v i)))
    (ha:∀ᶠ i in l, Integrable (p i) (μ i))(hs: RateLE l (ruler C m) (fun i=>∫ j, ‖p i j‖ ∂μ i) 0)
    (hv:∀ᶠ i in l, Integrable (fun j=> p i j • R.packet u (x i j) (A i) (o i)) (μ i))
    (hP: Intervals l (ruler C m) 0 (sole ∘ o) y)(hy:Kept l (ruler C m) 0 y)
    (hW:∀ᶠ i in l, Integrable (fun j=> p i j *Orbits.whole (spectator T (z i)) (x i j) (A i) (y i) w) (μ i)) :
       RateLE l (ruler C m) (fun i=> sales (μ i) (p i) (x i) (spectator T (z i)) (A i) (y i) w - upon (spectator T (z i)) u (o i) (y i) w (sampled T R u (μ i) (p i) (x i) (o i) (A i))) (-(u+1:ℝ)):=by
    let X i j:= Orbits.balance T (spectator T (z i)) R u (x i j) (o i) (A i) (y i) w
    have hξ (v:ι→K) : RateLE l (ruler C m) (fun i=> Orbits.balance T (spectator T (z i)) R u (x i (v i)) (o i) (A i) (y i) w) (-(u+1:ℝ)) := by
        have hh : enveloped l (ruler C m) 1 (fun i=> x i (v i)) o∧ Kept l (ruler C m) 1 (fun i=>x i (v i)):= hx v
        exact @keeps_balance G C f S T H R φ _ hf I J _ _ ι l _ m ht u d e A hA w (fun i=>x i (v i)) o z y hh.1 hh.2 hP hy
    have clearance:= (Kept.sole l (ruler C m) o 0|>.chorus hy hP|>.inject)
    refine (tally_error u X (ruler C m) hξ hs ha).congr ?_
    filter_upwards [hW,hv,clearance] with i hW hv hI; exact (sampled_capture T R u w (A i) (x i) (o i) (z i) (y i) (μ i) (p i) hI hW hv).symm

end YM.RGComparison.Core16.Astage.Panel
