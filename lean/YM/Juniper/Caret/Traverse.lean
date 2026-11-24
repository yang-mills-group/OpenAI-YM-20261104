import YM.Juniper.Caret.Projection
/-!
 # Caret traversal price

 No free projection. Constants may depend on field system at d but inequality
 uniform PERIOD from actual world, `X` any representation with that vacuum
 (not just selected Voice), all derivative costs through full indicated H.
 Formula explicit! physical period tails in later file. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Caret
open Function Filter Lattice MeasureTheory Wilson RG Input
open PhysicalNext.Repeat Lantern Next.Foundations
open ConnectedActivityE6 Blaze Brush Analysis Work.G05
open Measure Metric Set Labels Extra.Histories Source
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n d : ℕ}

section sums
variable {n : Side} (B:BudgetPoint)(o:Site n)(H : Hol G) {S:ℕ→Support n} (f:ℕ→ Config G n→ℂ) {b:ℕ→ℝ}
  (hd:d ≤ B.order) (hp:∀ i,B.Regular (S i) (f i)) (hs: Summable b)(he:∀ i, B.supBounds o (S i) (f i) (b i))
private lemma event {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y]{A:ℝ→Y}(h: ContDiffAt ℝ d A 0) : ∃ K:ℝ, ∀ᶠ x in 𝓝 0,Brush d K 1 A x:= by
   let f(i:ℕ):= normJ i A 0+1
   have hp(i:Fin (d+1)) : ∀ᶠ x in 𝓝 0, normJ i A x ≤ f i:= (h.continuousAt_iteratedFDeriv (Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt))).norm.tendsto.eventually_le_const (lt_add_one _) -- lemma syntax?
   refine ⟨∑ i∈ Finset.range (d+1),f i,?_⟩
   filter_upwards [eventually_all.mpr hp,h.eventually (by simp)] with x he h
   exact Brush.offer.2 ⟨h,fun i hi=> (he ⟨i,Nat.lt_succ_of_le hi⟩).trans (Finset.single_le_sum (f:=f) (s:=Finset.range (d+1)) (fun i _=> add_nonneg (norm_nonneg _) zero_le_one) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))⟩
include hd hp he hs
-- don't give width-free bounds from hK; it's for summability only
lemma journey (J: Jet G) : let p:= H.testLinks d o J; let y(i:ℕ):= f i ∘ p; let F:= fun x=> ∑' i,y i x
    ContDiffAt ℝ d F 0∧ ∀ i≤d, HasSum (fun k=>iteratedDeriv i (y k) 0) (iteratedDeriv i F 0):= by
  intro p y F
  let L:=testLog H d o J; have hz:L 0=0:= testLog_zero ..; have hd':ContDiffAt ℝ d L 0:= (testLog_diff H d o J).of_le le_top
  obtain ⟨W,hW⟩:= event hd'; obtain ⟨C,hC⟩:= complete B f o hd hp he; let s (i:ℕ):=clump d W (C*b i)
  have hL := (show Tendsto L (𝓝 0) (𝓝 0) from (by simpa only [hz] using hd'.continuousAt.tendsto)).eventually hC
  have hP: ∀ᶠ x in 𝓝 0,p x=(increment (1:Config G n) ∘ L) x:=increment_testLog H d o J
  have hK:∀ᶠ x in 𝓝 0,∀ i, Brush d (s i) 1 (y i) x:= by
     filter_upwards [hL,hW,eventually_eventually_nhds.mpr hP] with x hL hW hQ i; exact (composite hW (hL i)).shimmy (show f i ∘ p =ᶠ[𝓝 x] (f i ∘ increment (1:Config G n)) ∘ L from hQ.mono fun v hv=> congr_arg (f i) hv)
  obtain ⟨hk,hK⟩:= german hK (show Summable s from by unfold s clump; exact ((hs.mul_left C).mul_left _).mul_right _)
  exact ⟨hk,fun i hi=> (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i=>ℝ) ℂ (fun _=>1)).hasSum (hK i hi)⟩ -- defin eq
end sums

def reach (P: BudgetPoint)(n:Side):ℝ:= ((n.val:ℝ)/10-2*P.B)/(4*(P.B:ℝ)+2)
def traversal (P:BudgetPoint)(n: Side): ℝ:= Real.exp (-(P.supportExponent*reach P n))
private lemma earns {N: Side}(X:Support N)(o:Site N)(hp:o∈X)(h:¬Nonwrapping X o) (t:ℝ)(ht:0≤t)(P:BudgetPoint): t ≤ traversal P N * P.mass X t:=by
   unfold Nonwrapping at h; push Not at h; obtain ⟨i,hi,he⟩:=h
   have hv:= Corona.extent X P.B hi hp; have hz: reach P N≤ coverNumber P.B X:=by
      unfold reach; rw [div_le_iff₀ (show 0<4*(P.B:ℝ)+2 by positivity)]; have h: (N.val:ℝ) ≤ 10*((coverNumber P.B X:ℝ)*(4*(P.B:ℝ)+2)+2*(P.B:ℝ)):= (by exact_mod_cast le_trans he (Nat.mul_le_mul_left 10 hv)); linarith only [h]
   have hp:1 ≤ Real.exp (-(P.supportExponent*reach P N)+P.supportExponent*(coverNumber P.B X)):= Real.one_le_exp (by linarith only [ mul_le_mul_of_nonneg_left hz P.exponent_pos.le])
   unfold traversal BudgetPoint.mass; rw [← mul_assoc, ← Real.exp_add]; exact le_mul_of_one_le_left ht hp

variable (F:Labels.Frame G d) (B: SectionData F) (H: Hol G) (h:B.Sound H)
include h
lemma quote : ∃ K:ℝ,0<K∧ ∀ (n:Side) (o:Site n) (R:Rep G n) (P:Coefficient F n) (v u:ℝ),
     P.Format o H R→ P.remBound o R v u → Sits F B n→ d≤R.p.order → d ≤ R.p.power→
     F.coeffSize (naturalK F o H R (P.density o B R)-P.x) ≤ K * traversal R.p n * u := by
   obtain ⟨Z,C,hC,hU⟩:= Push.Local.probe_budget F
   choose f hK hM using fun i: Push.Local.Probe G d=> test_bound H i.1 d i.2.val (Nat.le_of_lt_succ i.2.isLt)
   let X:=1+∑ i∈Z,f i; have ht:0<X:=add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _=> hK i))
   refine ⟨C*X,mul_pos (zero_lt_one.trans_le hC) ht,fun n o R P v u hp hu hr hf hg=>?_⟩
   let θ:= R.p.threshold; let A:= P.density o B R; let η:= traversal R.p n; let Φ:= R.p; let z:= naturalK F o H R A
   have he := bills F o B H R P hr hp hu hf h -- order
   have hB:0≤u:= rem_nonneg hu; have hR:0≤η:= (Real.exp_pos _).le
   refine le_trans (b:= C*(X*η*u)) (hU (z-P.x) _ (by positivity) (fun i hi=>?_)) (le_of_eq (by unfold η; ring))
   let j:= i.2.val; have hj:j ≤ d:=Nat.le_of_lt_succ i.2.isLt; let f':= B.places (F.scaled θ⁻¹ P.x) o; let p:= H.testLinks d o (θ • i.1); let q:=f' ∘ p; let g k:= P.regular k ∘ p
   let K(x : ℝ):=∑' i,g i x
   have hV : JetTest H o (F.coords.symm (F.scaled θ⁻¹ P.x)) f':=by
     have hT:= placed_reads (H:=H) B o hr h (F.scaled θ⁻¹ P.x); rwa [Reads,if_pos (nonwrapping_placement B o hr)] at hT
   obtain ⟨a,b,-,hb,hz,-,⟨qA,hkA,hA⟩,-⟩:=hu
   have hu:Summable qA:= Summable.of_nonneg_of_le (fun i=> (hA i).1) (fun i=> Φ.loMass _ _ (hA i).1) hkA.2.1
   obtain ⟨hW,h⟩:= journey Φ o H P.regular hf hp.smooth hu hA (θ • i.1);
   have hv:iteratedDeriv j K 0 = Push.Local.runProbe F i (z-P.x):=by
      rw [map_sub, (he.listens i).2]; have hv:= appears F o H R i hV; rw [F.coords.apply_symm_apply,F.scaled_inv (show θ≠0 from R.p.threshold_pos.ne')] at hv; rw [hv]
      have h' : ratio R A ∘ p=ᶠ[𝓝 0] q+K:=(near_test o H R _).mono fun t ht=> unveil F o B H R P _ ht ‹_›
      rw [h'.iteratedDeriv_eq]; change iteratedDeriv j K 0=iteratedDeriv j (q+K) 0-iteratedDeriv j q 0; rw [iteratedDeriv_add (show ContDiffAt ℝ (↑j) q 0 from (hV (θ • i.1)).1.of_le (Nat.cast_le.mpr hj)) (show ContDiffAt ℝ (↑j) K 0 from hW.of_le (Nat.cast_le.mpr hj)), add_sub_cancel_left]
   have hx:∀ k, ‖iteratedDeriv j (g k) 0‖ ≤ X*η * Φ.mass (P.support k) (qA k):=by
      intro k; by_cases hy:Nonwrapping (P.support k) o
      · rw [show iteratedDeriv j (g k) 0=0 from (hp.projects k hy (θ • i.1)).2 j hj, norm_zero]; exact mul_nonneg (mul_nonneg ht.le hR) (hkA.1 k)
      have hp' : f i≤X:= le_trans (Finset.single_le_sum (s:=Z) (fun i _=>hK i) hi) (le_add_of_nonneg_left zero_le_one)
      rw [mul_assoc]; exact le_trans (hM i _ _ _ _ _ _ hf hg (hp.smooth k) (hA k)) (mul_le_mul hp' (earns (P.support k) o (hp.origin k) hy _ (hA k).1 Φ) (hA k|>.1) ht.le)
   have hu := Summable.of_nonneg_of_le (fun i=> norm_nonneg _) hx (hkA.2.1.mul_left _)
   rw [← hv,← (show ∑' i, iteratedDeriv j (g i) 0 = _ from (h j hj).tsum_eq)]
   refine (norm_tsum_le_tsum_norm hu).trans ((hu.tsum_le_tsum hx (hkA.2.1.mul_left _)).trans ?_); rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left ((hkA.2.2).trans (by linarith only [hz,hb])) (mul_nonneg ht.le hR)
end YM.Juniper.Caret
