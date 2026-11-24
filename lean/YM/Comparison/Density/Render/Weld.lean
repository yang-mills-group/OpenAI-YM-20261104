import YM.Comparison.Density.Render.Stow

/-!
No omission even on flag emissions. Clover sum before charging extends
signed symmetry. Per-K cancellation invoked BEFORE model addition and
support-specific masks. This suffices for choosing canonical model with
every alpha (prefactor from order); retains ability to emit pairs in a
same-vacuum merged artifact with a named reimbursement. If input chose
fresh masks instead of keeping old, keep these payments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Render.Frame
open Fusing Markers RG Lattice Function Finset MeasureTheory Filter Wilson
open Ovens Extra.Iteration Push.AbsoluteSums Assembly Marker
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo Next.Scheduling Next.Scheduling.Wages Precision Work.F03 Work.G07 StressFlux
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff InnerProductSpace
open Transport AnalyticBridge.SectorAffine.Offset FreeResolvent.Affine FreeResolvent.TestD
variable {G : Gauge} {n : Side} {B : BudgetPoint} {P : Rep G n}
variable (F : ℕ→Atom G 2) (n : Side) (a : ℝ)

-- Equivalent formulation as imposing the clover-obstruction
-- vanishes on ALL Flux arguments (e.g. after applying signed
-- hypercubic average -- if only that is supplied, use (SignedCentral)
-- below, which is the same obstruction after averaging all seats).
-- Includes infinite-cover winding paths even in a finite application.
-- Never silently discard a wrap error in this nullity assertion.
def Central (F : ℕ → Atom G 2) := ∀ v, HasSum (fun i=> tag (F i) v) 0

def SignedCentral := ∀ w : Flux G, HasSum (fun i=> ∑ s:Signed, tag (F i) (reframe w s)) 0

variable (hf : ∀ i,(F i).Invariant) {B : BudgetPoint} {σ C : ℝ} (he : SumBudget (fun i=> (F i).budget σ) C) (hp : 0<σ)
    (hs : B.supportExponent / B.B ≤ σ/4) (hc : 2 ≤ B.B)
variable {n}
-- summable at true group, masks separate. pollen Mark ONLY on single stencil,
-- never at displaced root.
private lemma normle (A : Flux G) (i : PlaqAxes): ‖A i‖ ≤ ‖A‖ := norm_le_pi_norm A i

omit hf hp hs hc he in
lemma clovers (a : Atom G 2) (w : Flux G) : |tag a w| ≤ a.magnitude* ‖w‖^2:= by
  unfold tag Atom.poly Atom.magnitude; rw [sum_mul]; apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  refine sum_le_sum fun i _=> ?_; rw [abs_mul,abs_prod]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine le_trans (Finset.prod_le_prod (fun _ _=> abs_nonneg _) (fun j _=> show |(w (a.leg j).plaq) (i j)| ≤ ‖w‖ from ?_)) (by simp)
  let b:=(a.leg j).plaq; rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ (w b) (i j)]; simpa only [OrthonormalBasis.norm_eq_one,one_mul] using (abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ (i j)) (w b)).trans (by simp [normle w b])
include hp he
lemma proceeds (w : Flux G) : Summable fun i=> tag (F i) w := by
  have hq:= he.2.1.of_nonneg_of_le (g:=fun i=>(F i).magnitude) (fun i=> show 0 ≤ (F i).magnitude from Finset.sum_nonneg fun _ _=> abs_nonneg _) fun i=> (F i).lower_budget σ hp
  apply Summable.of_norm; exact (hq.mul_right (‖w‖^2)).of_nonneg_of_le (fun _=>norm_nonneg _) fun i=> clovers _ _
private lemma drip (B : BudgetPoint) (v : Seat n) (x) : Summable fun i=> pollenMark F B n a i ((Seat.view v) x):= by
  let V:= Seat.view v x
  unfold pollenMark recipe; simp only [full,if_true]; by_cases ht:Healthy B.threshold (halo 2 {(0:Site n)}) (v.view x)
  · simp only [masked_eq _ _ _ _  (show _ from ht),Pi.smul_apply]; exact (proceeds F he hp _).const_smul _
  simp_rw [masked_ne _ _ _ _  (show _ from ht)]; exact summable_zero
private lemma litmus (hz : SignedCentral F) (B : BudgetPoint) (x : Config G n) :
    HasSum (fun v:Cycle n=> pollenMark F B n a v.2 (v.1.view x)) 0:= by
  let v:= fun i:Cycle n=> pollenMark F B n a i.2 (i.1.view x)
  have hb:Summable v:= Summable.of_norm ((summable_prod_of_nonneg (fun i=>norm_nonneg _)).mpr ⟨fun i=>(drip F a he hp B i x).norm,Summable.of_finite⟩)
  apply hb.hasSum_iff.mpr
  rw [hb.tsum_prod,tsum_fintype, Fintype.sum_prod_type, sum_comm]; apply sum_eq_zero; intro t _
  let f(s:Signed):Seat n:= (s,t)
  have heH (s:Signed): Healthy B.threshold (halo 2 {(0:Site n)}) ((f s).view x) ↔ Healthy B.threshold (halo 2 {t}) x:= by
    rw [← Seat.healthy]; rw [show (f s).spread (halo 2 {(0:Site n)})= halo 2 {t} from ?_]
    simpa only [f,Seat.spread,affine,Signed.act_zero,zero_add] using! (Mirrors.neighborhood_signed 2 0 t s).symm
  change (∑ s,∑' i,v (f s,i))=0
  by_cases hH:Healthy B.threshold (halo 2 {t}) x
  · rw [← Summable.tsum_finsetSum (f:=fun s i=> v (f s,i)) (fun s _=> drip F a he hp B (f s) x)]
    have ht s i:v (f s,i)=(factor*a)*tag (F i) (reframe (petals x t) s) := by
      unfold v pollenMark recipe; rw [masked_eq _ _ _ _ ((heH s).2 hH)]; simp only [full,pollen,Seat.view,f,if_true,Pi.smul_apply,smul_eq_mul,petals_moves,affine,Signed.act_zero,zero_add]
    simp_rw [ht,← mul_sum,tsum_mul_left,(hz (petals x t)).tsum_eq,mul_zero]
  have hu s i : v (f s,i)=0:= masked_ne _ _ _ _ (mt (heH s).1 hH)
  simp_rw [hu,tsum_zero,sum_const_zero]

include hs hc hf

variable {P : Rep G n} {V : Type} [DecidableEq V] {R : Census V} {X : V→Type} [∀ v,NormedAddCommGroup (X v)] [∀ v,NormedSpace ℂ (X v)]
omit [∀ v,NormedAddCommGroup (X v)] [∀ v,NormedSpace ℂ (X v)] in
lemma pays (p : Activities G n) (hz : SignedCentral F) (U:Config G n):
    (∑' i,(Frame.pours F B a V R X).real.value i U)=((makeRose F n a full).coffee p).additive B U-((rack n F a full).coffee p).additive B U := by
  let Y:= makeRose F n a full; let Z:=rack n F a full
  have hu : ((Y.coffee p).EBound B _):= Frame.economics p (rose_era F n a full hf B) (in_time F n a hp hs hc full he)
  have hv:= main_price F a full p hf he hp hs
  have ht {T : Frame G n} {r : ℝ} (w : (T.coffee p).EBound B r): HasSum (fun i=> (T.coffee p).regularOccurrence B i U) ((T.coffee p).additive B U) := by
    let A:= T.coffee p; obtain ⟨b,hb,H⟩:= Activities.E_total w
    refine (show Summable (fun i=> (A.regularOccurrence B i U)) from ?_).hasSum
    apply Summable.of_norm; apply hb.of_nonneg_of_le (fun i=> norm_nonneg _) fun i=> ?_
    unfold Activities.regularOccurrence; by_cases hp : Healthy B.threshold (A.reg i).support U
    · rw [masked_eq _ _ _ _ hp]; exact (H i).2 U hp [] (by simp) (by simp)
    rw [masked_ne _ _ _ _ hp,norm_zero]; exact (H i).1
  have hp := ((numbering (Cycle n)).hasSum_iff).2 (litmus F a he hp hz B U)
  rw [show (makeRose F n a full)=Y from rfl, ← add_zero ((Y.coffee p).additive ..)]
  refine HasSum.tsum_eq (((ht hu).add hp|>.sub (ht hv)).congr_fun (fun i=> ?_))
  let N:= numbering (Cycle n) i; let s:=N.1
  change Frame.deficit F B n a _ (s.view U)= masked B.threshold (s.spread _) (Y.dataF _ ∘ s.view) U + _ - masked _ (s.spread _) (Z.dataF _ ∘ s.view) _
  rw [Seat.distribute,Seat.distribute]; rfl
omit [∀ v,NormedAddCommGroup (X v)] [∀ v,NormedSpace ℂ (X v)] in
lemma gratis (Q : Assembly R X G n) (T : Rep G n) (p : Activities G n) (h : SignedCentral F) (hcB : B=T.p) (hP:P.p=B)
    (hx : ∀ U,P.exponent U+((rack n F a full).coffee p).additive B U=T.exponent U+((makeRose F n a full).coffee p).additive B U):
    Conversion P Q T Q.exponent (Frame.pours F B a V R X):= by
  refine ⟨hP.trans hcB,fun U=> ?_,fun x U=> ?_⟩
  · rw [pays F a hf he hp hs hc p h]; linarith [hx U]
  unfold pours; dsimp only; rw [tsum_zero, add_zero]
end YM.Comparison.Density.Render.Frame
