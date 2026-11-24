import YM.OPE.Compatible.Shore.Paint
/-!
# Marked evaluation of restore under superposition

Pay on the source column assigned after identifying orientations.
The corresponding linear pull can cost before the roots are sewn.
No cost paid by the charges of the witnessing *other* frames.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Deb
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem Mirror
open scoped Topology BigOperators Classical
variable {V I J W : Type}[Fintype V][DecidableEq V] [Fintype W][DecidableEq W]{G:Gauge}{n : Side} (f:V→W)(c:V→ℂ)
variable {p p' : Words V}{r:ℝ}{χ:Guard (Bud V)}{χ':Guard (Bud W)}
lemma deliver_borne {o:V→ Site n} {o':W→ Site n} {Y: Config G n→Marker.Poly (Bud V)}{s:Support n}
    (h:Borne o s Y r)(hp:o'∘ f=o): Borne o' s (sendAll f c ∘ Y) r:=by
    refine ⟨fun _ _ hi hk=> congr_arg (sendAll f c) (h.home _ _ hi hk),fun _ _=>congr_arg (sendAll f c) (h.turns ..), fun i=>?_,fun U i hi=>?_⟩
    · change Measurable (fun U:Config G n=>∑ j: Mode V,ite _ _ _); refine Finset.measurable_sum _ (fun j _=> ?_); split; next he=> exact measurable_const.mul (h.me _)
      next=> exact measurable_const
    change ∑ j: Mode V,ite _ _ _=0 -- parsing
    refine sum_eq_zero fun j _=> ?_; split
    next he=> refine mul_eq_zero.mpr (Or.inr (not_not.mp (fun hv=>hi (fun i' he'=> ?_))))
              obtain ⟨v,hV,rfl⟩:= mem_image.mp (he.2.symm ▸ he' : i'∈ (landed f j).val); rw [← hp] at h; exact h.place j U hv (mem_image_of_mem _ hV) -- method `scope`, hi? see Mirror.high
    rfl
lemma deliver_pad {o:V→Site n}{o':W→Site n}{F:Support n→ Config G n→Words V}{K:Box n→ Config G n→Words V} (h:Carton o F K r)(hp:o'∘f=o): Carton o' (fun i=> sendAll f c∘F i) (fun i=>sendAll f c∘K i) r:=by
   have hh {p:Words V}(he : Accent.rises p): Accent.rises (sendAll f c p):=by
      intro i hi; change ¬ (∑ j:Mode V,ite _ _ _)= (0:ℂ) at hi; obtain ⟨j,_,hj⟩:= exists_ne_zero_of_sum_ne_zero hi; split at hj; next h => obtain ⟨hx,rfl⟩:=h; exact (he j (fun H=> hj (by rw [H,mul_zero]))).trans_eq (card_image_of_injOn hx|>.symm)
      contradiction
   refine ⟨fun i=> ⟨⟨deliver_borne f c (h.exp i).1.toBorne hp, fun i' he=>(h.exp i).1.permits i' (fun H=>he ((congr_arg (sendAll f c) H).trans (map_zero (sendAll f c)))),fun i'=>?_⟩, fun x=>hh ((h.exp i).2 x)⟩,fun i=>⟨⟨deliver_borne f c (h.flag i).1.toBorne hp, fun x he=>(h.flag i).1.permits x (fun H=>he ((congr_arg (sendAll f c) H).trans (map_zero (sendAll f c))))⟩,fun x=>hh ((h.flag i).2 x)⟩⟩
   exact (deliver_zero ..).trans ((h.exp i).1.sil i')
variable {v:V→ℝ}{w:W→ℝ}
lemma deliver_tow {F:I→J→ Words V}{S:I→Support n}{n':ℕ}{t:ℝ}
    (h:Towed v S F n' t r) (ht:∀ i,0<w i)(hV:∀ i,w (f i)*‖c i‖≤ v i): Towed w S (fun i=>sendAll f c∘ F i) n' t r:=by
    obtain ⟨Q,hx,hg,hH⟩:=h; refine ⟨Q,hx,hg,fun i=>?_⟩
    obtain ⟨x,hx,hP,hr⟩:=hH i
    let a (k:Mode V):= ∏ j∈ k.val,c j; let p(j:Mode W)(k:Mode V):= Flat f k∧landed f k=j; let y(j:Mode W)(k:Mode V):= if p j k then ‖a k‖*x k else 0; let w' j:=∑ k,y j k
    have hs(j k):0 ≤ y j k:=by unfold y; split; exact mul_nonneg (norm_nonneg _) (hx _); rfl
    refine ⟨w', fun j=>sum_nonneg (fun k _=> hs j k), fun U j=> ?_, le_trans ?_ hr⟩
    · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _=> ?_); change ‖ite (p j k) (a k*_) 0‖ ≤ y j k; unfold y; split
      next hp=> rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hP U k) (norm_nonneg _)
      next=> rw [norm_zero]
    unfold wordsPrice w'; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; refine sum_le_sum fun j _=> ?_; rw [sum_eq_single (landed f j)]; swap
    · intro b _ he; rw [show y b j=0 from if_neg (fun H=> he H.2.symm),mul_zero]
    swap; · simp
    let t:= landed f j; have hz : 0 ≤ Poly.toll v j:= Finset.prod_nonneg (fun i _=> (mul_nonneg (ht _|>.le) (norm_nonneg _)).trans (hV i))
    change _ * (if _ then _ else _)≤ _; split
    next he=>
        rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (hx j); unfold Poly.toll landed a; rw [prod_image he.1,Complex.norm_prod,← prod_mul_distrib]; apply Finset.prod_le_prod; exact fun i _=> mul_nonneg (ht _|>.le) (norm_nonneg _); exact fun i _=> hV _
    next=> rw [mul_zero]; exact mul_nonneg hz (hx _)
-- root scopes by chosen flat patterns before applying line transport
lemma deliver_safe (h:χ.Saw p p')(hF:∀ i,Flat f i→χ'.safe (landed f i)→χ.safe i): χ'.Saw (sendAll f c p) (sendAll f c p'):=by
   intro i hi; refine sum_congr rfl fun j _=> ?_; change (if _ then (∏ v∈ j.val,c v)*_ else (0:ℂ))=ite _ _ _; split_ifs
   next ht=> rw [h j (hF j ht.1 (ht.2.symm ▸ hi))]
   rfl -- inspect
end YM.MergeProof.Ribbons.ManyCopies.Deb
