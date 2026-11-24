import YM.OPE.Compatible.Village.Fork
/-!
# Pass the gain ratio; naive estimate without. All polynomial overhead hidden inside PaidWeight; no rate slack in s.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade Cov Cov.Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U: Finset X}
   {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(A:Allot C)
variable {φ:Filter I}{r m:I→ℝ}{s:I→X→ℝ}{p:X→ S.Tag}
variable {η M:ℝ}{x:I→X→E4}(hx:∀ᶠ i in φ,Ridge (s i) η M D U (away (x i) (x i ⊥)))
variable (Y:Burst D U φ r s)(hη:0<η)(hM:0 ≤ M)(hO:Lanes (F:=Λ) T.sector.derivatives)(H:Services C Λ S)
variable (a:Tones T)(d:X→ℕ)
abbrev padding (D:Origin X)(U:Finset X)(p:X→ S.Tag)(n:ℕ)(s:X→ℝ):= costed D U n (fun i=> (p i.val).1) s
local notation "W"=>fun i=> padding D U p a.fst (s i)
local notation "W'"=>fun v b i=>padding D (Arboreal.trim U v) (paint T v p b) a.fst (s i)
set_option quotPrecheck false
local notation "b!"=> Ward.expose ∘ p
variable {v:X}(hv:v∈ rest U)
include Y hv
lemma price_gap : ∀ᶠ i in φ,0 < rat D (s i) v ∧ rat D (s i) v ≤ 1 :=by
    let t:=Y.fresh 1 one_pos; have hw:v∈U:=(rest_mem ..).1 hv |>.2; have hg:=t.crowned.roots (par_le D v) hw; filter_upwards [t.dim,(t.fade v hw).eventually self_mem_nhdsWithin,(t.fade _ hg).eventually self_mem_nhdsWithin] with i hi hT hU; exact ⟨div_pos hT hU,(div_le_one hU).2 (hi _ hw _ (par_le ..))⟩
omit Y hv in
lemma levy {s:X→ℝ}{d k:ℕ}(p:X→ S.Tag) : leverage D U (fun i=> (p i.val).fst) v s d k = padding D U p k s * ((rat D s v)^d)⁻¹:=by unfold leverage rat padding costed; rw [← inv_pow,inv_div]; ring
lemma bill_turn (p:X→ S.Tag)(b:Tones T)(s:X→ℝ)(k:ℕ): tallInk D U (fun i=> (p i.val).1) v s b.fst k= padding D (Arboreal.trim U v) (paint T v p b) k s:=by
    -- eta labels
    have hx:=trimmed_units D (Ward.expose ∘ p) (s:=s) (Burst.crown D Y) hv (Ward.expose (title T b)); unfold tallInk padding costed; congr 1
    let f := fun i: brim D (Arboreal.trim U v)=> (pallet (Ward.expose ∘ p) (Ward.expose (title T b)) v i.val).1; refine Eq.trans hx.symm (congr_arg (fun F=> volume D (Arboreal.trim U v) F s) (show f = _ from ?_)); ext i; dsimp only [f]; by_cases h:i.val=v
    · rw [h,pallet,paint,update_self,update_self]; rfl
    rw [pallet,paint,update_of_ne h,update_of_ne h]; rfl
omit hv in
lemma pad_up (n:ℕ)(p:X→S.Tag): ∀ᶠ i in φ,0 < padding D U p n (s i):= cost_pos D Y (picked (brim D U) p) n
include A hx H hO hη hM
lemma send {m:I→ℝ}(hm:∀ᶠ i in φ, 0 ≤ m i) (b:Tones T) {f:I→ℂ} (hh:PaidWeight φ r (fun i=> W' v b i * m i) f) : PaidWeight φ r (fun i=> W i*m i) (fun i=> shoot D T U v b (s i) (x i) p * f i):=by
    let S i:= shortInk D U (fun i=> (p i.val).1) v (s i) b.fst; -- i shadow
    let S' i:= S i * (W' v b i*m i); have hp: PaidWeight φ r S' (fun i=> shoot D T U v b (s i) (x i) p * f i):= PaidWeight.accrue (glen_bill D T v p hv Y H hO A hη hM hx b) hh (Eventually.of_forall fun _=> rfl)
    refine hp.monoWeight (by filter_upwards [pad_up D Y a.fst p,hm] with i hi he using mul_nonneg hi.le he) ?_
    filter_upwards [pad_up D Y a.fst p, price_gap D Y hv,hm] with i hi hu hM
    have ht:S' i= (W i*((rat D (s i) v)^b.fst)⁻¹)*m i:=by rw [← levy]; have he:= reloaded D (U:=U) v b! b.fst a.fst (s i); change S i * (W' v b i*m i)= _; have hE:= bill_turn D T Y hv p b (s i) a.fst; rw [← mul_assoc]; exact congr_arg₂ _ ((congr_arg (S i * ·) hE.symm).trans he.symm) rfl
    rw [ht]; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hi.le ((one_le_inv₀ (pow_pos hu.1 _)).2 (pow_le_one₀ hu.1.le hu.2))) hM
omit hv
lemma mean (p:X→S.Tag): PaidWeight φ r (fun i=> padding D U p a.fst (s i)) (fun i=> nests D T d U a (s i) (x i) p):=by
    revert hx p Y; apply Finset.lt_wf.induction U
    intro P ih hx Y p
    by_cases he: (rest P).Nonempty
    · let v:=bud P he; let s':= shades (facets T) (d v); let G b i:= shoot D T P v b (s i) (x i) p*nests D T d (trim P v) a (s i) (x i) (paint T v p b)
      have hF:=remains _ (Burst.crown D Y) (bud_trunk P he); have he' :∀ b∈ s', PaidWeight φ r (fun i=> padding D P p a.fst (s i)) (G b):=by
         intro b _; have ht:= ih _ (lighter P (bud_live P he)) (hx.mono fun i hi=> Ridge.heals D (filter_subset ..) _ hi) (Burst.heal D Y (filter_subset ..) hF) (paint T v p b)
         have hh:=send D T A hx Y hη hM hO H a (bud_mem P he) (m:=fun _=>1) (Eventually.of_forall fun _=> zero_le_one) b (by simpa only [mul_one] using ht); simpa only [mul_one] using hh
      refine PaidWeight.alter (PaidWeight.summon _ _ (Burst.life D Y) ((pad_up D Y a.fst p).mono fun _ h=>h.le) he') ?_
      filter_upwards with i; rw [nests,dif_pos he]
    apply PaidWeight.alter (solid_beam T D A hO H Y hx hη hM (picked (brim D P) p) a)
    filter_upwards with i; rw [nests,dif_neg he]; rfl
end YM.OPE.Arboreal.Trace
