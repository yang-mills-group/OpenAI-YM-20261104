import YM.OPE.Compatible.Bower.Picket
/-!
# Cost endorsements of particular crown packs. Prospective first capture field requires its own bill (not product over peers).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Wave
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave
open scoped Topology BigOperators Classical
variable {X V I G' W : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U Q F K:Finset X}{v:X} {m j:X→ℕ}
    [Fintype V][DecidableEq V][Fintype W][DecidableEq W]
    {G:Gauge}{C:Family G}{p n N b d k g H l:ℕ}{A:Allot C}
variable (S:Wave m F K n){P: Ensemble V} {E : Track C.path V p}{X' : X→Track C.path V p}
set_option quotPrecheck false
local notation "F'"=> riseUp W D S
local notation "V'"=> ↥(brim D F)⊕ W
local notation "V!"=> ↥(brim D K)⊕ W
-- proof cost arbitrary Lines endpoints
variable {u:brim D F ⊕ W→ℕ}{s v' : brim D K⊕ W→ℕ}{o:brim D F ⊕ W→Track C.path V p}{o':brim D K ⊕ W→Track C.path V p}
variable {M: Lights A P N p u (n+1) b E o}{T:Lights A P N p s n b E o'}
omit [Fintype V][DecidableEq V] in
lemma off_load {c:V'→ℝ} (x:brim D K) : ∏ i∈ (F').contents (.inl x),Sum.elim c 1 i = ∏ i∈(elements D S).contents x,c (.inl i):=by
    let t:(brim D F→(V'⊕starts D F K)):= Sum.inl ∘Sum.inl
    rw [← prod_subset (s₁:= Finset.image t ((elements D S).contents x)) (s₂:=(F').contents (.inl x)),prod_image (by intro i _ j _ h; exact Sum.inl.inj (Sum.inl.inj h))]; rfl
    swap -- inspect
    · rintro a ha hn; cases a
      next i=> cases i
               next i=> exact False.elim (hn (mem_image_of_mem t ((Fibers.focuses ..).2 (Sum.inl.inj (((F').focuses ..).1 ha)))))
               next i=> exact False.elim (Sum.inl_ne_inr (((F').focuses ..).1 ha|>.symm))
      rfl
    intro i hi; obtain ⟨a,ha,rfl⟩:= mem_image.mp hi; exact ((F').focuses ..).2 (congr_arg Sum.inl (((elements D S).focuses ..).1 ha))
-- raw numerical budget penalty. Encourage α as single payment threshold.
def event_fee (H:ℕ)(η : ℝ) : ℝ:= η^(H+1)
lemma return_ticket (h:Issues M l H F' T v')(hm:Bind C P E F' o o' n u s v')(hH:Fintype.card (V'⊕starts D F K) ≤ H)(hL:0 < H)(hp:C.ref 0 ≤ n)
    (x:brim D K) {η:ℝ}(he:0 < η)(ht:η≤ Lights.valve C H b l n)
    (hA:x.val∈F → η ≤ Run.Below C.path (sash C n/2) (v' (.inl x)) (s (.inl x))):
    event_fee H η * (∏ i∈ (elements D S).contents x,M.bottom (.inl i)) ≤ T.bottom (.inl x):=by
    let c:= Sum.elim M.bottom (1:(↑(starts D F K))→ℝ); let v:V!:= .inl x; let U':=(F').contents v
    have hv: η ≤ 1:= ht.trans (min_le_left ..); have hR(i):0<c i:=by cases i; exact M.bottom_pos _; exact zero_lt_one
    let P := ∏ i∈ U', η*c i; have hP : 0 ≤ P:= Finset.prod_nonneg (fun _ _=>mul_nonneg he.le (hR _|>.le))
    have hK : event_fee H η* (∏ i∈ (elements D S).contents x,M.bottom (.inl i)) ≤ η * P:=by
       rw [← off_load (W:=W) D S x,event_fee,Nat.add_comm H,pow_add,pow_one]; unfold P; rw [prod_mul_distrib,prod_const, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he.le hv (le_trans (Finset.card_le_univ _) hH)) he.le) (prod_pos (fun i _=> hR i)|>.le)
    refine le_trans hK (le_trans ?_ (bill M h hL hp hm M.bottom (fun i=>M.bottom_pos _) le_rfl v)); unfold tender; split
    next hh=>exact (mul_le_of_le_one_left hP hv).trans (prod_le_prod (fun i _=>(mul_pos he (hR i)).le) (fun i _=>mul_le_mul_of_nonneg_right ht (hR i|>.le)))
    next hh=>
       let z:= grouped C.path (renal C.path.levels) H l n (Sum.elim (fun i=>M.bottom i/(β C (n+1))^b) 1) F' v
       have hz : P ≤ z:=by
           let δ:=license C.path (renal C.path.levels) H l n; let p':=β C (n+1)^b; have hp:p'≥1:=one_le_pow₀ (β_one C _|>.le); have hq:η*p' ≤ δ:= (le_div_iff₀ (zero_lt_one.trans_le hp)).1 (ht.trans (min_le_right ..)); refine prod_le_prod (fun i _=> (mul_pos he (hR i)).le) (fun i _=> ?_); cases i
           next i heI=>
              change η*M.bottom i ≤ δ*(M.bottom i/p'); rw [← mul_div_assoc]; apply (le_div_iff₀ (zero_lt_one.trans_le hp)).2; rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right hq (M.bottom_pos _|>.le)
           next i=> exact mul_le_mul_of_nonneg_right ((le_mul_of_one_le_right he.le hp).trans hq) zero_le_one
       have he' : η ≤ Run.Below C.path (sash C n/2) (v' v) (s v):= hA (not_not.mp (fun h=> hh ((solos W D S x).mpr h)))
       refine (mul_le_mul he' hz hP (Run.below_fee _ (div_pos (sash_pos ..) zero_lt_two)|>.le)).trans_eq ?_; unfold Run.Below; unfold z; ring
lemma check_counter (h:Issues M l H F' T v') (z:W) (he:s (.inr z)=u (.inr z)) {η:ℝ}(ht:η ≤ valve C H b l n): η*M.bottom (.inr z) ≤ T.bottom (.inr z):=le_trans (mul_le_mul_of_nonneg_right ht (M.bottom_pos _|>.le)) (le_of_eq (bill_solo M h (pilots D S z) rfl he).symm)
end YM.OPE.Arboreal.Wave
