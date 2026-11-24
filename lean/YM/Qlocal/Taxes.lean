import YM.Qlocal.Service
/-! Discrepancy factor kept on each of the **joint** attachments. In addition
 to the actual launch at provisional radii, we permit relative-product norm
calculation: at any multimarker load only recover up to that radius cost per
nonzero tag, or per disjoint set of Leaf tags. Already present when the price
of the contributing Leaf tag has its own envelope; can be extremely small.
Keep that same envelope in the weighted norm of the output; no attempt to
infer comparison of whole-density ratios by this device.

 This makes no assumption on the actual weights in the nilpotent
 calculation: the estimates hold for ANY family with stated costs on
 products, and this module supplies those costs. Nothing changed on the
 θ-history.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Emissions
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b d δ C A B θ:ℝ}
open Merge Switch UniformPays Publishing

abbrev Brand (Z:ι→Poly R) (u:R.Mode→ℝ) (C:ℝ) : Prop:= ∀ U:Finset ι, priceQ (zProd (Z:=Z) U) u ≤ C
structure Sign (q:ι→ R.Mode)(s:V→Support n)(e:ι→Support n):Prop where
  written i : (q i).val.Nonempty
  ink i : speech (q i) (e i) s
variable {q:ι→R.Mode}{e:ι→Support n} (B':ι→ℂ)
def receipt (q:ι→ R.Mode) (α:ι→ℂ) (i:ι):Poly R:=Poly.send (q i) (α i)
lemma Syntax.for_radii (h: Sign q s e) : Syntax (receipt q B') s e :=by
 refine ⟨fun i=> ?_,fun i v hv=>?_,fun i=>?_⟩
 · rw [receipt,Poly.part_send, if_neg (show R.quiet≠q i from fun he=> (h.written i).ne_empty (congr_arg Subtype.val he.symm))]
 · have he:v=q i:= Classical.byContradiction (fun he=> hv (by rw [receipt,Poly.part_send,if_neg he])); exact he.symm ▸ h.ink i
 by_contra hp; obtain ⟨z,hZ⟩:= merges_of_tagged_mul hp; obtain ⟨j,hj⟩:= h.written i; exact Finset.disjoint_left.mp hZ.1 hj hj
lemma singletonPrice (u:R.Mode→ℝ)(v:R.Mode)(b:ℂ): priceQ (Poly.send v b) u=u v* ‖b‖:=by
 unfold priceQ; rw [Finset.sum_eq_single v]; · simp
 · intro x _ h; simp [h]
 simp
variable {B'}
lemma postage (hC : ∀ T,∀ h:Fits q T,c (unionTag q T h)*(∏ i∈T,‖B' i‖) ≤ C) (he:0≤ C): Brand (receipt q B') c C:=by
 intro U; by_cases h:Fits q U;
 · unfold zProd receipt; rw [tagged_prod q U h,singletonPrice,norm_prod]; exact hC ..
 rw [show zProd (Z:=receipt q B') U=0 from Classical.byContradiction fun hp=>h (fits_of_tagged_prod q hp),priceQ]; simpa only [Poly.part_nil,norm_zero,mul_zero,sum_const_zero]

lemma unity (hw : ∀ i,0<w i) {Z:ι→Poly R} (h : ∀ i, Poly.price w (Z i) ≤ 1) : Brand Z (fun q=>Poly.toll w q) 1:= by
 intro U; exact (Poly.multiple hw ..).trans (Finset.prod_le_one (fun _ _=>Poly.nonnegative hw _) (fun i _=>h i))

-- tropical mode q already includes old costs. Allows min or exactly multiplicative.
structure Charge (q:ι→R.Mode)(C:R.Mode→ℝ):Prop where
 positive q' : 0 < C q'
 joint (U:Finset ι) (h:Fits q U) : ∏ i∈U,C (q i) ≤ C (unionTag q U h)
 quiet : C R.quiet=1
lemma owed (h:∀ i,0<w i) (q:ι→R.Mode) : Charge q (envelopeProduct w):= ⟨fun x=> Poly.worth h x, fun U hx=> by rw [show envelopeProduct w _= _ from (show envelopeProduct w (unionTag q U hx)= ∏ i∈U,envelopeProduct w (q i) from toll_union q U hx w)], Poly.quiet_toll ⟩

-- estimate at actual radii w (which may already charge enough per slot),
-- with at most y per contributing incoming mark variable at normalization.
lemma incurred {Y:ℝ} (h:∀ i,(q i).val.Nonempty)(hw:∀ i,0<w i)
    (H : Charge q c) (hq: ∀ i, Poly.toll w (q i)*‖B' i‖ ≤ c (q i)*Y) (hz:1≤ Y)
    (hp:∀ U:R.Mode,U.val.card≤ k) : Brand (receipt q B') (exchange (fun v=> (c v)⁻¹) w) (Y^k):=by
 let Z v:=c v; let V' v:= (Z v)⁻¹; have hZ : 0 < Y:= zero_lt_one.trans_le hz
 refine postage (fun U ht=>?_) (pow_pos hZ _).le; let α:= unionTag q U ht
 have hK: U.card ≤ k:= by
     have he:(∑ _∈U,1:ℕ)=(U.card):=by simp
     refine he ▸ (Nat.le_trans (sum_le_sum (f:=fun _=>1) (g:=fun i=>(q i).val.card) (fun i _=>card_pos.mpr (h i))) ?_)
     rw [← Finset.card_biUnion ht.1]; exact hp α
 let p i:= c (q i); have ho:0≤∏ i∈U,c (q i):= Finset.prod_nonneg fun i hi=> (H.positive _).le
 unfold exchange; rw [mul_right_comm, toll_union q _ ht, ← Finset.prod_mul_distrib];
 calc
   _ ≤ (∏ i∈U,c (q i)*Y)*(c α)⁻¹:=mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun i _=> mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (fun i _=> hq i)) (inv_nonneg.mpr (H.positive _).le)
   _ ≤ c α * Y^k * (c α)⁻¹ := by rw [Finset.prod_mul_distrib,Finset.prod_const]; apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (H.positive _).le); exact mul_le_mul (H.joint _ ht) (pow_le_pow_right₀ hz hK) (pow_pos hZ _|>.le) (H.positive _).le
   _ = _ := by field_simp [(H.positive α).ne']
end YM.Qlocal.Emissions
