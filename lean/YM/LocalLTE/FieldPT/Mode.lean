import YM.LocalLTE.FieldPT.Grain
/-!
 `Concert F` unmasked stencil Taylor **coefficients** on Arts. Order=
 s prefactor + field rank. Retain path and angular basis representation, not merely
 list of Log-H moments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset MeasureTheory
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n L : Side} {j z k m i:ℕ} {W κ K U C V t H u v ε: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
open Scene
variable {a:RegularAddress n}(X:Art a z)(p:BudgetPoint)(f:ℝ→Pot G n)(s:ℝ)
noncomputable def stub (κ:ℝ)(u:J k ×Fin m) := Weft.mark k u.1 s • Price.banner X f κ u.1 u.2
noncomputable def genre (a:J k ×Fin m):= a.1.val+a.2.val
-- region over finite $J$ (parameter purchases permit large $k$)
noncomputable def coverPT (κ:ℝ)(k m i:ℕ):= ∑ u∈ (univ:Finset (J k ×Fin m)).filter (fun u=> Price.genre u≤k+i), Price.stub X f s κ u
noncomputable def trunkPT {a:RegularAddress n}(o:Option (Σ z, Art a z)) (f:ℝ→Pot G n) (s κ:ℝ)(k m i:ℕ) :Config G n→ℝ:= match o with
   | Option.some X=> Price.coverPT X.2 f s κ k m i
   | Option.none => 0
private lemma regTotals {α:Type*}(s:Finset α) {X:Support n}{F:α→ Config G n→ℝ}(hp:∀ i∈s,p.Regular X (F i)):p.Regular X (∑ i∈s,F i):= by
   induction s using Finset.induction_on with
   | empty=> exact reg_const _
   | insert i s h ih=> rw [Finset.sum_insert h,← sub_neg_eq_add,← neg_one_smul ℝ]; exact reg_sub (hp i (mem_insert_self ..)) (AnalyticBridge.CouplingShape.reg_scale (-1) (ih (fun j hj=> hp j (mem_insert_of_mem hj))))
lemma supTotals {α:Type*}(s:Finset α) {X:Support n}{v:Site n} {g:α→ Config G n→ℝ} (w:α→ℝ)(h:∀ i∈s,p.Regular X (g i))(hp:∀ i∈s,p.supBounds v X (g i) (w i)): p.supBounds v X (∑ i∈s,g i) (∑ i∈s,w i):=by
   induction s using Finset.induction_on with
   | empty=> exact sup_le (sup_const 0) abs_zero.le
   | insert i s he ih=>
      rw [Finset.sum_insert he,Finset.sum_insert he,← sub_neg_eq_add (g i),← neg_one_smul ℝ]; have hh j (hj:j∈s):=h j (mem_insert_of_mem hj); refine sup_sub (h i (mem_insert_self ..)) (AnalyticBridge.CouplingShape.reg_scale (-1) (regTotals p s hh)) (hp i (mem_insert_self ..)) (?_); simpa only [abs_neg,abs_one,one_mul] using! AnalyticBridge.CouplingShape.sup_scale (-1) (ih hh (fun j hj=>hp j (mem_insert_of_mem hj)))
variable (hp:Reliable G κ K) {y:ℝ}
def glowing (k m i : ℕ) (y ε:ℝ):= (Fintype.card (J k × Fin m):ℝ)* y^( (-(1/2):ℝ)*(i+1:ℕ)+ε)
include hp
lemma cosign (H: PhotoJ X s y ε p f κ C k m)(h:∀ s∈Weft.clip,p.Regular a.support (f s)) (he:1≤ y)(hs:s∈Weft.clip)(i:ℕ) : p.Regular a.support (Price.coverPT X f s κ k m i) ∧ p.supBounds a.site a.support (f s - Price.coverPT X f s κ k m i) (C* glowing k m i y ε):=by
   let g:= Price.stub X f s κ (k:=k) (m:=m); let Y:= (univ:Finset (J k ×Fin m)); let S:= Y.filter fun i'=> Price.genre i'≤k+i; let q:= y^( (-(1/2):ℝ)*(i+1:ℕ)+ε); have h₀:q>0:=Real.rpow_pos_of_pos (zero_lt_one.trans_le he) _
   have hX(u:J k ×Fin m):p.Regular a.support (g u):= AnalyticBridge.CouplingShape.reg_scale _ (Price.play_cost X p hp _)
   have hv:f s = ∑ i∈Y,g i := (Price.advance X p f hp h H.isScene hs).trans (by rw [show Y=univ from rfl,Fintype.sum_prod_type]; rfl)
   refine ⟨regTotals p _ (fun i _=> hX i),?_⟩
   have hK(i': J k ×Fin m)(hi:i'∈ Y\ S): p.supBounds a.site a.support (g i') (C*q):=by
      have hJ:k+i < i'.1.val+i'.2.val:= Nat.lt_of_not_ge (fun h'=> (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h'⟩))
      have hk : ((k:ℝ)-(i'.1.val:ℝ) -i'.2.val)/2+ε ≤ (-(1/2):ℝ)*(i+1:ℕ)+ε:= by
         have he: ↑((k+i)+1:ℕ) ≤ (↑(i'.1.val+i'.2.val:ℕ):ℝ):=by exact_mod_cast hJ
         push_cast at *; linarith only [he]
      exact sup_le (H.rebates i'.1 i'.2|>.2) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le he hk) H.isScene.price)
   have ht:= supTotals p _ _ (fun i _=>hX i) hK; rw [show f s - Price.coverPT X f s κ k m i=∑ i∈ Y \ S, g i from eq_sub_of_add_eq (Finset.sum_sdiff (s₁:=S) (f:=g) (Finset.subset_univ S) |>.trans hv.symm) |>.symm]; simp only [sum_const,nsmul_eq_mul] at ht; refine sup_le ht ((mul_le_mul_of_nonneg_right (show (↑(Y\ S).card:ℝ) ≤ Fintype.card (Weft.J k × Fin m) from Nat.cast_le.mpr (Finset.card_le_univ _)) (mul_nonneg H.isScene.price h₀.le)).trans_eq (?_)); unfold glowing q; ring -- edit
lemma congrat (h:Scene X.grove κ X.radius k m f C)(s:ℝ) (hg:∀ z∈Weft.clip,Comic G a p (f z)) (hG:G.Simple)(i:ℕ): Comic G a p (Price.coverPT X f s κ k m i) := Comic.totals _ (fun A _=> (Price.filmPlot X p f hp h hg hG A.1 A.2).weight _)
variable {u:Type}
lemma delivers {o:Option (Σ z, Art a z)} (h:DNA a o p z m k κ C f) (hv:∀ (i:ℕ)(V':Art a i),o=.some ⟨i,V'⟩→ PhotoJ V' s y ε p f κ C k m) (he:1 ≤ y)(hs:s∈Weft.clip)(i:ℕ): p.Regular a.support (Price.trunkPT o f s κ k m i)∧ p.supBounds a.site a.support (f s - Price.trunkPT o f s κ k m i) (C*glowing k m i y ε) :=by
    cases o
    · rw [trunkPT,h.blank rfl s hs,sub_zero]; unfold glowing; refine ⟨reg_const _,sup_le (sup_const 0) ?_⟩; rw [abs_zero]; exact mul_nonneg h.sure (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_le_one.trans he) _))
    next v=> rw [trunkPT]; exact cosign _ p f _ hp (hv v.1 v.2 rfl) h.nucleus he hs _
end YM.AnalyticBridge.VerifiedReset.Collection.Price
