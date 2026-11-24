import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Scales
import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Columns
/-! # Compact-cost compositions on `Guard` pricing, and all-row trial substitutions -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open XSpace XSpace.Normalize XSpace.Structure1 Matrix
open Scale ScaleCost O.Score O.Enh Comparing Dframe Reg.Point
open scoped Topology ContDiff BigOperators Classical Matrix
variable {G:Gauge} {I J E:Type*} [Norm E] {L:Filter I} {m n d:ℕ}
    {w w' t v T g : I → ℝ} (pay : t=O[L] g)
    (ht : ∀ᶠ i in L, |t i| ≤ 1) (hg : ∀ᶠ i in L, |g i| ≤ 1)
    (hT : ∀ᶠ i in L, 1≤T i)
    {P Q : I → Guard G d} {U V : I → FieldEnd G d}
-- for the step proofs all `FieldEnd` are single-cap; compatibility with Guide etc later
local notation "b" => (fun _ : I=> (1:ℝ))
def Notes (L:Filter I)(T t g:I→ℝ)(p:ℕ)(w:I→ℝ)(A:I→FieldEnd G d)(Z:I→Guard G d) : Prop := ∀ i j,
    Coin L T t g p w (fun k=> Comparing.columns (A k) i j) (fun k=>prose (Z k) i j)
def Uniform (T:I→ℝ)(L:Filter I)(w : I→ℝ)(Z:I→Guard G d):= ∀ i j, Tunes T L w (fun k=> prose (Z k) i j)
include pay ht hg hT
lemma Notes.product (hu:Notes L T t g m w U P) (hv:Notes L T t g m w' V Q) :
    Notes L T t g m (fun i=>w i*w' i) (fun i=>U i*V i) (fun i=>P i*Q i) := by
  intro i j; have e := Coin.sum hT (s:=Finset.univ) (fun a (_:a∈(Finset.univ:Finset (Toon G d)))=> Coin.mul pay ht hg hT (hu i a) (hv a j))
  simp_rw [prose_mix]; refine e.congr ?_ (EventuallyEq.refl ..) (EventuallyEq.refl ..)
  exact Eventually.of_forall fun k=> congr_arg (fun z:Matrix (Toon G d) (Toon G d) ℂ=>z i j) (Comparing.composition' (U k) (V k))
omit pay ht hg hT
lemma sum_coords (A:Guard G d)(p:ℕ)(t:ℝ) (i j: Toon G d) :
    columns (∑ k∈Finset.range (p+1), (t:ℂ)^k • coeff k A) i j = crop p t (prose A i j) := by
  unfold columns; simp_rw [LinearMap.sum_apply,map_sum,LinearMap.smul_apply,_root_.map_smul, crop_apply,prose,coeff_mk,smul_eq_mul]; rfl

def accepts (Z: Guard G d)(p:ℕ)(t:ℝ):FieldEnd G d:=∑ k∈Finset.range (p+1), (t:ℂ)^k • coeff k Z
lemma Notes.for_crop (h:Uniform T L w P) : Notes L T t g m w (fun i=>accepts (P i) m (t i)) P := by
  intro i j; simp_rw [accepts,sum_coords]; exact Coin.already (h i j)
lemma Notes.compact_constant (Z:Guard G d) : Uniform (G:=G) T L b (fun _=>Z) := fun _ _ _=> Fare.constant _

-- common horizon point assessment, all terms full multilinear
abbrev Eval (L : Filter I) (T t g : I→ℝ) (p:ℕ)(w:I→ℝ)(A:I→Structure1.Point G d n)(B:I→ℕ→Structure1.Point G d n) :=
    ∀ u : BasisSlots G (fun _:Fin n=>d), Coin L T t g p w (fun i=> A i (word u)) (fun i=> Reg.Point.story (B i) (word u))
lemma occupant (A:Guard G d)(P:ℕ→Structure1.Point G d n)(u:BasisSlots G (fun _:Fin n=>d)) :
    Reg.Point.story (status A P) (word u) = ∑ c:BasisSlots G (fun _:Fin n=>d),
      (∏ j,prose A (c j) (u j))*Reg.Point.story P (word c) := by
  ext1 k; simp_rw [map_sum,Constants.admits,Reg.Point.story, prose, coeff_mk,Comparing.columns,seen]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _=> word_sigma (pulseU j A (word u)) _

variable (X : I→Structure1.Point G d n) (Y : I→ℕ→Structure1.Point G d n)
include hT
lemma Uniform.product (hp: Uniform T L w P)(hq:Uniform T L w' Q):Uniform T L (fun i=>w i*w' i) (fun i=>P i*Q i) := by
  intro i j; simp_rw [prose_mix]; exact Tunes.sum hT _ _ (fun a _=> Tunes.mix hT (hp i a) (hq a j))
lemma Uniform.switched {u:I→PowerSeries ℂ} (ht:∀ i, MS.Book.Program.Rooted (u i)) (H: Tunes T L b u) (h:Uniform T L w P) : Uniform T L w (fun i=>stepV (u i) (P i)) := by
  intro i j; simp_rw [prose_subst _ _ (ht _)]; exact ScaleCost.submitted hT H (h i j) ht
include pay ht hg
lemma labels (h: Eval L T t g m w X Y)(hp: Notes L T t g m w' U P) :
    Eval L T t g m (fun i=> w' i^n*w i) (fun i=> (X i).compLinearMap (fun _=>U i)) (fun i=>status (P i) (Y i)) := by
  intro u; simp_rw [occupant,MultilinearMap.compLinearMap_apply,word_sigma (fun j=> U _ (word u j))]
  apply Coin.sum hT; intro c hc
  have H:= Coin.prod pay ht hg hT (s:=Finset.univ) (fun (_:Fin n)=> w') (fun j _=> hp (c j) (u j))
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,coordinates,word, columns,smul_eq_mul] using (Coin.mul pay ht hg hT H (h c))
lemma Eval.fixed (a:Tags G d n)(h:Eval L T t g m w X Y) : Coin L T t g m w
    (fun i=>X i a) (fun i=>Reg.Point.story (Y i) a) := by
  simp_rw [word_sigma a (X _)]; have H := Coin.sum hT (s:=Finset.univ) (fun j (_:j∈(Finset.univ:Finset (BasisSlots G (fun _:Fin n=>d))))=> Coin.mul pay ht hg hT (Coin.literal _ (Fare.constant (coordinates j a))) (h j) )
  refine H.congr (EventuallyEq.refl ..) (Eventually.of_forall fun i=>?_) (Eventually.of_forall fun i=>one_mul _)
  exact PowerSeries.ext fun k=> by simp_rw [map_sum, coeff_C_mul, Reg.Point.story, coeff_mk]; exact Eq.symm (word_sigma a _)
end YM.FVA2.GradedFar259.Quotes
