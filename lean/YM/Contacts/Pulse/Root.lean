import YM.Push.ABSOLUTE_SUMS.Array
/-! # Rooted cover calculus for arbitrary orders

A weight-space version of polymer row sums; positions can be infinite-volume, no
embedding of small period slots as fictitious distinct copies. Supports combined
coarse/fine and constraint calculations. Multiplicative pseudo-distance can carry
analytic or polynomial width. No loss on connected multiplication and loop closure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pulse
open Function Set Finset Filter RG Push.AbsoluteSums
open scoped Classical Topology BigOperators NNReal
variable {ι κ X Y Z α β : Type*} {E : Type*} [NormedAddCommGroup E]

structure Range (X : Type*) where
  fee : X→ X→ ℝ≥0
  one x y : 1 ≤ fee x y
  flat x : fee x x=1
  mirror x y : fee x y=fee y x
  fold x y z : fee x z≤ fee x y*fee y z
variable (l : Range X)
namespace Range
def cheap (X : Type*) : Range X := ⟨fun _ _=>1,fun _ _=>le_rfl,fun _=>rfl,fun _ _=>rfl,fun _ _ _=>by simp⟩
def pull (f : Y→X) : Range Y := ⟨fun i j=>l.fee (f i) (f j),fun _ _=> l.one _ _,fun _=> l.flat _,fun _ _=>l.mirror _ _,fun _ _ _=>l.fold _ _ _⟩
def height [Fintype ι] (x : ι→X) : ℝ≥0 := max 1 ((univ:Finset ι).sup fun i=>(univ:Finset ι).sup fun j=> l.fee (x i) (x j))
abbrev step (x y:X):ℝ:=(l.fee x y:ℝ)
abbrev bill [Fintype ι] (x : ι→X):ℝ := l.height x
section
variable [Fintype ι] [Fintype κ] (f : κ→ι)(g:Y→X){x y:X}(u:ι→ X)(i j:ι)
lemma one_fee : 1≤ l.step x y := by exact_mod_cast l.one x y
lemma triangle (a b c:X): l.step a c≤l.step a b*l.step b c := by exact_mod_cast l.fold a b c
lemma one_bill : 1≤ l.bill u := by exact_mod_cast (show 1≤l.height u from le_max_left ..)
lemma width : l.step (u i) (u j)≤l.bill u := NNReal.coe_le_coe.mpr ((Finset.le_sup_of_le (mem_univ i) (Finset.le_sup (f:=fun j=>l.fee (u i) (u j)) (mem_univ j))).trans (le_max_right ..))
lemma wide {C:ℝ} (h:1 ≤ C) (he : ∀ i j,l.step (u i) (u j) ≤ C):l.bill u ≤ C := by
  lift C to ℝ≥0 using (zero_le_one.trans h)
  have hc: (1:ℝ≥0) ≤ C:=by exact_mod_cast h
  exact NNReal.coe_le_coe.mpr (max_le hc (Finset.sup_le fun i _=> Finset.sup_le fun j _=> NNReal.coe_le_coe.mp (he i j)))
lemma restrict : l.bill (u ∘ f) ≤ l.bill u := l.wide _ (l.one_bill _) (fun i j=> l.width _ (f i) (f j))
lemma retrieve (h: Surjective f) : l.bill (u ∘ f)=l.bill u:= le_antisymm (l.restrict ..) (l.wide _ (l.one_bill _) fun i j=> by obtain ⟨a,rfl⟩:=h i; obtain ⟨b,rfl⟩:=h j; exact l.width (u∘f) a b)
end
end Range

/-- Restrict to tuples having argument a at slot i. -/
abbrev Locked (X:Type*) {ι:Type*} (i:ι)(a:X) := {x : ι→ X // x i=a}
/-- The row-sum header asks for nonnegative bound too (empty alphabet can be used). -/
structure Rooted [Fintype ι] (F : (ι→X)→E) (b:ℝ) : Prop where
  cash : 0 ≤ b
  row (i:ι)(a:X) : SumBudget (fun x:Locked X i a=> ‖F x.val‖*l.bill x.val) b
lemma budget_map {f:α→ℝ} {g:β→ℝ}{C:ℝ} (h:SumBudget g C)(φ:α→β)(hφ:Injective φ)(hp : ∀ a, f a=g (φ a)) : SumBudget f C := by
  rw [show f=fun i=>g (φ i) from funext hp]; exact budget_pull _ hφ h
lemma budget_comm {f:α×β→ℝ}{C:ℝ} (h:SumBudget (fun x:β×α=> f (x.2,x.1)) C) : SumBudget f C := budget_map h Prod.swap Prod.swap_injective (fun _=>rfl)
lemma budget_trim {f:α×β→ℝ}{C:ℝ} (h:SumBudget f C): SumBudget (fun x=>∑' i, f (x,i)) C:= by
  refine ⟨fun x=> tsum_nonneg fun i=>h.1 _, h.2.1.prod,?_⟩
  exact h.2.1.tsum_prod.symm.trans_le h.2.2
lemma budget_crop {f:α→ℝ}{p:α→Prop}{C:ℝ} (h:SumBudget f C) : SumBudget (fun x:Subtype p=> f ↑x) C:= budget_pull _ Subtype.coe_injective h
lemma budget_zero : SumBudget (fun _ : α => (0:ℝ)) 0 := ⟨fun _=> le_rfl,summable_zero,by simp⟩

lemma budget_join [CompleteSpace E]{f:α→β→E}{v:α→ℝ}{a:ℝ} (h:∀ i, 0≤ v i) (hf : SumBudget (fun p:α×β=> ‖f p.1 p.2‖*v p.1) a) : SumBudget (fun i=> ‖∑' j, f i j‖ * v i) a := by
  apply budget_mono (budget_trim hf) (fun i=> mul_nonneg (norm_nonneg _) (h i))
  intro i; by_cases hi : v i=0
  · simp [hi]
  change _ ≤ ∑' j, ‖f i j‖ * v i; rw [tsum_mul_right]; refine mul_le_mul_of_nonneg_right ?_ (h _); apply norm_tsum_le_tsum_norm
  exact (summable_mul_right_iff hi).1 (show Summable (fun j=> ‖f i j‖ * v i) from hf.2.1.prod_factor i)

lemma budget_collect {f:ι→(α→E)}{s:Finset ι}{v:α→ℝ}{a:ι→ℝ} (h:∀ i,0≤v i)(hf:∀ i∈s, SumBudget (fun j=> ‖f i j‖*v j) (a i)) : SumBudget (fun j=> ‖∑ i∈s, f i j‖*v j) (∑ i∈s,a i):= by
  apply budget_mono (budget_over s (fun i j=> ‖f i j‖*v j) _ hf) (fun i=>mul_nonneg (norm_nonneg _) (h _))
  intro i; rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (norm_sum_le ..) (h i)

namespace Rooted
variable {l} [Fintype ι] [Fintype κ] {F G : (ι→X)→E}{b c:ℝ}
lemma weaken {k:Range X} (h: Rooted l F b) (hx:∀ i,l.bill i≥ k.bill (i:ι→X))(hc:b≤c) : Rooted k F c:= ⟨h.cash.trans hc,fun i x=> budget_loosen (budget_mono (h.row i x) (fun y=> by positivity) (fun y=> mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _))) hc⟩ -- NNReal auto
lemma compare (h : Rooted l F b) (he : ∀ x, ‖G x‖ ≤ ‖F x‖) : Rooted l G b := ⟨h.cash,fun i x=> budget_mono (h.row i x) (fun _=>by positivity) (fun q=> mul_le_mul_of_nonneg_right (he _) (by positivity))⟩
lemma tranquility (l : Range X): Rooted l (fun _ : ι→X=> (0:E)) 0 := ⟨le_rfl, fun i x=>by simpa using (budget_zero (α:=Locked X i x))⟩
lemma add (h:Rooted l F b)(k:Rooted l G c): Rooted l (F+G) (b+c) := ⟨add_nonneg h.cash k.cash, fun i x=> budget_mono (budget_plus (h.row i x) (k.row i x)) (fun _=>by positivity) fun u=> by simp only [Pi.add_apply,← add_mul]; gcongr; exact norm_add_le ..⟩
lemma smul {𝕜:Type*}[NormedField 𝕜][NormedSpace 𝕜 E] (h:Rooted l F b)(a:𝕜): Rooted l (a • F) (‖a‖*b) := by
  refine ⟨mul_nonneg (norm_nonneg _) h.cash, fun i x=> ?_⟩; simpa only [Pi.smul_apply,norm_smul,mul_assoc] using budget_scale (norm_nonneg a) (h.row i x)
lemma neg (h:Rooted l F b) : Rooted l (-F) b := h.compare (fun _=> by simp)
lemma sub (h:Rooted l F b)(k:Rooted l G c) : Rooted l (F-G) (b+c) := sub_eq_add_neg F G ▸ h.add k.neg
lemma bound (h:Rooted l F b)(x:ι→X)(i:ι): ‖F x‖ ≤ b := (le_mul_of_one_le_right (norm_nonneg _) (l.one_bill _)).trans (budget_single (h.row i (x i)) ⟨x,rfl⟩)
lemma raw (h:Rooted l F b)(i:ι)(a:X): SumBudget (fun x:Locked X i a=>‖F x.val‖) b:= budget_mono (h.row i a) (fun _=>norm_nonneg _) (fun _=>le_mul_of_one_le_right (norm_nonneg _) (l.one_bill _))
lemma rotate (h:Rooted l F b)(e:ι≃κ): Rooted l (fun x : κ→X=> F (x ∘ e)) b := by
  refine ⟨h.cash,fun i x=>?_⟩
  let f (p:Locked X i x): Locked X (e.symm i) x :=⟨p.val ∘ e,by simp [p.property]⟩
  refine budget_map (h.row (e.symm i) x) f (fun p q h=> Subtype.ext ?_) (fun p=> ?_)
  · exact funext (e.surjective.forall.mpr fun j=> congr_fun (congr_arg Subtype.val h) j)
  simp only [f,l.retrieve (f:=(e:ι→κ)) p.1 e.surjective]
end Rooted
end YM.Pulse
