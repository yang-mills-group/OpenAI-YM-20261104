import YM.MS.Swirl.Plane

/-!
# FVA Wilson coefficients: a coordinate-change supplier for the *actual MS input API*

Change variables in the finite super Wick operation used in `Endμ`, including its
numerator, marks, and denominator. Only the *symmetric/antisymmetric list jets* are
used in the API (the Wick map has a formal extension to all lists). It is important
not to change variables silently on that extension: `Shot` uses an unspecified linear
splitting. We always qualify agreement by the **finite correlation rank** restriction
per row (which we check at uses below). The map on arrays is bilinear in the legs of K
(no complex conjugation, even though a Fourier transform need not be real).
-/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Modes

open MS MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book
open MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP
open MS.Puff.Actors MS.Puff.Mom MS.Cylinder Finset

variable {A B : Type} (m : B → A → ℂ) {p : Sector A} {q : Sector B}
  [Fintype A]

/-- Each `A` field is a linear combination of `B` fields with coefficients `m b a`.
Use full jets with parity from the MS coefficient API. -/
def plug : BL A →ₗ[ℂ] BL B := (shade m).comp region.symm.toLinearMap

@[simp] theorem plug_cyl (F : Cyl A ℂ) : plug m F.val = shade m F := by
  change shade m (region.symm (region F)) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem plug_nil (F : BL A) : plug m F [] = F [] := rfl

lemma plug_product (hp : Tie p q m) (F H : BL A) :
    plug m (product p F H) = product q (plug m F) (plug m H) := by
  let f : Cyl A ℂ := region.symm F
  let h : Cyl A ℂ := region.symm H
  change plug m (couple p f h).val = _
  rw [plug_cyl,hp.prod]
  rfl

lemma plug_D (F : BL A) (x : B) : D x (plug m F) = ∑ a : A,m x a • plug m (D a F) := by
  have h : Uses (↑(Finset.univ : Finset A) : Set A) (region.symm F).val := by
    rw [coe_univ]; exact Uses.entire _
  change _ = ∑ a : A,m x a • plug m (enter a (region.symm F)).val
  simp_rw [plug_cyl]
  exact shade_drop m x _ h

lemma plug_coin (c : ℂ) : plug m (coin c) = coin c := by
  change plug m (piece c).val = _
  rw [plug_cyl]; exact coin_turn m c

lemma plug_limit (h : ℤ) (F : BL A) (hf : Limit F h) : Limit (plug m F) h :=
  Limit.shades (region.symm F) hf m

lemma plug_mini (F : BL A) (h : F ∈ Mini A) : plug m F ∈ Mini B := by
  obtain ⟨n,hn⟩ := h
  exact minH (plug_limit m _ F hn)

lemma plug_symm (hp : Tie p q m) (F : BL A) (h : Symm p F) : Symm q (plug m F) :=
  hp.sym (region.symm F) h

lemma plug_pure (hp : Tie p q m) (F : BL A) (b : Bool) (h : Pure p b F) :
    Pure q b (plug m F) := hp.pure (region.symm F) h

section press
variable [Fintype B]

/-- Covariance in the A variables induced from that in B variables.
Both are `Grain`: i.e. store **half** the covariance. -/
def induceK (K : Grain B) : Grain A := fun a b =>
     ∑ i : B, ∑ j : B, K i j * (m i a * m j b)

omit [Fintype A] in
lemma induce_chill (K : Grain B) (a b : A) :
    Chill (induceK m K) a b = ∑ i : B,∑ j : B, Chill K i j * (m i a * m j b) := by
  simp_rw [Chill,induceK,Finset.mul_sum,mul_assoc]

omit [Fintype A] in
lemma induce_symm (h : Tie p q m) (K : Grain B) (hp : Cog.Sym q K) :
    Cog.Sym p (induceK m K) := by
  intro a b; simp_rw [induceK, Finset.mul_sum]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  by_cases hj : m j a = 0; simp [hj]
  by_cases hi : m i b = 0; simp [hi]
  rw [hp j i, h _ _ hj, h _ _ hi]; ring
omit [Fintype A] in
lemma induce_clear (h : Tie p q m) (K : Grain B) (hp : Clear q K) : Clear p (induceK m K) := by
  intro a b he
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  obtain ⟨j,_,hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  rw [h a i (left_ne_zero_of_mul (right_ne_zero_of_mul hj)),
      h b j (right_ne_zero_of_mul (right_ne_zero_of_mul hj)), hp i j (left_ne_zero_of_mul hj)]

private theorem shuffle4 {X : Type} [AddCommMonoid X]
    (f : B→B→A→A→X) :
    ∑ i : B,∑ j : B,∑ a : A,∑ b : A,f i j a b =
    ∑ a : A,∑ b : A,∑ i : B,∑ j : B,f i j a b := by
  classical
  rw [show (∑ i : B,∑ j : B,∑ a : A,∑ b : A,f i j a b) =
             ∑ i : B×B,∑ a : A×A,f i.1 i.2 a.1 a.2 by simp_rw [Fintype.sum_prod_type]]
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_prod_type]

lemma frame_plug (K : Grain B) (F : BL A) :
    Cog.frame K (plug m F) = plug m (Cog.frame (induceK m K) F) := by
  simp_rw [fpΩ, diffPair_apply, plug_D, map_sum, map_smul, Finset.smul_sum,
    induceK, Finset.sum_smul, smul_smul]
  simp_rw [plug_D, Finset.smul_sum, smul_smul, mul_assoc]
  exact shuffle4 (fun i j a b => (K i j*(m i a*m j b)) • plug m (D b (D a F)))

lemma tep_plug (K : Grain B) (n : ℕ) (F : BL A) :
    tep K n (plug m F) = plug m (tep (induceK m K) n F) := by
  induction n with
  | zero => simp only [rise]; rfl
  | succ n ih => rw [teen,teen,ih,frame_plug,map_smul]

lemma effect_plug (K : Grain B) (n : ℕ) (F : BL A) :
    effect K n (plug m F) = plug m (effect (induceK m K) n F) := by
  simp_rw [effect,LinearMap.sum_apply,map_sum,tep_plug]

theorem shot_plug (K : Grain B) {F : BL A} (h : F ∈ Mini A) :
    Shot K (plug m F) = plug m (Shot (induceK m K) F) := by
  obtain ⟨n,hn⟩ := h
  rw [dawn K (plug_limit m n F hn),dawn _ hn,effect_plug]

theorem view_plug (K : Grain B) {F : BL A} (h : F ∈ Mini A) :
    View K (plug m F) = View (induceK m K) F :=
  (congr_fun (shot_plug m K h) [])
end press

abbrev seriesPlug : SpecB A →ₗ[ℂ] SpecB B := pointL ℕ (plug m)

lemma keepsRanks (h : Tie p q m) {X : SpecB A} (hx : Γ X p) : Γ (seriesPlug m X) q := by
  intro i _
  obtain ⟨hp,hf⟩ := fee_spec (hx i (Set.mem_univ _))
  exact ⟨plug_symm m h _ hp,plug_mini m _ hf⟩

lemma plug_tether (h : Tie p q m) : Tether (plug m) (actor p) (actor q) :=
  ⟨ plug_coin m 1, plug_product m h ⟩

lemma seriesPlug_tether (h : Tie p q m) :
    Tether (seriesPlug m) (PermV p) (PermV q) := (plug_tether m h).Extrapolation useN

lemma seriesPlug_product (h : Tie p q m) (F H : SpecB A) :
    seriesPlug m ((PermV p).core F H) = (PermV q).core (seriesPlug m F) (seriesPlug m H) :=
  (seriesPlug_tether m h).craft F H

lemma seriesPlug_exp (h : Tie p q m) (Q : SpecB A) :
    seriesPlug m (exp0 p Q) = exp0 q (seriesPlug m Q) := by
  ext1 i
  exact (plug_tether m h).figure useN Q i

lemma seriesPlug_sources (h : Tie p q m) {W : Type} [LinearOrder W]
    (V : Mate A W) (s : Finset W) :
    seriesPlug m (Font p V s) = Font q (seriesPlug m ∘ V) s :=
  (seriesPlug_tether m h).figure (marked W) V s

variable [Fintype B]

lemma seriesPlug_view (K : Grain B) {F : SpecB A} (h : ∀ i : ℕ,F i ∈ Mini A) :
    ℶV K (seriesPlug m F) = ℶV (induceK m K) F := by
  ext1 i
  exact view_plug m K (h i)

/-- Rank-restricted at each degree, but all orders in g. Because the denominator is included,
the **same interaction jets plug** in both places. All degrees/horizons and markers can use the
same coordinate change at a regulator. No claim in this step about compatibility between meshes. -/
theorem plug_end (K : Grain B) (h : Tie p q m)
    {Q V : SpecB A} (hq : Γ Q p) (hv : Γ V p) (Z : T ℂ) :
    Endμ K q (seriesPlug m Q) (seriesPlug m V) Z ↔ Endμ (induceK m K) p Q V Z := by
  unfold Endμ
  rw [← seriesPlug_exp m h,← seriesPlug_product m h,
    seriesPlug_view m K (fun i => (fee_spec (ΤΓ_pair (expΓ hq) hv i (Set.mem_univ _))).2),
    seriesPlug_view m K (fun i => (fee_spec (expΓ hq i (Set.mem_univ _))).2)]

end YM.FVA2.Modes
