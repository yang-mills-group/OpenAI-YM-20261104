import YM.SchemeConversionRG11.FirstW.Invoice.Invoice
/-! Auxiliary fixed-profile-top schedule estimates, not actual remainder estimates. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Set Metric Lattice Pert Align Topology
open scoped BigOperators Classical
variable {T : Itinerary} {E F G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {f g : ℕ→E} {r : ℕ→F}
def Fleck (T : Itinerary) (f : ℕ→E) : Prop := ∀ p:ℕ,Tendsto (fun j=>(T.gap j^p)⁻¹ • f j) atTop (𝓝 0)
def Dear (T : Itinerary) (f : ℕ→E) : Prop := ∃ p:ℕ,Tendsto (fun j=>(T.gap j^p) • f j) atTop (𝓝 0)
lemma flecks {f:ℕ→E} : Fleck T f ↔ ∀ p:ℕ,Tendsto (fun i=>(T.gap i^p)⁻¹*‖f i‖) atTop (𝓝 0) := by
  unfold Fleck; apply forall_congr'; intro a; rw [tendsto_zero_iff_norm_tendsto_zero (E:=E)]; simp only [norm_smul,norm_inv,norm_pow]; simp_rw [show ∀ i, ‖T.gap i‖=T.gap i from fun i=>Real.norm_of_nonneg (T.positive i).le]
lemma Fleck.cheap (h : Fleck T f) : Tendsto f atTop (𝓝 0) := by simpa only [pow_zero,inv_one,one_smul] using h 0
lemma Fleck.push (h : Fleck T f) (L : E→L[ℝ] F) : Fleck T (fun i=>L (f i)) := by
  intro k; simp_rw [←L.map_smul]; apply Tendsto.comp (g:=L) _ (h k);  rw [←L.map_zero]; exact L.continuous.continuousAt.tendsto -- occurrence
lemma Fleck.sale (h : Fleck T f) (p : ℕ): Fleck T (fun i=> (T.gap i^p)⁻¹ • f i) := fun j=>by simpa only [smul_smul,pow_add,mul_inv] using h (j+p)
lemma Fleck.roll (h : Fleck T f) (hp : Fleck T g) : Fleck T (fun i=>f i+g i) := fun j=> by simpa only [smul_add,add_zero] using (h j).add (hp j)
lemma Fleck.still : Fleck T (fun _=> (0:E)) := fun j=>by simp
lemma Fleck.collect {s : Finset A} {f : A→ℕ→E} (h : ∀ x∈s,Fleck T (f x)) : Fleck T (fun i=>∑ x∈s,f x i) := by
  induction s using Finset.induction with | empty => simp only [Finset.sum_empty]; exact Fleck.still | insert a s he ih=>simp only [Finset.sum_insert he]; exact (h a (Finset.mem_insert_self ..)).roll (ih (fun x hx=>h x (Finset.mem_insert_of_mem hx)))
lemma Fleck.const (h : Fleck T f) (t : ℝ) : Fleck T (fun i=>t•f i) := h.push (t • ContinuousLinearMap.id ℝ E)
lemma Dear.given {x : E} (h : Tendsto f atTop (𝓝 x)) : Dear T f := ⟨1,by simpa only [pow_one,zero_smul] using T.cutoff.smul h⟩
lemma Fleck.with (h : Fleck T f) (p : Dear T r) (B : E →L[ℝ] F→L[ℝ] G) : Fleck T (fun i=> B (f i) (r i)) := by
  obtain ⟨t,H⟩:=p
  intro k
  have he (i : ℕ):B ((T.gap i^(k+t))⁻¹ • f i) (T.gap i^t • r i) = (T.gap i^k)⁻¹ • B (f i) (r i) := by simp [pow_add,map_smul,smul_smul,(T.positive i).ne']
  have h1 := B.continuous.continuousAt.tendsto.comp (h (k+t))
  have h2 := ContinuousAt.tendsto (x:=(B 0,(0:F))) ((continuous_fst.clm_apply continuous_snd : Continuous (fun v : (F→L[ℝ] G) × F=> v.1 v.2)).continuousAt); have h3:= h2.comp (h1.prodMk_nhds H) ; simp only [map_zero] at h3; exact h3.congr he
lemma Dear.raise {p q : ℕ} (h : Tendsto (fun j=>(T.gap j^p) • f j) atTop (𝓝 0)) (hpq:p≤q) : Tendsto (fun j=>(T.gap j^q) • f j) atTop (𝓝 0) := by
  have e (j : ℕ) : T.gap j^(q-p)*T.gap j^p=T.gap j^q := by rw [←pow_add, Nat.sub_add_cancel hpq]
  simpa only [smul_smul, e, smul_zero] using (T.cutoff.pow (q-p)).smul h
lemma Dear.roll (h : Dear T f) (p : Dear T g) : Dear T (fun i=> f i+g i) := by obtain ⟨i,hi⟩ := h; obtain ⟨j,hj⟩ := p; exact ⟨max i j,by simpa only [smul_add,zero_add] using (Dear.raise hi (le_max_left i j)).add (Dear.raise hj (le_max_right i j))⟩
lemma Dear.push (h : Dear T f) (L : E→L[ℝ] F) : Dear T (fun i=>L (f i)) := by
  obtain ⟨k,hk⟩:=h; have hp:=L.continuous.continuousAt.tendsto.comp hk; rw [map_zero] at hp; exact ⟨k,hp.congr (fun i=>L.map_smul ..)⟩
lemma Dear.sale (h : Dear T f) (p : ℕ) : Dear T (fun i=>(T.gap i^p)⁻¹ • f i) := by
  obtain ⟨q,hq⟩:=h; refine ⟨q+p,hq.congr ?_⟩; intro i; dsimp only; rw [smul_smul,pow_add,mul_assoc, mul_inv_cancel₀ (pow_ne_zero p (T.positive i).ne'),mul_one]
lemma Dear.pair (h : Dear T f) (p : Dear T r) (L : E→L[ℝ] F→L[ℝ] G) : Dear T (fun i=>L (f i) (r i)) := by
  obtain ⟨i,H⟩:=h; obtain ⟨j,H'⟩:=p; refine ⟨i+j,?_⟩
  have h1:=(L.continuous.continuousAt.tendsto.comp H)
  have he:= (show Continuous (fun v:(F→L[ℝ] G) × F=>v.1 v.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (h1.prodMk_nhds H'); dsimp only [comp_def] at he; rw [map_zero] at he
  apply he.congr; intro k; simp [pow_add,map_smul,smul_smul,mul_comm]
lemma Dear.const (h : Dear T f) (s : ℝ) : Dear T (fun i=>s • f i) := h.push (s • ContinuousLinearMap.id ℝ E)
lemma Dear.collect {s : Finset A} {f : A→ℕ→E} (h : ∀ x∈s,Dear T (f x)) : Dear T (fun i=>∑ x∈s,f x i) := by
  induction s using Finset.induction with | empty=> simp only [Finset.sum_empty]; exact Dear.given tendsto_const_nhds | insert a s he ih=> simp only [Finset.sum_insert he]; exact (h a (Finset.mem_insert_self ..)).roll (ih (fun x hx=>h x (Finset.mem_insert_of_mem hx)))
lemma Dear.lump (h : Fleck T f) : Dear T f := Dear.given h.cheap
lemma Dear.tower {C : ℝ} (h : ∀ᶠ i in atTop, ‖f i‖ ≤ C) : Dear T f := by
  refine ⟨1,tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (h.mono fun i hi=>show _≤ T.gap i*C from ?_) (by simpa only [zero_mul] using T.cutoff.mul_const C))⟩
  rw [pow_one,norm_smul,Real.norm_of_nonneg (T.positive _).le]; exact mul_le_mul_of_nonneg_left hi (T.positive _).le
lemma Fleck.seale {C:ℝ} (h : ∀ᶠ i in atTop,((T.period i).val:ℝ) * ‖f i‖ ≤ C) : Fleck T f := by
  apply flecks.mpr; intro p; have e:=T.huge p
  apply squeeze_zero' (Eventually.of_forall (fun i=> mul_nonneg (by have hh:=T.positive i; positivity) (norm_nonneg _))) _ (show Tendsto (fun i=> (T.gap i^p*(T.period i).val)⁻¹*C) atTop (𝓝 0) from by simpa only [mul_zero,comp_def,mul_comm] using (tendsto_inv_atTop_zero.comp e).mul_const C)
  refine h.mono fun i hi=>?_; rw [mul_inv,mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (by have hh:=T.positive i; positivity); rw [inv_mul_eq_div, le_div_iff₀ (Full.val_pos _)]; rwa [mul_comm]
lemma Fleck.minus (h : Fleck T f) : Fleck T (fun i=> -f i) := by simpa only [neg_smul,one_smul] using h.const (-1)
end YM.RG11.FirstW
