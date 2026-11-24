import YM.WilsonCoeffUV.Thermo.TensorPacking
/-!
# Local swatches to normalized page. Template also allows repeated addresses,
graded certifies literal stencil accounting even at small periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{U α I : Type*}{r:ℕ}

section paint
-- a patch. tap can be dark explicitly
variable [DecidableEq U][DecidableEq α] [AddGroup U]
abbrev Leads (U α I :Type*) := I→Option (U×α)
def plank (b:Leads U α I)(x:U): Matrix I (U×α) ℝ:= Matrix.of fun i j=> if b i=some ((jog x).symm j) then 1 else 0
lemma plank_norm (b:Leads U α I)(x i j): |plank b x i j| ≤ 1:=by rw [plank,Matrix.of_apply]; split <;> norm_num
lemma plank_origin (b:Leads U α I)(x i){j : U×α}(h:b i=some j): plank b x i= Pi.single (jog x j) 1:=by ext k; simp_rw [plank,Matrix.of_apply,Pi.single_apply,h, Option.some.injEq]; simp only [Equiv.eq_symm_apply]; simp [eq_comm]
lemma plank_blank (b:Leads U α I)(x i)(h:b i=none): plank b x i=0:=by ext k; simp [plank,h]
variable [Fintype I]
-- alpha local support. anchor internal singleton with bottom

def iris (b:Leads U α I) (Q: Gen ℝ I)(r:ℕ) : canal U (ULift.{0} Unit) α ℝ 1 r := fun x y=> fade (plank b (y 0).1) Q r x
end paint
lemma pet_index [DecidableEq α] (b:Leads Cover α I)(x:Cover)(i:I)(j : Cloth α) : ∀ᶠ n:Side in atTop,
    plank (U:=Site n) (Option.map (foldUnder n) ∘ b) (wrap n x) i (foldUnder n j)=plank b x i j:= by
  cases h:b i with
  | none=> apply Eventually.of_forall; intro n; simp [plank,h]
  | some u=> filter_upwards [fold_faith j (jog x u)] with n hn
             rw [plank_origin _ _ i (show _=some (foldUnder n u) from by simp [Function.comp_apply,h]),plank_origin b x i h]; simp only [Pi.single_apply, ← fold_move,hn]
private lemma pinch_n (n:Side)(x:Site n)(y : Cover) : (tor n).gap x (x+wrap n y) ≤ terrain.gap 0 y:=by change size (lift (_-_))≤size (y-0); rw [add_sub_cancel_left,sub_zero]; exact wrap_size n y

variable [Fintype I][DecidableEq α]
section
variable (b:Leads Cover α I)(P:Gen ℝ I)(r:ℕ)
def click : ℕ:= Finset.univ.sup fun i=> (b i).elim 0 (fun x=>size x.1)
omit [DecidableEq α] in
lemma click_mark {i}{x:Cloth α}(h:b i=some x): size x.1 ≤ click b:= by
  simpa only [h,Option.elim_some,click] using Finset.le_sup (s:=Finset.univ) (f:=fun i=> (b i).elim 0 (fun x=>size x.1)) (Finset.mem_univ i)
lemma iris_design {V:Type*} [AddGroup V][DecidableEq V] {d:Distance V} (A:Leads V α I){D:ℕ}(h:∀ x:V,∀ i: I,∀ j: V×α, plank A x i j≠0 → d.gap x j.1≤D)(s:ℝ)(he:0≤s) : pairCup d s ((∑ i:Fin r→I, ‖P r i‖)*Real.exp (s*(D+D:ℕ))) (iris A P r):= by
  set K:= ∑ i:Fin r→I, ‖P r i‖; have ht:0≤K:= Finset.sum_nonneg fun _ _=> by positivity
  refine ⟨by positivity, fun x y=>?_⟩; set n:=course d x y; set v:= (y 0).1
  by_cases hh:n ≤ D+D
  · apply le_trans (b:=K) ?_ ?_
    · unfold iris fade; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>?_))
      rw [norm_smul,Real.norm_eq_abs,Finset.abs_prod]; conv_rhs=> rw [←one_mul ‖_‖]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun j _=>plank_norm A (y 0).1 _ _)).trans_eq (Finset.prod_const_one)
    rw [mul_assoc,← Real.exp_add]; apply le_mul_of_one_le_right ht
    rw [Real.one_le_exp_iff]; linarith only [mul_le_mul_of_nonneg_left (show (n:ℝ)≤(D+D:ℕ) from Nat.cast_le.mpr hh) he]
  have hz : iris A P r x y=0:= by
    unfold iris fade; apply Finset.sum_eq_zero; intro i _
    rw [show (∏ j, plank A (y 0).1 (i j) (x j))=0 from ?_,zero_smul]
    by_contra hn
    have he j: plank A v (i j) (x j) ≠ 0:= fun H=> hn (Finset.prod_eq_zero (Finset.mem_univ j) H)
    let f:=Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y)
    have hw k:d.gap v (f k)≤ D := by
      cases k with
      | inl k=> exact h v _ _ (he k)
      | inr k=> rw [show f (.inr k)=v by rw [Subsingleton.elim k 0]; rfl,d.self]; positivity
    exact hh (league_le d f fun j l=> (d.tri _ v _).trans (add_le_add (by rw [d.swap]; exact hw j) (hw l)))
  rw [hz,norm_zero]; positivity
lemma page_sup (s:ℝ)(he:0≤s) : pairCup terrain s ((∑ i:Fin r→I, ‖P r i‖)*Real.exp (s*(click b+click b:ℕ))) (iris b P r):= by
  apply iris_design P r b _ s he; intro x i j h
  rw [plank, Matrix.of_apply] at h; split at h; swap; · simp at h
  rename_i he; refine (le_of_eq ?_).trans (click_mark b he); unfold jog terrain; simp; congr 1; abel
lemma iris_pages : Tremor (fun n=>iris (Option.map (foldUnder n) ∘ b) P r) (iris b P r):=by
  refine ⟨fun x y=> ?_, Eventually.of_forall (fun n b' x y=>?_),1,((∑ i:Fin r→I, ‖P r i‖)*Real.exp (1*(click b+click b:ℕ))),one_pos,Eventually.of_forall fun n=>?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_all.mpr (fun j=>eventually_all.mpr fun i=> pet_index b (y 0).1 i (x j))] with n hn
    unfold iris fade; apply Finset.sum_congr rfl; intro i _; congr 1
    exact Finset.prod_congr rfl fun j _=> (hn _ _).symm
  · unfold iris fade; apply Finset.sum_congr rfl; intro t _; congr 1; apply Finset.prod_congr rfl; intro i _
    unfold plank; simp only [Function.comp_apply,Matrix.of_apply,show ((jog ((jog b' (y 0)).1)).symm (jog b' (x i)))=(jog (y 0).1).symm (x i) from Prod.ext (by change -(b'+(y 0).1)+(b'+(x i).1) = -(y 0).1+(x i).1; abel) rfl]; congr
  apply iris_design P r _ (D:=click b) _ 1 zero_le_one
  intro x i j h; set P':=Option.map (foldUnder n) ∘ b
  cases hx:b i with
  | none=> simp [plank,P',hx] at h
  | some u=>
    have hy:P' i=some (foldUnder n u):= by simp [P',hx]
    rw [plank_origin P' _ _ hy,Pi.single_apply] at h; split at h; swap; · simp at h
    rename_i ht; subst j; change (tor n).gap x (x+wrap n u.1)≤click b; refine (pinch_n n x u.1).trans ?_
    unfold terrain; simpa using click_mark b hx

def sunflower : Gen ℝ (Cloth α):= fun r=> worn (iris b P r)
lemma it_cost (s:ℝ)(h:0≤s): ∃ A:ℝ,Amber terrain s A (sunflower b P r):= ⟨_,worn_amber (page_sup b P r (s+1) (by linarith)) h (by linarith)⟩
lemma sunflowerY : Yields (fun n=> wear (iris (Option.map (foldUnder n) ∘ b) P r)) (sunflower b P r) := (iris_pages b P r).transfers

variable {b P r}
lemma iris_apply (P:Gen ℝ I)(A:Leads (Site n) α I): wear (iris A P r)=∑ x:Site n, fade (plank A x) P r := by ext i; rw [wear, ← Equiv.sum_comp (Equiv.funUnique (Fin 1) _).symm]; simp only [Fintype.sum_prod_type, Fintype.sum_unique,Finset.sum_apply]; rfl
end
section plot
variable [Fintype α]
abbrev casement (A:Leads Cover α I)(b: Site n):= plank (Option.map (foldUnder n) ∘ A) b
-- finite Taylor identification
omit [DecidableEq α] in
lemma beam (M:Matrix I α ℝ) (f:Lawn I→ℝ)(h:Green f)(i) : sprig (fun u:Lawn α=> f (M*ᵥ u)) i 0= fade M (sprig f i 0):=by
  have he: Green (fun u:Lawn α=> f (M*ᵥ u)):=by
    apply ContDiffAt.comp (g:=f) 0 _ (board _); simp; apply h
  funext k
  by_cases hh:k=i+0
  · subst k; unfold sprig; rw [shine_lit]; apply unique_kernel (rye_sym he _) (fade_pure (shine_pure (rye_sym h _)) _ _)
    rw [fade_one,shine_lit,←jet_apply,←jet_apply, ←loom_jet M f h,loom,PowerSeries.coeff_map]; rfl
  unfold sprig; rw [shine_dark (Ne.symm hh)]; funext i; unfold fade; simp_rw [shine_dark (Ne.symm hh)]; simp

lemma daisies {J:Type*}[Fintype J] {P:(n:Side)→ Lawn (Co n α)→ℝ}{b:J→ Lawn I→ℝ}(h:∀ j,Green (b j)) (A:J→Leads Cover α I) (he:∀ n:Side,∀ᶠ v : Lawn (Co n α) in 𝓝 0, P n v=∑ j:J,∑ x:Site n,b j (casement (A j) x*ᵥ v))
    (H:∀ n,Green (P n)) (k t r): Yields (fun n=>sprig (P n) k t r) ((∑ j:J,sunflower (A j) (sprig (b j) k t)) r):=by
  let R (j:J)(n:Side)(r): Ten ℝ (Co n α) r:= wear (iris (Option.map (foldUnder n) ∘ A j) (sprig (b j) k t) r)
  refine (parcelY (P:=fun n j i=> R j n i) (fun j _=> sunflowerY (A j) (sprig (b j) k t) r)).congr ?_
  refine Eventually.of_forall fun n=>?_
  rw [Finset.sum_apply]
  by_cases h':r=k+t
  · subst r
    let F (j:J)(x:Site n)(v:Lawn (Co n α)) := b j (casement (A j) x *ᵥ v)
    have hb j x: Green (F j x) := by
      apply ContDiffAt.comp (g:=b j) 0 _ (board _); simp; apply h
    have hy j : Green (∑ x:Site n, F j x):= by
      unfold Green; rw [show (∑ x:Site n,F j x)=fun v=>∑ x:Site n,F j x v from funext fun v=>Finset.sum_apply ..]; apply ContDiffAt.sum; exact fun _ _=>hb ..
    have hv : jet (P n)= ∑ j:J,∑ x:Site n, jet (F j x):=by
      rw [show (∑ j:J,∑ x:Site n, jet (F j x))= ∑ j:J, jet (∑ x:Site n,F j x) from Finset.sum_congr rfl (fun j _=> (jet_sum _ _ (fun x _=> hb j x)).symm), ← jet_sum _ _ (fun j _=> hy j)];
      exact jet_congr ((he n).mono (fun v hk=> by simpa only [Finset.sum_apply] using hk))
    have hd j : R j n (k+t)= ∑ x:Site n, rye (F j x) (k+t):= by
      unfold R; rw [iris_apply]; apply Finset.sum_congr rfl; intro x _;
      have he: sprig (b j) k t=sprig (b j) (k+t) 0:= by simp [sprig]
      rw [he,← beam (casement (A j) x) (b j) (h j),sprig, Nat.add_zero,shine_lit]
    simp_rw [hd,sprig,shine_lit]; apply unique_kernel (Smooth.sum _ ) (rye_sym (H n) _); swap; exact fun i _=> Smooth.sum fun j _=>rye_sym (hb ..) _
    rw [← jet_apply, hv]; simp_rw [map_sum]; simp only [jet_apply]
  unfold R; rw [sprig,shine_dark (Ne.symm h')]; apply Finset.sum_eq_zero; intro i _; rw [iris_apply]; apply Finset.sum_eq_zero; intro x _; funext v; unfold fade; simp_rw [sprig,shine_dark (Ne.symm h')]; simp
end plot
end YM.WilsonCoeffUV.Bank
