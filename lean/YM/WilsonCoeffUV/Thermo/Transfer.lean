import YM.WilsonCoeffUV.Thermo.Amalgam
/-!
# Dominated thermodynamic passage, & same-scale bilinear operations API -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{U α β V ι : Type*}{k r:ℕ} {A B σ η : ℝ}

def unfoldAt (p:Cover)(y:dock (Site n) α k): dock Cover α k:= fun i=>(p+ lift ((y i).1-wrap n p), (y i).2)
abbrev slideC (n : Side) (y:dock Cover α k):dock (Site n) α k:= foldUnder n ∘ y
lemma slides_back (p: Cover)(y:dock (Site n) α k): slideC n (unfoldAt p y)=y:= funext fun i=> Prod.ext (by change wrap n (p+ _)=_; simp) rfl
lemma base_change (x:dock Cover β r) : wrap n (bearing x)=bearing (slideC n x) := by cases r; apply map_zero; rfl
lemma near_change (p:Cover)(x:dock (Site n) α k)(i): terrain.gap p ((unfoldAt p x) i).1=(tor n).gap (wrap n p) (x i).1:=by
  change size (p+ _-p) = _; rw [add_sub_cancel_left]; rfl
lemma slide_end (p:Cover)(y:dock Cover α k): ∀ᶠ n in atTop, unfoldAt p (slideC n y)=y:=by
  filter_upwards [eventually_all.mpr (fun i=>lift_ready ((y i).1-p))] with n hn
  simp only [map_sub] at hn; ext1 i; exact Prod.ext (by change p+lift (wrap _ _-wrap n p)=_; rw [hn,add_comm,sub_add_cancel]) rfl
-- generic pointwise passage (same block)
variable [NormedAddCommGroup V]
abbrev berth (α β V: Type*) (k r:ℕ):= (n:Side)→canal (Site n) α β V k r
structure Tremor (P:berth α β V k r)(F:canal Cover α β V k r) : Prop where
  point : ∀ x y,Tendsto (fun n=>P n (slideC n x) (slideC n y)) atTop (𝓝 (F x y))
  move : ∀ᶠ n in atTop, mooring (P n)
  stood : ∃ σ A:ℝ, 0<σ ∧ ∀ᶠ n in atTop,pairCup (tor n) σ A (P n)

variable {P R:berth α β V k r}{F Q:canal Cover α β V k r}
lemma Tremor.add (h:Tremor P F)(g:Tremor R Q): Tremor (P+R) (F+Q):= by
  obtain ⟨s,a,hp,H⟩:=h.stood; obtain ⟨t,b,ht,J⟩:=g.stood
  refine ⟨fun x y=>(h.point x y).add (g.point x y), ?_, min s t,a+b,lt_min hp ht,(H.and J).mono (fun _ ⟨he,hf⟩=>(he.mono (min_le_left ..)).add (hf.mono (min_le_right ..)))⟩
  filter_upwards [h.move,g.move] with n hn hv
  intro b x y; simp only [Pi.add_apply]; rw [hn b x y,hv b x y]
lemma Tremor.zero : Tremor (0:berth α β V k r) 0:= ⟨fun _ _=>tendsto_const_nhds, Eventually.of_forall fun _ _ _ _=>rfl,1,0,one_pos, Eventually.of_forall fun _=>pairCup.zero⟩
lemma Tremor.sum (s:Finset ι){P:ι→berth α β V k r}{F:ι→canal Cover α β V k r}(h:∀ i∈s,Tremor (P i) (F i)): Tremor (∑ i∈s,P i) (∑ i∈s,F i):= by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Tremor.zero
  | @insert i s he H=> rw [Finset.sum_insert he,Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).add (H fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma Tremor.covers (h:Tremor P F):∃ σ A:ℝ,0<σ ∧ pairCup terrain σ A F:=by
  obtain ⟨s,a,he,H⟩:=h.stood; obtain ⟨w,hw⟩:= H.exists
  refine ⟨s,a,he,hw.1,fun x y=>le_of_tendsto (h.point x y).norm ?_⟩
  let z : Fin r⊕Fin k→ Cloth (PUnit.{1}) := Sum.elim (fun i=>((x i).1,.unit)) (fun i=>((y i).1,.unit))
  filter_upwards [touched z,H] with n hn hp
  have hh n: soar (tor n) (foldUnder n ∘ z)=course (tor n) (slideC n x) (slideC n y):= congr_arg (league _) (funext fun j=>by cases j<;> rfl)
  have hx: soar terrain z=course terrain x y:=congr_arg (league _) (funext fun j=> by cases j<;> rfl)
  rw [←hx,←hn,hh]; exact hp.2 ..

variable {F':canal Cover α β V (k+1) r}{P':berth α β V (k+1) r}
lemma Tremor.tie (h:Tremor P' F')(x y): Tendsto (fun n=> tie (P' n) (slideC n x) (slideC n y)) atTop (𝓝 (tie F' x y)):=by
  have he : ∀ᶠ n:Side in atTop, ((slideC n y 0).1=0 ↔ (y 0).1=0):=by
    filter_upwards [lift_ready (y 0).1] with n hn; change wrap n (y 0).1=0 ↔ _
    refine ⟨fun H=> ?_,fun H=> by rw [H,map_zero]⟩
    rw [← hn,H]; simp
  by_cases hv:r=0 ∧ (y 0).1 ≠ 0
  · rw [Bank.tie, if_pos hv]; refine (tendsto_const_nhds (x:=(0:V))).congr' ?_
    filter_upwards [he] with n hn; exact Eq.symm (if_pos ⟨hv.1,mt hn.mp hv.2⟩)
  rw [Bank.tie,if_neg hv]; refine (h.point x y).congr' ?_
  filter_upwards [he] with n hn; exact Eq.symm (if_neg (fun ⟨hh,h'⟩=> hv ⟨hh,mt hn.mpr h'⟩))

lemma slip_rule [DecidableEq α] (p:Cover) (F: dock (Site n) α k→V) [Fintype α] : ∑' y:dock Cover α k, (if unfoldAt p (slideC n y)=y then F (slideC n y) else 0)=∑ i,F i:=by
  classical
  have H : Injective (unfoldAt (n:=n) (α:=α) (k:=k) p):= LeftInverse.injective (slides_back p)
  rw [tsum_eq_sum (s:= Finset.univ.image (unfoldAt (n:=n) p)), Finset.sum_image H.injOn]
  · simp only [slides_back,↓reduceIte]
  intro b hb; rw [if_neg]; intro he; exact hb (Finset.mem_image.mpr ⟨_, Finset.mem_univ _,he⟩)

variable [NormedSpace ℝ V]
lemma Tremor.smul (h:Tremor P F)(b:ℝ): Tremor (b•P) (b•F):= by
  obtain ⟨s,a,he,H⟩:=h.stood; refine ⟨fun x y=>tendsto_const_nhds.smul (h.point x y),?_,s,|b| *a,he,H.mono (fun n hn=>hn.smul b)⟩
  filter_upwards [h.move] with n hn; intro b x y; simp only [Pi.smul_apply]; rw [hn b x y]
variable [CompleteSpace V][Fintype α]
theorem Tremor.transfers (h:Tremor P' F'): Yields (fun n=>wear (P' n)) (worn F'):=by
  classical
  obtain ⟨s,a,hp,H⟩:=h.stood
  set t := s/2; have ht:0<t:= by unfold t; linarith
  have hg : t<s:= by unfold t; linarith
  refine ⟨fun x=>?_,h.move.mono (fun _ hn=>north_stroll hn), t, _,ht,(H.and h.move).mono (fun _ ⟨he,hf⟩=>wear_amber he hf ht.le hg)⟩
  let c:= s/(k+1:ℕ); have hc :0<c:= by unfold c; positivity
  set p:=bearing x
  let W (n:Side)(y) := if unfoldAt p (slideC n y)=y then Bank.tie (P' n) (slideC n x) (slideC n y) else 0
  let B (y:dock Cover α (k+1)):= a*sail c terrain p y
  have hv : Tendsto (fun n=>∑' y,W n y) atTop (𝓝 (∑' y,Bank.tie F' x y)):=by
    refine tendsto_tsum_of_dominated_convergence (bound:=B) ((train_pay hc p _).2.1.mul_left a) (fun y=>?_) ?_
    · refine (h.tie x y).congr' ((slide_end p y).mono fun n hn=>?_); exact Eq.symm (if_pos hn)
    filter_upwards [H] with n hn
    intro y; unfold W; split
    · rename_i hr
      have he:= tie_bound hn (η:=0) hp le_rfl (slideC n x) (slideC n y)
      simp only [sub_zero,neg_zero, zero_mul,Real.exp_zero,mul_one] at he
      apply he.trans_eq; apply congr_arg (a*·); apply Finset.prod_congr rfl; intro i _
      rw [show (tor n).gap _ _= terrain.gap p (y i).1 from ?_]
      have hy:= near_change p (slideC n y) i
      rw [hr] at hy
      rw [show (wrap n p)=bearing (slideC n x) from base_change x] at hy; exact hy.symm
    rw [norm_zero]; exact mul_nonneg hn.1 (sail_nn ..)
  refine hv.congr' ?_
  filter_upwards [h.move] with n hn
  rw [slip_rule p, dilute_wear hn]

-- subtraction commute with cover projection
omit [NormedSpace ℝ V] in
lemma worn_sub {F Q:canal Cover α β V (k+1) r}(h:pairCup terrain σ A F)(e:pairCup terrain σ B Q)(he:0<σ): worn (F-Q)=worn F-worn Q:=by
  funext x
  have hp : tie (F-Q) x=tie F x-tie Q x:= funext fun i=>by rw [Bank.tie]; split<;> rename_i hh <;> simp [Bank.tie,hh]
  unfold worn; change _=(∑' y,tie F x y)-(∑' y,tie Q x y)
  rw [hp]; exact (Summable.tsum_sub ((tie_cost h he le_rfl x).2.1.of_norm) ((tie_cost e he le_rfl x).2.1.of_norm))
end YM.WilsonCoeffUV.Bank
