import YM.RG11Proof.Rigidity.Pig

/-!
# A finite word-horizon channel's attainable subspace
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free Submodule Filter Set Function
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge}

abbrev Canal (T : Finset (Pig G)) := G.ColorIndex→ (↥T)→ℝ

def current (T : Finset (Pig G)) (v : Foil) (y : E4) : Canal T := fun c t=> line (toss v y c) t

def seaside (T : Finset (Pig G)) (U : Finset E4) : Submodule ℝ (Canal T) :=
    span ℝ {f|∃ a y,y∉U ∧ f=current T a y}

def cabin (c : G.ColorIndex) (x : E4) (k : ℕ) (μ : Flavor k→ℝ) (v : Pig G) : ℝ :=
    if h : v.origin=x ∧ v.dart.tone=c ∧ v.dart.degree=k then μ (h.2.2 ▸ v.dart.mode) else 0

lemma seaside_pitch (c d : G.ColorIndex) {x z : E4} (hz : z≠0) (v : Foil) {t : ℝ} (ht : 0<t)
    (p : Pig G) (hp : p.origin=x) :
    let j:=p.dart.degree
    let b := cell v.1 v.2
    line (toss v (x-t • z) d) p = t⁻¹^(4+j)* cabin d x j (fun a=> fare c a b z) p := by
  intro j b
  have hx : x-(x-t•z)≠0 := by rw [sub_sub_cancel]; exact smul_ne_zero ht.ne' hz
  rw [line_sym]; unfold line
  rw [if_neg (sub_ne_zero.mp ?_),show p.origin-(toss v (x-t•z) d).origin= t•z by change p.origin-(x-_) = _; rw [hp]; abel]
  · change legKernel (flavor j p.dart.tone p.dart.mode) (flavor 0 d b) (t•z)=_
    rw [any_ink c _ _ _ _ (smul_ne_zero ht.ne' hz),show fare c p.dart.mode b (t•z)=t⁻¹^(4+j)*fare c p.dart.mode b z from (kernel_pole _ _).degree _ ht _ hz,cabin]
    by_cases he : p.dart.tone=d <;> simp [hp,he,j]
  rw [hp]; exact hx

/-- Isolate a pole weight, on real ray. Negative powers at other, unassigned
legs simply absent modulo a bounded function. -/
theorem float_fare (T : Finset (Pig G)) (U : Finset E4) (v : Foil) {x z : E4}
    (hz : z≠0) (c : G.ColorIndex) (k : ℕ) :
    (fun d (t : ↥T)=> cabin d x k (fun a=>fare c a (cell v.1 v.2) z) (↑t))∈ seaside T U := by
  let μ (i : ℕ) (a : Flavor i) := fare c a (cell v.1 v.2) z
  let Φ (i : ℕ) : Canal T := fun d t=> cabin d x i (μ i) t
  change Φ k∈ _
  let J := T.image (fun t=> t.dart.degree)
  suffices pull : ∀ i, (∀ j : ℕ, i < j → Φ j∈ seaside T U) → Φ i ∈ seaside T U by
    -- downward clipped at finite degree
    let N:= J.sup id
    have hg (i : ℕ) (hi : N < i) : Φ i=0 := by
      ext1 d; funext p
      change (if h : _ ∧ _ ∧ p.val.dart.degree=i then _ else _) = _
      have hJ : p.val.dart.degree ≤ N := Finset.le_sup (f:=id) (Finset.mem_image_of_mem _ p.property)
      rw [dif_neg (by rintro ⟨h,hv,hk⟩; omega)]; rfl
    suffices he : ∀ n j, N - n ≤ j → Φ j∈ seaside T U by apply he N k (by omega)
    intro n; induction n with
    | zero=> intro j hj; rcases eq_or_lt_of_le (show N≤j from hj) with hh|hh; swap; rw [hg _ hh]; exact Submodule.zero_mem _
             exact pull j (fun i hi=> (hg i (by omega)).symm ▸ (seaside T U).zero_mem)
    | succ n ih=> intro j hj; exact pull j (fun i hi=> ih _ (by omega))
  intro i ih
  let s := nhdsWithin (0:ℝ) (Ioi 0)
  have hl : Tendsto id s (𝓝 (0:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  let y (t : ℝ) := x - t • z
  let A (t : ℝ) := t^(4+i) • (current T v (y t) - ∑ j ∈ J with i<j,t⁻¹^(4+j) • Φ j)
  have he : ∀ᶠ t in s, A t∈ seaside T U := by
    have hh (a : E4) : ∀ᶠ t in s,y t≠a := by
      by_cases ha : x=a
      · subst a; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
        simp [y,smul_ne_zero (show t≠0 from (show 0<t from ht).ne') hz]
      exact (tendsto_const_nhds.sub (hl.smul (tendsto_const_nhds (x:=z)))).eventually (isOpen_ne.mem_nhds (show x-(0:ℝ) • z≠a by simpa))
    filter_upwards [(Filter.eventually_all_finset U).mpr (fun a _=>hh a)] with t ht
    refine (seaside T U).smul_mem _ ((seaside T U).sub_mem (subset_span ⟨v,y t,fun h=>ht _ h rfl,rfl⟩) (Submodule.sum_mem _ ?_))
    intro j hj; exact (seaside T U).smul_mem _ (ih j (Finset.mem_filter.mp hj).2)
  refine (seaside T U).closed_of_finiteDimensional.mem_of_tendsto ?_ he
  refine tendsto_pi_nhds.mpr fun d=> tendsto_pi_nhds.mpr fun b=> ?_
  simp_rw [A,Pi.smul_apply,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,current]

  let j := (b: Pig G).dart.degree
  have hiJ : j∈J := Finset.mem_image_of_mem _ b.property
  by_cases h : b.val.origin=x
  · have hh (t : ℝ) : (∑ u∈ J with i<u,t⁻¹^(4+u)*Φ u d b)=if i<j then t⁻¹^(4+j)*Φ j d b else 0 := by
      have hf (u : ℕ) (hu : u≠j) : Φ u d b=0 := dif_neg fun he=> hu.symm he.2.2
      split_ifs with H
      · exact Finset.sum_eq_single_of_mem j (Finset.mem_filter.mpr ⟨hiJ,H⟩) fun u _ hw=> by rw [hf u hw,mul_zero]
      exact Finset.sum_eq_zero fun u hu=> by rw [hf u (by rintro rfl; exact H (Finset.mem_filter.mp hu).2),mul_zero]
    simp_rw [hh]
    have hp (t : ℝ) (ht : 0<t) : line (toss v (y t) d) b=t⁻¹^(4+j)*Φ j d b := seaside_pitch c d hz v ht b h
    rcases lt_trichotomy i j with hj|hj|hj
    · apply Tendsto.congr' (f₁:=fun _ : ℝ=>Φ i d b) ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
      rw [hp t ht,if_pos hj,sub_self,mul_zero,show Φ i d b=0 from dif_neg (by rintro ⟨h,hv,hk'⟩; exact (Nat.ne_of_lt hj) (show i=j from hk'.symm))]
    · subst i
      apply Tendsto.congr' (f₁:=fun _ : ℝ=>Φ j d b) ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
      have ht : 0<t:=ht
      rw [hp t ht,if_neg (lt_irrefl _),sub_zero]; rw [inv_pow]; field_simp
    have hf : Φ i d b=0 := dif_neg (by rintro ⟨h,hv,hk'⟩; exact (Nat.ne_of_lt hj) (show j=i from hk'))
    have hP := (hl.pow (i-j)).mul_const (Φ j d b)
    rw [zero_pow (Nat.sub_ne_zero_of_lt hj),zero_mul,← hf] at hP
    refine hP.congr' ?_
    filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
    rw [hp t ht,if_neg (not_lt.mpr hj.le),sub_zero,show 4+i=(i-j)+(4+j) by omega, pow_add]; change t^(i-j)*_=_
    have ht : 0<t:=ht; rw [inv_pow]; field_simp
  have hh (u : ℕ) : Φ u d b=0 := dif_neg fun he=> h he.1
  simp_rw [hh,mul_zero,Finset.sum_const_zero,sub_zero]
  -- line with another center bounded
  have hx : Tendsto y s (𝓝 x) := by simpa using (tendsto_const_nhds (x:=x)).sub (hl.smul (tendsto_const_nhds (x:=z)))
  let a := flavor (G:=G) 0 d (cell v.1 v.2)
  let p := (b: Pig G).dart.flip.2
  have hL := (hl.pow (4+i)).mul (((kernel_pole a p).diff _ (show x-b.val.origin∈ away from sub_ne_zero.mpr (Ne.symm h))).continuousAt.tendsto.comp (hx.sub tendsto_const_nhds))
  rw [zero_pow (show 4+i≠0 by omega),zero_mul] at hL
  refine hL.congr' ?_
  filter_upwards [hx.eventually (isOpen_ne.mem_nhds (show x≠b.val.origin from (Ne.symm h)))] with t ht
  change t^(4+i)*_= t^(4+i)*line (toss v (y t) d) b
  change _=t^(4+i) * (if y t=(b: Pig G).origin then 0 else _); rw [if_neg ht]; rfl
lemma foil_span : Submodule.span ℝ {p : Flavor 0|∃ v : Foil, p=cell v.1 v.2} = ⊤ := by
  have ht := unitStay 0
  rw [eq_top_iff, ← ht]; apply span_mono; rintro p ⟨u,i,j,rfl⟩
  exact ⟨(i,j), congr_arg (fun t=> stay t _ _) (Subsingleton.elim ..)⟩

lemma all_rays (k : ℕ) (c : G.ColorIndex) : span ℝ {q : Module.Dual ℝ (Flavor k)|∃ (z:E4) (h : z≠0) (v:Foil),q=(assay c h k 0).flip (cell v.1 v.2)} = ⊤ := by
  let W := span ℝ {q : Module.Dual ℝ (Flavor k)|∃ (z:E4) (h:z≠0) (v:Foil),q=(assay c h k 0).flip (cell v.1 v.2)}
  change W=⊤
  have ht : W.dualCoannihilator=⊥ := by
    apply le_antisymm _ bot_le; intro p hp; apply (Submodule.mem_bot ..).mpr
    refine ranging c p 0 fun z hz w=> ?_
    let f := assay c hz k 0 p
    rw [← fare_pair c p w hz]; change f w=0; rw [show f=0 from ?_]; rfl
    refine LinearMap.ext_on foil_span ?_
    rintro w ⟨v,rfl⟩
    exact (Submodule.mem_dualCoannihilator _).mp hp ((assay c hz k 0).flip (cell v.1 v.2)) (show _∈W from Submodule.subset_span ⟨z,hz,v,rfl⟩)
  apply Submodule.eq_top_of_finrank_eq
  have he:=Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [ht, finrank_bot,add_zero] at he
  rw [he]; exact (Subspace.dual_finrank_eq ..).symm

/-- Listen independently for *any* on shell jet covector. Spans include all
transverse/dual sectors simultaneously; colors not varied one at a time. -/
lemma cabin_span (T : Finset (Pig G)) (c : G.ColorIndex) (U : Finset E4) (x : E4) (k : ℕ) (u : Sheet k) :
    (fun d (t:↥T) => cabin d x k (fun q=>q u) t)∈ seaside T U := by
  let f : Module.Dual ℝ (Flavor k) →ₗ[ℝ] (Canal T) :=
    { toFun a d t := cabin d x k a t
      map_add' a b:=by
        ext1 d; funext t; simp only [Pi.add_apply]; unfold cabin; split_ifs; rfl; exact (add_zero 0).symm
      map_smul' a b:=by
        ext1 d; funext t; simp only [Pi.smul_apply]; unfold cabin; split_ifs; rfl; exact (smul_zero _).symm }
  suffices hv : ⊤ ≤ (seaside T U).comap f from
    hv (show Module.Dual.eval ℝ (Sheet k) u ∈ (⊤ : Submodule ℝ _) from mem_top)
  rw [← all_rays k c,span_le]; rintro v ⟨z,hz,q,rfl⟩
  exact float_fare T U q hz c k

end YM.RG11.Rigidity
