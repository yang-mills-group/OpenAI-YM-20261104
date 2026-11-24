import YM.Trace.Fock.Polar
/-!
Polarization and removal of the symmetric tensor permutation on the actual vacuum
matrix elements, with uniform spacelike neighborhoods for the tested electric slots.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace YM.Trace.Shell
open YM Boundary Function MeasureTheory Filter Complex Set
open scoped Topology BigOperators InnerProductSpace Pointwise
variable {m n:ℕ} (w : Test4→L[ℂ] Sum m) (h : FieldImage w)
noncomputable def permuteBasis (π : Equiv.Perm (Fin n)) : Cords n ≃ᵐ Cords n := MeasurableEquiv.piCongrLeft (fun _=>Mom) π.symm
noncomputable def permuteColor (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → Mode m) := π.symm.arrowCongr (Equiv.refl (Mode m))
lemma permuteBasis_eq (π : Equiv.Perm (Fin n)) (x : Cords n) : permuteBasis π x = x ∘ ⇑π := by
    funext i; exact Eq.trans (by simp only [Equiv.symm_apply_apply] : permuteBasis π x i=permuteBasis π x (π.symm (π i)))
       (MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _:Fin n=> Mom) π.symm x (π i))
lemma permute_measure (π : Equiv.Perm (Fin n)) : MeasurePreserving (permuteBasis π) (νpow n) (νpow n) := measurePreserving_piCongrLeft (fun _=>_) π.symm
lemma several_inner (v : @Mixed n m) (b : Wave m n) : inner ℂ b (several n m v) = ∫ p, inner ℂ (b p) (productMany v p) ∂νpow n := (L2.inner_def ..).trans
    (integral_congr_ae (several_coe_eq v|>.mono (fun i hi=> congr_arg _ hi)))
lemma evaluated_right (v : @Mixed n m) (b : Wave m n) (π : Equiv.Perm (Fin n)) (hs : symmetry b) : inner ℂ b (several n m (v ∘ π))=inner ℂ b (several n m v) := by
    simp_rw [several_inner]
    have H (a : @Mixed n m) (p : Cords n) (I : Fin n→Mode m): productMany a p I = ∏ k, jet (p k) (a k) (I k) := rfl
    rw [← (permute_measure π|>.integral_comp (permuteBasis π|>.measurableEmbedding) (fun p=> inner ℂ (b p) (productMany (n:=n) (v ∘ π) p)) ) ]
    refine integral_congr_ae (hs π|>.mono fun x hx=> ?_)
    simp only [PiLp.inner_apply]
    rw [← Equiv.sum_comp (permuteColor (m:=m) π) (fun I : Fin n→Mode m => inner ℂ (b _ I) ((productMany (v ∘ ⇑π) (permuteBasis π x)) I))]
    apply Finset.sum_congr rfl
    intro i _
    have hc : (permuteColor π i)=i ∘ π := rfl
    have he := Equiv.prod_comp π (fun k => jet (x k) (v k) (i k))
    simp only [permuteBasis_eq,hc,hx,H,comp_def,he] -- order matters
    congr 1
    exact hx i
lemma evaluated_left (v : @Mixed n m) (b : Wave m n) (π : Equiv.Perm (Fin n)) (hs : symmetry b): inner ℂ (several n m (v ∘ π)) b=inner ℂ (several n m v) b := by
    apply star_injective (R:=ℂ)
    simpa [inner_conj_symm] using evaluated_right v b π hs

private lemma space_close (f : E4→ℝ) (x y:E4) : ‖spatial x‖- |time x| ≤ ‖spatial (x-y)‖-|time (x-y)| + 2*‖y‖ := by
    have hA := abs_sub (time x) (time y)
    have ht (y) := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg y)).mp (show |time y|^2 ≤ _ by rw [Mink.squares,sq_abs]; nlinarith)
    have hs (y) := (sq_le_sq₀ (norm_nonneg (spatial y)) (norm_nonneg y)).mp (show _ ≤ ‖y‖^2 by rw [Mink.squares]; nlinarith)
    have hb := norm_add_le (spatial (x-y)) (spatial y)
    have hv : x-y+y=x := sub_add_cancel x y
    simp only [← Mink.rest_add,hv] at hb
    rw [show time (x-y)=time x-time y from map_sub Mink.clockL _ _]
    simp only [← sub_eq_add_neg]; linarith [ht y,hs y]

lemma spacelike_margin (K : Set E4) (hK : IsCompact K) (hS : K ⊆ Mink.spacelike) : ∃ r> (0:ℝ), ∃ E : Set E4, IsOpen E ∧ K ⊆ E ∧
   ∀ x∈closure E, ∀ y∈Metric.closedBall 0 r, (x-y)∈Mink.spacelike := by
   let d (x:E4) := ‖spatial x‖-|time x|
   have hd : Continuous d := by unfold d; fun_prop
   obtain hK₀|hK₀:=K.eq_empty_or_nonempty
   · refine ⟨1,zero_lt_one, ∅,isOpen_empty,hK₀.le,?_⟩; simp
   obtain ⟨q,hq,hU⟩ := hK.exists_isMinOn hK₀ hd.continuousOn
   have hp : ∀ p∈K, 0<d p := fun p hp=> sub_pos.mpr (Mink.lateral p |>.1 (hS hp))
   let r := d q/3
   have hr : 0<r:=by dsimp [r]; linarith [hp q hq]
   refine ⟨r/4,by positivity,{x | r<d x}, isOpen_lt continuous_const hd, (fun z h=> ?_), fun x hx y hy=> ?_⟩
   · change r < d z; exact (by unfold r; linarith [hp q hq] : r < d q).trans_le (hU h)
   have hC : r≤ d x := closure_minimal (fun z (hz : r<d z)=> hz.le) (isClosed_le continuous_const hd) hx
   have hy : ‖y‖ ≤ r/4 := by simpa using hy
   apply (Mink.lateral _).2
   have:=space_close d x y; dsimp only [d] at hC ⊢; linarith

private lemma bar_scalar (r : ℂ) (a : Test4) : Probe.bar (r • a)=(star r) • Probe.bar a := by
    apply DFunLike.ext; intro x; rw [Probe.bar_at,smul_apply,smul_eq_mul,star_mul']; rfl
private lemma bar_squared (a : Test4) : Probe.bar (Probe.bar a)=a := by apply DFunLike.ext; intro x; simp [Probe.bar_at]
private noncomputable def barSlotField (m) (v : SlotField m) : SlotField m := fun j=> Probe.bar (v j)
private noncomputable def splitE (b : Fin 2) (f : SlotField m) : SlotField m := if b=0 then
        (↑(1/2:ℝ):ℂ) • (f+barSlotField m f) else (-I * (↑(1/2:ℝ):ℂ)) • (f-barSlotField m f) -- define barSlotField
private def coeffE (b : Fin 2) : ℂ := if b=0 then 1 else I
private lemma split_sum (f : SlotField m) : f=∑ b : Fin 2, coeffE b • splitE b f := by
    rw [Fin.sum_univ_two,coeffE,splitE,coeffE,splitE, if_pos rfl, if_pos rfl, if_neg (by decide), if_neg (by decide)]
    ext i x; simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_apply,sub_apply,add_apply,barSlotField,smul_eq_mul,neg_mul]
    ring_nf; simp; ring_nf
private lemma supportE_compact (f : SlotField m) (h : ∀ i, CC (f i)) : IsCompact (supportE f) := _root_.isCompact_iUnion h
private lemma split_support (f : SlotField m) (h : ∀ i, CC (f i)) (i : Fin 2) : supportE (splitE i f) ⊆ supportE f := by
   unfold supportE; refine iUnion_subset (fun j => closure_minimal (fun p hx => Classical.byContradiction (fun hn=> hx ?_)) (supportE_compact _ h|>.isClosed) )
   have hp : f j p=0 := image_eq_zero_of_notMem_tsupport (fun hp=> hn (mem_iUnion.mpr ⟨_,hp⟩))
   unfold splitE barSlotField; split_ifs <;> exact (by simp [*,Probe.bar_at])
private lemma split_electric (f : SlotField m) (h : ∀ i, CC (f i)) (i : Fin 2) : ElectricTest (splitE i f) := fun j => by
   constructor
   · unfold splitE barSlotField; split_ifs with ht
     all_goals simp only [Pi.smul_apply, Pi.add_apply,Pi.sub_apply,bar_scalar,map_add,map_sub,bar_squared,star_mul',star_def,map_neg _,conj_I,neg_neg,conj_ofReal]
     · rw [add_comm]
     rw [← neg_sub,smul_neg,← neg_smul,neg_mul]
   exact (supportE_compact f h).of_isClosed_subset isClosed_closure ((subset_iUnion _ j).trans (split_support f h i))
private lemma signs_support {K : Set E4} (v : @Mixed n m) (hK : IsClosed K) (hv : ∀ i, supportE (v i)⊆K) (r : Fin n→ℝ) :
    supportE (∑ i, (r i:ℂ) • v i) ⊆ K := by
   unfold supportE; refine iUnion_subset (fun j => closure_minimal (fun p hx => Classical.byContradiction (fun hn=> hx ?_)) hK)
   simp only [Finset.sum_apply, sum_apply,Pi.smul_apply,smul_zero,Finset.sum_const_zero,smul_apply,
     show ∀ i, (v i j) p=0 from fun i=> image_eq_zero_of_notMem_tsupport (fun he => hn (hv i (mem_iUnion.mpr ⟨_,he⟩)))]
   -- simp_rw generic sum apply?
private lemma signs_electric (v : @Mixed n m) (hv : ∀ i, ElectricTest (v i)) (r : Fin n→ℝ) : ElectricTest (∑ i, (r i:ℂ) • v i) := fun j=> by
  constructor
  · simp only [Finset.sum_apply,map_sum]
    exact Finset.sum_congr rfl fun i _=> (ElectricTest.scale (r i) _ (hv i) j).1
  have hc : IsCompact (⋃ i, supportE (v i)) := _root_.isCompact_iUnion (fun i=> supportE_compact (v i) (fun j=> (hv i j).2))
  exact hc.of_isClosed_subset isClosed_closure ((subset_iUnion _ j).trans (signs_support v hc.isClosed (fun i=> subset_iUnion (fun j=> supportE (v j)) i) r))


include h in
private lemma pair_perm (a : @Mixed n m) (f : Test4) (e : Equiv.Perm (Fin n)) : let F := pairLeft (w f n) - pairRight (w (Probe.bar f) n)
    F (a ∘ ⇑e)=F a := by
    dsimp only [MultilinearMap.sub_apply]; apply congrArg₂ (·-·) (evaluated_left (barSlots a) _ _ (h.symmetric f n)) (evaluated_right _ _ _ (h.symmetric _ _))
    -- inferred?
omit h in
private lemma cancel_of_matrix (g : SlotField m) (f : Test4) (hR : ElectricTest g)
    (he : ∀ z : ℝ, inner ℂ (pulse (-(z:ℂ) • g)) (w f) = inner ℂ (w (Probe.bar f)) (pulse (z • g))) : -- parser -(s:ℂ) -> r
    (pairLeft (w f n) - pairRight (w (Probe.bar f) n)) (fun _=>g)=0 := by
     have ht := pulse_identity_terms g (w f) (w (Probe.bar f)) n (fun z : ℝ=> by simpa only [← neg_smul] using! he z)
     apply sub_eq_zero.mpr
     change inner ℂ (several n m (barSlots _)) (w f n) = inner ℂ (w (Probe.bar f) n) (several n m _)
     have hg : barSlots (fun _:Fin n=>g)=(fun _=>g) := funext (fun _=> funext (fun j=> (hR j).1))
     rw [hg,several_diag]; exact ht
include h in
lemma exchange_terms (v : @Mixed n m) (hV : ∀ i j, CC (v i j)) (sV : ∀ i, supportE (v i) ⊆ Mink.spacelike):
    ∃ r>0, ∀ f : Test4, tsupport f ⊆ Metric.ball 0 r →
    pairLeft (w f n) v = pairRight (w (Probe.bar f) n) v := by
   let K := ⋃ i, supportE (v i)
   have hK : IsCompact K := _root_.isCompact_iUnion (fun i=> supportE_compact (v i) (hV i))
   obtain ⟨t,ht,E,hE,heS,hd⟩ := spacelike_margin K hK (iUnion_subset sV)
   obtain ⟨δ,hδ,hA⟩ := h.compatible ∅ (by simp)
   obtain ⟨s,⟨(hs₀:0<s),hδs,H⟩,hT⟩ := (((show ∀ᶠ r in (𝓝[>] (0:ℝ)), r>0 from self_mem_nhdsWithin).and hA).and
       ((Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds ht)) : ∀ᶠ i in (𝓝[>]0), i < t)).exists
   refine ⟨s,hs₀,fun f hf=> ?_⟩
   let F := pairLeft (w f n) - pairRight (w (Probe.bar f) n)
   apply sub_eq_zero.mp (show F v=0 from ?_)
   have hm (a : @Mixed n m) (ha : ∀ i, ElectricTest (a i) ∧ supportE (a i) ⊆ K) : F a=0 := by
       refine polar_vanish F a (fun e=> ?_) (fun b=> ?_)
       · exact pair_perm w h ..
       let g := ∑ i : Fin n, (b i:ℂ) • a i
       have hg : supportE g ⊆ K := signs_support _ hK.isClosed (fun i=> (ha i).2) b
       have hR : ElectricTest g := signs_electric _ (fun i => (ha i).1) _
       apply cancel_of_matrix w g f hR (fun z : ℝ=> by
           simpa only [neg_smul] using! H f (isCompact_closedBall (0:E4) s |>.of_isClosed_subset isClosed_closure (hf.trans Metric.ball_subset_closedBall))
             ((z:ℂ) • g) (ElectricTest.scale z g hR) ⟨E,hE, ((support_scale ..).trans hg).trans heS, hf, fun x hx y hy => hd x hx y ((Metric.closedBall_subset_closedBall hT.le) hy)⟩)
   rw [show v=(fun i => ∑ j, coeffE j • splitE j (v i)) from funext (fun _ => split_sum _), F.map_sum]
   apply Finset.sum_eq_zero
   intro i _
   rw [F.map_smul_univ] -- update syntax
   refine (congr_arg ((∏ j, coeffE (i j)) • ·) (hm _ (fun j=> ⟨split_electric _ (hV _) (i j), (split_support _ (hV _) (i j)).trans (subset_iUnion (fun j=>supportE (v j)) j)⟩))).trans ?_
   exact smul_zero _


end YM.Trace.Shell
