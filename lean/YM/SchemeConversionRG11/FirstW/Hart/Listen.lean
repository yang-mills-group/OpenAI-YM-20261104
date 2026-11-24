import YM.SchemeConversionRG11.FirstW.Hart.Garden
/-! Correct fitted stencil to genuinely harmonic co-closed in all tests. No lost power. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Metric Lattice Pert Align Topology Maxwell Submodule
open Laurent (size)
open scoped BigOperators Classical InnerProductSpace
variable {T : Itinerary} {G : Gauge} {k : ℕ} {r : ℝ}
-- discrete local erosion
structure Echoes (A : ℕ→Field4 G) : Prop where
  lune : ∀ x : Cover,∀ a : Axis,∀ᶠ i in atTop, atoneLap (field4 a (A i)) x=0
  tide : ∀ x : Cover,∀ᶠ i in atTop, atoneDiv (A i) x=0
lemma dress_charge (q : ℕ→ stor G k) (h : Court (fun i=> (T.gap i^(k+2))⁻¹ • q i)) : Messed T r k (fun i=>(q i).val) := by
  let b:=Module.finBasis ℝ (stor G k); choose P Hp hP using fun i=>lump_eval (b i)
  choose f Hf F using fun i=>h (b.coord i)
  refine ⟨1 + ∑ i,f i *P i, add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg (fun i _=> mul_nonneg (Hf i).le (Hp i).le)),?_⟩
  refine (eventually_all.mpr F).mono fun j hj a D he v hv=> ?_
  have hq (l): ‖b.coord l (q j)‖≤ T.gap j^(k+2) * f l := by have H:= hj l; change ‖b.coord l ((T.gap j ^(k+2))⁻¹ • q j)‖≤_ at H; rwa [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg_of_nonneg (pow_nonneg (T.positive j).le _)), inv_mul_le_iff₀ (pow_pos (T.positive j) _)] at H -- indentation
  have heq : field4 a (q j).val = ∑ l, b.coord l (q j) • field4 a (b l).val := by
    let X := post (G:=G) a ∘ₗ (stor G k).subtype; change X (q j)=_
    nth_rw 1 [← b.sum_repr (q j)]; rw [map_sum]; exact Finset.sum_congr rfl fun l _=>X.map_smul ..
  rw [heq,sum_combine,Finset.sum_apply]; apply le_trans (norm_sum_le ..); let W:=T.gap j^(k+2) * (1+(size v:ℝ))^(k+1-D.length)
  apply le_trans (b:=∑ l, f l*P l*W) (Finset.sum_le_sum (fun l _=>?_))
  · rw [← Finset.sum_mul,add_mul,add_mul]; unfold W; nlinarith [pow_pos (T.positive j) (k+2), show 0≤ (1+(size v:ℝ))^(k+1-D.length) by positivity] -- maybe target order reversed
  rw [combine_smul,Pi.smul_apply,norm_smul]; exact le_trans (mul_le_mul (hq l) (hP l a D he v) (norm_nonneg _) (mul_nonneg (pow_nonneg (T.positive j).le _) (Hf l).le)) (le_of_eq (by unfold W; ring))
variable (W : ℕ→Field4 G)
-- correction linear algebra
private def sight4 (e : Edge Cover) : Field4 G →ₗ[ℝ] G.Color := LinearMap.proj e
private def quizD (G : Gauge) (x : Cover) : Field4 G→ₗ[ℝ] G.Color := ∑ i:Axis,(sight4 (x,i)-sight4 (x-step i,i))
private def quizL (G : Gauge) (x : Cover) (a : Axis) : Field4 G→ₗ[ℝ] G.Color := ∑ i:Axis,(sight4 (x+step i,a)+sight4 (x-step i,a)-(2:ℕ) • sight4 (x,a))
private lemma quizD_eq (B: Field4 G) (x): quizD G x B=atoneDiv B x := by simp [quizD,sight4,atoneDiv]
private lemma quizL_eq (B:Field4 G)(x a): quizL G x a B=atoneLap (field4 a B) x := by simp [quizL,sight4,atoneLap,field4, two_nsmul]
private def saleable {U:Type*} [AddCommGroup U] [Module ℝ U] (f : ℕ→U) : Submodule ℝ (Low U) where
 carrier:=setOf fun p=> ∃ C>0,∀ᶠ i in atTop, ‖p (f i)‖ ≤ C
 zero_mem':=⟨1,one_pos,Eventually.of_forall fun i=>by simp⟩
 add_mem':= by
  rintro a b ⟨C,hC,H⟩ ⟨D,hD,F⟩; exact ⟨C+D,by positivity,(H.and F).mono fun i hi=> le_trans (norm_add_le (a (f i)) _) (add_le_add hi.1 hi.2)⟩
 smul_mem':= by
  rintro r a ⟨C,hC,H⟩; refine ⟨1+‖r‖*C,by positivity, H.mono fun i hi=> ?_⟩; rw [LinearMap.smul_apply,norm_smul]; exact (mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans (le_add_of_nonneg_left zero_le_one)
private lemma ticket_price {f : ℕ→ Field4 G} (hr:r>0) (hp : Messed T r k f) (t : G.ColorIndex) (x : Cover) (i:Axis):
  let J := (innerSL ℝ (unitColor G t)).toLinearMap; let P:=fun v:ℕ=> (T.gap v^(k+2))⁻¹ • f v
  J.comp (quizL G x i) ∈ saleable P ∧ J.comp (quizD G x)∈ saleable P := by
  intro J P
  have he (l : Edge Cover) : (J.comp (sight4 l))∈ saleable P := by
    obtain ⟨C,hC,H⟩:=Messed.known _ hr hp l; refine ⟨1+‖unitColor G t‖ *C,by positivity,H.mono fun j hj=>?_⟩
    change ‖inner ℝ (unitColor G t) ((T.gap j^(k+2))⁻¹ • f j l)‖≤_; exact (abs_real_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left hj (norm_nonneg _)).trans (le_add_of_nonneg_left zero_le_one))
  constructor
  · unfold quizL; rw [show J.comp (∑ u:Axis,(sight4 (x+step u,i)+sight4 (x-step u,i)-(2:ℕ)•sight4 (x,i)))= _ from -- expected sum
          (show _ = ∑ u:Axis,(J.comp (sight4 (x+step u,i))+J.comp (sight4 (x-step u,i))- (2:ℝ) • J.comp (sight4 (x,i))) from LinearMap.ext (fun q=>by simp [two_smul ℝ, two_nsmul]))]
    apply Submodule.sum_mem; intro u _; exact Submodule.sub_mem _ (Submodule.add_mem _ (he _) (he _)) (Submodule.smul_mem _ _ (he _))
  unfold quizD; rw [show J.comp _ = ∑ u:Axis,(J.comp (sight4 (x,u))-J.comp (sight4 (x-step u,u))) from LinearMap.ext (fun q=> by simp)]
  apply Submodule.sum_mem; exact fun i _=> Submodule.sub_mem _ (he _) (he _)
lemma tuning (hp : Warrant T r k W) (hr : r>0) (hd : Echoes W) : ∃ Y:ℕ→ Nu G k,
    Messed T r k (fun i=> W i-(Y i).val) ∧
    Court (fun i=> (T.gap i^(k+2))⁻¹ • (planR k (W i) - (Submodule.inclusion cabin_stor) (Y i))) := by
  let M:=cabin G k; let N:=stor G k; let S : M →ₗ[ℝ] N := Submodule.inclusion cabin_stor
  obtain ⟨F,H⟩:=LinearMap.exists_leftInverse_of_injective S (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective _))
  let K:=LinearMap.id (R:=ℝ) (M:=↥N) - S.comp F
  have he (p : N)(h:p.val∈M): K p=0 := by
    let q:M:=⟨p.val,h⟩; have hQ:S q=p:=Subtype.ext rfl
    have hy:F (S q)=q:=by change F.comp S q=q; rw [H]; rfl
    simp only [K,LinearMap.sub_apply, LinearMap.comp_apply,LinearMap.id_apply,←hQ,hy,sub_self]
  let A:= fun i=>(T.gap i^(k+2))⁻¹ • planR k (W i)
  have hw:= initial_warrant W hp
  have hq : Court (fun i=> K (A i)) := by
    intro L
    let j t: G.Color→ₗ[ℝ] ℝ := (innerSL ℝ (unitColor G t)).toLinearMap; let T0 := Cover× (Option Axis) × G.ColorIndex
    let e : Option Axis→ Cover→ Field4 G→ₗ[ℝ] G.Color := fun a x=> match a with | none => quizD G x | some a=>quizL G x a
    let p (v:T0):↥N →ₗ[ℝ] ℝ := j v.2.2 ∘ₗ (e v.2.1 v.1 ∘ₗ N.subtype)
    change ∃ C>0,∀ᶠ i in atTop, ‖(L.comp K) (A i)‖ ≤ C
    apply subPrice p ?_
    · -- argument order infer?
      rintro ⟨x,v,t⟩; let f:=fun i=>W i-(planR k (W i)).val
      have hu : j t∘ₗ e v x∈ saleable (fun i=> (T.gap i^(k+2))⁻¹ • f i) := by cases v with | none=>exact (ticket_price hr hw t x 0).2 | some a=> exact (ticket_price hr hw t x a).1
      obtain ⟨C,hC,hb⟩:=hu; refine ⟨C,hC,?_⟩
      have hx : ∀ᶠ i in atTop,(e v x) (W i)=0 := by
        cases v with
        | none=> simp_rw [e,quizD_eq]; exact hd.tide x
        | some a=> simp_rw [e,quizL_eq]; exact hd.lune x _
      filter_upwards [hx,hb] with i hi hB
      let q := e v x
      change ‖j t (q (( (T.gap i^(k+2))⁻¹ :ℝ) • _))‖ ≤ _ at hB
      change ‖j t (q ((( (T.gap i^(k+2))⁻¹):ℝ) • (planR k (W i)).val))‖ ≤ _
      unfold f at hB; rw [q.map_smul,q.map_sub,hi,zero_sub, smul_neg, (j t).map_neg,norm_neg] at hB; rwa [q.map_smul]
    intro u hu
    have hz : u.val∈M := ⟨u.property, fun a=>funext fun x=> by
                                      apply ink_zero; intro t; rw [← quizL_eq]; exact hu ⟨x,some a,t⟩,
                                   funext fun x=> by
                                      apply ink_zero; intro t; rw [← quizD_eq]; exact hu ⟨x,none,t⟩⟩
    rw [LinearMap.comp_apply,he u hz,map_zero]
  let Y:=fun i=>F (planR k (W i)); let D i := planR k (W i) - S (Y i)
  unfold A at hq; simp only [map_smul] at hq
  refine ⟨Y,?_,hq⟩
  convert! plus_field _ _ hw (dress_charge D hq) using 1; funext i; change _-_=_-_+( (planR k (W i)).val-(Y i).val); abel
end YM.RG11.FirstW
