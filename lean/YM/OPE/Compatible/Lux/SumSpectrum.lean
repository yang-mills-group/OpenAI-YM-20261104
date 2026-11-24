import YM.OPE.Compatible.Lux.Weighted
/-!
# Whole signed scores, phase bounds for weighted inputs
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Display
open Function Set Filter Table MeasureTheory Survey
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
   {P : DiffPlan S} {R : S.Rotation} {ρ : S.RealSpin} {l B J : Type}[Fintype B][Fintype J]{φ:Filter l}{T t:l→ℝ}
   {K:B→Type}[∀ b,Fintype (K b)]{y:l→E4}
variable {x:∀ b,l→K b→E4}{p:∀ b,l→K b→ S.Tag}{a:B→l→ℂ}{d:ℕ}
variable (ht:Tendsto T φ atTop)(hu:∀ᶠ i in φ, 0 ≤ t i)
include ht hu
lemma extendList (H:Fits K y x φ)(h: ∀ (X:Type)[Fintype X] (w:X→ S.Tag)(u:l→ X→E4){c:ℝ},0<c→ (∀ᶠ i in φ,ClearOf (y i) (u i) c)→ PaidWeight φ T t (fun i=>∑ b,a b i * kernel S (beside (x b i) (u i)) (beside (p b i) w))) (d:ℕ): PaidWeight φ T t (fun i=>∑ b, a b i • ray U d (x b i) (p b i) (y i)):=by
   let A b i:=(t i:ℂ)*a b i
   have hQ:SharpProbes K y x p A φ T:=by
       constructor; intro X _ w u c hc hv; refine ((PaidWeight.ascaled hu).1 (h X w u hc hv)).congr ?_; filter_upwards with i; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun b _=> ?_; unfold A; rw [mul_assoc]; rfl
   apply (PaidWeight.ascaled hu).2; refine (possess K y x p A ht H hQ U.phase.transport.spots U.room.kernel (supplies S) d).congr ?_; filter_upwards with i; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun b _=>?_ ; exact mul_smul ..
-- absorb one vector
lemma approximate {I:Type}[F_:Fintype I]{p:l→ I→ S.Tag}{q:l→ S.Field d}{x:l→ I→ E4}
   (he:Tendsto (fun i=> away (x i) (y i)) φ (𝓝 0)) (hs:∀ᶠ i in φ,Injective (x i))
   (hf:∀ (X:Type)[Fintype X] (w:X→ S.Tag)(u:l→ X→ E4){c:ℝ},0<c→(∀ᶠ i in φ, ClearOf (y i) (u i) c)→ PaidWeight φ T t (fun i=>kernel S (beside (x i) (u i)) (beside (p i) w)- Cov.insert S S (y i) (u i) w d (q i))) : PaidWeight φ T t (fun i=> ray U d (x i) (p i) (y i)-q i):=by
    let K:Unit⊕Unit→ Type:= Sum.elim (fun _=>I) (fun _=> Unit); let v(j:l)(i:Unit): S.Tag := ⟨d,q j⟩
    let a:∀ b:Unit⊕Unit,l→ K b → E4:= Sum.rec (fun _=> x) (fun _ j=> sole (y j)); let A:∀ b:Unit⊕Unit,l→ K b→ S.Tag:= Sum.rec (fun _=> p) (fun _=> v); let b : Unit⊕Unit→ l→ℂ:=Sum.elim (fun _ _=>1) (fun _ _=> -1)
    let Ft : Fintype Unit:=inferInstance; letI : ∀ i,Fintype (K i) := Sum.rec (fun _=> F_) (fun _=>Ft)
    have h : Fits K y a φ:=by
        constructor
        · rintro (v|v); exact he
          refine tendsto_const_nhds.congr fun i=>?_ ; exact funext fun _=> (sub_self (y i)).symm
        rintro (v|v); exact hs; exact Eventually.of_forall fun i=> injective_of_subsingleton (sole (y i))
    refine PaidWeight.alter (extendList U (a:=b) (p:=A) ht hu h ?_ d) ?_
    · intro X _ w u c hc hw; refine (hf X w u hc hw).alter ?_; filter_upwards [Fits.separated _ _ _ h (.inr ()) u hc hw] with i hi; rw [Fintype.sum_sum_type,Fintype.sum_unique,Fintype.sum_unique]; change _=1 * _ + -1* kernel S (beside (sole (y i)) (u i)) (beside (sole (⟨d,q i⟩:S.Tag)) w)
      rw [insert_apply S U.room.kernel.laws.toSymmetric (fun _=>le_rfl) (y i) (u i) w d (q i) hi]; simp only [one_mul, neg_mul, sub_eq_add_neg]; try rfl
    filter_upwards with i; rw [Fintype.sum_sum_type,Fintype.sum_unique,Fintype.sum_unique]; change (1:ℂ) • ray U _ (x i) _ _ + (-1:ℂ) • ray U _ (sole (y i)) (sole (⟨d,q i⟩:S.Tag)) (y i) = _
    unfold ray; rw [show away (sole (y i)) (y i)=sole 0 from funext fun _=> sub_self _,ascend_fix _ U.phase.transport.spots U.room.kernel U.phase.transport.motion]; simp [sub_eq_add_neg,A] -- caution lambda
lemma adj_cost (H:Services C F S) [φ.NeBot]{v:l→ S.Field d}(w:J→ S.Tag)(r:l→ Viewers U) (u:l→J→E4) {δ:ℝ}(hc:0<δ)(h:∀ᶠ i in φ,ClearOf (y i) (u i) δ)(hf:PaidWeight φ T t v) : PaidWeight φ T t (fun i=> Cov.insert S (spectator U (r i)) (y i) (u i) w d (v i)):=by
   have hv := Real.tendsto_log_atTop.comp ht; obtain ⟨hw,hb⟩:= free_clear hv hc h; obtain ⟨k,hp⟩:= (PaidWeight.ascaled hu).1 hf
   apply (PaidWeight.ascaled hu).2; refine ⟨_, (count_insert U H hv _ _ w r hb le_rfl hw le_rfl hp).congr ?_⟩; filter_upwards with i; exact map_smul _ _ _
end YM.OPE.Cov.Display
