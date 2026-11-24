import YM.LocalLTE.Weft.Arp
/-! Weft germs. Pointwise interpolation suffices. Avoids measure issues away from configurations admitted in profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Set Metric Function MeasureTheory Finset
open Tensor Analysis ConnectedActivityE6.Blaze
open scoped Topology BigOperators Classical ContDiff
variable {E F A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup A][NormedSpace ℝ A]
variable {k n m : ℕ} {C d v w :ℝ}
structure Warp (k j:ℕ) (C:ℝ)(f:ℝ→E→F) : Prop where
    hymn : ∃ g:ℝ→E→F, Arp k j C g∧∀ s∈clip,f s=ᶠ[𝓝 0]g s
lemma Arp.opening {u:E→F}(hP:Brush k C 1 u 0)(h:u 0=0) {s:ℝ}(hs:s∈clip) : Brush k C 1 (fun x:E=> s⁻¹ • u (s • x)) 0:= by
    have he: Null 1 k u := by
       intro i _ hi; obtain rfl:= Nat.eq_zero_of_le_zero (show i≤0 by omega)
       apply norm_le_zero_iff.mp; rw [norm_iteratedFDeriv_zero,h,norm_zero]
    simpa only [pow_one] using! ((Arp.reduced (h:=hP) he).brush s hs)
variable {f g : ℝ→E→F}
lemma Arp.warp (h: Arp k n C f): Warp k n C f:= ⟨f,h,by simp⟩
lemma Arp.splice {u:A→E}(hp:u 0=0)(h:Arp k m C f)(he:Brush m d 1 u 0): Arp k m ((m.factorial:ℝ)*C*(1+(1+d)*1)^m) (fun s=> f s ∘ u):= by
   refine ⟨Hex.invert (fun i=> (h.hex.use (u i))), fun s hs=> ?_⟩
   let g(i:A):=s⁻¹ • u (s • i); let F(i:E):= f s (s • i); have hv:g 0=0:=by unfold g; rw [smul_zero,hp,smul_zero]
   have hf:= (Arp.opening he hp hs).pine (show Brush m C 1 F (g 0) from (by rw [hv]; exact h.brush s hs))
   exact hf.trim.shimmy (Eventually.of_forall (fun i=> congr_arg (f s) (smul_inv_smul₀ hs.1.ne' _).symm))
namespace Warp
lemma define (h:Arp k n C g)(he:∀ i∈clip,f i=ᶠ[𝓝 0]g i): Warp k n C f:= ⟨g,h,he⟩
lemma spoken (h:∀ i∈clip, f i=ᶠ[𝓝 0] (∑ j,mark k j i • pick k f j))(he:∀ s∈clip, Brush n C 1 (f s ∘ orb s) 0): Warp k n C f:=by
   let g s:= (∑ j,mark k j s • pick k f j);
   refine ⟨g, ⟨⟨pick k f,fun _ _=> rfl⟩,fun i hi=> (he i hi).shimmy ?_⟩,h⟩
   have hv:Tendsto (orb (E:=E) i) (𝓝 0) (𝓝 0):=by
      simpa using! ((orb (E:=E) i).continuous.tendsto 0)
   exact (h i hi).symm.comp_tendsto hv
lemma grow (h:Warp k n C f)(he:k≤ m)(hp:C≤ d): Warp m n d f:= by
   obtain ⟨g,H,ht⟩:=h.hymn; exact ⟨g,H.climb he hp,ht⟩
lemma sumQ {ι:Type*}(S:Finset ι) (F:ι→ℝ→E→F)(C:ι→ℝ)(h:∀ i∈S, Warp k n (C i) (F i)): Warp k n (∑ i∈S,C i) (fun s=> ∑ i∈S,F i s):=by
   induction S using Finset.induction_on with
   | empty=> exact Arp.zero'.warp
   | insert i S hi ih=>
      simp_rw [Finset.sum_insert hi]; obtain ⟨u,hA,hu⟩:= (h i (mem_insert_self ..)|>.hymn); obtain ⟨w,H,hw⟩:= (ih fun j hj=> h j (mem_insert_of_mem hj)).hymn;
      exact ⟨fun s=>u s+w s,((hA.sumAdd H).climb (max_eq_left le_rfl|>.le) le_rfl),fun i hp=> (hu i hp).add (hw i hp)⟩
lemma smul (h:Warp k n C f)(s:ℝ): Warp k n (|s| *C) (fun i=> s • f i):=by
   obtain ⟨g,H,ht⟩:=h.hymn; exact ⟨fun i=>s • g i,H.scales _,fun i hi=> (EventuallyEq.refl (f:=fun _:E=>s) _).smul (ht i hi)⟩ -- edit
omit [NormedAddCommGroup A][NormedSpace ℝ A] in
lemma ballads (S:Finset A) {u:A→ℝ→E→ℝ}{C:A→ℝ}(h:∀ i∈S,Warp k n (C i) (u i)): Warp (k*S.card) n ((∏ i∈S,C i)*(1+(S.card:ℝ))^n) (fun s x=>∏ i∈S,u i s x):=by
    let I:= S.attach; choose f H hp using fun i:S=> h i i.2|>.hymn
    have he : Arp (k*I.card) n ((∏ i∈I,C i.val)*(1+(∑ _i∈I,(1:ℝ)))^n) (fun s x=>∏ i∈I,f i s x):= by
       refine (⟨Hex.invert (fun _=> Hex.product (k:=k) I (fun i _=> (H i).hex.use _)),fun i hi=> (Brush.trim (Brush.all_prod I _ (fun i=>C i.val) (fun _=>1) (fun j hj=>H j|>.brush _ hi)))⟩: Arp (k*I.card) n ((∏ i∈I,C i.val)*(1+(∑ _i∈I,(1:ℝ)))^n) (fun s x=> ∏ i∈I, f i s x)) -- edit
    simp only [I, Finset.prod_attach,Finset.card_attach,sum_const,nsmul_eq_mul,mul_one] at he
    refine Warp.define he fun s hs=> ?_
    filter_upwards [eventually_all.mpr (fun i=> hp i s hs)] with i hi; rw [← Finset.prod_attach]; exact prod_congr rfl fun i _=> hi i
section
variable [FiniteDimensional ℝ E] {Ω:Type} [MeasurableSpace Ω] {μ:Measure Ω}[IsProbabilityMeasure μ]{φ:ℝ→E→Ω→ℝ}
lemma load (h:∀ i:Ω,Arp k n C (fun s x=> φ s x i))(hd:∀ s∈clip, ∃ B:ℝ,∀ᶠ y in 𝓝 0,∀ i, Brush n B 1 (fun x=> φ s x i) y)
    (hm:∀ s∈clip,∀ᶠ y in 𝓝 0,Measurable (φ s y)): Warp k n C (fun (s:ℝ) (x:E)=>∫ u,φ s x u ∂μ):=by
   let A s x:=∫ u,φ s x u ∂μ
   let r i:=probe k i
   have hp s (hs:s∈clip): Meristem (φ s) 0 μ n∧∀ᶠ y:E in 𝓝 0, Integrable (φ s y) μ:= by
      obtain ⟨B,hB⟩:= hd _ hs; exact Meristem.points _ _ ⟨_,integrable_const B,hB⟩ (hm _ hs)
   refine Warp.spoken (f:=A) (fun s hs=> ?_) (fun s hs=> ?_)
   · apply Filter.Eventually.mp (eventually_all.mpr (fun i=> hp _ (probes k i)|>.2)|>.and (hp _ hs).2)
     refine Eventually.of_forall fun x ⟨hg,hx⟩=> ?_
     let f i:= φ i x; have hv (i:J k): Integrable (pick k f i) μ:= integrable_finsetSum' _ (fun j _=> (hg j).smul (slate k j i))
     have he: Hex k f := Hex.invert (fun i => (h i).hex.use x)
     have ht i: ∫ j,pick k f i j ∂μ= pick k (fun s=> A s x) i:=by
        unfold pick; simp_rw [Finset.sum_apply]; rw [integral_finsetSum]; simp_rw [Pi.smul_apply, smul_eq_mul, integral_const_mul]; rfl; exact fun i _=> (hg i).smul (slate k i _)
     change (∫ i,f s i ∂μ)=(∑ i,mark k i s • pick k A i) x; rw [he.seen hs, Finset.sum_apply]; simp_rw [Finset.sum_apply,Pi.smul_apply]; rw [integral_finsetSum]; simp_rw [integral_smul,ht,calcK]; exact fun i _=> (hv i).smul (mark k i s)
   -- For Arp: s>0 fixed implies near-zero bounds on scaled F factored using orb_cost. Doesn't need uniform open B across s.
   obtain ⟨B,hg⟩:= hd _ hs
   let F(x:E):= φ s (orb s x); have he : ‖orb (E:=E) s‖≤1:= by unfold orb; rw [norm_smul,Real.norm_of_nonneg hs.1.le]; exact mul_le_one₀ hs.2 (norm_nonneg _) ContinuousLinearMap.norm_id_le
   have hp:Tendsto (orb (E:=E) s) (𝓝 0) (𝓝 0) := by simpa using! ((orb (E:=E) s).continuous.tendsto 0) -- edit
   have hx : ∀ᶠ y in 𝓝 (0:E),∀ i,Brush n B 1 (fun x=>F x i) y:=by
       filter_upwards [hp.eventually hg] with y hy i; have ht:= Brush.reading (orb s) (hy i) he; rw [one_mul] at ht; exact ht
   exact ((Meristem.points F μ ⟨_,integrable_const B,hx⟩ (hp.eventually (hm _ hs))).1.buds (fun _=> C) (integrable_const C) zero_le_one (by simp) (ae_of_all _ fun i=> (h i).brush s hs))
end
end Warp
end YM.LocalLTE.Weft
