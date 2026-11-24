import YM.LocalLTE.Weft.Bloom
/-! Budget transport for stencil projections. Exact re-expression only at requested Laurent stubs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Mask Matter Coat Frond
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side}
open Fan Brush Foramen Pastel
variable {V v z r C w s t y η γ B a ε α κ K: ℝ} {j n m k N M : ℕ}
open Weft AnalyticBridge.VerifiedReset FrameBox Tensor
local notation "E"=> Directions G c
namespace Scene
variable {o:Site c} {X:Grove o}
lemma craneP (s:Seat c): ‖Hall.crane (G:=G) s.1 s.2‖≤1:= by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a=>?_; rw [one_mul]; refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i=>?_); rw [Hall.valCrane]; split
    · rw [norm_neg]; exact norm_le_pi_norm ..
    exact norm_le_pi_norm ..
lemma turning {f:ℝ→ Config G c→ℝ} (P:Scene X κ N j n f C)(h:Reliable G κ v)(s:Seat c): Scene (Hall.transplanted s.1 s.2 X) κ N j n (fun i=> f i ∘ s.view) C:=by
    refine ⟨P.price,Hex.invert (fun i=> P.weft.use _),fun i hi=> ?_⟩; let g:= Hall.crane (G:=G) s.1 s.2; obtain ⟨Q,hp,hF⟩:= P.plaque i hi
    simp_rw [hp]; refine ⟨_,Hall.packet s.1 s.2 X h _ Q,fun k=>?_⟩; rw [norm_smul]; apply le_trans (b:=‖i^k.val • Q k‖) _ (hF k); rw [norm_smul];
    exact mul_le_mul_of_nonneg_left ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le (Q k) (fun _=>g)).trans (mul_le_of_le_one_right (norm_nonneg _) (by simpa only [prod_const,card_univ,Fintype.card_fin] using pow_le_one₀ (norm_nonneg g) (craneP s) (n:=k.val)))) (norm_nonneg _)
lemma rhymed {f g:ℝ→ Config G c→ℝ} (P:Scene X κ N j n f C) (Q:Scene X κ N j n g V): Scene X κ N j n (fun t=> f t+g t) (C+V):=by
    refine ⟨add_nonneg P.price Q.price,P.weft.add Q.weft,fun s hs=> ?_⟩; obtain ⟨p,h₁,hF⟩:=P.plaque s hs; obtain ⟨q,h₂,hG⟩:= Q.plaque s hs; simp_rw [h₁,h₂]; refine ⟨p+q,funext fun i=>?_,fun i=>?_⟩
    · unfold FrameBox.realise; rw [Cabana.actual_add]; rfl
    simp only [Pi.add_apply,smul_add]; exact (norm_add_le ..).trans (add_le_add (hF i) (hG i))
lemma lyric {f g:ℝ→ Config G c→ℝ} (P:Scene X κ N j n f C) (Q:Scene X κ N j n g V): Scene X κ N j n (fun t=> f t-g t) (C+V):=by simpa only [sub_eq_add_neg,neg_one_smul,abs_neg,abs_one,one_mul] using P.rhymed (Q.scale X (-1)) -- edit
-- pad degree without changing scenes.M.Phase.Mixed. finite Power interpolation stamped.
lemma padding {f:ℝ→ Config G c→ℝ}(P:Scene X κ N j n f C) (he:n≤ M): Scene X κ N j M f C:=by
    induction he with
    | refl=> exact P
    | @step y hh ih=>
       refine ⟨P.price,P.weft,fun s hs=>?_⟩; obtain ⟨p,hv,h⟩:=ih.plaque _ hs
       let Q: Cabana.Pkt (Directions G c) (y+1) := fun i=> if hi:i.val<y then p ⟨i.val,hi⟩ else 0
       refine ⟨Q,hv.trans (funext fun v=>?_ ),fun i=>?_⟩
       · unfold FrameBox.realise Cabana.actual; rw [Fin.sum_univ_castSucc]; simp only [Finset.sum_apply,Pi.add_apply]; rw [show Tensor.diagonal (Q (Fin.last y)) (X.crook N Chi.canonical κ v)=0 from (by rw [show Q (Fin.last y)=0 from dif_neg (by simp)]; rfl),add_zero]; apply Finset.sum_congr rfl; intro i h; unfold Q; rw [dif_pos (by simp)]; rfl
       unfold Q; split; next hz=> exact h ⟨i.val,hz⟩
       simpa using! P.price
end Scene
section pay
open Extra.Iteration PhysicalNext.Repeat PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset.Collection.Price Progress.DirectedRecipe
lemma playsB {ι:Type} {k:ι→ℝ}{Q:ℝ}{p:BudgetPoint} (A:ι→ RegularAddress c) (h:Quotes.anchored p A k Q): Quotes.anchored p (revolve A) (fun i=> |Rim c| * k i.snd) Q:=by
   intro x; let d:= Rim c; have hQ:0 ≤ Q:= Cost.nonneg (h (0:Site c)); have hb:0≤d:= Song.rim_nn _; simp_rw [abs_of_nonneg (rim_nn c)];
   rw [show Q= (Fintype.card (Seat c):ℝ)*(Rim c*Q) by rw [← mul_assoc, Song.balance]; simp]; refine Cost.product (Cost.finite _ (by positivity : 0 ≤ d*Q)) fun i=>?_
   let y:= StepData.sendSites i.1 i.2
   have hu : ∀ j, affine i.1 i.2 j=x ↔ j=y.symm x:= fun j=> y.apply_eq_iff_eq_symm_apply
   have hh j : (revolve A (i,j)).site=x ↔ (A j).site = y.symm x := hu _
   have hv j : coverNumber p.B (revolve A (i,j)).support = coverNumber p.B (A j).support := Seat.visit_count i _
   convert (Cost.scale (h (y.symm x)) d hb) using 2 with r; simp only [hh,hv,BudgetPoint.mass]; split
   next=> unfold d; ring
   rw [mul_zero]
lemma witnessB {a : RegularAddress c}(A:Art a N)(s:Seat c) (y:RegularAddress c)(hs:y.site=affine s.1 s.2 a.site)(he:y.support=s.spread a.support) (f:ℝ→ Config G c→ℝ)(p:Scene A.grove κ A.radius j n f C)(hk:Reliable G κ v): Scene (A.turn s y hs he).grove κ (A.turn s y hs he).radius j n (fun i=> f i ∘ s.view) C:=by
    have ht (B:Site c) (hB:B=affine s.1 s.2 a.site) : let X:Grove B:=by rw [hB]; exact Hall.transplanted s.1 s.2 A.grove
                                          Scene X κ A.radius j n (fun i=> f i∘s.view) C:= by
       subst B; exact p.turning hk s
    exact ht y.site hs
end pay
end YM.LocalLTE.Weft
