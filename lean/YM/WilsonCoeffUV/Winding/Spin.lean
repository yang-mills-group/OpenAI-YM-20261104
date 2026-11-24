import YM.WilsonCoeffUV.Winding.Wreath
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Mer Wheel Wheel.Mark Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type}{G:Gauge}{D:ι→ℕ}{i j k r e a l:ℕ}{s A B C W t q :ℝ}
variable {J I S:Finset ι}{p:ι→Cover}{x:ι}[NormedAddCommGroup V][NormedSpace ℝ V]
omit [NormedSpace ℝ V] in
lemma grapple_more {F:canal U α β V k r}{p:ι→U}{d:Bank.Distance U}(h:Grapple d p s A J F)(v:A≤ B): Grapple d p s B J F:=⟨h.1.trans v,fun i j=>(h.2 i j).trans (mul_le_mul_of_nonneg_right v (by positivity))⟩
lemma beamMany (x:dock Cover α k)(y:dock Cover β j): course Bank.terrain x y≤ billow Bank.terrain p J x y:=by apply reachL; rintro (i|i); exacts [⟨.inl (.inr i),rfl⟩,⟨.inr i,rfl⟩]
lemma bandRise (x:dock Cover α k)(y:dock Cover β r)(h:J⊆ S){z:dock Cover β l}(p':∀ i,∃ j, (z i).1=visitN p S x y j) : Syn Bank.terrain p J z≤billow Bank.terrain p S x y:=by apply reachL; rintro (i|i); exacts [⟨.inl (.inl ⟨i.val,h i.property⟩),rfl⟩,p' i]
lemma bandBase (x:dock Cover α k)(y:dock Cover α r)(i)(b:J⊆ S)(f:Fin l→Fin k): Syn Bank.terrain p J (Fin.cons (y i) (x ∘ f)) ≤ billow Bank.terrain p S x y:= bandRise x y b (fun u=> Fin.cases ⟨.inr i,rfl⟩ (fun j=>⟨.inl (.inr (f j)),rfl⟩) u)
omit [NormedSpace ℝ V] in
lemma MarkU.pore {F: Ten V (Cloth α) k}{Q:Ten V (Co n α) k}(p':MarkU p J Q F s A)(v:0≤s)(x)(h:4*Syn Bank.terrain p J x<n.val):Pore (Q (slideC n x)) (F x) A A (catchW s n):= ⟨(p'.bill.2 _).trans (mul_le_of_le_one_right p'.bill.1 (catch_peak v _)),(p'.access.2 _).trans (mul_le_of_le_one_right p'.access.1 (catch_peak v _)),p'.gulf.local_w _ h⟩
lemma MarkC.trawl {M:ropes (Site n) α β}{T:ropes Cover α β}{F:Ten V (Cloth α) k}{Q: Ten V (Co n α) k}(h:MarkU p J Q F s A)(g:Rail M T s B)(x:0≤s): MarkC p J (gloss M Q) (gloss T F) s ((k+1:ℕ)*B^k*A):=by
    have hp:= rub_eye B A k g.berth.1 h.bill.1
    refine ⟨grapple_more (motionNp g.berth h.access x) hp,grapple_more (motionNp g.bow h.bill x) hp,⟨(motionNp g.berth h.access x).1.trans hp,?_⟩⟩; rintro ⟨y,z⟩ v
    have hu :4*course Bank.terrain y z<n.val:= vn (beamMany y z) v
    have he (i: Fin k): Pore (M (slideC n z i) (slideC n y i)) (T (z i) (y i)) B B (catchW s n):= Pore.rails g x (vn (vPulse (x:=y) (y:=z)) hu)
    have hh:= ((Pore.prod _ (fun i (_:i∈Finset.univ)=> he i)).mu (h.pore x z (vn (bandRise (z:=z) y z (le_refl J) (fun j=>⟨.inr j,rfl⟩)) v))).gap
    apply hh.trans_eq; simp only [Finset.card_univ,Fintype.card_fin]; push_cast; ring
section
variable {M:ropes (Site n) α α}{T:ropes Cover α α}{F:Gen V (Cloth α)}{Q: Gen V (Co n α)}{Z:Gen ℝ (Co n α)}{Y:Gen ℝ (Cloth α)}
lemma MarkC.wet (p':Rail M T s A)(h:MarkU p J (Q (r+2)) (F (r+2)) s B)(v:0≤s): MarkC p J (rain M Q r) (rain T F r) s (ore r (r+1)*2*A*B):=by
   let C:= A*B* (sealM r (r+1)); have hp:0≤ C:= (grassyRain (P:=Q) p'.bow h.bill v).1; have hx: C+C=ore r (r+1)*2*A*B:=by unfold ore C sealM; push_cast; ring
   refine ⟨grapple_more (grassyRain p'.berth h.access v) ((le_add_of_nonneg_right hp).trans_eq hx), grapple_more (grassyRain p'.bow h.bill v) ((le_add_of_nonneg_right hp).trans_eq hx),⟨(add_nonneg hp hp).trans_eq hx,?_⟩⟩
   rintro ⟨x,y⟩ u; change ‖rain M Q r (slideC n x) (slideC n y)-rain T F r x y‖ ≤ _; simp_rw [rain_spell]; have hy:= Pore.rails p' v (x:=y 0) (y:=y 1) (vn ((vLine (x:=x) (y:=y)).trans (beamMany x y)) u); let W : dock Cover α (r+2):= Fin.cons (y 1) (Fin.cons (y 0) x); have hh:= h.pore v W (vn (bandRise (z:=W) x y (le_refl J) fun i=> ?_) u)
   swap
   · refine Fin.cases ⟨.inr 1,rfl⟩ (fun i=> Fin.cases ⟨.inr 0,rfl⟩ (fun j=>⟨.inl (.inr j),rfl⟩) i) i
   have hv:= ((hy.joinEye (r+1) (r+2)).mu hh).gap; unfold W at hv; rw [slideC,← comps_head,←comps_head] at hv; apply hv.trans_eq; unfold ore; push_cast; ring
lemma MarkC.rillL (p':Rail M T s A)(h:MarkU p J (Q (j+1)) (F (j+1)) s C)(g:Sight (Z (i+1)) (Y (i+1)) s B)(v:0≤s): MarkC p J (rill M Z Q (i+j) i j) (rill T Y F (i+j) i j) s (ore i j*3*A*B*C):=by
   have he:=g.aim; rw [pruce_down] at he; let K:= sealM i j*A*B*C; have hp:0≤ K:=(grassyFlow (P:=Z) (Q:=Q) p'.bow he h.bill v).1; have hx: K+(K+K)=ore i j*3*A*B*C:=by unfold ore K sealM; ring
   refine ⟨grapple_more (grassyFlow p'.berth g.bound h.access v) ((le_add_of_nonneg_right (add_nonneg hp hp)).trans_eq hx), grapple_more (grassyFlow p'.bow he h.bill v) ((le_add_of_nonneg_right (add_nonneg hp hp)).trans_eq hx), ⟨(add_nonneg hp (add_nonneg hp hp)).trans_eq hx,?_⟩⟩; rintro ⟨x,y⟩ u; change ‖rill M Z Q (i+j) i j (slideC n x) (slideC n y) - rill T Y F _ i j x y‖≤ _; simp_rw [rill_spell]; have hf:4*course Bank.terrain x y<n.val:= vn (beamMany x y) u
   have hy:= Pore.rails p' v (x:=y 0) (y:=y 1) (vn vLine hf); have hh:= Pore.ten g v _ (vn (reach_head x y (Fin.castAdd j) 0) hf); have hg:= h.pore v _ (vn (bandBase x y 1 (le_refl J) (Fin.natAdd i)) u); have hv:= (((hy.joinEye (i+1) (j+1)).mu hh).mu hg).gap; simp_rw [slideC,←comps_head] at hv; apply hv.trans_eq; unfold ore; ring

variable [DecidableEq ι]
lemma Pore.joins {x y:Pen D J}{z w:Pen D (S\J)}(b:J⊆ S)(h:Pore x y A B q)(p:Pore z w C W q): Pore (joinL b D x z) (joinL b D y w) (A*C) (B*C+A*W) q:=by
   have H (x:Pen D J)(y):‖joinL b D x y‖≤ ‖x‖*‖y‖:=by rw [waveJoy]; exact joy_norm ..
   have ha:= (norm_nonneg _).trans h.nearC
   refine ⟨(H x z).trans (mul_le_mul h.nearC p.nearC (norm_nonneg _) ha),(H ..).trans (mul_le_mul h.farC p.farC (norm_nonneg _) ha),?_⟩; let f:= joinL b D
   have he: f x z-f y w= f (x-y) z+f y (z-w):=by simp only [map_sub,_root_.sub_apply]; abel
   change ‖f x z-f y w‖≤_; rw [he]; apply (norm_add_le ..).trans; rw [add_mul,mul_right_comm B C q,mul_assoc A W q]; exact add_le_add ((H ..).trans (mul_le_mul h.gap p.nearC (norm_nonneg _) ((norm_nonneg _).trans h.gap))) ((H ..).trans (mul_le_mul h.farC p.gap (norm_nonneg _) ha))
lemma MarkC.cluster {F:Gen (Pen D J) (Cloth α)}{Q: Gen (Pen D J) (Co n α)}{Z:Gen (Pen D (S\J)) (Co n α)}{Y:Gen (Pen D (S\J)) (Cloth α)}(p':Rail M T s A)(b:J⊆ S)(h:MarkU p J (Q (i+1)) (F (i+1)) s B)(g:MarkU p (S\J) (Z (j+1)) (Y (j+1)) s C)(v:0≤s) : MarkC p S (lakeL M b Q Z (i+j) i j) (lakeL T b F Y (i+j) i j) s (sealM i j*3*A*B*C):=by
   let K:= sealM i j*A*B*C; have hp:0≤ K:=(grassyLeaf (P:=Q) (Q:=Z) b p'.bow h.bill g.bill v).1; have hx: K+(K+K)=sealM i j*3*A*B*C:=by unfold K; ring
   refine ⟨grapple_more (grassyLeaf b p'.berth h.access g.access v) ((le_add_of_nonneg_right (add_nonneg hp hp)).trans_eq hx),grapple_more (grassyLeaf b p'.bow h.bill g.bill v) ((le_add_of_nonneg_right (add_nonneg hp hp)).trans_eq hx), ⟨(add_nonneg hp (add_nonneg hp hp)).trans_eq hx,?_⟩⟩; rintro ⟨x,y⟩ u; change ‖lakeL M b Q Z _ i j (slideC n x) (slideC n y) - lakeL T b F Y _ i j x y‖ ≤ _; simp_rw [lakeV]
   have hy:= Pore.rails p' v (x:=y 0) (y:=y 1) (vn ((vLine (x:=x) (y:=y)).trans (beamMany x y)) u); have hU:= h.pore v _ (vn (bandBase x y 0 b (Fin.castAdd j)) u); have hV:=g.pore v _ (vn (bandBase x y 1 Finset.sdiff_subset (Fin.natAdd i)) u); have hv:= (((Pore.ice (sealM i j) (by unfold sealM; positivity)).mu hy).mu (hU.joins b hV)).gap; simp_rw [slideC,←comps_head] at hv; apply hv.trans_eq; ring
end
lemma swing (d:Bank.Distance U)(p:ι→U)(x:dock U α i)(y:dock U β j)(S:Finset ι)(g : Equiv.Perm (Fin i)): billow d p S (x ∘ g) y=billow d p S x y:=by
      let W:= ((Equiv.refl S).sumCongr g).sumCongr (Equiv.refl (Fin j)); have he: visitN p S (x ∘ g) y = visitN p S x y ∘ W:= funext fun v=>by cases v with | inr i=> rfl | inl i=> cases i <;> rfl
      unfold billow; rw [he,league_equiv]
lemma MarkC.swings {P:canal (Site n) α α V 2 k}{G:canal Cover α α V 2 k}(h:MarkC p J P G s A): MarkC p J (swivel P) (swivel G) s A:=by
    refine ⟨h.access.spin,h.bill.spin,⟨h.bill.1,?_⟩⟩; rintro ⟨x,y⟩ u; change ‖swivel P (slideC n x) (slideC n y) - swivel G x y‖ ≤ _
    have he (i:Equiv.Perm (Fin k)): ‖P (slideC n x ∘ i) (slideC n y)- G (x ∘ i) y‖ ≤ _:= h.gulf.local_w (x ∘ i,y) (by change 4*billow _ _ _ _ _<_; rw [swing]; exact u)
    let v:ℝ:= Fintype.card (Equiv.Perm (Fin k)); have hp:0<v:=by unfold v; positivity
    simp only [swivel,Pi.smul_apply,Finset.sum_apply,← smul_sub,norm_smul]; apply le_trans (mul_le_mul_of_nonneg_left (spin_floor (ι:=Equiv.Perm (Fin k)) (f:=fun i=>P (slideC n x ∘ i) _) (g:=fun i=> G (x ∘ i) y) (S:=Finset.univ) (fun i _=>he i)) (norm_nonneg _)); rw [Finset.card_univ]; change ‖v⁻¹‖*(v*_ )≤_; rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),inv_mul_cancel_left₀ hp.ne']
end YM.WilsonCoeffUV.Winding
