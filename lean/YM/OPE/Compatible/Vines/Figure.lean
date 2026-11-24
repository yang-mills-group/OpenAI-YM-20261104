import YM.OPE.Compatible.Vines.Taffy
/-! Template finite pilot -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{V W I T:Type*}{G:Gauge}
namespace Script
open Page
abbrev Realm {X Y Z:Type*} (f:(X→Y)→Z) :Prop:=∃ s:Finset X,∀ v w, Set.EqOn v w s→ f v=f w
lemma realms {I:Type*}{Y:I→Type*}[Fintype I] {f:∀ i:I, W→Y i}{X:(T→V)→W}(h:∀ i,Realm (f i ∘ X)):Realm fun t i=> f i (X t):=by -- J unused
    choose p hp using h; refine ⟨univ.biUnion p, fun v w he=> funext fun i=>?_⟩; exact hp i _ _ (he.mono fun x (h: x∈p i)=> mem_biUnion.mpr ⟨i,mem_univ _,h⟩)
lemma realmSub [AddCommGroup W] {f g:(I→V)→W}(h:Realm f)(hp:Realm g):Realm (f-g):=by obtain ⟨s,h⟩:=h; obtain ⟨t,hp⟩:=hp; exact ⟨s∪t,fun v w he=> by rw [Pi.sub_apply,Pi.sub_apply,h _ _ (he.mono fun i hi=>Finset.mem_union_left _ hi),hp _ _ (he.mono fun i hi=>Finset.mem_union_right _ hi)]⟩
lemma realmMap {Y:Type*} {f:(I→V)→W} (h:Realm f)(g:W→Y):Realm (g∘f):=by obtain ⟨s,h⟩:=h; exact ⟨s,fun v w he=>congr_arg g (h v w he)⟩
lemma realmHeal (x:Cover) (i:Axis): Realm fun t=> heal G i t x:=by
    refine ⟨univ.image (fun j: G.ColorIndex=> (x,i,j)),fun v w h=>?_⟩; ext j; exact h (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
lemma realmTrain [AddCommGroup W][Module ℝ W]{Y:(I→V)→(Cover→W)}(h:∀ i, Realm fun q=> Y q i)(p:Fin d→Axis)(v:Cover): Realm fun t=> trainX W d p (Y t) v:=by
    induction d generalizing Y with
    | zero=> exact h v
    | succ d ih=> exact ih (Y:=fun t=>movesX W (p 0) (Y t)) (fun i=>realmSub (f:=fun t=>Y t (i+step _)) (g:=fun t=>Y t i) (h _) (h _)) _
lemma realmBase :Realm (templateX G d):=by
   let h (i:Axis)(x:Cover)(u:fieldX (Shade G)):= heal G i u x
   have he(x:Cover)(i j:Axis):Realm (fun t=> movesX _ i (heal G j t) x):=realmSub (f:=h j (x+step i)) (realmHeal _ _) (realmHeal _ _)
   suffices H:Realm (slopeH G d) from realmMap H (fun v=>YM.Pert.Bare.radialize v)
   let f:fieldX (Shade G)→ YM.Pert.Bare.Response G d:=slopeH G d; apply realms (I:=Axis) (f:=fun i (Y:YM.Pert.Bare.Response G d)=> Y i) (X:=f)
   intro i; apply realms (I:=Axis) (X:=f) (f:=fun j (y:YM.Pert.Bare.Response G d)=> y i j)
   intro j; apply realms (I:=Fin d→Axis) (X:=f) (f:=fun k (y:YM.Pert.Bare.Response G d)=>y i j k)
   intro k; have hT(x:Cover): Realm fun q=> curve G i j q x:=realmSub (he x i j) (he x j i); exact realmMap (realmTrain hT k 0) (fun v=> (d.factorial:ℝ)⁻¹ • v)
-- With controlled linear projections, any tensor value is realized as finite script
abbrev Brief (p:Script T r):Prop:=∃ s:Finset (Page T r),∀ i,i∉s→p i=0
lemma script_forms (L:MultilinearMap ℝ (fun _:Fin r=>fieldX T) ℝ)
   (s:Finset (Cover×T))(h:∀ (v w:Fin r→fieldX T),(∀ i,EqOn (v i) (w i) s)→ L v=L w):
   ∃ p:Script T r,Brief p ∧ wholeX p=L:=by
       let S:= Fintype.piFinset fun _:Fin r=> s; let z(j:Cover×T):fieldX T:= Pi.single j 1; let k(y:Page T r):= L fun i=>z (y i); let p(y):=if y∈S then k y else 0
       refine ⟨p,⟨S,fun j hj=> if_neg hj⟩,funext fun v=>?_⟩; let V(i:Fin r):fieldX T:=∑ j∈s, v i j • z j; unfold wholeX; rw [tsum_eq_sum (s:=S)]; swap; · exact fun j hj=>by simp [p,hj]
       rw [show L v=L V from h v V (fun i u (hu:u∈s)=>by unfold V; rw [Finset.sum_apply,sum_eq_single u]; simp [z]; exact (fun b _ hb=> by simp [z,Ne.symm hb]);exact fun hx=>False.elim (hx hu))]; unfold V; rw [L.map_sum_finset]; refine sum_congr rfl fun i hi=>?_ ; rw [L.map_smul_univ]; rw [show p i=k i from if_pos hi]; exact mul_comm ..  -- elaboration
lemma briefFee {p:Script T r}(h:Brief p) (m:ℕ):∃ c, soot m p c:=by
    obtain ⟨s,h⟩:=h; exact ⟨_,fun i=>mul_nonneg (zero_le_one.trans (payer m _)) (norm_nonneg _),summable_of_ne_finset_zero (s:=s) (by intro j hj; rw [h j hj,norm_zero,mul_zero]),le_refl _⟩
end Script
end YM.OPE.Flume
