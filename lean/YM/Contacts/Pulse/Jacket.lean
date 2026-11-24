import YM.Contacts.Pulse.Sow
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration Quill
open scoped Classical Topology BigOperators NNReal ENNReal
noncomputable section
variable {α β X Y Z : Type}{L:Side}{k n t:ℕ} {C D:ℝ} {η δ σ:ℝ≥0}
def graphE (α:Type) (t:ℕ): (Breed t α×Cover)×Tailor t≃ Breed t (Node α) where
  toFun p:= publish p.1.2 p.1.1 p.2
  invFun x:=((alphabet x,(x 0).1),degree x)
  left_inv | ⟨⟨a,b⟩,z⟩=> Prod.ext (Prod.ext rfl (by simp [publish,legLane])) (deg_issue ..)
  right_inv x:= retrieve x
def locket (α:Type)(y:α): Locked α (0:Fin (t+1)) y≃(Fin t→α) where
  toFun z:= Fin.tail z.val
  invFun q:=⟨Fin.cons y q,rfl⟩
  left_inv z:= Subtype.ext (by exact funext (fun i=> Fin.cases (show Fin.cons y (Fin.tail z.val) 0=z.val 0 from z.property.symm) (fun j=> rfl) i))
  right_inv q:= by simp
lemma monoTerrace {n k:ℕ} (h: n≤k)(hz:η≤σ) [Fintype Z](x:Z→Node α) : (bath η n α).bill x ≤ (bath σ k α).bill x:= by
  refine (bath η n α).wide x ((bath σ k α).one_bill x) fun i j=>?_ ; apply le_trans _ ((bath σ k α).width _ i j); change Real.exp _* (1+_)^_ ≤ Real.exp _*(1+_)^_; gcongr; simp
lemma bath_terrace [Fintype Z](x:Z→Node α): (terrain η α).bill x≤ (bath η k α).bill x:= (terrain η α).wide x ((bath η k α).one_bill x) fun i j=> le_trans (show _≤(bath η k α).step (x i) (x j) from le_mul_of_one_le_right (Real.exp_pos _).le (one_le_pow₀ (by simp))) ((bath η k α).width x i j)
lemma faded {G:X→Y→ℝ}{T:X→Y→ℝ} (h: Weirs T G C D)(he:∀ x y,1≤ T x y): Weirs (fun _ _=>1) G C D := by simpa only [one_mul] using Weirs.coupons (v:=fun _ _=>1) h (d:=1) (by norm_num) (fun _ _=>zero_le_one) (by simpa only [one_mul] using he)
  
lemma monochrome (l:Range X) (α:Type) : Ripple l (Range.cheap α) (fun _ _=>1):= ⟨fun _ _=>le_rfl, fun x y _ _ => by rw [mul_one,one_mul]; exact l.one_fee⟩
variable {R: Fin (t+1)→Cross L α β} {F:Breed t (Node α)→ℝ}
lemma pressage (hL:Odd L.val)(H:∀ i (v:List Axis), v.length≤ k → Weirs (hook η n L) (install (advanceC L (R i) v)) ((L.val:ℝ)^4*(C/(L.val:ℝ)^(1+v.length))) (C/(L.val:ℝ)^(1+v.length))) (hk:k≤n)(hv:η≤δ)(he:(2*(η:ℝ)/(L.val:ℝ))*(t+1) ≤ σ)(hs:0<σ)(hc:0≤C) (hw: softRank k F)(hu:Rooted (bath σ n α) F D)(hf:author (extract F)=F) (y:Node β)[Fintype α]:
    Balanced (fun q:Fin t→Node β=> allAt (install ∘ R) F (Fin.cons y q)) (gas η n y)
      ((( Fintype.card (Breed t α) * ((mist δ n 6)*(k+1)*(t+1:ℝ)^n))* ((L.val:ℝ)^4*(C/(L.val:ℝ))))* (C/(L.val:ℝ))^t/(L.val:ℝ)^k * D):= by
  let a:=graphE α t; let w:= gas η n y (t:=t); have ha p:0≤ w p:= by unfold w gas; positivity
  let A := Breed t α × Cover; let head (p:A): Node α:=(p.2,p.1 0)
  let E:= fun (b:A) => install (R 0) (head b) y; let M:= install ∘ Fin.tail R; let f (b:A)(u:Tailor t):=F (a (b,u)); let g (b:A)(q:Fin t→Node β)(v:Tailor t):= network M b.2 b.1 v q
  have e0 (b:A)(v:Tailor t): a (b,v) 0=head b:= by change publish b.2 b.1 v 0=_; simp only [publish,head,legLane,Fin.cons_zero,add_zero]
  have hE i: Weirs (hook η n L) (install (R i)) ((L.val:ℝ)^4*(C/(L.val:ℝ))) (C/(L.val:ℝ)):= by simpa only [advanceC,List.length_nil,add_zero,pow_one] using H i [] (by simp)
  have hC₀ := fun i=> faded (hE i) (fun x y=>mist_one (Nat.cast_nonneg _))
  have hg q b u: F (a (b,u))*(∏ i, (install ∘ R) i (a (b,u) i) (Fin.cons y q i)) = E b*f b u*g b q u:= by rw [Fin.prod_univ_succ]; simp only [Function.comp_apply,Fin.cons_succ,Fin.cons_zero]; rw [e0]; unfold E f g network; change _= (_ * _)*∏ i,install (R _) _ _; ring_nf; try rfl
  let K b u (q:Fin t→Node β):= E b * (f b u * Quill.tail k (g b q) u)
  let T:= mist δ n 6*(k+1)*(t+1:ℝ)^n; let S (b:A)(v:Tailor t):= (T*( (bath σ n α).bill (a (b,v))*hook η n L (head b) y)*(C/(L.val:ℝ))^t/(L.val:ℝ)^k)
  have hk b v:Balanced (fun q=>K b v q) w (‖E b‖*(‖f b v‖*S b v)):= by
    refine budget_mono (budget_scale (norm_nonneg (E b)) (budget_scale (norm_nonneg (f b v)) (plume (R:=Fin.tail R) (z:=b.2) (b:=b.1) hL σ η δ (fun i l h x=> by
      unfold Quill.Balanced; simp_rw [mul_comm (hook _ _ _ x _) _]; exact (H i.succ l h).rows x) hk hv he hc y v))) (fun q=> mul_nonneg (ha _) (norm_nonneg _)) fun q=> le_of_eq ?_
    unfold K; simp only [norm_mul]; unfold g M w; ring
  let χ (b:A) := ‖E b‖*hook η n L (head b) y
  have hX b:0≤χ b:= (hE 0).columns y|>.1 (head b)
  let r:= (L.val:ℝ); let d:= r^4*(C/r); have hY:=hu.cash; have hy:0≤T:= by unfold T; have h:= mist_pos (σ:=δ) (n:=n) (a:=6) (by norm_num); positivity
  have hχ : SumBudget χ (Fintype.card (Breed t α)* d):= by
    refine Cost.product (Cost.finite d (show 0≤d by unfold d r; positivity)) fun x=> budget_pull (fun v:Cover=>(v,x 0)) (fun u v h=> congr_arg Prod.fst h) ((hE 0).columns y)
  let z:= Fintype.card (Breed t α)*d* (D*(T*(C/r)^t/r^k))
  have hS (b:A) : SumBudget (fun v=> ‖E b‖*(‖f b v‖ * S b v)) (χ b*(D*(T*(C/r)^t/r^k))):= by
    let e (v:Tailor t):Locked (Node α) (0:Fin (t+1)) (head b):=⟨a (b,v),e0 b v⟩; have hj : Injective e:= fun x y h=> congr_arg Prod.snd (a.injective (congr_arg Subtype.val h))
    refine budget_mono (budget_scale (hX b) (Cost.scale' (budget_pull _ hj (hu.row 0 (head b))) (T*(C/r)^t/r^k) (by unfold r; positivity))) (fun v=>Cost.nonneg (hk b v)) ?_
    intro v; apply le_of_eq; dsimp only [e,f,S,r,χ]; ring
  have hT : SumBudget (fun b:A× Tailor _=> ‖E b.1‖*(‖f b.1 b.2‖*S b.1 b.2)) z:= Cost.product (Cost.scale' hχ _ (by unfold r; positivity)) hS
  let P:= fun (b:A) (q:Fin _→Node β)=> ∑' v,K b v q
  have hl: SumBudget (fun p:(Fin _→ Node β) × A=> w p.1 * ‖P p.2 p.1‖) z:= by
   
    refine budget_comm (Cost.product (Cost.scale' hχ _ (by unfold r; positivity)) (fun b=>?_))
    simp_rw [mul_comm (w _)]; exact budget_join (f:=fun q v=> K b v q) ha (budget_comm (Cost.product (hS b) (fun v=> by simpa only [Quill.Balanced,mul_comm (w _) _] using (hk b v))))
  suffices H: ∀ q, allAt (install ∘ R) F (Fin.cons y q)=∑' b,P b q by
    simp_rw [H]
    apply budget_loosen (D:=_) (C:=z) (f:=fun x=> w x*_) ?_ (le_of_eq (by dsimp only [z,d,T,r]; ring)); simp_rw [mul_comm (w _)] at *; exact budget_join ha hl
  intro q; rw [allAt, ← a.tsum_eq]; change (∑' p:A × Tailor t, F (a (p.1,p.2))* ∏ i,(install ∘ R) i (a (p.1,p.2) i) (Fin.cons (α:=fun _=>Node β) y q i))=_; simp_rw [hg]; have he : Summable (fun p:A× Tailor t=> E p.1 *f p.1 p.2*g p.1 q p.2):= by
    simp_rw [←hg]; exact (a.summable_iff (f:=fun p=> F p*∏ i,(install ∘ R) i (p i) (Fin.cons (α:=fun _=>Node β) y q i))).mpr (all_summable (G:=install ∘ R) hu (monochrome _ (Node β)) hC₀ _).of_norm
  rw [he.tsum_prod]; apply tsum_congr; intro j; unfold P K; let ρ:=σ / (t+1); have hρ:0<ρ:= div_pos hs (by positivity)
  have hq : f j=extract F j.1:= funext fun v=> by unfold f; rw [← congr_fun hf (a _)]; change extract F (alphabet _) (degree (publish j.2 j.1 v)) = _; rw [deg_issue]; rfl
  have hu:= export_price (η:=ρ) (hu.weaken bath_terrace le_rfl) j.1 (show (t:ℝ)*ρ≤ σ from by push_cast; unfold ρ; have ht:=NNReal.coe_nonneg σ; push_cast; field_simp; nlinarith)
  have hj:Summable (fun v=> E j * (f j v* zen k (g j q) v)) := hq.symm ▸ ((zen_summable hρ hu (g j q) k).of_norm.mul_left _)
  have hy := stars hρ hu (g j q) k (hw j.1); simp_rw [Quill.tail, Pi.sub_apply,_root_.mul_sub]; rw [Summable.tsum_sub]; · simp_rw [hq, mul_assoc,tsum_mul_left,hy]; ring
  · simp_rw [← mul_assoc]; exact he.prod_factor j
  exact hj
end
end YM.Pulse.Spine
noncomputable section
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration Quill
open scoped Classical Topology BigOperators NNReal ENNReal
variable {α β X Y Z : Type}{L:Side}{k n t:ℕ} {C D:ℝ} {η δ σ:ℝ≥0}
lemma allAt_poem [Fintype X]{F:Field X α}(U:α→β→ℝ)(h:Poem F): Poem (allAt (fun _=>U) F) := by
  intro p x; unfold allAt; let e:= Equiv.arrowCongr p.symm (Equiv.refl α); rw [← e.tsum_eq]; apply tsum_congr; intro v; rw [show e v=v ∘ p from rfl,h]; exact congr_arg _ (Equiv.prod_comp p (fun i=>U (v i) (x i)))
lemma bill_title {F:Breed t X→ℝ}{l:Range X}(h:Poem F)(hc:0≤C)(ha:∀ x,Balanced (fun q:Fin t→X=>F (Fin.cons x q)) (fun q:Fin t→X=>l.bill (Fin.cons x q)) C) : Rooted l F C:= by
  have ht x: SumBudget (fun z:Locked X (0:Fin (t+1)) x=>‖F z.val‖ * l.bill z.val) C:= by
    let e:= locket X x (t:=t); refine budget_map (ha x) _ e.injective fun p=> ?_; dsimp only; rw [mul_comm,show Fin.cons x (e p)=p.val from congr_arg Subtype.val (e.symm_apply_apply p)]
  refine ⟨hc,fun i x=>?_⟩; let p:= Equiv.swap i 0; let U:=orientLocks X p i x; have hi:p i=0 := by simp [p]
  refine budget_map (g:=fun z:Locked X (p i) x=>‖F z.val‖ * l.bill z.val) (by rw [hi]; exact ht x) U U.injective fun v=>?_; change _=‖F (v.val∘p.symm)‖*_; rw [h p.symm]; exact congr_arg _ (l.retrieve (u:=v.val) p.symm p.symm.surjective).symm
/-! Cost before block choice, even if the Gaussian widths are post-block.
 Input resolution a function of cutoff/scale, paid by the ratio inequality.
 Both widths may be arbitrarily small. Gives also polynomially strong closure down UV.
-/
theorem prolonged (δ:ℝ≥0)(h:0<δ) (α β:Type)[Fintype α][Fintype β] (t n k:ℕ)(hk:k≤ n)(C:ℝ)(hC:0≤C): ∃ A:ℝ, 0≤A ∧ ∀ (L:Side), Odd L.val → ∀ η σ:ℝ≥0,0<σ→ (η:ℝ)*2≤δ → (2*(η:ℝ)/(L.val:ℝ))*(t+1)≤σ → ∀ R:Cross L α β,(∀ l:List Axis, l.length ≤ k → Row.strip (advanceC L R l) δ (C/(L.val:ℝ)^(1+l.length))) →
    ∀ F:Breed t (Node α)→ℝ,Poem F→ author (extract F)=F→softRank k F→∀ D,Rooted (bath σ n α) F D → Rooted (bath η n β) (allAt (fun _=>install R) F) (A*(L.val:ℝ)^4/(L.val:ℝ)^(t+1+k)*D):= by
  obtain ⟨a,ha,hb⟩:= coatContract δ n h α β C hC; let T:= mist δ n 6; let d:= Fintype.card (Breed t α); let A:= d*(T*(k+1)*(t+1:ℝ)^n)*a*a^t; have hA : 0≤A:= by have hh : 1≤T:= mist_one (by norm_num); unfold A; positivity -- parser
  refine ⟨A,hA,fun L hL η σ hs he hu R hr F hF hE hW D hf=> bill_title (allAt_poem _ hF) (by have hh:= hf.cash; positivity) fun x=> ?_⟩; convert pressage (R:=fun _=>R) hL (fun i l hl=> hb L η he (advanceC L R l) (1+l.length) (hr l hl)) hk (by exact_mod_cast (le_trans (a:=(η:ℝ)) (b:= η*2) (by simp [mul_two]) he)) hu hs ha hW hf hE x using 1 <;> try rfl
  unfold A T d; simp only [pow_add,div_pow]; field_simp
end YM.Pulse.Spine
