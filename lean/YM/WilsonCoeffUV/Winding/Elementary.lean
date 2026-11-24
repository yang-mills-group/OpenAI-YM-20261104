import YM.WilsonCoeffUV.Winding.Move
/-!
# Per-site jobs: width reservation for winding error. Polchinski trees & folds
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent
open scoped Topology BigOperators
variable {n L:Side}{ι I J U X α β V:Type*}{i j k l r:ℕ}{s a A B C D E t q w v:ℝ}
variable {d:Bank.Distance U}[NormedAddCommGroup V][NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
lemma pairMore {P:canal U α β V k r}(h:pairCup d s A P)(p:A≤B): pairCup d s B P:=⟨h.1.trans p,fun x y=>(h.2 x y).trans (mul_le_mul_of_nonneg_right p (by positivity))⟩
lemma reachL [Fintype I][Fintype J]{x:I→U}{y:J→U}(h:∀ i,∃ j,x i=y j): league d x≤ league d y:= by
   refine league_le d _ fun i j=>?_ ; obtain ⟨k,hk⟩:=h i; obtain ⟨l,hv⟩:= h j; rw [hk,hv]; exact leg_le ..

structure Pore (x y : V)(A B v:ℝ): Prop where
   nearC : ‖x‖ ≤ A
   farC : ‖y‖ ≤ A
   gap : ‖x-y‖ ≤ B*v
lemma Pore.mu {x y:V}{a b:ℝ}(h:Pore a b A B v)(p:Pore x y C D v): Pore (a•x) (b•y) (A*C) (B*C+A*D) v:=by
   have hh:= (norm_nonneg _).trans h.nearC
   refine ⟨by rw [norm_smul]; exact mul_le_mul h.nearC p.nearC (norm_nonneg _) hh,by rw [norm_smul]; exact mul_le_mul h.farC p.farC (norm_nonneg _) hh,?_⟩
   rw [show a•x-b•y=(a-b)•x+b•(x-y) from by rw [sub_smul,smul_sub]; abel]; apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,add_mul,mul_assoc A D v,mul_right_comm B C v]; exact add_le_add (mul_le_mul h.gap p.nearC (norm_nonneg _) ((norm_nonneg _).trans h.gap)) (mul_le_mul h.farC p.gap (norm_nonneg _) hh)
lemma Pore.ice (a:ℝ)(h:0 ≤ a): Pore a a a 0 v:=⟨by simp [abs_of_nonneg h],by simp [abs_of_nonneg h],by simp⟩
variable {P:ropes (Site n) α β}{G:ropes Cover α β}{F:Ten V (Cloth α) r}{Q:Ten V (Co n α) r}
lemma Pore.rails (h:Rail P G s A)(p:0≤s){x:Cloth α}{y: Cloth β}(v:4*Bank.terrain.gap x.1 y.1 < n.val): Pore (P (foldUnder n x) (foldUnder n y)) (G x y) A A (catchW s n):= ⟨(h.bow.2 ..).trans (mul_le_of_le_one_right h.bow.1 (catch_peak p _)), (h.berth.2 ..).trans (mul_le_of_le_one_right h.berth.1 (catch_peak p _)),h.far x y v⟩
lemma Pore.ten {F:Ten V (Cloth α) (r+1)}{Q:Ten V (Co n α) (r+1)}(h:Sight Q F s A)(p:0≤s)(x)(u:4*soar Bank.terrain x<n.val): Pore (Q (slideC n x)) (F x) A A (catchW s n):=by
    have hx:= h.aim; rw [pruce_down] at hx; refine ⟨(hx.2 _).trans (mul_le_of_le_one_right hx.1 (catch_peak p _)),(h.bound.2 _).trans (mul_le_of_le_one_right h.bound.1 (catch_peak p _)),?_⟩; have he:= h.gall; rw [pruce_down] at he; exact he.local_w _ u
lemma Pore.prod {f g:ι→ℝ}(S:Finset ι)(p:∀ i∈S,Pore (f i) (g i) A A q): Pore (∏ i∈ S,f i) (∏ i∈ S,g i) (A^S.card) (S.card*A^S.card) q:=by
   classical
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.prod_empty,Finset.card_empty,Nat.cast_zero,pow_zero,zero_mul]; exact Pore.ice _ zero_le_one
   | @insert i S hi ih=> have he:= (p i (Finset.mem_insert_self ..)).mu (ih fun j hj=>p j (Finset.mem_insert_of_mem hj)); rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi,pow_succ',show (↑(S.card+1):ℝ)*(A*A^S.card)=A*A^S.card+A*(S.card*A^S.card) from by push_cast; ring]; exact he
lemma vLine {x:dock U β r}{y:dock U α k}{i j:Fin k}: d.gap (y i).1 (y j).1≤course d x y:=leg_le d (Sum.elim (Prod.fst∘ x) (Prod.fst ∘ y)) (Sum.inr i) (Sum.inr j)
lemma vMark {x:dock U β r}{y:dock U α k}: soar d y≤ course d x y := league_le d _ fun _ _=> vLine
lemma vPulse {x:dock U β r}{y:dock U α k}{i j}: d.gap (y i).1 (x j).1≤ course d x y:=leg_le d (Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y)) (Sum.inr i) (Sum.inl j)
lemma vn {x y : ℕ}(h:x≤ y)(p:4*y<n.val):4*x<n.val:=by omega
lemma rub_eye (X Y:ℝ)(k:ℕ)(p:0≤X)(h:0≤Y): X^k*Y≤ (k+1:ℕ)*X^k*Y:=by
   gcongr; calc
            _ ≤ 1 * X^k := (one_mul _).ge
            _ ≤ _ := by gcongr; exact_mod_cast Nat.le_add_left ..
lemma SiteW.ribbons {Z: Ten V (Cloth α) (r+1)}{Y: Ten V (Co n α) (r+1)}(h:Rail P G s A)(e: Sight Y Z s B)(p:0≤s): SiteW (gloss P Y) (gloss G Z) s ((r+2:ℕ)*A^(r+1)*B):=by
    have hz:= e.aim; rw [pruce_down] at hz
    have hk:=rub_eye A B (r+1) h.berth.1 hz.1
    refine ⟨pairMore (gloss_cup h.bow hz p) hk,pairMore (gloss_cup h.berth e.bound p) hk,⟨hk.trans' (gloss_cup h.bow hz p).1,?_⟩,fun b x y=> ?_⟩
    · rintro ⟨x,y⟩ v
      let n' (i:Fin (r+1)) := P (slideC n y i) (slideC n x i); let t i:= G (y i) (x i)
      have hP i: Pore (n' i) (t i) A A (catchW s n):= Pore.rails h p (vn (vPulse (x:=x) (y:=y)) v)
      have hw:= ((Pore.prod _ fun i (_:i∈Finset.univ)=>hP i).mu (Pore.ten e p y (vn vMark v))).gap
      apply hw.trans_eq; simp only [Finset.card_univ,Fintype.card_fin]; push_cast; ring
    unfold gloss Bank.ribbon; rw [e.strollT b]; congr 1; exact Finset.prod_congr rfl fun i _=> h.haul b _ _
lemma reach_head (x:dock U α k)(y:dock U α r)(f:Fin l→Fin k)(i: Fin r): soar d (Fin.cons (y i) (x∘f)) ≤ course d x y:= by
   apply reachL; intro j; refine Fin.cases ⟨Sum.inr i,rfl⟩ (fun z=>⟨Sum.inl (f z),by simp⟩) j
lemma reach_head2 (x:dock U α r)(y:dock U α 2): soar d (Fin.cons (y 1) (Fin.cons (y 0) x)) ≤ course d x y:=by
   apply reachL; intro j; refine Fin.cases ⟨Sum.inr 1,rfl⟩ (fun z=>?_) j
   simp only [Function.comp_apply,Fin.cons_succ]; refine Fin.cases ⟨Sum.inr 0,rfl⟩ (fun z=>⟨Sum.inl z, by simp⟩) z

section
variable {P:ropes (Site n) α α}{G:ropes Cover α α}{F: Gen V (Cloth α)}{Q:Gen V (Co n α)}{Y:Gen ℝ (Cloth α)} {Z:Gen ℝ (Co n α)}
lemma Pore.joinEye {x y :ℝ}(h:Pore x y A B v)(i j : ℕ): Pore (1/2*x*i*j) (1/2*y*i*j) ((1/2:ℝ)*i*j*A) ((1/2:ℝ)*i*j*B) v:=by
   let a:ℝ:=1/2*i*j; have he:0≤a:=by unfold a; positivity
   have ht:= (Pore.ice a he).mu h; rw [zero_mul,zero_add] at ht; convert ht using 1 <;> unfold a <;> simp only [smul_eq_mul]<;>ring
abbrev ore (i j:ℕ): ℝ:=1/2*(i+1:ℕ)*(j+1:ℕ)
lemma SiteW.rainL (p:Rail P G s A)(h:Sight (Q (r+2)) (F (r+2)) s B)(v:0≤s): SiteW (rain P Q r) (rain G F r) s (ore r (r+1)*2*A*B):=by
   have ht:= h.aim; rw [pruce_down] at ht; let C:= A*B*((1/2:ℝ)*(r+1:ℕ)*(r+2:ℕ))
   have he:0≤ C:= (rain_bill (P:=Q) p.bow ht v).1; have hx: C+C=ore r (r+1)*2*A*B:=by unfold ore C; push_cast; ring
   refine ⟨pairMore (rain_bill p.bow ht v) ((le_add_of_nonneg_right he).trans_eq hx),pairMore (rain_bill p.berth h.bound v) ((le_add_of_nonneg_right he).trans_eq hx),⟨(add_nonneg he he).trans_eq hx,?_⟩,fun b x y=> ?_⟩
   · rintro ⟨x,y⟩ u; change ‖rain P Q r (slideC n x) (slideC n y)-rain G F r x y‖ ≤ _; simp_rw [rain_spell]
     have hy:= Pore.rails p v (x:=y 0) (y:=y 1) (vn vLine u)
     let W:dock Cover α (r+2):= Fin.cons (y 1) (Fin.cons (y 0) x); have hh:= Pore.ten h v W (vn (reach_head2 x y) u)
     have hv:= ((hy.joinEye (r+1) (r+2)).mu hh).gap; unfold W at hv; rw [slideC,←comps_head,←comps_head] at hv
     apply hv.trans_eq; unfold ore; push_cast; ring
   simp_rw [rain_spell,Function.comp_apply,p.haul b,comps_head,h.strollT b]
lemma SiteW.rillL (p:Rail P G s A)(e:Sight (Z (i+1)) (Y (i+1)) s C)(h:Sight (Q (j+1)) (F (j+1)) s B)(v:0≤s): SiteW (rill P Z Q (i+j) i j) (rill G Y F (i+j) i j) s (ore i j*3*A*C*B):=by
   have ht:= h.aim; have hV:= e.aim; rw [pruce_down] at ht hV; let K:= ore i j*A*C*B
   have he:0≤ K:= (rill_bill (P:=Z) (Q:=Q) p.bow hV ht v rfl).1; have hx: K+ (K+K)=ore i j*3*A*C*B:=by unfold ore K; ring
   refine ⟨pairMore (rill_bill p.bow hV ht v rfl) ((le_add_of_nonneg_right (add_nonneg he he)).trans_eq hx), pairMore (rill_bill p.berth e.bound h.bound v rfl) ((le_add_of_nonneg_right (add_nonneg he he)).trans_eq hx), ⟨(add_nonneg he (add_nonneg he he)).trans_eq hx,?_⟩,fun b x y=>?_⟩
   · rintro ⟨x,y⟩ u; change ‖rill P Z Q (i+j) i j (slideC n x) (slideC n y)-rill G Y F _ i j x y‖ ≤ _; rw [rill_spell,rill_spell]
     have hy:= Pore.rails p v (x:=y 0) (y:=y 1) (vn vLine u); have hh:= Pore.ten e v _ (vn (reach_head x y (Fin.castAdd j) 0) u); have hg:= Pore.ten h v _ (vn (reach_head x y (Fin.natAdd i) 1) u)
     have hv:= (((hy.joinEye (i+1) (j+1)).mu hh).mu hg).gap; simp_rw [slideC,←comps_head] at hv
     apply hv.trans_eq; unfold ore; ring
   simp_rw [rill_spell,Function.comp_apply,p.haul b,Function.comp_assoc,comps_head,e.strollT b,h.strollT b]
end

omit [NormedSpace ℝ V] in
lemma spin_floor {S:Finset ι}{f g:ι→V}(h:∀ i∈ S, ‖f i-g i‖ ≤ A): ‖(∑ i∈ S,f i)-∑ i∈ S,g i‖ ≤ S.card*A:=by
   rw [←Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans; apply le_trans (Finset.sum_le_sum h); simp
lemma SiteW.spin {P:canal (Site n) α α V 2 r}{G:canal Cover α α V 2 r}(h:SiteW P G s A): SiteW (swivel P) (swivel G) s A:=by
    refine ⟨swivel_cup h.aim,swivel_cup h.bound,⟨h.aim.1,?_⟩,?_⟩
    · rintro ⟨x,y⟩ u; change ‖swivel P (slideC n x) (slideC n y) - swivel G x y‖ ≤ _
      have he (i:Equiv.Perm (Fin r)): ‖P (slideC n x ∘ i) (slideC n y)- G (x ∘ i) y‖ ≤ _:= h.fall.local_w (x ∘ i,y) (by change 4*course _ _ _<_; rw [course_roll]; exact u)
      let v:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hp:0<v:=by unfold v; positivity
      simp only [swivel,Pi.smul_apply,Finset.sum_apply,← smul_sub,norm_smul]; apply le_trans (mul_le_mul_of_nonneg_left (spin_floor (ι:=Equiv.Perm (Fin r)) (f:=fun i=>P (slideC n x ∘ i) _) (g:=fun i=> G (x ∘ i) y) (S:=Finset.univ) (fun i _=>he i)) (norm_nonneg _)); rw [Finset.card_univ]; change ‖v⁻¹‖*(v*_ )≤_; rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),inv_mul_cancel_left₀ hp.ne']
    intro b x y; simp only [swivel,Pi.smul_apply, Finset.sum_apply]; exact congr_arg (_ • ·) (Finset.sum_congr rfl fun i _=> h.port b (x ∘ i) y)
section
variable {F:Gen V (Cloth α)}{Q:Gen V (Co n α)}
def glassC [Fintype α] (r:ℕ)(s A:ℝ) :ℝ:= if r=0 then 1 else priceM α r s * (r+1:ℕ)*A^r
variable [CompleteSpace V][Fintype α]
lemma SiteW.glass (h:Rail P G s A)(p:Sight (Q r) (F r) s B)(v:0<s): Sight (fade P Q r) (prism G F r) (s/32) (glassC (α:=α) r s A*B):=by
    cases r with
    | succ r=> rw [glassC,if_neg (by omega),show priceM α (r+1) s*(r+1+1:ℕ)*A^(r+1)*B=priceM α (r+1) s*((r+1+1:ℕ)*A^(r+1)*B) from by ring]; exact (ribbons h p v.le).worthy v
    | zero=>
        apply Sight.mono (s:=s) _ (by linarith)
        rw [glassC,if_pos rfl,one_mul]; have ht x: pruce (fade P Q 0) x= pruce (Q 0) default:=by simp [pruce,fade];
        refine ⟨⟨p.aim.1,fun x=>?_⟩,⟨p.bound.1,fun x=>?_⟩,⟨p.aim.1,fun x u=>?_⟩,fun b x=>congr_arg (fade P Q 0) (Subsingleton.elim ..)⟩
        · rw [ht]; simpa only [soar,league,Finset.univ_eq_empty,Finset.sup_empty] using p.aim.2 default
        · simpa only [Bank.prism,Bank.reflectCut,soar,league,Finset.univ_eq_empty,Finset.sup_empty] using p.bound.2 default
        rw [ht]; have hv:=p.gall.local_w default (by simp [soar,league])
        rw [Subsingleton.elim (slideC n _) default] at hv
        exact hv
end
end YM.WilsonCoeffUV.Winding
