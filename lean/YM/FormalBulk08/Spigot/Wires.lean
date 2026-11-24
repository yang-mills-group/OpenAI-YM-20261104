import YM.FormalBulk08.Spigot.Firth

/-! Ward gradient prices on full polynomial probes. Rank1 included. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Tensor
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{l n d m :ℕ}{A B η θ:ℝ}{o:Loc G 1}
open Grail

def prairie (u:Cover→hue G→ℝ)(x:edgeL G):= u x.1 x.2.2
def precipice (u:Cover→hue G→ℝ)(x:edgeL G):= u (x.1+step (bearing x)) x.2.2
def loped (u:Cover→hue G→ℝ):= prairie u-precipice u
def rivulet (u:Cover→hue G→ℝ)(x:edgeL G):= if x.2.1= Exterior.coord 0 then prairie u x else 0
lemma faded (u:Cover→hue G→ℝ)(ht: Stipend (prairie u))(ht':Stipend (precipice u))(hg:Stipend (loped u))(hh:Stipend (rivulet u))(x:chain (edgeL G) l)(T:Tile (edgeL G) (l+1))(hp:0<η)(h:Knoxville (fame _) η (0,o) T A)(hs:Knoxville (fame _) η (0,o) (tap T) B):
     (∑' i,T (Fin.cons i x)* loped u i)=∑' i,tap T (Fin.cons i x)*rivulet u i := by
    let S (y:Cover)(a : TypeFace 1)(i:hue G):= T (Fin.cons (y,a,i) x)
    have H(i:hue G)(a: TypeFace 1):
       (∑' y:Cover, T (Fin.cons (y,a,i) x)*loped u (y,a,i))=∑' y:Cover,(S y a i-S (backwards y a) a i)* u y i := by
         let g : Cover ≃ Cover := Equiv.addRight (step (axisEquiv.symm a)); let F (y:Cover): edgeL G:= (y,a,i);
         have hF:Injective F:= fun p q hx=> congr_arg (fun p:edgeL G=>p.1) hx
         have hv: Summable fun y=> S y a i*u y i:= (pace_term _ x T h ht hp).comp_injective hF
         have he : Summable (fun y=> S y a i * u (g y) i) := by
            have hh := (pace_term _ x T h ht' hp).comp_injective hF
            apply hh.congr; intro y; rfl
         let w (y:Cover):=backwards y a
         have hP y:w (g y)=y:= by simp [w,g,backwards]
         have hU: (fun y=>S y a i* u (g y) i) = (fun y=> S (w y) a i *u y i) ∘ g:=by ext y; simp [hP]
         have hu : Summable fun y=> S (w y) a i *u y i:= g.summable_iff.mp (hU ▸ he)
         have hj y: loped u (y,a,i)= u y i-u (g y) i:=rfl
         simp_rw [hj,mul_sub,sub_mul]; change (∑' y,(S y a i*u y i- S y a i * u (g y) i))= _; rw [Summable.tsum_sub hv he,Summable.tsum_sub hv hu];congr 1;change (∑' y,(fun t=> S t a i*u (g t) i) y)=_; rw [hU]; exact g.tsum_eq (fun y => S (w y) a i * u y i)
    rw [Glide.sum_strip (pace_term _ x T h hg hp),Glide.sum_strip (pace_term _ x _ hs hh hp)]; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; conv_lhs=> rw [Finset.sum_comm];
    conv_rhs=> rw [Finset.sum_comm];
    refine Finset.sum_congr rfl fun i hi=>?_ ; rw [Finset.sum_eq_single (s:= (Finset.univ:Finset (TypeFace 1))) (f:=fun a=> ∑' y:Cover,tap T (Fin.cons (y,a,i) x)*rivulet u (y,a,i)) (Exterior.coord 0)]; swap;· intro a _ ha; simp [rivulet,ha]
    swap; · simp
    simp_rw [H]; rw [← Summable.tsum_finsetSum]; swap
    · intro a _; let F(y:Cover):edgeL G:=(y,a,i); let g : Cover≃Cover:=Equiv.addRight (step (axisEquiv.symm a)); simp_rw [sub_mul]; apply Summable.sub
      · exact (pace_term _ x T h ht hp).comp_injective (i:=F) (fun p q hx=> congr_arg (fun p:edgeL G=>p.1) hx)
      apply g.summable_iff.mp; apply ((pace_term _ x T h ht' hp).comp_injective (i:=F) (fun p q hx=> congr_arg (fun p:edgeL G=>p.1) hx)).congr;intro x; simp [precipice,g,backwards,F,S,bearing]
    apply tsum_congr; intro y; rw [←Finset.sum_mul]; simp only [tap, rivulet, Fin.cons_zero,Fin.tail_cons,↓reduceIte, riverP,Finset.sum_apply,Pi.sub_apply]; rfl


lemma subsidize {f g:edgeL G→ℝ}(h:Stipend f)(ht:Stipend g) (b:Bool): Stipend (if b=true then f+g else f-g):= by
    obtain ⟨A,n,ha,H⟩:=h;obtain ⟨B,m,hb,M⟩:=ht; refine ⟨A+B,n+m,add_nonneg ha hb,fun x=>?_⟩
    have he : ‖f x‖+‖g x‖≤(A+B)*liftCost (n+m) x.1:= by rw [add_mul]; refine (add_le_add (H x) (M x)).trans (add_le_add (mul_le_mul_of_nonneg_left ?_ ha) (mul_le_mul_of_nonneg_left ?_ hb)) <;> unfold liftCost <;> exact pow_le_pow_right₀ (by simp) (by omega)
    split
    · exact (norm_add_le ..).trans he
    exact (norm_sub_le ..).trans he
lemma ranch (s: Cover→hue G→ℝ)(h:Stipend (prairie s)): Stipend (precipice s) ∧ Stipend (loped s) ∧ Stipend (rivulet s):= by
   have he : Stipend (precipice s):= by
      obtain ⟨A,n,hA,H⟩:= h; refine ⟨A*2^n,n,mul_nonneg hA (by positivity),fun x=>?_⟩
      apply (H (x.1+step (bearing x),x.2)).trans; rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ hA
      unfold liftCost; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity); have he : size (x.1+step (bearing x))≤size x.1+1:= by simpa only [show size (step (bearing x):Cover)=1 from price_vec ⟨bearing x,false⟩] using size_add x.1 (step (bearing x))
      have hx: (size (x.1+step (bearing x)):ℝ) ≤ size x.1+1:= by exact_mod_cast he
      linarith
   refine ⟨he,subsidize h he false,?_⟩
   obtain ⟨A,n,hA,H⟩:=h; exact ⟨A,n,hA,fun i=> by
     unfold rivulet; split
     · exact H i
     rw [norm_zero]; exact mul_nonneg hA (liftCost_pos ..)⟩
lemma idle_tariff (T: Tile (edgeL G) m)
    (ht: Agate T)(h:Knoxville (fame _) η (0,o) T A)(he:0<η)(hp:Torrid T η 0 o)(U V:Fin m→edgeL G→ℝ)(hu:∀ i, Stipend (U i))(i:Fin m)(s:Cover→hue G→ℝ)(hm:Stipend (prairie s))(hV: V= Function.update U i (U i + loped s)): tariffs V T=tariffs U T:= by
   subst V
   cases m with
   | zero=> exact Fin.elim0 i
   | succ m=>
     let v:Fin (m+1)→edgeL G→ℝ:=Function.update U i (U i + loped s)
     let S:=Equiv.swap 0 i; have hh:=ranch s hm
     have hw(j):Stipend (v j):= by
        by_cases hx:j=i
        · subst j;rw [show v i=U i+loped s from update_self ..]; exact subsidize (hu i) hh.2.1 true
        unfold v; rw [update_of_ne hx]; exact hu j
     rw [←tariff_turn U T ht S]
     change _=_; rw [←tariff_turn v T ht S,press_merit (v ∘ S) o T h he (fun j=>hw (S j)), press_merit (U ∘ S) o T h he (fun j=>hu (S j))]; apply tsum_congr; intro p
     have hk j : (v ∘ S) (Fin.succ j) = (U ∘ S) (Fin.succ j):= by
        unfold v; rw [comp_apply,comp_apply,update_of_ne]; intro hx; have hc:= S.injective (hx.trans (show S 0=i by simp [S]).symm); simp at hc
     have he₁ : (U ∘ S) 0= U i:= by simp [S]
     have he₂ : (v ∘ S) 0=U i + loped s:= by simp [v,S]
     have hp' :=hp m rfl
     have hx (v:chain (edgeL G) (m+1)) : tap T v=0:= by
        have hz : ‖tap T v‖*Real.exp (η*herb (fame _) (0,o) v)≤0:= penn_chill _ hp'
        exact norm_le_zero_iff.mp ((nonpos_of_mul_nonpos_left hz (Real.exp_pos _)))
     simp_rw [hk,he₁,he₂,Pi.add_apply,mul_add]; rw [Summable.tsum_add (pace_term _ p _ h (hu i) he) (pace_term _ p _ h hh.2.1 he), faded s hm hh.1 hh.2.1 hh.2.2 p T he h hp']; simp_rw [hx,zero_mul,tsum_zero,add_zero]
lemma tariff_grain (T: Tile (edgeL G) m)(ht:Agate T)(h:Knoxville (fame _) η (0,o) T A)(he:0<η)(hp:Torrid T η 0 o)(U V:Fin m→edgeL G→ℝ)(hu:∀ i, Stipend (U i)) (S:Fin m→Cover→hue G→ℝ)(hM:∀ i, Stipend (prairie (S i)))(hv:∀ i,V i=U i+loped (S i)): tariffs V T=tariffs U T:= by
    let f(P:Finset (Fin m))(i):= if i∈P then V i else U i
    have heq (P:Finset (Fin m)): tariffs (f P) T = tariffs U T:= by
       induction P using Finset.induction with
       | empty=> rw [show f ∅=U from funext fun i=> by simp [f]]
       | @insert i P hi ih=>
            refine Eq.trans ?_ ih; apply idle_tariff T ht h he hp _ _ ?_ i (S i) (hM i) ?_
            · intro j; unfold f;split
              · rw [hv]; exact subsidize (hu j) (ranch _ (hM j)).2.1 true
              exact hu _
            ext1 j; by_cases hl:j=i <;> simp [hl,f,hv,hi]
    rw [show V=f Finset.univ from ?_, heq];ext1 i; unfold f;simp
end YM.FormalBulk08.Spigot
