import YM.FormalBulk08.Grail.Milk
import YM.FormalBulk08.Grail.Epic

/-! Ward gradient prices on full polynomial probes. Rank1 included. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Tensor
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{l n d m :ℕ}{A B η θ : ℝ}{o:Loc G 1}

def ground (f:E4→ G.Color)(p:edgeL G):ℝ:= f (Place.seat p.1) p.2.2
def patcher (f:E4→G.Color)(p:edgeL G):= if p.2.1=Exterior.coord 0 then ground f p else 0
lemma ground_pay (f:E4→ G.Color)(h:f∈rangeLt G.Color n): Stipend (ground f):= by
    obtain ⟨A,hA,H⟩:=band_growth h; refine ⟨_,n,hA,fun x=>?_⟩
    unfold ground; rw [←EuclideanSpace.basisFun_inner G.ColorIndex ℝ _ _]; apply le_trans (norm_inner_le_norm ..);rw [OrthonormalBasis.norm_eq_one,one_mul]; apply (H _).trans (mul_le_mul_of_nonneg_left _ hA); unfold liftCost; exact pow_le_pow_left₀ (by positivity) (by linarith [shade_seat x.1]) _
lemma patcher_pay (f:E4→G.Color)(h:f∈rangeLt G.Color n): Stipend (patcher f):= by
    obtain ⟨B,n,hB,hF⟩:=ground_pay f h
    refine ⟨_,n,hB,fun i=>?_⟩; unfold patcher;split;exact hF i
    rw [norm_zero]; exact mul_nonneg hB (liftCost_pos n i.1)
lemma jump_pay (f:E4→G.Color)(h:f∈rangeLt G.Color (n+1)) : Stipend (assigns (jump f)):= shoulder (jump_band h)
lemma flyers (f:E4→G.Color)(h:f∈ rangeLt G.Color n): Stipend (fun p:edgeL G=> f (Place.seat p.1 + basis (bearing p)) p.2.2):= by
    obtain ⟨A,H,hp⟩:=band_growth h; refine ⟨A*2^n,n,mul_nonneg H (by positivity),fun p=>?_⟩
    dsimp only; rw [←EuclideanSpace.basisFun_inner G.ColorIndex ℝ _ _]; apply le_trans (norm_inner_le_norm ..); rw [OrthonormalBasis.norm_eq_one,one_mul]; apply (hp _).trans
    rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ H; unfold liftCost; rw [←mul_pow];apply pow_le_pow_left₀ (by positivity); have he:= shade_seat p.1; have hh:=norm_add_le (Place.seat p.1) (basis (bearing p)); rw [show ‖basis (bearing p)‖=1 from by simp [basis]] at hh; linarith
lemma press_merit (S:Fin (l+1) → edgeL G→ℝ)(o:Loc G 1)(T:Tile (edgeL G) (l+1))(h:Knoxville (fame _) η (0,o) T A)(he:0<η)(hp:∀ i, Stipend (S i)): tariffs S T=∑' v:chain (edgeL G) l,(∑' i:edgeL G,T (Fin.cons i v) * S 0 i) * ∏ i,S (Fin.succ i) (v i):= by
   let e:chain (edgeL G) l × edgeL G≃ chain (edgeL G) (l+1):= (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _:Fin (l+1)=> _)); let F(v:chain (edgeL G) (l+1)):= T v*∏ i,S i (v i); have H:(Summable (F ∘ e)):= e.summable_iff.mpr ((pays_product S o he hp).choose_spec.2 T A h).1
   change (∑' v,F v)=_; rw [←Equiv.tsum_eq e F]
   change (∑' v, (F ∘ e) v)= _; rw [Summable.tsum_prod H]; refine tsum_congr fun v=> ?_; rw [←tsum_mul_right]; refine tsum_congr fun x=>?_ ; unfold F;change T _*(∏ i: Fin (l+1), S i ((Fin.cons x v : chain (edgeL G) (l+1)) i)) = _; rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ, mul_assoc];rfl
lemma pace_term (f:edgeL G→ℝ)(v:chain (edgeL G) l)(T:Tile (edgeL G) (l+1))(H:Knoxville (fame _) η (0,o) T A)(h:Stipend f)(he:0<η): Summable (fun x=> T (Fin.cons x v)* f x):= by
    let U (i:Fin (l+1)) : edgeL G → ℝ :=Fin.cases f (fun _=>fun _=>1) i; have hz i:Stipend (U i):= by refine Fin.cases ?_ (fun i=>?_) i; exact h; exact ⟨1,0,zero_le_one,fun i=> by change ‖(1:ℝ)‖≤ _; simp [liftCost]⟩
    have hv := (pays_product U o he hz).choose_spec.2 T A H |>.1; apply ((hv.comp_injective (show Injective (fun x=> (Fin.cons x v : chain (edgeL G) (l+1))) from fun x y e=>congr_fun e 0))).congr
    intro i; simp only [comp_apply,Fin.prod_univ_succ,U, Fin.cases_succ, Fin.cases_zero,Fin.cons_zero,Finset.prod_const_one,mul_one]
lemma fade (f:E4→ G.Color)(ht:f∈rangeLt G.Color (n+1))(x:chain (edgeL G) l)(T:Tile (edgeL G) (l+1))(hp:0<η)(h:Knoxville (fame _) η (0,o) T A)(hs:Knoxville (fame _) η (0,o) (tap T) B):
     (∑' i,T (Fin.cons i x)* assigns (jump f) i)=∑' i,tap T (Fin.cons i x)*patcher f i := by
    let u (p:Cover):= f (Place.seat p)
    let S (y:Cover)(a : TypeFace 1)(i:hue G):= T (Fin.cons (y,a,i) x)
    have H(i:hue G)(a: TypeFace 1):
       (∑' y:Cover, T (Fin.cons (y,a,i) x)*assigns (jump f) (y,a,i))=∑' y:Cover,(S y a i-S (backwards y a) a i)* u y i := by
         let g : Cover ≃ Cover := Equiv.addRight (step (axisEquiv.symm a)); let F (y:Cover): edgeL G:= (y,a,i);
         have hF:Injective F:= fun p q hx=> congr_arg (fun p:edgeL G=>p.1) hx
         have hv: Summable fun y=> S y a i*u y i:= (pace_term _ x T h (ground_pay f ht) hp).comp_injective hF
         have he : Summable (fun y=> S y a i * u (g y) i) := by
            have hh := (pace_term _ x T h (flyers f ht) hp).comp_injective hF
            apply hh.congr; intro y; unfold u g; simp only [Place.seat_add,seat_step,Equiv.coe_addRight];rfl
         let w (y:Cover):=backwards y a
         have hP y:w (g y)=y:= by simp [w,g,backwards]
         have hU: (fun y=>S y a i* u (g y) i) = (fun y=> S (w y) a i *u y i) ∘ g:=by ext y; simp [hP]
         have hu : Summable fun y=> S (w y) a i *u y i:= g.summable_iff.mp (hU ▸ he)
         have hj y: assigns (jump f) (y,a,i)= u y i-u (g y) i:=by unfold assigns jump u g; simp only [Place.seat_add,seat_step,Equiv.coe_addRight]; rfl
         simp_rw [hj,mul_sub,sub_mul]; change (∑' y,(S y a i*u y i- S y a i * u (g y) i))= _; rw [Summable.tsum_sub hv he,Summable.tsum_sub hv hu];congr 1;change (∑' y,(fun t=> S t a i*u (g t) i) y)=_; rw [hU]; exact g.tsum_eq (fun y => S (w y) a i * u y i)
    rw [Glide.sum_strip (pace_term _ x T h (jump_pay f ht) hp),Glide.sum_strip (pace_term _ x _ hs (patcher_pay f ht) hp)]; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; conv_lhs=> rw [Finset.sum_comm];
    conv_rhs=> rw [Finset.sum_comm];
    refine Finset.sum_congr rfl fun i hi=>?_ ; rw [Finset.sum_eq_single (s:= (Finset.univ:Finset (TypeFace 1))) (f:=fun a=> ∑' y:Cover,tap T (Fin.cons (y,a,i) x)*patcher f (y,a,i)) (Exterior.coord 0)]; swap;· intro a _ ha; simp [patcher,ha]
    swap; · simp
    simp_rw [H]; rw [← Summable.tsum_finsetSum]; swap
    · intro a _; let F(y:Cover):edgeL G:=(y,a,i); let g : Cover≃Cover:=Equiv.addRight (step (axisEquiv.symm a)); simp_rw [sub_mul]; apply Summable.sub
      · exact (pace_term _ x T h (ground_pay f ht) hp).comp_injective (i:=F) (fun p q hx=> congr_arg (fun p:edgeL G=>p.1) hx)
      apply g.summable_iff.mp; apply ((pace_term _ x T h (flyers f ht) hp).comp_injective (i:=F) (fun p q hx=> congr_arg (fun p:edgeL G=>p.1) hx)).congr;intro x; simp [u,g,backwards,F,S,Place.seat_add,seat_step,bearing]
    apply tsum_congr; intro y; rw [←Finset.sum_mul]; simp only [tap, patcher, Fin.cons_zero,Fin.tail_cons,↓reduceIte, riverP,Finset.sum_apply,Pi.sub_apply]; rfl
end YM.FormalBulk08.Grail
