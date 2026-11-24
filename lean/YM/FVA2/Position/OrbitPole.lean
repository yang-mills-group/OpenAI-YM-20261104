import YM.FVA2.Position.Park
/-! # Projection equivariance of dimensional-pole program, before continuum evaluation -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Park
open Function Set Filter Finset MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Landau MS.Koszul MS.Landau.Detect
open MS.Book MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire MS.Alps
open MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Hem MS.Dock MS.Train MS.Pearl
open _root_.YM.MS.Shine Brass MS.Color
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {J:Type}{m n k:ℕ}{G:Gauge} (s t:Signed)
variable {X Y:Rack G m}{A B F: Mob G}{f:ℂ→Mob G}{U:Rip G}{r q:ℤ}
local notation "Ω"=> hoop s
lemma sh_h (h:Shine.Lift f F): Shine.Lift (fun i=> Ω (f i)) (Ω F):= by obtain ⟨g,R,hr,hg,h,rfl⟩:= h; exact ⟨_,R,hr,holS s hg,h.mono fun i hi=> congr_arg (Ω) hi,rfl⟩
lemma live_w (h:Live f): Live (fun i=>Ω (f i)):= h.elim fun _ h=> Exists.intro _ (sh_h s h)
lemma mer_w (h:mer f): mer (fun i=>Ω (f i)):= by obtain ⟨u,h⟩:=h; refine ⟨u,?_⟩; rw [altitude, show paid u (fun i=> Ω (f i))= (fun i=>Ω (paid u f i)) from funext (fun i=> (map_smul Ω (i^u) _).symm) ]; exact live_w s h
lemma price_h (h:Sun false f): Sun false (fun i=>Ω (f i)):= ⟨mer_w s h.mer,(sunny h).mono fun _ hi=> (flows s hi).token⟩
lemma tint (x:Shore G m) (f:Rack G m): D x (Brass.cash s m f)=(tt s x.1:ℂ) • Brass.cash s m ( D (torso s x) f ):= by ext l; rw [at_D,evaluate,Track,rack,List.map_cons,List.map_cons,List.prod_cons,Complex.ofReal_mul,mul_assoc,Pi.smul_apply,evaluate]; rfl
lemma pace_t (ξ:G.El)(f:Rack G m): repeatC ξ (Brass.cash s m f)=Brass.cash s m (repeatC ξ f) := by
 ext l; induction l generalizing f with| nil=> simp | cons x l ih=> simp only [ D_eval x, c_prefix,tint,map_smul,map_sum, ih, Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=> mul_left_comm ..)
lemma symm_w (h: Rock.sym F): Rock.sym (Ω F):= by
 intro m l i j k; have he: Track s (l++i::j::k)= Track s (l++j::i::k):= by simp only [Track,List.map_append,List.map_cons,List.prod_cons,List.prod_append]; rw [mul_left_comm (tt s i.1)];
 rw [hop,hop, he]; unfold rack; simp only [List.map_append,List.map_cons]; rw [ h m ]; have hv ( i:Shore G m):field Landau.parity (torso s i)=field Landau.parity i:=by rcases i with ⟨⟨⟨ _|i,b⟩,c⟩,p⟩ <;> rfl
 rw [hv,hv,mul_left_comm]
lemma issue_w (h:Issue r F): Issue r (Ω F):= by intro m w hw; rw [hop,h m _ (show ( ( rack s w).length:ℤ)>r from ?_),mul_zero]; simpa [rack] using hw -- shadow >.
lemma hair_h (w:Legs (Shore G m)): hair (rack s w)=hair w:= by induction w with| nil=>rfl|cons i l ih=> rw [rack,List.map_cons,Garment.hair,field_cons,show fieldDim ghostNo (l.map (torso s))= _ from ih]; unfold Garment.hair; rw [field_cons]; rcases i with ⟨⟨⟨ _|i,b ⟩,c⟩,p⟩ <;> cases b <;>rfl
lemma coagulant (h:Collar r F): Collar r (Ω F) := ⟨symm_w s h.sym,(by intro m ξ; change repeatC ξ (Brass.cash s m _) = _ ; rw [pace_t,h.color]; rfl), (by intro m w hw; rw [hop,h.ghost m _ (hair_h s w|>.symm ▸ (show hair w ≠ r from hw) : hair (rack s w) ≠ _ ), mul_zero])⟩ -- ▸ misuse
lemma rear_s (w:Legs (Shore G m)): rack s (invertMom w)=invertMom (rack s w) ∧ Track s (invertMom w)= Track s w:= by
    unfold rack invertMom Track; simp only [ List.map_map ]; refine ⟨ ?_,rfl ⟩; congr! 1; funext i; exact Prod.ext rfl (map_neg ( viewD s m ).turn i.2)
lemma sees_w (h:Sight F): Sight (Ω F):= by intro m l; rw [hop,hop,(rear_s s l).1,(rear_s s l).2,h m,star_mul']; simp -- star ofReal
lemma Fw (h:Fine false r f) : Fine false r (fun i=>Ω (f i)):= ⟨price_h s h.tune,h.ghost.mono fun _ hi=> coagulant s hi, show realAlong _ _ from Eventually.mono h.sense fun _ hi=> sees_w s hi ⟩
lemma Cw (h:Cap0 false r q f): Cap0 false r q (fun i=>Ω (f i)):= ⟨Fw s h.fine,h.cap.mono fun _ hi=>issue_w s hi⟩
open MS.Hem.Mell
-- scaling and differentiated heat kernels commute
lemma weightP (w:Legs (Shore G m)): mass (rack s w)=mass w:= by induction w with| nil=>rfl | cons i l ih=> rw [rack,List.map_cons,Price_cons, (show mass ( l.map (torso s) )= _ from ih), Price_cons]; rcases i with ⟨⟨⟨_|i,b⟩,c⟩,p⟩ <;> cases b <;> rfl
lemma weightL (t:ℝ)(w:Legs (Shore G m)): rack s (sr t w) = sr t (rack s w) ∧ Track s (sr t w)=Track s w:= by unfold rack sr Track; simp only [List.map_map]; refine ⟨ ?_,rfl⟩; congr! 1; funext i; exact Prod.ext rfl (map_smul (viewD s m).turn (Real.exp t) _)
lemma plow_t (x:ℂ)(t:ℝ): plow x t (Ω F)= Ω (plow x t F):= by ext l i; rw [hop]; simp_rw [plow,hop,weightP,(weightL s t i).2, (weightL s t i).1]; exact mul_left_comm ..
lemma nervous {i:ℂ}(h:Mell.Trail A B i): Mell.Trail (Ω A) (Ω B) i:= by refine ⟨ fun t=>?_⟩; intro m w; simp_rw [ plow_t,hop ]; exact (h.derive t _ (rack s w)).const_mul _
lemma station (h:Home F k): Home (Ω F) k:= by intro x; rw [plow_t,h x]
lemma W {L:Filter J}{v:J→ Mob G}(h:Wind v L F): Wind (Ω ∘ v) L (Ω F):= by intro m l; simp_rw [Function.comp_apply,hop]; exact ( h m ( rack s l ) ).const_mul _
lemma cone_t (h:Cool f): Cool (fun i=>Ω (f i)):= by
    let Q:= tapeL (G:=G) (fun _=>Ω); suffices he: cone G ≤ Submodule.comap Q (cone G) from he h; refine Submodule.span_le.mpr ?_; rintro f ⟨m,h,F,rfl⟩; change Cool (fun i=>Ω ( Ice m F i )); simp_rw [Ice,map_smul]; exact iceC _ m h
-- `Flats` = stores arbitrary ℓ, fixed each rank.)
def coat_t : Coat G→ₗ[ℂ] Coat G:= tapeL fun _=> Ω
def flats_t : Flats G→ₗ[ℂ] Flats G:= blast 0 (coat_t s)
lemma coat_x (f:Coat G)(x:ℂ): coat_t s f x=Ω (f x):= rfl
lemma flats_x (F:Flats G)(x:ℕ): ( flats_t s F ) x= coat_t s (F x):=blade 0 F (coat_t s) x
lemma flats_zk (F:Coat G)(i:ℕ): flats_t s (Finsupp.single i F)=Finsupp.single i (coat_t s F):= blast_sl ..
variable {X Y P: Flats G}{p f: Coat G}
lemma clash (h:ClockD false q r X): ClockD false q r (flats_t s X):= by intro i; rw [flats_x]; exact Cw s (h i)
lemma sky_t (h:Vibe k X Y): Vibe k (flats_t s X) (flats_t s Y):=by filter_upwards [h] with i hi l; rw [flats_x,flats_x]; exact nervous s (hi l)
lemma billow {f:Coat G}(h:Return X f k): Return (flats_t s X) (coat_t s f) k:= by filter_upwards [h] with i hi; simp_rw [flats_x,coat_x, plow_t]; exact W s hi
lemma ticket_y (f:Mob G)(x:ℂ)(h ℓ:ℕ)(y t:ℝ) : hikeP x h ℓ y t (Ω f)= Ω (hikeP x h ℓ y t f) := by unfold hikeP; rw [plow_t,map_smul]
lemma card (F:Flats G)(x:ℂ)(h:ℕ)(y u:ℝ): Parade (flats_t s F) h y u x= Ω ( Parade F h y u x ):= by
 induction F using Finsupp.induction_linear with -- syntax
 | zero=> simp_rw [map_zero,pageZ,Pi.zero_apply,map_zero];
 | add X Y hx hy=> simp only [map_add,page_add, Pi.add_apply,hx,hy]
 | single i A=> rw [flats_zk,page_sl,page_sl]; exact ticket_y ..
lemma Direct (h:Joint k P X f p): Joint k (flats_t s P) (flats_t s X) (coat_t s f) (coat_t s p):= by
 refine ⟨ sky_t s h.advance,fun y t=>?_, ?_, cone_t s h.ice, mer_w s h.worth, fun i=> station s (h.back i), by rw [← map_add]; exact billow s h.sip⟩
 · rw [funext (card s X · k y t) ]; exact live_w s (h.toll y t)
 intro m; rw [flats_x]; exact mer_w s (h.wet m)
end YM.FVA2.Position.Park
