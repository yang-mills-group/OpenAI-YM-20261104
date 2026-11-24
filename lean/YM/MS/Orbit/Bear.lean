import YM.MS.Orbit.Alto
/-!
# Initial finite bulk.Just plane signs & Perk; no approximation. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {I A:Type}{G:Gauge}{p:Sector A}{n:Lattice.Side}{f:Law G}{x y:Lengths G}
local notation "Γ"=> field (parity (C:=G.ColorIndex) ( A:=Axis ))
lemma mir_formula (S:Cog p)(F:Raw A ℂ)(w:List A): S.mirror F w =(w.map S.spin).prod * F (w.map S.mode):= by
    induction w generalizing F with| nil=> simp only [Cog.mirror, Cog.wheel_nil,List.map_nil,List.prod_nil,one_mul]| cons i l ih=> rw [ D_eval i (S.mirror F), Cog.reflect ]; simp only [Pi.smul_apply, ih, at_D, List.map_cons,List.prod_cons, smul_eq_mul, mul_assoc]
def turnW (x:Lengths G): Lengths G:= x.map (fun x=>reverseX x)
lemma γ_turn (x:Lane4 G) : permute antiZ x=reverseX x:= by rcases x with ⟨⟨⟨_|i,b⟩,k⟩,p⟩ <;> rfl
lemma ting (x:Lengths G): hook switch x * hook lace (turnW x)= hook (negateField antiZ) x * hook lace x := by
    induction x with| nil=> rfl| cons i l h=>
       unfold turnW hook at *; simp only [List.map_cons, List.prod_cons]; rw [mul_mul_mul_comm (switch i), h, mul_mul_mul_comm (negateField antiZ i)]; obtain he:=lace_ i; have hv: lace (reverseX i)=weightψ i:= by unfold lace reverseX; simp; rfl
       rw [hv, switch]; change (negateField antiZ i*lace i^2* _)*_= _; congr 1; apply Eq.trans _ (mul_one (negateField antiZ i*lace i)); rw [← he]; ring -- indentation likely
lemma spins_b (h: SignedScope true f)(hx:net x=0): hook switch x*sleeve lace f (turnW x)=sleeve lace f x:= by rw [sleeve_here,sleeve_here,← mul_assoc,ting,show turnW x=x.map (permute antiZ) from (by rw [ funext (γ_turn (G:=G)) ]; rfl) ]; rw [mul_comm _ (hook lace x),mul_assoc]; exact congr_arg (hook lace x * ·) (h antiZ x (fun _=>hx)) -- `γ_turn point simp_rw` requires functional rewriting
lemma turn_twin (h:twins x y): twins (turnW x) (turnW y):= by induction h with| nil=>exact .nil| cons ht hp ih=> exact .cons ⟨ ht.1,ht.2.opp⟩ ih
lemma switch_u (x y:Lane4 G)(h:peer x y): switch x=switch y:= by obtain ⟨i,p⟩:=x; obtain ⟨j,q⟩:=y; obtain ⟨he,hx⟩: i=j∧ congrQ p q:=h; subst j; exact switch_pin _ hx
lemma fusionV (h:twins x y): hook switch x=hook switch y:= by induction h with| nil=> rfl| cons H h hz=> exact congr_arg₂ (· * ·) (switch_u _ _ H) hz -- Σ script
lemma gratis (x:Lengths G) (h: congrQ (net x) 0): ∃ y:Lengths G,twins x y ∧ net y=0:= by
   cases x with| nil=>exact ⟨ [],.nil,rfl ⟩| cons i l=> refine ⟨ (i.1,-net l)::l,.cons ⟨rfl,?_⟩ (asc l),by simp ⟩; obtain ⟨v,hx⟩:=h; refine ⟨ v,?_⟩; rw [net_cons,zero_add] at hx; rw [ ← hx ]; change i.2= -(net l)+(i.2+net l); rw [add_left_comm,neg_add_cancel,add_zero]
lemma step_t (h: Perk f)(hz:SignedScope true f)(hx: congrQ (net x) 0): hook switch x*sleeve lace f (turnW x)=sleeve lace f x:= by obtain ⟨w,hw,H⟩:= gratis x hx; rw [ volt h (turnW x) (turnW w) ( turn_twin hw ),fusionV hw, spins_b hz H ]; exact (volt h _ _ hw).symm
lemma sphere_d (w:List (FixedMode G n)): List.map ( iota G n ).spin w= List.map switch (stage w):= by induction w with| nil=>rfl| cons a w ih=> rw [List.map_cons,show stage (a::w)=addr a::stage w from rfl,List.map_cons, ih]; rfl
lemma twin_re (w:List ( FixedMode G n )): twins (stage (w.map (iota G n).mode)) ( turnW (stage w) ):= by induction w with| nil=>exact .nil| cons i l ih=> exact .cons ⟨rfl,(ξ_neg i.2).sym⟩ ih
lemma net_m (w:Legs (FixedMode G n)): net (List.map (iota G n).mode w)= - net w:= by induction w with| nil=> exact (neg_zero (G:=Lattice.Site n)).symm | cons i l h=> rw [List.map_cons,net_cons,h,net_cons, neg_add]; rfl -- group argument neg_zero. maybe no
lemma invarBulk (h:Perk f)(hp:SignedScope true f): (iota G n).Invar (Bulk G n ( sleeve lace f )):= by
   ext w; rw [mir_formula,bulkZ, bulkZ,sphere_d,net_m]; by_cases he: net w=0; swap; · simp only [ neg_eq_zero, if_neg he, mul_zero ]
   simp only [he, neg_zero, if_true, point, volt h _ (turnW (stage w)) ( twin_re w )]; rw [ mul_left_comm ]; apply congr_arg (brightness n*·); refine step_t h hp ?_; obtain hv:= θ_net w; rw [he, ξ_zero] at hv; exact hv
lemma pureB {u:Bool}(h:Pure Γ u f): Pure (σbranch (G:=G) ( n:=n )) u ( Bulk G n ( sleeve lace f )):= by
   intro i hi; rw [bulkZ]; split; · simp only [ point,sleeve_here,h _ ( Λ_d i ▸ hi ), mul_zero ];
   rfl
end YM.MS.Orbit
