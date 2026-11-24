import YM.FVA2.SteadyBooked
/-!
# distinct sign from signed-axis and ghost grading: interaction-order involution of Landau
left/right marks. Auxiliary high continuation, transported through pole contractions (not after).
-/
noncomputable section
set_option autoImplicit false
namespace YM.MS.Reed
open Filter Topology Set Function MeasureTheory
open Plane Lifting Landau Landau.Detect Koszul Book Book.Convolve Book.Program Dock
open Pearl Train Outlook Mach Arts Arts.Spin Halo Arc Garment Hem Rock Rock.Path Alps Rock.Oceans
open Plane.Wire Arts.Pilot Color Flux
open scoped Topology Classical ContDiff
variable {A P:Type*}(K:A→Bool) {G:Gauge} {R:Type*}[CommRing R]
variable {l:Legs (Mode A P)} {m n h:ℕ}{v:ℤ}
section raw
variable {F H: Raw A R}
-- inversion by number of slots only; no relation to spin or BRST parity
abbrev ϕ (n:ℕ) : R:=(-1:R)^n
def J (A R:Type*) [CommRing R]: Op A R where
    toFun F l:= ϕ l.length*F l
    map_add' F H:=funext fun l=>mul_add (ϕ l.length) (F l) (H l)
    map_smul' c F:= funext fun l=> mul_left_comm (ϕ l.length) c (F l)
lemma rite (F: Raw A R)(l:Legs A): J A R F l=ϕ l.length*F l:=rfl
lemma c_l {c:ℕ} (l:Legs A) (H:l.length=c): (ϕ l.length:R)=ϕ c:= H ▸ rfl
@[simp] lemma rite1 : ϕ (n+1)=-(ϕ n:R):= by unfold ϕ; rw [pow_succ,mul_neg,mul_one]
lemma invol (n:ℕ) : ϕ n* (ϕ n:R)=1:= by unfold ϕ; rw [← mul_pow]; simp
lemma negC (a:A)(F:Raw A R) : D a (J A R F)=-(J A R (D a F)):= by ext l; rw [at_D,rite,List.length_cons,rite1,neg_mul ]; rfl
lemma J_sq (F: Raw A R): J A R ( J A R F )= F:= by ext l; rw [rite, rite,← mul_assoc,invol,one_mul ]
lemma collectL (s:Sector A)(l:Legs A)(f:Shared A R)(c:R): c*scatter s l f=scatter s l (fun i j=>c*f i j):= (map_smul (allocate s l) c f).symm
lemma vertex (p:Sector A)(F H: Raw A R) : J A R (product p F H)=product p (J A R F) ( J A R H):= by
    ext l; rw [rite,scattered, scattered, collectL]; refine scatter_congr _ _ _ _ fun i j hij=>?_ ; rw [← split_length hij,ϕ,pow_add,rite,rite]; unfold ϕ; ring
lemma pilot {A P:Type}[AddCommGroup P][Fintype A]{p:Sector A}(s:Arts.Pilot ℂ P p)(f:Row A P ℂ) : J _ ℂ (s.beam f)= s.beam (J _ ℂ f):= by
    ext l; induction l generalizing f with
    | nil=> simp [rite,ϕ]
    | cons i l ih=>
       rw [rite, Pilot.met, Pilot.met]; simp_rw [negC,map_neg,Pi.neg_apply,← ih,rite,List.length_cons,rite1, Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _=>?_ ); ring
                  -- replace
variable [Fintype A][AddCommGroup P]
lemma joins (K: Flux A P R)(s:Sector A)(F H: Row A P R): J _ R (tree s K F H)=tree s K (J _ R F) (J _ R H):= by
    ext l; rw [rite]; unfold Flux.tree; rw [collectL ]; refine scatter_congr _ _ _ _ fun i j hij=>?_ ; unfold attaches; dsimp only; simp_rw [Finset.mul_sum, rite,List.length_cons,← split_length hij,rite1, ϕ,pow_add ]; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=>?_ )); ring
lemma loop (K:Flux A P R)(q:P)(F:Row A P R) : J _ R (trc K q F)=trc K q ( J _ R F):= by
    ext l; rw [rite]; simp only [at_trc]; simp_rw [Finset.mul_sum,rite,List.length_cons,rite1,neg_neg, mul_left_comm (ϕ l.length) ]
end raw
section commentJ
variable {G:Gauge} {F:Mob G}
private lemma colorJ (f:Rack G n) (k:G.El) : repeatC k ( J _ ℂ f )= J _ ℂ ( repeatC k f ):= by
   ext l; induction l generalizing f with
   | nil=> simp [rite,ϕ]
   | cons i l ih=> rw [rite,repeat_cons,repeat_cons]; simp only [List.length_cons,negC,map_neg,ih,Pi.neg_apply,rite1,rite, Finset.mul_sum ]; refine Finset.sum_congr rfl (fun i _=>?_ ); ring
def χ (G:Gauge) : Mob G→ₗ[ℂ] Mob G where
   toFun F i:= J _ _ (F i)
   map_add' F H:= funext (fun i=>map_add (J _ _) (F i) (H i))
   map_smul' c F:= funext (fun i=> map_smul (J _ _) c (F i))
lemma reels (F:Mob G)(l:Legs (Shore G m)): χ G F m l=ϕ l.length * F m l:= rfl
lemma churn (F:Mob G) : χ G ( χ G F)=F:= funext fun i=> J_sq (F i)
private lemma sturdyJ {b:Bool}(he:Sturdy b F): Sturdy b ( χ G F) where
    turn n x h:= ( pilot _ _|>.symm ).trans (congr_arg ( J _ ℂ ) (he.turn n x h))
    grows h l:= Eq.trans ( reels .. ) (congr_arg₂ (· * ·) ( c_l _ (List.length_map ..) ) (he.grows h l))
private lemma cap_j (he: Issue v F): Issue v (χ G F):= fun n l h=> by rw [reels,he n l h,mul_zero]
private lemma collar_j (he:Collar v F): Collar v (χ G F):= by
    refine ⟨?_, fun i k=> Eq.trans (colorJ _ k) (congr_arg _ (he.color i k)),fun n l hl=> by rw [reels,he.ghost n _ hl,mul_zero]⟩
    intro i l p q r; simp only [reels, List.length_append,List.length_cons, he.sym i l p q r, mul_left_comm (ϕ _) ] -- rewrite he both matching?
private lemma sight_j (he:Sight F): Sight (χ G F):= by
    intro n w; rw [reels,reels,star_mul',he]; simp only [ϕ,star_pow,star_neg,star_one,invertMom,List.length_map ]
lemma hats {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](F:Mob G)(p:Touch G n E)(x:E) : fieldVal ((χ G F) n) p x=ϕ p.length * fieldVal (F n) p x:= Eq.trans (reels ..) (congr_arg ( · * F n ( sail p x ) ) ( c_l _ (List.length_map ..) ))
private lemma price {Y:Type} {z:UScale Y} {a:Y→ℝ}{f:Y→Mob G}(he:fell z a f) : fell z a (fun i=>χ G ( f i )):= by intro i E _ _ _ p; simp_rw [funext (hats (f _) p)]; exact (he i E p).L ((ContinuousLinearMap.mul ℝ ℂ) (ϕ p.length))
private lemma Jhol {D:Set ℂ}{f: Coat G}(he:Hol D f): Hol D (fun i=>χ G (f i)):= ⟨ fun c R hQ hZ=> price (he.price c R hQ hZ), fun i z=> by simp_rw [reels]; exact fun p hp=>(he.top _ _ p hp).const_mul _ ⟩
lemma loop_mer {f:Coat G}(hp:Shine.Lift f F): Shine.Lift (fun p=>χ G (f p)) (χ G F):= by obtain ⟨g,R,hr,h,H,rfl⟩:=hp; exact ⟨_,R,hr, Jhol h,H.mono (fun i hi=> congr_arg _ hi), rfl⟩
lemma mer_leaf {f:Coat G}(hp:Shine.mer f): Shine.mer (fun p=>χ G (f p)):= by obtain ⟨n,p,H⟩:= hp; exact ⟨n,_,Shine.Lift.congr (loop_mer H) (Eventually.of_forall fun i=> map_smul (χ G) (i^n) (f i))⟩
lemma Jfin {b:Bool}{t:ℤ}{f: Coat G}(he:Cap0 b t v f): Cap0 b t v (fun p=>χ G (f p)) := ⟨ ⟨ ⟨mer_leaf he.fine.tune.mer, he.fine.tune.dice.mono (fun _ h=> sturdyJ h) ⟩, he.fine.ghost.mono (fun _ h=> collar_j h), (show realAlong _ _ from Eventually.mono he.fine.sense (fun _ h=> sight_j h)) ⟩, he.cap.mono (fun _ h=> cap_j h) ⟩
lemma coverJ {b:Bool} {K:Mob G} (h:Form0 b K): Form0 b (χ G K):= ⟨ price h.price, sturdyJ h.token⟩
end commentJ
end YM.MS.Reed
