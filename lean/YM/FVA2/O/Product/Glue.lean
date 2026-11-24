import YM.FVA2.O.Product.Snake
/-!
# Crossing operations. product covariance including integer ghost.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Serve
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives
open scoped Topology ContDiff
variable {G:Gauge}{B:Deck G}{O:Booked B} {x y:Law G}{I J:Type}{F H F' H':Glade G I}{S:MS.Scale J}{p q: I→ QP}{X X' Y Y':T (Glade G I)}{M:MS_Data G O}{η:I→ℝ}{r n:ℤ}{i:I}
local infix:70 " ⋄ " => product (field Landau.parity)
lemma solidP (h:Solid false x r)(hp: Solid false y n): Solid false ( x ⋄ y ) (r+n):= by
    obtain ⟨he,hx⟩:=(Local.Physical.room _ _).mp h; obtain ⟨hh,hy⟩:=( Local.Physical.room _ _).mp hp; apply (Local.Physical.room _ _).mpr; refine ⟨ ⟨ (clayS h).times (clayS hp), fun i=>?_,?_ ⟩,(show Rails (ghostNo ∘ Prod.fst) (r+n) _ from Rails.product hx hy)⟩
    · rw [ show repeatC i ( x ⋄ y ) = _ from Lifting.linkC (F:=x) (H:=y) i, he.color i,hh.color i ]
    rw [ show overC (x ⋄ y) = _ from ( Lifting.over_p ( F:=x ) ( H:=y ) ), he.shadow, hh.shadow ]
-- scaled cost all momenta
lemma leaseP {a b:J→ℝ}{X Y:J→Law G}(h:Latch.Lease false false S X a)(hp:Latch.Lease false false S Y b) : Latch.Lease false false S (fun j=> X j ⋄ Y j) (a*b):= by
    intro E _ _ w _ _; unfold Cape Chart; simp_rw [scattered,sail_scatter]; refine gather_bound w fun l r ht=>?_ ;
    obtain hl:= Costs.mul (h E l (fun x=>Bool.noConfusion x) (fun x=>Bool.noConfusion x)) (hp E r (fun x=>Bool.noConfusion x) (fun x=>Bool.noConfusion x)); apply hl.raise; apply Cost.of_le; intro i p _; simp only [Pi.mul_apply]; rw [← w_mass ht,zpow_add₀ (S.pos _).ne']; exact le_of_eq (by ring)
-- grid pair & operator.Powers.Pow.
abbrev joint (G:Gauge)(I:Type) : Pair (Glade G I):= Puff.points I (fun _=> Puff.points ℝ (fun _=> product (field Landau.parity) ))
lemma joint_mem (h:Bank F r)(he:Bank H n): Bank (joint G I F H) (r+n) where
    cross:= by
       constructor; · intro i t ht; obtain hx:= leaseP ( h.cross.cost i t ht ) ( he.cross.cost i t ht ); rw [one_mul] at hx; exact hx
       intro i l hx; simp_rw [show ∀ t,joint G I F H i t= _ from fun t=> (show joint G I F H i t= F i t ⋄ H i t from rfl),scattered ]; exact walk_tree.gath l _ (fun l r _=>Continuous.mul (h.cross.walk _ _ (fun x=>Bool.noConfusion x)) ( he.cross.walk _ _ (fun x=> Bool.noConfusion x) ))
    heat:= by obtain ⟨m,hm⟩:=h.heat; obtain ⟨k,hk⟩:= he.heat; refine ⟨m+k,?_⟩; rw [ Nat.cast_add ]; exact fun i t=>( hm i t ).pair (hk i t)
    tone i t:= solidP (h.tone i t) (he.tone i t)
lemma dual (h:Velocity F F')(he: Velocity H H') : Velocity (joint G I F H) (joint G I F' H+joint G I F H'):= fun i t=> Puff.HeatFlow.lead_pair (h i t) (he i t)
-- blending coefficients.
abbrev bond (G:Gauge)(I:Type): Pair (T (Glade G I)) := pairW (joint G I)
lemma joins (h:Banks X r)(ht:Banks Y n): Banks (bond G I X Y) (r+n) := fun i=> Bank.all_fin (antidiagonal i) (fun _ _=> joint_mem (h _) (ht _))
lemma cruise (h:∀ i, Velocity (X i) (X' i))(he:∀ i,Velocity (Y i) (Y' i))(n:ℕ): Velocity (bond G I X Y n) ((bond G I X' Y+ bond G I X Y') n):= by simp only [ bond,Pi.add_apply,paired, ← Finset.sum_add_distrib ]; exact Velocity.sum _ (fun i _=> dual (h _) ( he _ ))
end YM.FVA2.O.Serve
