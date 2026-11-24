import YM.RegulatorIR.Axial.Held

/-!
# Auxiliary budget inheritance and W1 across all horizons
Figures as before, prices only at each *fixed* release.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight PowerSeries
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {W:Type}{M:W→ℕ}{n:Page M→Side} {G:Gauge} {s m p k:ℕ}
variable {f:Side}

-- repetition of axial symmetry
lemma distributed {x y:ℝ→ Horizon G f} (a:Signed)(q:Side)(h:Even f.val)(hp:ribbon a x y): ribbon a (Halo.signed q x) (Halo.signed q y):=by
 apply hp.mono; intro t ht
 have hx (u: Edge (Site (q*f))) : castEdge q f (sent a u)= sent a (castEdge q f u):=by
    let v:= (posDir u.2).rotate a
    have hv: castSite q f (a.act u.1)= a.act (castSite q f u.1):=by rw [← wrap_lift u.1,wrap_signed,Halo.falls,Halo.falls,← wrap_signed]
    change castEdge q f (v.used (a.act _+0))=v.used (_+0)
    change _=v.used (a.act (castSite q f _)+0); rw [add_zero,add_zero]
    unfold Step.used castEdge; split <;> (dsimp only; first| (rw [map_sub,Halo.val_step,hv])|(rw [hv]))
 have hf (x:ℝ→ Horizon G f)(u) : orbLift (climb (t • Halo.signed q x t)) u= orbLift (climb (t • x t)) (castEdge q f u):=by rw [← show Halo.stampL q (t • x t) = t • Halo.signed q x t from (Halo.stampL q).map_smul t (x t)]; exact fire_orb q _ h _
 ext1 i;change climb (t • Halo.signed q x t) i=pull a 0 (orbLift _) i.val
 let v:= castEdge q f i.val
 rw [← show orbLift _ i.val = _ from lift_at (climb _) i,hf x i.val,ht,lifted a _ h, look,look, hf y (sent a i.val),hx];rfl

variable {S:Heir n G} (H:Reel S)(T:S.Accounts) (V:H.Follows T)(w:W) (hh:Common H)
variable {L:Meter W} (A:S.Supplies T L p k)(B:Aug.Amenities S L p k)
local notation "E" => eternal H w
local notation "R" => grove H w hh
local notation "F" => tele H T w
lemma recoup (x:Page (extent M w))(k): (E).census.cone k x= S.census.cone k (Sight.ray w x):=by
 let K:=Tariff.native (S.l (Sight.ray w x)) (S.hl _) k
 change K.uses _= K.uses (S.maps (Sight.ray w x)).pos;rw [H.realms];rfl
lemma recouple (x:Flap (extent M w))(k): (E).ceilingRoom.cone k x= S.ceilingRoom.cone k (slide' w x):=by
 rcases x with ⟨x,i,h⟩; exact Aug.cost_r H w i h x k
include V A hh
lemma scaled : (E).Supplies (F) Aug.light p k:=by
 refine ⟨?_,fun x i j h=> helium (R) (F) (knows H T w hh V) _ _ _⟩
 intro i hi j; obtain ⟨c,⟨v,b,hv,hb⟩,hH⟩:= A.bulk_price i hi j; refine ⟨_,Poly.standard _ (show v*(L.val w)^b≠⊤ from ENNReal.mul_ne_top hv (ENNReal.pow_ne_top (L.below _))),fun x=>?_⟩
 rw [recoup]; intro z y; exact (hH (Sight.ray w x) z y).trans (hb (Sight.ray w x))
omit V A hh
include B
lemma scaledA : Aug.Amenities E Aug.light p k:=by
 refine ⟨?_,?_,?_⟩
 · obtain ⟨c,⟨v,b,hv,hb⟩,hH⟩:= B.line; refine ⟨_,Poly.standard _ (show v*(L.val w)^b≠⊤ from ENNReal.mul_ne_top hv (ENNReal.pow_ne_top (L.below _))),fun x=>?_⟩; rw [recouple]; exact ⟨(fun z=> ((hH (slide' w x)).1 z).trans (hb (slide' w x))),fun z=> ((hH (slide' w x)).2 z).trans (hb (slide' w x))⟩
 · obtain ⟨c,⟨v,b,hv,hb⟩,hH⟩:= B.mean; refine ⟨_,Poly.standard _ (show v*(L.val w)^b≠⊤ from ENNReal.mul_ne_top hv (ENNReal.pow_ne_top (L.below _))),fun x=>?_⟩;rw [recouple]; exact ⟨(fun z=> ((hH (slide' w x)).1 z).trans (hb (slide' w x))),fun z=> ((hH (slide' w x)).2 z).trans (hb (slide' w x))⟩
 intro i hi j; obtain ⟨c,⟨v,b,hv,hb⟩,hH⟩:= B.budget i hi j; refine ⟨_,Poly.standard _ (show v*(L.val w)^b≠⊤ from ENNReal.mul_ne_top hv (ENNReal.pow_ne_top (L.below _))),fun x=>?_⟩
 rw [recouple]; intro z y; exact (hH (slide' w x) z y).trans (hb (slide' w x))

variable (i:ℕ)(h:i ≤ M w)
variable (hp:14≤k)
local notation "v" => Page.mk w i h
variable (ht:Layer.Sym (S.maps (Page.mk w i h)) (S.maps (Page.mk w i h)) (H.stem (Page.mk w i h)))(hR:Billed (H.stem (Page.mk w i h)))
variable (x y : ℝ→ Horizon G (n (Page.mk w i h)))(hx:ContDiffAt ℝ ∞ x 0)(hy:ContDiffAt ℝ ∞ y 0)
include V A B hx hy ht hh hp hR
-- any period gauge before separating inputs
lemma exhibit (D : reel_prop x y ∨ ∃ p,ribbon p x y) : Squares p (money (H.stance (Page.mk w i h)) (haloT T (Page.mk w i h)) x) (money (H.stance (Page.mk w i h)) (haloT T (Page.mk w i h)) y):=by
 intro j hj; apply sub_eq_zero.mp; apply flash
 let z:= fun p:Side=> Aug.sheet w i h p
 let f(Z:Side) := (F).orb (z Z); let g(Z:Side):= (R).stance (z Z); let t(Z:Side)(x:ℝ→Horizon G (n (Page.mk w i h))):= money (g Z) (f Z) (Halo.signed (Sight.slab Z) x)
 apply Carry.mono (Carry.add (defectC H T A B hp V hh w i ht hR hx hj) (defectC H T A B hp V hh w i ht hR hy hj))
 intro Z; obtain ⟨g,U,Y,hr⟩:= lode R F (knows H T w hh V) (z Z)
 have hx':t Z x=t Z y:=by
    rcases D with h|⟨a,h⟩
    · exact Ward.RangeR.norms Y (Halo.wave _ hx) (Halo.wave _ hy) (waveV _ (H.even _) h)
    exact (gilded Y hr (Halo.wave _ hx) (Halo.wave _ hy) (distributed a (Sight.slab Z) (H.even _) h)).symm
 let a:=t Z y;let l:= counts (Sight.slab Z)
 let X:= coeff j (money (H.stance (Page.mk w i h)) (haloT T (Page.mk w i h)) x); let u:= coeff j (money (H.stance (Page.mk w i h)) (haloT T (Page.mk w i h)) y)
 change ‖l*(X-u)‖ₑ≤ ‖coeff j (t Z x)-l*X‖ₑ+ ‖coeff j (t Z y)-l*u‖ₑ
 rw [hx',show l*(X-u)= -(coeff j (t Z y) - l*X)+ (coeff j (t Z y)-l*u) by ring, ← enorm_neg (coeff j (t Z y)-l*X)]; exact enorm_add_le ..
omit x y hx hy
set_option maxHeartbeats 1400000 in
lemma deeper (z:Side): let u:= Aug.sheet w i h z; ∀ x y:ℝ→ Horizon G (big w n u),ContDiffAt ℝ ∞ x 0 → ContDiffAt ℝ ∞ y 0 → reel_prop x y ∨ (∃ a,ribbon a x y) → Squares p (money ((R).stance u) (haloT F u) x) (money ((R).stance u) (haloT F u) y):=by
 intro u x y hx hy ht'
 refine exhibit R F (knows H T w hh V) z (fun _=>rfl) (scaled H T V w hh A) (scaledA H w B) i h hp ?_ hR x y hx hy ht'
 intro d x y; have hh: Layer.Sym (Carto G _ _ (H.even (Page.mk w i h)) (H.phase (Page.mk w i h))) (Carto G _ _ (H.even _) (H.phase (Page.mk w i h))) (H.stem (Page.mk w i h)):= by rw [← H.realms];exact ht
 specialize hh (Halo.filling (Sight.slab z) d) x y
 change H.stem (Page.mk w i h) ((playS (G:=G) (Sight.slab z) (H.even (Page.mk w i h)) (H.phase _)).wind d x) ((playS (G:=G) (Sight.slab z) (H.even (Page.mk w i h)) (H.phase (Page.mk w i h))).wind d y)=_ -- arg
 rw [Halo.steering,Halo.steering]; exact hh
end YM.RegulatorIR.Axial
