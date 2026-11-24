import YM.MS.Orbit.Papers
/-!
# midpoint → based phase wheel.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch
open scoped Topology ContDiff Interval
variable {A I E: Type}{G:Gauge}{F H: Law G}{P Q: Latch.Edge G}
abbrev Lengths (G:Gauge):= Legs ( Lane4 G )
local notation "Z"=> field ( parity ( A:=Axis ) ( C:=G.ColorIndex) )
def weightψ (i: Lane4 G):= bill i.2 (offset i.1.1)
def flag (k:BH G)(p:QP):= weightψ (k,p)
def lace (i:Lane4 G):= flag i.1 (-i.2)
lemma lace_nc (k: Lane4 G): lace k≠0:= Complex.exp_ne_zero _
lemma nonza (k:Lane4 G): weightψ k≠0:= Complex.exp_ne_zero _
lemma inversePa (i: Lane4 G): lace i=( weightψ i )⁻¹:= opp ..
lemma lace_ (k:Lane4 G): weightψ k*lace k=1:= by rw [inversePa]; exact mul_inv_cancel₀ (nonza k)
lemma flag_ (k:BH G)(q:QP): flag k q * flag k (-q) =1:= lace_ (k,q)
lemma flagR (k:BH G)(i:Cover)(p:QP): flag k (p+rep i)= flag k p*veil i k:= payadd ..
lemma flagN (k:BH G)(i:Cover)(p:QP): flag k (p-rep i)= flag k p*veil i k:= by rw [sub_eq_add_neg,← map_neg, flagR, backv]
lemma laceR (k:BH G)(i:Cover)(p:QP): lace (k,p+rep i)= lace (k,p)*veil i k:= by unfold lace; simp only; rw [ show -(p+rep i)=-p-rep i from (by abel),flagN ]
-- multiplier.Health.
abbrev hook (k:Lane4 G→ℂ) (x:Lengths G):= (x.map k).prod
def sleeve (k:Lane4 G→ℂ) : Op (Lane4 G) ℂ:={
   toFun F:= fun x=> hook k x* F x
   map_add' a b:= by ext; exact mul_add ..
   map_smul' u v:= by ext; exact mul_left_comm .. }
@[simp] lemma sleeve_here (k:Lane4 G→ℂ)(F:Law G)(x:Lengths G): sleeve k F x=hook k x* F x:=rfl
lemma hook_c (x:Lengths G): hook weightψ x*hook lace x=1:= by induction x with| nil=> exact one_mul _| cons i x ih=> rw [ show hook lace (i::x)= _ from List.prod_cons, show hook weightψ (i::x)=_ from List.prod_cons, mul_mul_mul_comm ]; rw [lace_, ih,one_mul] -- `{_, List.prod_cons}` parse
abbrev dope (P:Latch.Edge G): Latch.Edge G:= fun i j p=> flag i p * lace (j,p) * P i j p
lemma dope_p (K: Latch.Edge G)(i j:BH G)(p:QP): dope K i j p= flag i p * flag j (-p) * K i j p:=rfl
lemma Dk_rev (hk:Reverse P parity): Reverse (dope P) parity:= by intro i j p; simp only [dope_p,neg_neg,hk]; ring
lemma Dk_near (hk:City.Near P)(p q:QP)(i j:BH G)(hp:congrQ p q): dope P i j p= dope P i j q:= by obtain ⟨v,rfl⟩:=hp; unfold dope; rw [flagR,laceR,hk ]; ring_nf; simp [pow_two, testX ] -- grouping
lemma Dk_cl {c:Bool}(h:Flux.closed P parity c): Flux.closed (dope P) parity c:= fun i j p hp=> h i j p ( right_ne_zero_of_mul hp ) -- names inspect
/- strict reversal of vector fields only. -/
def antiZ : Signed := ⟨ Equiv.refl _,fun _=> true ⟩
def gscore (i:Lane4 G):ℂ:= City.tick antiZ i.1
lemma g_2 (i:Lane4 G): gscore i*gscore i=1:= City.tick2 ..
lemma antiR (p:QP): antiZ.act p= -p:=rfl
lemma antiN (k:BH G): passN antiZ k=k:= by rcases k with ⟨⟨_|i,b⟩,k⟩ <;> rfl
def switch (i:Lane4 G): ℂ:= gscore i*lace i^2
abbrev reverseX (i:Mode A E) [Neg E]: Mode A E:= ⟨ i.1,-i.2 ⟩
lemma turnβ (i:Lane4 G): switch i * switch (reverseX i)=1:= by unfold reverseX switch; rw [ show gscore (i.fst,-i.snd)=gscore i from rfl, show lace (i.fst,-i.snd)= weightψ i from (by unfold lace; simp; rfl), mul_mul_mul_comm,g_2, ← mul_pow,mul_comm (lace _), lace_, one_pow,one_mul ] -- `$simp` flag
lemma switch_pin (i:BH G): pinQ (fun p=>switch (i,p)):= by rintro p q ⟨x,rfl⟩; dsimp only; unfold switch; rw [ laceR,mul_pow, pow_two (veil _ _),testX,mul_one]; rfl -- gscore rfl
lemma cpuS (t:ℝ)(i j:BH G)(p:QP): Cpu G t i j (-p)= gscore (i,p)*gscore (j,p)* Cpu G t i j p := by simpa only [antiR, antiN] using! turn_p antiZ p t i j
lemma scoreD (t:ℝ)(i j:BH G)(p:QP): dope (Cpu G t) i j (-p)= dope (Cpu G t) i j p *(switch (i,p)*switch (j,-p)):= by
   simp only [ dope_p, neg_neg,cpuS,switch,lace ]; rw [ show gscore (j,-p)=gscore (j,p) from rfl ]; let a:= flag i p; let b:= flag i (-p); let v:=flag j p; let c:=flag j (-p);
   calc
     _ = ( flag i p * flag i (-p))*( flag j p * flag j (-p))*(flag i (-p)* flag j p* ( gscore (i,p)*gscore (j,p)*Cpu G t i j p)):= by rw [ flag_,flag_,one_mul,one_mul ]
     _ = _:= by ring
end YM.MS.Orbit
