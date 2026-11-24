import YM.MS.Swirl.Mace
/-!
# Infinitesimal diagonal regrading
Requires C S C = - C (only an inverse on the gauge slice); no inverse on residuals.
 Include fees by hand for ghost/read powers: fee is on middle leg and must land on _last_,
 not first, for fermion-kinetic pairing with two differently scaled kinds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Cylinder Orbit Cog Orbit.LogReal Book Convolve Puff Actors
open scoped Topology ContDiff Interval
variable {I E A:Type}{p:Sector A}{F H:BL A}{n j k:ℕ}{h v:ℤ}{K L:Grain A} (b:A→ℂ)
local infix:70 " ⋆ "=> product p
abbrev Owed (b:A→ℂ)(l:List A):= (l.map b).sum
/-- Dressed arity clock. Linear on ordered series -/
def Tick (b:A→ℂ): Op A ℂ := {
   toFun f l:= Owed b l * f l
   map_add' _ _:= funext fun _=> mul_add ..
   map_smul' _ _:= funext fun _=> mul_left_comm .. }
lemma till_bt (f:A) : D f (Tick b F)= Tick b ( D f F)+b f • D f F:= by ext l; change (b f+Owed b l) * F (f::l) =_+_; simp [add_mul,Tick,add_comm]
lemma TIC : Tick b ( F ⋆ H )= (Tick b F) ⋆ H+F ⋆ ( Tick b H ):= by
    funext l; rw [ Pi.add_apply, scattered,scattered ]; let Q:= allocate p l ( R:=ℂ ); change Owed b l*(F ⋆ H) l=Q _+ Q _; rw [ ← map_add,scattered,show Owed b l * scatter p l (fun a d=> F a*H d)=_ from ( Q.map_smul (Owed b l) (fun a d=>F a*H d) ).symm ]
    refine scatter_congr p _ _ _ ?_; intro a d hp; change Owed b l *( F a*H d )=Owed b a*F a* H d+ F a*(Owed b d*H d); rw [show Owed b l=Owed b a+Owed b d from (by simpa using ( (split_perm hp).map b ).sum_eq.symm) ]; ring
variable [Fintype A] (he:Clear p K)(hv:Cog.Sym p K)(hp:Symm p F)(hF:F∈ Mini A)
omit [Fintype A] in
lemma trSym (h:Symm p F): Symm p (Tick b F):= by intro l i j r; change _* F _=_*(_ * F _); rw [h l i j r]; simp_rw [Owed,List.map_append,List.map_cons,List.sum_append,List.sum_cons]; ring
lemma collect (f:A)(t:A→BL A): (∑ i:A, b i • ( D f (atLetter i) ⋆ t i ))= b f • t f:= by
    classical
    rw [ Finset.sum_eq_single_of_mem f ( Finset.mem_univ _ ),hear ]; · rw [coin_product,one_smul]
    intro i hi ht; rw [unheard i (Ne.symm ht)]; simp
lemma overture (h:Symm p F): Tick b F=∑ x:A,b x • ( atLetter x ⋆ D x F ):= by
   funext l; induction l generalizing F with
   | nil=> rw [ Finset.sum_apply, Finset.sum_eq_zero ]; exact zero_mul _ -- tick 0* maybe not rfl
           intro i hi; rw [ Pi.smul_apply,smul_eq_mul ]; rw [ show (atLetter i ⋆ D i F) []=0 from Eq.trans (times_nil ..) ( zero_mul _ ), mul_zero ]
   | cons i l ih=>
       rw [ D_eval i ( Tick b F ),D_eval i (∑ x:A,b x • ( atLetter x ⋆ D x F )), till_bt,map_sum ]; simp_rw [map_smul,D_product, smul_add, Finset.sum_add_distrib ]; rw [ collect ];
       have hm (x:A): Koszul.sign p (p i) (atLetter x) ⋆ ( D i ( D x F))= atLetter x ⋆ ( D x (D i F)):= by rw [ h.commute i x,(speaks_p x).signs, map_smul, map_smul, LinearMap.smul_apply,cross_comm (p x) (p i), smul_smul,cross_cross,one_smul ]; -- `_`
       rw [ Finset.sum_congr rfl (show ∀ x (_:x∈ Finset.univ), b x • ( Koszul.sign p (p i) (atLetter x) ⋆ (D i ( D x F))) = b x • (atLetter x ⋆ ( D x (D i F) )) from fun x _ => congr_arg ( b x • · ) ( hm x )) ]; rw [Pi.add_apply,Pi.add_apply, ih (h.drop i),add_comm ] -- ih F implicit?
omit [Fintype A] in
lemma rankM (h:Book.rank v F): F ∈ Mini A:= minH (Limit.up ( h:=v ) (fun l hp=> h l (by rw [Book.mod_int]; omega)) le_rfl)
lemma playbill (H:Book.rank 2 F)(x:A): D x F= ∑ j:A,F [x,j] • atLetter j:= by
    classical
    funext l; rw [ Finset.sum_apply ]; rcases l with _|⟨i,_|a⟩
    · rw [Finset.sum_eq_zero]; exact H _ (by simp); intro i _; exact mul_zero _
    · rw [Finset.sum_eq_single_of_mem i ( Finset.mem_univ i )]; · rw [Pi.smul_apply,speaks]; simp
      intro j hj ht; rw [Pi.smul_apply,notNamed _ (Ne.symm ht),smul_zero]
    rw [Finset.sum_eq_zero]; exact H _ (by rw [mod_int]; simp; omega); exact fun i _=> mul_zero _
omit [Fintype A] in
lemma ddS (H:Book.rank 2 F)(i j:A): D j (D i F)= coin ( F [i,j] ):= funext fun l=> by rcases l with _|⟨k,l⟩; rfl; exact H _ (by rw [mod_int]; simp; omega)
-- tilted changes.Difference
structure Green (b:A→ℂ)(K:Grain A)(S:BL A): Prop where
   reads (x y:A) : ∑ i:A, ∑ j:A, b i* Chill K x i* S [i,j] * Chill K j y = - b y * Chill K x y
abbrev billT (K:Grain A)(b:A→ℂ)(H:BL A):= ∑ i:A,∑ j:A,b i * Chill K i j * H [i,j]
local notation "W"=> View K
local notation "C"=> Chill K
variable {b}
-- note Wick integrates BOTH degrees. contraction $…$ S oriented as listed.
include hv
lemma handsT (Hq: Green b K H)(x z:A)(j:A→A→ℂ): ∑ i:A,∑ k:A, b i * C i x * cross (p x) (p i) * H [i,k] * C k z*j x z = -b z*C x z*j x z := by
    simp_rw [ show ∀ i:A, b i* C i x* cross (p x) (p i)= b i* C x i from fun i=> by nth_rw 1 [traceS x i hv]; ring, ← Finset.sum_mul,Hq.reads ]
-- debt dimensions. $Z trace d F
include hp hF he
lemma trust (b:A→ℂ): W ( Tick b F )= ∑ i:A,∑ j:A, b j * C i j * W (D j (D i F)):= by
    rw [ overture b hp,map_sum ]; simp_rw [map_smul, smul_eq_mul];
    rw [ Finset.sum_comm ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [ ibpV i he hv (hp.drop i) (miD hF i), Finset.mul_sum ]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [traceS i j hv,hp.commute i j,map_smul,smul_eq_mul,cross_comm (p j) (p i)]; ring
-- quartet order
omit hv he hp hF
lemma square_sum (f:A→A→A→A→ℂ) : (∑ i,∑ x,∑ j,∑ z,f i x j z)=(∑ x,∑ z, ∑ i,∑ j,f i x j z):= by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; simp_rw [ show ∀ i:A,(∑ j,∑ z,f i x j z)=(∑ z,∑ j,f i x j z) from fun _=> Finset.sum_comm]; exact Finset.sum_comm
include he hv
-- contraction of S.P
lemma ssPal {i z:A}(h:Book.rank 2 H)(hx:Symm p F)(hp:F∈ Mini A): W ( D i H ⋆ D z F )=∑ j,∑ l, H [i,j]*C j l * W (D l ( D z F )):= by rw [playbill h,map_sum,LinearMap.sum_apply,map_sum]; refine Finset.sum_congr rfl fun j _=>?_; rw [map_smul,LinearMap.smul_apply,map_smul, ibpV j he hv ( hx.drop z ) (miD hp z), smul_eq_mul,Finset.mul_sum]; simp_rw [mul_assoc]
include hp hF
lemma pulseβ (b:A→ℂ)(hx:Book.rank 2 H)(ha: Pure p false H)(i j:A): b i * C i j * W ( D j ( D i H ⋆ F ))= b i * C i j * H [i,j] * W F + (∑ x,∑ z,b i*C i j* cross (p j) (p i)*H [i,x]*C x z * W ( D z ( D j F ) ) ):= by
    rw [ D_product, ddS hx,(ha.drop i).signs, Bool.false_xor,coin_product,map_smul,LinearMap.smul_apply,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,ssPal he hv hx hp hF ]; simp_rw [mul_add,Finset.mul_sum,mul_assoc] -- args order. h unused
lemma wage (h:Green b K H)(hx:Book.rank 2 H)(hs:Symm p H)(ha:Pure p false H): W ( Tick b F + ( Tick b H ) ⋆ F )= billT K b H * W F := by
    let z(i j:A):= W ( D j (D i F) ); rw [map_add, trust he hv hp hF b ]; -- args
    conv_lhs=> rw [ overture b hs ]; simp only [map_sum, LinearMap.sum_apply,map_sum,map_smul,LinearMap.smul_apply,smul_eq_mul,times_assoc,show ∀ i:A,W (atLetter i ⋆ ( D i H ⋆ F ))= _ from fun i=> ibpV i he hv ((hs.drop i).times hp) (miPair ( miD (rankM hx) i ) hF), Finset.mul_sum, show ∀ x y:A, b x * (C x y * W (D y ( D x H ⋆ F )))= _ from fun x y=> (mul_assoc (b x) (C x y) _).symm, pulseβ he hv hp hF b hx ha, Finset.sum_add_distrib ] -- order multiplication may rewrite inside ∑. hv ordering
    rw [ square_sum (fun i j x y=> b i* C i j* cross (p j) (p i) * H [i,x] * C x y* z j y) ]; simp_rw [handsT hv h,billT,Finset.sum_mul,neg_mul,Finset.sum_neg_distrib]; -- hp order hands
    unfold z; abel -- inspect
end YM.MS.Swirl
