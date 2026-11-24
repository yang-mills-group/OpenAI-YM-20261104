import YM.MS.Swirl.Dry
/-!
# Scaling the raw-leg symbol measure by multiplicative order series
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Filter Set Finset MeasureTheory Real
open Koszul Plane Cylinder Orbit Orbit.Cog Orbit.LogReal Book Convolve Program Puff Engine SplitP Actors Dynamics
open Mom (useN)
open PowerSeries (coeff)
open scoped Topology ContDiff Interval
variable {I E F J A:Type} [AddCommGroup E][Module ℂ E][AddCommGroup F][Module ℂ F]
variable {p:Sector A}{L H:BL A}{n:ℕ}{B:Actors E}(P:SplitP I)
-- SL with linear derivations is θ since no differential order index
lemma slCinch (M:I→ Linear E E)(h:∀ i,M i B.unit=0)(he:∀ i x,x∈ B.guard→ M i x ∈ B.guard)(hp:∀ i x y,M i (B.core x y)=B.core (M i x) y + B.core x ( M i y )) : Cinch P B ( SL P M ) := by
    refine {toFiltered:= Filtered.sl P M, still:= funext fun i=> (look_c P M i B.unit).trans (h i), earn:=fun {x} hx=>?_,earns:=?_ }; · exact (universe0 B.guard).mpr fun i=> B.guard.sum_mem (fun _ _=> he _ _ (hx _ ( Set.mem_univ _ )) )
    intro x y; funext i; change SL P M (P.Lift B.core x y) i= P.Lift B.core _ _ _+P.Lift B.core _ _ _; simp_rw [ slΩ,P.loan,slΩ,map_sum,hp,Finset.sum_add_distrib,LinearMap.sum_apply ]; exact congr_arg₂ (·+·) ( P.trip E i (fun i j k=> B.core ( M i ( x j ) ) (y k)) ) ( rewrap P E (fun i j k=> B.core ( x j ) ( M i ( y k ))) i )
local infix:70 " ⋆ "=> product p
abbrev ModeT (b:T ( A→ℂ )):= SL useN ( Tick ∘ b )
lemma acre (b:A→ℂ)(h:Pure p false H): Pure p false ( Tick b H ):= by intro l hl; change _ * H _=_; rw [ h l hl,mul_zero ]
lemma latchT (b:T ( A→ℂ )): Cinch useN (actor p) (ModeT b):= slCinch useN _ (fun i=> by ext l; change _*(coin (1:ℂ) (A:=A)) l = _; cases l; exact zero_mul _; exact mul_zero _ ) (fun i x hx=> acre ( b i ) hx) (fun i x y=> TIC ( b i ))
-- taxi.OK support and multiplicative
variable (V:A→ Cn)
set_option quotPrecheck false
local notation "Mτ"=> ( actor p ).stack useN
local notation "U"=> Program.taxi V
local infix:70 " ★ "=> Actors.core (Mτ)
lemma sl_taxi : U= SL useN (merit V):= rfl
lemma nilC (h:∀ i:A, Low ( V i ))(l:List A): Low (l.map V).prod:= by
    induction l with| nil=> exact PowerSeries.coeff_zero_one | cons i l ih=> unfold Low; simp only [ List.map_cons,List.prod_cons,PowerSeries.coeff_mul,Nat.antidiagonal_zero,Finset.sum_singleton ]; rw [ ( show coeff 0 (V i)=1 from h i ), show coeff 0 (l.map V).prod=1 from ih, one_mul ] -- prefix ambiguity
lemma taxi0 (h:∀ i:A,Low (V i))(X:T ( BL A )) : U X 0=X 0:= by rw [sl_taxi,slΩ,show useN.pieces 0=antidiagonal 0 from rfl,Nat.antidiagonal_zero,Finset.sum_singleton]; ext l; rw [offer,show coeff 0 (l.map V).prod=1 from nilC V h l, one_mul]
lemma translate0 (h:∀ i:A, Low ( V i )){X:T ( BL A )} (he:Happy useN X): Happy useN ( U X ):= Eq.trans (taxi0 V h X) he
lemma pureLeg (k:ℕ)(hx: Pure p false H): Pure p false (merit V k H):= by intro l hl; rw [offer,hx l hl,mul_zero]
lemma taxiP {X:T (BL A)}(h:X∈ (Mτ).guard): U X∈ (Mτ).guard:= fun i _=> Pure.sum (antidiagonal i) (fun j _=> pureLeg V j.1 ( h j.2 ( Set.mem_univ _ ) ))
lemma taxiUnit : U ( Mτ ).unit=( Mτ ).unit:= by
    ext i l; change U (useN.refineV ( Koszul.coin (1:ℂ) )) i l= useN.refineV (actor p).unit i l; rw [ sl_taxi,look_c ]; unfold SplitP.refineV; by_cases he:i=useN.origin
    · rw [ if_pos he ]; cases l; · rw [he,offer]; exact (show coeff 0 1 * 1=1 by simp) -- cast i error
      rw [offer]; exact mul_zero _
    rw [ if_neg he,offer ]; cases l; exact (show coeff i 1 * (1:ℂ)=0 by rw [PowerSeries.coeff_one, if_neg ( show i≠0 from he ),zero_mul] ); exact mul_zero _
lemma metra {X F:T ( BL A )} : U ( X ★ F )= U X ★ U F:= by
    apply retrace.injective; rw [ receipt, show ( _ ★ _ )=pairW ( product p ) X F from rfl, ← product_r, rv_prod ]; change _= retrace ( pairW ( product p ) _ _ ); rw [ ← receipt,← receipt, product_r ]
lemma taxshift (x:T (BL A))(hx:Happy useN x): U ( (actor p).Cheer useN x )=(actor p).Cheer useN (U x):= by
    have H:Tether U (Mτ) (Mτ):= ⟨ taxiUnit V,fun _ _=> metra V ⟩; funext i; rw [show Cheer _ useN (U x) i= U ((Mτ).cheers x i) i from (congr_fun (H.cheersV i x) i).symm]; rw [sl_taxi]; symm; exact ( Filtered.sl useN _ ).stays (n:=i) (fun j hj=> ( actor p ).overbook useN _ hx hj ) i ( le_refl i ) -- syntax braces
-- eur identity on x=const.X polynomial
variable {V}
def Eder (f:Cn): Cn:= PowerSeries.mk fun k=> (k:ℂ) * coeff k f
lemma paysD (f:Cn)(i:ℕ): coeff i (Eder f)= (i:ℂ)*coeff i f:= PowerSeries.coeff_mk i _
lemma prod_der (f g:Cn): Eder ( f*g )= Eder f*g+f* Eder g := by
   ext n; simp_rw [map_add, paysD,PowerSeries.coeff_mul,paysD,Finset.mul_sum,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i hi=>?_ ; obtain hp:= Finset.mem_antidiagonal.mp hi; rw [← hp]; push_cast; ring
-- b ∂ log.S only. at zero.
def Carrier (V:A→Cn)(b:A→Cn): Prop:= ∀ i,Eder (V i)= b i * V i
namespace Carrier
variable {b:A→Cn}(h:Carrier V b)
include h
lemma derX (l:List A): Eder (l.map V).prod=(l.map b).sum*(l.map V).prod:= by
   induction l with| nil=> ext i; simp only [paysD, List.map_nil,List.sum_nil, List.prod_nil, zero_mul, map_zero,PowerSeries.coeff_one]; split; rename_i hm; rw [hm]; simp; rw [mul_zero]| cons i l ih=> rw [List.map_cons,List.map_cons,List.prod_cons,List.sum_cons,prod_der,h i,ih]; ring
abbrev fees (b:A→Cn) : ℕ→A→ℂ:= fun i a=> coeff i ( b a ) -- check variable binder
omit h in
lemma coeff_T (l:List A)(b:A→Cn)(i:ℕ): coeff i (l.map b).sum= Owed ( fees b i ) l:= by -- h include omit
   induction l with | nil=> exact map_zero _| cons x l ih=> simp only [List.map_cons,List.sum_cons,map_add,ih,Owed]
lemma tilted (x:BL A): clock useN ( BL A ) (U ( useN.refineV x ))=ModeT ( fees b ) ( U ( useN.refineV x )):= by
    rw [sl_taxi]; ext n l; unfold ModeT; rw [slΩ useN (Tick ∘ fees b),cloak, look_c ]; simp_rw [Finset.sum_apply, look_c]; change (n:ℂ)*(coeff n (l.map V).prod* x l)=∑ i∈ antidiagonal n, Owed (fees b i.1) l * (coeff i.2 (l.map V).prod*x l); rw [ ← mul_assoc,← paysD,derX h, PowerSeries.coeff_mul ]; simp_rw [ coeff_T, ← mul_assoc,← Finset.sum_mul ]
end Carrier
end YM.MS.Swirl
