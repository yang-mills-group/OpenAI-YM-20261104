import YM.FVAAlt2.Convert.Home
import YM.FVAAlt2.Convert.Agree
/-! Momentum counterterm matrix, after converting slot width for true position-scheme entry on Plan.
 Uptight at all steps.Y.Close for any ζ. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Convert
open Finset Filter MeasureTheory Function Topology
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10
open PertExtension PertExtension.LatticePT PertExtension.Position
open FormalOPE.RG10.Position (Plan)
open FormalOPE.RG10.Gazebo FormalOPE.RG10.Carryon MS MS.Koszul MS.Local.Physical MS.Menus MS.Book MS.Land
open PowerSeries (C coeff constantCoeff)
open Home Report Matrix Profiles
open scoped BigOperators Topology PowerSeries ContDiff Classical Matrix
variable {G:Gauge} {F:Frames G} {B:Deck G} {X:Prescription B} {V:Booked B} {Z: RichBook B}{T:MS_Data G V}
variable (W:Prescription B) {d m k n:ℕ} (s:Signed)(x a:ℝ)
-- exp matrix relation of same cap rows.Rheight, commute projectively. No bound on frame entries at μ stored.
local notation:max "A" d:max=> beamA W x a d
local notation "L"=> Glyph B d
local notation "Ι"=> (roster F B d)
local notation "N"=> stepR F B
lemma beam_cost (n:ℕ)(p:L)(j:Glyph B (Lobby.owner p).h): coeff n (A d p (up (high p) j)) = a^(( j.size:ℤ )- p.size) * ((W.fees (Lobby.owner p).h (Lobby.owner p).item n).register j).eval x:=by
 unfold beamA; rw [Matrix.map_apply,onOil,takeReal,PowerSeries.coeff_mk, rel,Lobby.changePrice, PowerSeries.coeff_C_mul,Billing.bore,PowerSeries.coeff_mk]; unfold oil; change ((a:ℂ)^((j.size:ℤ)- (↑p.size:ℤ)) *((((W.fees _ _ n).register j).eval x:ℝ):ℂ)).re=_; rw [← Complex.ofReal_zpow, ← Complex.ofReal_mul,Complex.ofReal_re]
lemma lonely (p q:L)(h:p.size<q.size): A d p q=0:= beam_no W x a _ _ (fun ⟨k,e⟩=> by subst q; apply Nat.not_lt_of_le ( Nat.le_of_lt_succ k.1.isLt ) h)
variable (F)
-- Ploose sec price per same exact engineering grade.
def chargeD (Q:(Plaid B d)→ Acts B d) (d':ℕ)(x:ℝ) : Matrix (Plaid B d) (Glyph B d) ℝ:= (wage_mat B d Q d').map (Polynomial.evalRingHom x)
lemma secured (h:Permit F (W.fees d)) : Ι s * chargeD ( W.fees d ) n x = chargeD ( W.fees d ) n x*( N d s ):= by
    let E:=Polynomial.evalRingHom x; obtain ht:=congr_arg (fun X: Matrix (Plaid B d) (Glyph B d) (Polynomial ℝ)=> X.map E ) ( h s n ); simp_rw [Matrix.map_mul] at ht; rw [show ((Ι s).map Polynomial.C).map E= Ι s from ?_, show ((N d s).map Polynomial.C).map E=N d s from ?_] at ht; exact ht
    all_goals apply Matrix.ext; intro i j; simp [E]
-- reduce to occupied weights g
variable {i j:ℕ}{d':ℕ} {P:Plan F}
local notation "Ph" n=> Plaid B n
set_option maxHeartbeats 700000 in
lemma cut_cos (h:∀ d,Permit F (W.fees d))(X:L)(Y:L): ∑ p:L, N d s X p*coeff n (A d p Y) = ∑ p:L,coeff n (A d X p) * ( N d s p Y ):= by
 let k:=X.size; let hn:=high X; let U(i:Glyph B k): L:=up hn i; let S(i):= ( N d s X i ) * coeff n (A d i Y); let V(i):= coeff n (A d X i)* ( N d s i Y ); -- V type maybe
 let W₀ (i:Plaid B k):= Land.read i; let T:= W₀ (Lobby.owner X).item
 have hu : U T=X:= Eq.symm (lampu X _); change ∑ i:L,S i=∑ i:L,V i;
 by_cases hr:Y∈Set.range U; swap
 · have ht:k < Y.size:= Nat.lt_of_not_le fun H=> hr (⟨up H (Land.read (ownCoord Y)),?under⟩); case under=> obtain ⟨⟨j,h⟩,p⟩:=Y;rfl
   rw [ Finset.sum_eq_zero (f:=S) (fun i _=>?_), Finset.sum_eq_zero (f:=V) (fun i _=>?_)]; -- goal order inspect
   swap
   · unfold S; by_cases hx:i.size=X.size; · rw [lonely W x a i Y (hx.symm ▸ ht),map_zero,mul_zero]
     rw [ only_r F s _ _ (fun h=>hx (congr_arg Prod.fst h.symm)),zero_mul]
   unfold V; by_cases hx:i.size=Y.size; · rw [ lonely W x a X i (hx.symm ▸ ht),map_zero,zero_mul]
   rw [ only_r F s _ _ (fun h=>hx (congr_arg Prod.fst h)),mul_zero]
 obtain ⟨Z,hZ⟩:=hr
 have hh (i:Plaid B k) : (U (W₀ i)).size=k:= rfl
 have hz (i:Plaid B k) : S (U (W₀ i))= a^((Z.size:ℤ)- X.size) * (roster F B k s (Lobby.owner X).item i * chargeD ( W.fees k ) n x i Z):= by
    let v:=U (W₀ i); unfold S; rw [← hZ,show U Z=up (high v) ( show Glyph B k from Z ) from rfl, beam_cost, show N d s X (U (W₀ i))=roster F B k s (Lobby.owner X).item i from (by nth_rw 1 [ ← hu ]; exact climb_r F s _ _ _) ]; rw [hh i]; change _* (_*_)=(a^((Z.size:ℤ)- X.size)) * (_ * _ ); rw [mul_left_comm]; rfl
 have ht (i:Glyph B k) : V (U i) = a^((Z.size:ℤ)-X.size) * (chargeD ( W.fees k ) n x (Lobby.owner X).item i * N k s i Z):= by
    unfold V U; rw [ beam_cost, ← hZ, show N d s _ (U Z)= _ from climb_r F s hn i Z ]; change (a^ ((i.size:ℤ)-X.size)) * _ * _ = _ ; by_cases hy:i.size= Z.size; · rw [hy,mul_assoc]; rfl
    rw [only_r F s _ _ (fun h=> hy (congr_arg Prod.fst h)), show N (Lobby.owner X).h s i Z=0 from only_r F s _ _ (fun h=> hy (congr_arg Prod.fst h)) ]; simp -- inner 0
 have hP:Injective (U ∘ W₀):= Injective.comp (up_inj hn) (fun _ _ he=> eq_of_heq (Sigma.mk.inj he).2)
 suffices he: (∑ i:Plaid B k,S (U (W₀ i)))=∑ i:Glyph B k,V (U i) by
    change ∑ i:Plaid B k,S ((U∘W₀) i)=_ at he; rw [← Finset.sum_image (f:=V) (g:=U) (up_inj _).injOn,← Finset.sum_image (f:=S) hP.injOn,Finset.sum_subset (s₁:=image (U∘W₀) univ) (Finset.subset_univ _) (fun i _ h=>?_), Finset.sum_subset (s₁:=image U univ) (Finset.subset_univ _) (fun i _ h=>?_)] at he; exact he
    swap;
    · unfold S; rw [ only_r F s _ _ (fun he=>?_ ), zero_mul ]; rcases i with ⟨⟨i,h₁⟩,p⟩; have h':i=k:= congr_arg Prod.fst he.symm; subst i; exact h (mem_image.mpr ⟨p,mem_univ _,rfl⟩)
    unfold V; apply mul_eq_zero_of_left _ _; rw [beam_no W _ _ _ _ (fun ⟨i,hv⟩=> h (mem_image.mpr ⟨i,mem_univ _,hv⟩)),map_zero]
 simp_rw [hz,ht]; simp_rw [← Finset.mul_sum]; exact congr_arg _ (congr_fun₂ (secured F W s x (h k) (n:=n)) (Lobby.owner X).item Z)
end YM.FVAAlt2.Convert
