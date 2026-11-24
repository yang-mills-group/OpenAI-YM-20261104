import YM.FVAAlt2.Home.Waltz
import YM.FVAAlt2.Turn.Linear
/-! Choose actual CONTINUUM MS booked lifts (polynomials in $g$, continued in D
 before MS minimal subtraction). `Suitable` and compatible equivariance from
 same frame S. Linear mode physical high compare tax. Customer:
 certified Taylor.Action in both engines after this. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Convert
open Function Finset Filter MeasureTheory Lattice
open MS MS.Koszul MS.Menus MS.Local.Physical MS.Land MS.FVA MS.FVA.Motions MS.FVA.Town MS.Lifting MS.Plane MS.Landau MS.Landau.Detect MS.Native MS.Theater
open MS.Mach MS.Outlook MS.Dock MS.Emit MS.Pearl MS.Hem.Mell MS.Motif MS.Motif.Literal MS.Book MS.Book.Convolve MS.Arts
open FormalOPE FormalOPE.RG10 Labels Source Home Matrix
open scoped Topology BigOperators ContDiff PowerSeries Classical Matrix
variable {G:Gauge} {F:Frames G} {B:Deck G} {d m:ℕ} {t:ℤ} {E I J:Type} [AddCommGroup E][Module ℂ E] [Fintype I] {p: Law G}
variable (F) (s t':Signed) (W:Position.Plan F){T:Box (Mob G)}
local notation "anc"=> (Fintype.card Signed:ℂ)⁻¹
lemma living : anc*(Fintype.card Signed:ℂ)=1:= by rw [inv_mul_cancel₀]; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
local notation "Y"=> seats W.liftOff W.certified
local notation "S"=> localStep F B d
local notation "ξ"=> Plaid B d
def routeAvg (R:Signed→ Matrix I I ℂ)(p:Signed→ I→ E)(i:I): E:= anc • ∑ s:Signed,∑ j:I,R s⁻¹ i j • p s j
lemma avgHere [DecidableEq I] (R:Signed→ Matrix I I ℂ)(p:I→ E)(hp:∀ s:Signed,R s⁻¹*R s=1)(i:I): routeAvg R (fun s i=> ∑ j:I,R s i j • p j) i=p i:=by
 unfold routeAvg; have h(s:Signed): ∑ j:I,R s⁻¹ i j • ∑ j':I,R s j j' • p j'= p i:= by simp_rw [ Finset.smul_sum, smul_smul ]; rw [ Finset.sum_comm ]; simp_rw [← Finset.sum_smul,← Matrix.mul_apply,hp]; simp [Matrix.one_apply, ite_smul, one_smul]
 simp_rw [h,Finset.sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℂ, smul_smul,living, one_smul ]
lemma companions (R:Signed→ Matrix I I ℂ)(hR:∀ s t:Signed,R s*R t=R (t*s))(X:Signed→Module.End ℂ E)(p:Signed→I→ E)(hp:∀ s t j,X s (p t j)=p (s*t) j) (s:Signed)(i:I): X s (routeAvg R p i)=∑ j:I,R s i j • routeAvg R p j:= by
 unfold routeAvg; simp only [map_smul,map_sum]; simp_rw [ smul_comm _ anc (∑ _ : Signed, _),  hp ]; rw [← Finset.smul_sum]; refine congr_arg _ ?_ -- metav
 simp_rw [Finset.smul_sum,smul_smul]; conv_rhs=> rw [Finset.sum_comm]
 conv_rhs=> rw [← Equiv.sum_comp (Equiv.mulLeft s)]
 apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul, ← Matrix.mul_apply,hR]; simp

lemma roadway (F:Box (Mob G)) : turnBo G s (turnBo G t' F)=turnBo G (s*t') F:=by
 ext q : 1; exact ( Literal.whole (μs G s) _ q ).trans ((congr_arg _ ( Literal.whole (μs G t') _ q )).trans ((anti_mu ..).trans ( Literal.whole (μs G (s*t')) _ q ).symm))
variable {F}
-- Optical fiber. repr matrix complex real
lemma elect_add {H:Law G} {U:Box (Mob G)} (h:Ele d m p T)(ht:Ele d m H U): Ele d m (p+H) (T+U) := by
 obtain ⟨H,h₁⟩:=h; simp_rw [Ele,map_add]; exact ⟨ (Gallery ..).add_mem H ht.1, congr_arg₂ (·+·) h₁ ht.2⟩
lemma elect_scale (h:Ele d m p T){v:ℂ}(hv:star v=v) : Ele d m (v • p) (v • T) := by
 obtain ⟨u,hu⟩:= Complex.conj_eq_iff_real.mp hv; rw [hu]; simp_rw [Ele,map_smul ]; refine ⟨ ?_, congr_arg ((u:ℂ) • ·) h.2⟩; have he: (fun z=> (u:ℂ) • value _ z T)= u • (fun z=>value ( Mob G ) z T):= funext fun z=> IsScalarTower.algebraMap_smul ℂ u (value _ z T); rw [he]; exact Submodule.smul_mem _ _ h.1
lemma elect0(d m:ℕ): Ele d m (0:Law G) 0:= by unfold Ele; simp_rw [map_zero]; exact ⟨Submodule.zero_mem _,rfl⟩
lemma electF {F:J→Law G}{P:J→ Box ( Mob G )}(Sx:Finset J)(h:∀ j∈Sx,Ele d m (F j) (P j)): Ele d m (∑ j∈Sx,F j) (∑ j∈Sx,P j):=by
 induction Sx using Finset.induction_on with | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact elect0 ..| insert i t hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact elect_add (h i (by simp)) ( ih fun i hi=> h i ( Finset.mem_insert_of_mem hi ))
lemma ele_star (i j:ξ) : star ((S s) i j)= (S s) i j:=by rw [show (S s) i j= (( stepR F B d s (Land.read i) (Land.read j):ℝ):ℂ) from Eq.symm (movesOn F s ..)]; simp
lemma ele_zero (i j:ξ)(h: (Land.read i).grade≠(Land.read j).grade): (S s) i j=0:= only_g F s _ _ fun b=> h (congr_arg Prod.snd b)
lemma returns0 (F:Frames G)(B:Deck G)(d:ℕ)(s:Signed): localStep F B d s⁻¹*localStep F B d s=1:=by rw [Ξ_roll,mul_inv_cancel,step_id]
-- default W or arbitrary Level. Native family choice later P. Build including any needed unit witness.
local notation "U₀"=> Box (Mob G)
local notation:max "K₀" d:max => localStep F Y d
variable (C:Booked (seats W.liftOff W.certified))
abbrev rentM (W:Position.Plan F)(C:Booked (seats W.liftOff W.certified))(d:ℕ): Plaid (seats W.liftOff W.certified) d → Box (Mob G) := routeAvg (localStep F (seats W.liftOff W.certified) d) (fun s i=> turnBo G s (C.optics d i))
lemma real_cv (i:Plaid Y d): Ele d (Land.read i).grade (Land.read i).read (rentM W C d i) := by
 let p(j: Plaid Y d):= ( Land.read j ).read; have hu(s:Signed)(i):= read_consist s W (d:=d) i
 change Ele d _ (p i) _; rw [← avgHere (K₀ d) p (returns0 F Y d) i, show (fun k j=> (∑ x,(K₀ d) k j x • p x))=(fun k j=>turnW G k (p j)) from funext fun k=> funext fun j=> ( hu .. ).symm ]; unfold rentM routeAvg; refine elect_scale (v:=anc) ?_ (by simp); apply electF; intro s hs; apply electF; intro j hj
 by_cases hv: (Land.read i).grade= (Land.read j).grade; · rw [hv]; exact elect_scale ( turned_E s (C.law d j) ) (ele_star s⁻¹ ..) -- syntax `(ele_star (F:=F) (B:=..)`
 rw [ ele_zero (F:=F) s⁻¹ i j hv,zero_smul,zero_smul ]; exact elect0 ..
def electric : Booked Y:= ⟨ rentM W C, fun _=> real_cv W C ⟩
-- public interface for compatible knots. Condition on Booked only; subsequently ANY MS_Data for those optics works. rather than retaining two spectra in conversion.
variable (F) in
def Spect (A:Booked B): Prop:=∀ s:Signed,∀ d:ℕ,∀ i:Plaid B d, turnBo G s ( A.optics d i )=∑ j:Plaid B d,localStep F B d s i j • A.optics d j
lemma electric_spec : Spect F (electric W C):= fun s d i=> companions _ (Ξ_roll F Y d) (fun s=>turnBo G s) (fun s i=> turnBo G s (C.optics d i)) (fun x y j=> roadway x y (C.optics d j)) s i

-- All coefficients evaluate; important thermal rotation in `$Archive` heading.MS
variable (V:Booked B) (R: MS_Data G V)
variable {V} (he:Spect F V) (x:ξ)
lemma emission (P: Finset J)(v:J→ Box (Mob G))(f:J→ℂ) : _root_.YM.MS.Emit.gloss (linear (Mob G) (∑ j∈P,f j • v j))= ∑ j∈P,f j • Emit.gloss (linear (Mob G) (v j)):= by funext i z; unfold Emit.gloss; simp_rw [ map_sum,map_smul, Finset.sum_apply,Pi.smul_apply ]
local notation "Rz"=> R.marks d
local notation "Tx"=> fun i:Plaid B d=> Archive d ( R.marks d i )
include he
lemma skyline_R (i:Plaid B d) : Town.pressX s (Archive d (R.marks d i)) = ∑ j:Plaid B d, (S s) i j • Archive d (Rz j):= by
 let E(j:Plaid B d):= Rz j; let v(y):= (S s) i y; let X:= Rz i; let F₁:= ∑ j,v j • E j; let pz:= R.poles d i
 have hG:= fun i n=> (gang (R.markOK d i n)).dost; obtain hp:= motionM (Γx s) R.bulkOK (R.markOK d i); rw [← turn_gloss, he, emission] at hp; have ht(j:Plaid B d):star (v j)=v j:= ele_star s i j; let Yz:= (mswing G (Γx s)) ∘ Rz i
 obtain hx:= SumM (X:=R.bulk) ( h:=fun j _=> singc (R.markOK d j) (ht j) ) univ;
 obtain hZ:= archive_eq (unique_M hp hx (fun _ _=> EventuallyEq.rfl)|>.2) (fun n=> ( gang (hp n) ).dost) (fun n=>( gang (hx n)).dost)
 rw [show Town.pressX s (Archive d X)=Archive d Yz from ?_, hZ,archive_sum _ ( X:=fun j=>v j • E j) ]; rotate_left
 · intro j hj t; exact MS.Train.Stay_scale (hG j t) (v j)
 · funext n y; rcases y with ⟨a,t⟩; have hpM := congr_fun (press_stay (h:=a) (x:=t) (Γx s) (hG i n)) 0; rw [motion_zero] at hpM; exact hpM.symm
 exact sum_congr rfl fun j _=> archive_c (E j) (hG j) (v j)
end YM.FVAAlt2.Convert
