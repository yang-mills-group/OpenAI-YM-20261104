import YM.FVA2.Scale.N
/-!
# Realizing the point arrays via smearing

In ordinary physical units, Test n as in position characterization. `fxt` witness for later
assembly & detector. No assumptions at collisions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale.Jury
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level Reg.Point Facets Equator Measure Reg.CoverTest
variable {G:Gauge}{n d k:ℕ}
local notation "P"=> Structure1.Point G d n
section smear
-- arbitrary family ext and comparison
variable (A:Way G d)(S: Reports G d)
local notation "S2" => Reports G d
def fxt (x:Points n): ℕ→ Structure1.Point G d n:= if h:x∈conf n then A n ⟨x,h⟩ else 0
lemma exactC (x:Stage n): fxt A x.val=A n x:= dif_pos x.property
lemma fxt_c (q:Cn)(x:Points n): fxt ( couple q A ) x=substitute q (fxt A x):= by
    unfold fxt; split_ifs; · rfl
    exact (map_zero _).symm
lemma fxt_m (T:Guard G d)(x:Points n): fxt (actMark T A) x=status T (fxt A x):= by
    unfold fxt; split_ifs; · rfl
    ext1 i; ext1 p; simp [seen]
def Thin (A:Way G d): Prop:=∀ n i, Continuum (fun x:Points n=> fxt A x i)
def Verdict (A:Way G d)(S:Reports G d) : Prop:= ∀ n i (t:Test n) (p:Tags G d n), S i n t p=t.applyTo (fun x=> fxt A x i p)
structure Orders (A:Way G d)(S: Reports G d): Prop where
    light : Thin A
    exact : Verdict A S
lemma peer {K: Reports G d}(h:Verdict A S)(u:Verdict A K): S=K:= by ext1 i; ext1 n; ext1 t; ext1 p; rw [h n i,u n i]
lemma Thin.glance {A:Way G d}(h: Thin A)(p:Cn): Thin (couple p A):= by
    intro n i v; simp_rw [ fxt_c,Dframe.translate,rules,smul_eq_mul ]; exact continuousOn_finsetSum _ (fun j _=> (h n j v).const_mul _)
lemma Thin.specify {A:Way G d}(h:Thin A)(W:Guard G d): Thin ( actMark W A ):= by
    intro n i v; simp_rw [fxt_m, seen]; exact continuousOn_finsetSum _ (fun i _=> h n (i none) _)
lemma Orders.glance {A:Way G d}{S:Reports G d}(h: Orders A S)(p:Cn): Orders (couple p A) (substitute p S):= by
    refine ⟨h.light.glance p,?_⟩; intro n i t v; rw [ ← Reg.Point.seenT ]; simp_rw [fxt_c, Dframe.translate,rules,smul_eq_mul, (show ∀ i v, S i n t v=t.applyTo (fun x=> fxt A x i v) from fun i=> h.exact n i t),Test.applyTo, Finset.mul_sum ]; rw [integral_finsetSum]; · refine Finset.sum_congr rfl (fun j _=>?_); rw [ ← integral_const_mul ]; apply integral_congr_ae; filter_upwards with a; ring
    intro j _; exact ( t.smearing ( (h.light n j v).const_mul _ ))
lemma Orders.specify {A:Way G d}{S:Reports G d}(h: Orders A S)(p:Guard G d): Orders (actMark p A) (realm p S):= by
    refine ⟨h.light.specify p,?_⟩; intro n i t v; rw [really]; simp_rw [fxt_m,seen, (show ∀ i v, S i n t v=t.applyTo (fun x=> fxt A x i v) from fun i=> h.exact n i t), Test.applyTo, Finset.mul_sum ]; rw [integral_finsetSum _ (fun j _=> t.smearing ( h.light _ _ _ ))]
abbrev prepare (A:Way G d)(h:Thin A) : Reports G d:= fun i n=> cone _ ( h n i )
lemma defined (h:Thin A): Orders A (prepare A h):= ⟨h,fun _ _ _ _=> rfl⟩
end smear
variable (ν:ℝ){O:Booked (Press.portDeck G)} (T:MS_Data G O)
lemma initial : Orders (wave ν T d) (Reg.State.kernel ν T d):= by
    refine ⟨ ?_,?_ ⟩; · intro n i v; refine ( Reg.CoverTest.measurable ν T i v ).congr ?_; intro x hx; dsimp only; rw [fxt,dif_pos hx]; rfl
    intro n i t p; unfold Reg.State.kernel; rw [indicative]; apply Test.apply_eq; intro x hx; dsimp only; rw [fxt,dif_pos hx]; rfl
variable (Y:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(S:Prescription (Press.portDeck G))
variable (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
include h hs hr hu
lemma enrolled : Orders (start Y K d) ( Reg.Faith.reports ν K T d ):= by
    rw [ ← together Y K ν T S h hs hr hu ]; exact ( (initial ν T).glance ( f K ν T ) ).specify _
-- uniqueness of frame. After an arbitrary coupling substitution (real).
variable {p q:Cn} (t:Guard G d)(hp:Rooted p)(hq:Rooted q)(tp:Reg.Unique.CoreR p)(tq:Reg.Unique.CoreR q)(H: Base t)
-- actual near equilibrium S2. Keep tested scope.Roll.
local notation "Q"=> Reg.Faith.reports ν K T d
local notation "L"=> V.measure d
local notation "P'"=> substitute p (Reg.Faith.reports ν K T d)
local notation "Q'"=> substitute q (Reg.Faith.reports ν K T d)
include ν
abbrev Positioned (V:Normalize.Store G)(S:Reports G d) := ( V.measure d ).Solved (0:Normalize.Pick G d) S -- remove include?
include tp hp
lemma solved : Positioned V (substitute p (Reg.Faith.reports ν K T d)):= by
    have ht (v:Reports G d) {q₀:Cn}(hQ:Rooted q₀)(hu:Reg.Unique.CoreR q₀) (hV:(V.measure d).Solved 0 v) : (V.measure d).Solved 0 (substitute q₀ v):= by
       rw [ show (0:Pick G d)= Reg.Unique.shift (0:Pick G d) q₀ from (?_ : _) ]; exact Reg.Unique.euclidean hQ hu (0:Pick G d) v hV; unfold Reg.Unique.shift; ext1 j; simp
    rw [ Reg.Faith.reports_use ν Y K S T h hs hr hu ]; apply ht _ hp tp; apply ht _ ( Reg.Faith.hearty ν Y K S T h hs hr hu |>.cost.own ) ( Reg.Faith.hearty ν Y K S T h hs hr hu |>.trueQ ); intro i; rw [ deck0, Normalize.author ]; exact ( Reg.State.success ν V T |>.2.1 ) i
include tq hq H
lemma measured_single (hS: actMark t (couple p (start Y K d))=couple q (start Y K d)): t=1:= by
    obtain r : Orders (start Y K d) Q := enrolled ν T Y K S h hs hr hu; obtain x:= ( r.glance p ).specify t; have hv:= peer _ (realm t P') x.exact (show Verdict (actMark t (couple p (start Y K d))) Q' from hS.symm ▸ (r.glance q).exact)
    obtain ⟨u,ht⟩:= H.lies.actions; rw [ ht ] at hv ⊢; have hc:u 0=0:= by
        apply Reg.Unique.inject; rw [ ← const_deck, ← ht,H.lead,stand0 ]
    have hU:(V.measure d).Solved u P':= by
        intro i; rw [hv]; exact ( show (V.measure d).D (Q' i)=_ from ( by obtain he:= solved ν T Y K S h hs hr hu (d:=d) hq tq i; rwa [deck0, Normalize.author] at he ) )
    have he: P' 0 = reference G d:= by rw [pay0]; change realm ( liftT K ν T d ) _ 0=_; rw [ Normalize.rest, pay0,(Measure.charges Y K ν T S (d:=d) h hs hr hu).zero, Screen.recruit_one, Reg.State.freeT ]
    rw [ Screen.shift_unique L P' u 0 hc hU ( solved ν T Y K S h hs hr hu hp tp ) ( by rw [ hc, he ]; intro x y h'; simpa only [XSpace.Normalize.regular _ (V.prepared d)] using h' ), deck0 ]
end YM.FVA2.Scale.Jury
