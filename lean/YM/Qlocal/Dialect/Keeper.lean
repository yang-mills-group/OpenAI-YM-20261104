import YM.Comparison.RG02.Order.Vacancy
/-!
# Translator for coupling-polarized coefficients vs markers. Even after explicit Φ exposure.
 Does NOT normalize differently. Any algebra map such as Φ basis-to-symbol shutter. Can read log grouped by any disjoint choices even with same Mark polynomial.Sem.Frame. Use on Fk projector in calendar Pose credentials. Reuses `Order.*` not an extra perturbative order ring. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Dialect
open Function Finset Set
open Marker MeasureTheory Extra.Trajectories
open Comparison Comparison.RG02 Comparison.RG02.Order
open scoped BigOperators Classical
variable {V I J K : Type} [DecidableEq I] [DecidableEq J] [DecidableEq K] [Fintype I][Fintype J][Fintype K]
variable {R:Census I}{S:Census J}{X:Census K}
open Join
-- keep also extension to Ψ.Print alphabet.Data.Scope.Clock.Fill_Bond(ArtFrame URI.Parent.Currency_LogLift). arbitrary right factors.X.Weight.Ph.Price context
namespace Keeper
noncomputable def sheet (R:Census I) (X:Census K)(y:X.Mode) : Poly (Join.room R X) →ₗ[ℂ] Poly R where
    toFun a:= Poly.inject (fun i=> a.part (Join.pair i y))
    map_add' _ _:=rfl
    map_smul' _ _:=rfl
variable (T: Poly R→ₐ[ℂ]Poly S)(hp:∀ x,(T x).part S.quiet=x.part R.quiet)(y:X.Mode)
    (p q:Poly (Join.room R X))
lemma attains (u:R.Mode): (sheet R X y p).part u = p.part (Join.pair u y):= rfl
lemma sheet_one : sheet R X y (1:Poly (Join.room R X))= if y=X.quiet then 1 else 0:=by
 apply Poly.ext; intro x; rw [attains, one_pair]; by_cases h:y=X.quiet <;> simp [h]
-- important generic RingHom t.Reader argument.Factor.Time.Setup.Math.Full.S.Stencil.Work.Account.Tag mask.
lemma sheet_mul : sheet R X y (p*q) = ∑ u:X.Mode,∑ v:X.Mode, if Poly.merges u v y then sheet R X u p*sheet R X v q else 0:=by
 apply Poly.ext; intro x; rw [attains, pair_product]; simp_rw [Poly.part_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> ?_
 let f(a : R.Mode) (b:R.Mode) (v:X.Mode):= if Poly.merges a b x∧ Poly.merges i v y then p.part (pair a i) * q.part (pair b v) else 0
 change ∑ a,∑ b,∑ v,f a b v=_; have h a:(∑ b,∑ v,f a b v)=∑ v,∑ b, f a b v:= Finset.sum_comm; simp_rw [h]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=>?_; split
 next hz=> rw [Poly.part_mul]; simp [f,hz,attains]; -- done
 next hz=> simp [f,hz]
-- Rost.α.Symbol. map determined
private noncomputable def lmap (X:Census K) : Poly (Join.room R X) →ₗ[ℂ] Poly (Join.room S X) where
 toFun p:= Poly.inject (fun u=> (T (sheet R X (Join.right u) p)).part (Join.left u))
 map_add' a b:= by apply Poly.ext; intro i; rw [Poly.part_plus]; change (T (sheet R X _ (a+b))).part _=_; rw [map_add,map_add, Poly.part_plus]; rfl
 map_smul' a b:= by apply Poly.ext; intro i; rw [Poly.part_smul]; change (T (sheet R X _ (a • b))).part _=_; rw [map_smul,map_smul,Poly.part_smul];rfl

variable (R) in
lemma sheet_ext {x y:Poly (Join.room R X)} (hz: ∀ i,sheet R X i x=sheet R X i y): x=y:= Join.both_parts (fun s t=> by simpa only [attains] using congr_arg (fun a:Poly R=>a.part s) (hz t))
private lemma lmap_sheet (i:X.Mode) : sheet S X i (lmap T X p)=T (sheet R X i p):= by apply Poly.ext; intro u; rw [attains]; change (T (sheet R X (Join.right (pair u i)) p)).part (left (pair u i))=_; simp
noncomputable def morph (X:Marker.Census K): Poly (Join.room R X) →ₐ[ℂ] Poly (Join.room S X):= by
 refine AlgHom.ofLinearMap (lmap T X) (sheet_ext S fun i=> ?_) (fun p q=>sheet_ext S (fun i=> ?_));
 · rw [lmap_sheet,sheet_one,sheet_one]; by_cases he:i=X.quiet <;> simp [he]
 rw [lmap_sheet,sheet_mul,sheet_mul]; simp_rw [lmap_sheet,map_sum]; apply Finset.sum_congr rfl; intro i _ ; refine Finset.sum_congr rfl fun j _=>?_; split<;> simp_all
lemma morph_sheet : sheet S X y (morph T X p)=T (sheet R X y p):= lmap_sheet T p y
lemma blank : (morph T X p).part (Join.room S X).quiet=(T (sheet R X X.quiet p)).part S.quiet:= by rw [←pair_quiet,←attains,morph_sheet]
include hp
lemma leading : (morph T X p).part (Join.room S X).quiet=p.part (Join.room R X).quiet:= by rw [blank,hp,←pair_quiet,attains]
-- power.S.Boot.Level param Marker
variable {r i:ℕ}(P:Grade R r)
local notation "B"=> Board R r
local notation "B'"=> Board S r
local notation "F"=> morph T (indices r)
lemma order_h : F (Order.denominator P)=Order.denominator (F P):= by
 have he (V:Type)[DecidableEq V][Fintype V](B_:Marker.Census V)(x:Grade B_ r)(u:Index r): sheet B_ (indices r) u (Order.denominator x)=(sheet B_ (indices r) u x).part B_.quiet • (1:Poly B_):= by
   refine Poly.ext fun i=>?_ ; unfold denominator; rw [attains, bottom_value, Poly.part_smul, Poly.one_part,attains]; by_cases ht:i=B_.quiet <;>simp [ht]
 apply sheet_ext S; intro u; rw [he, morph_sheet,he,map_smul,map_one,morph_sheet,hp]
lemma quotient (hP:UnitLeading P) : F (Order.ratio P)=Order.ratio (F P):= ratio_unique (leading T hp P|>.trans hP) (by rw [← order_h T hp,← map_mul,recovers hP])
lemma log (hP:UnitLeading P): F (Order.logMarked P)=Order.logMarked (F P):= by unfold logMarked; rw [Comparison.RG02.Cumulants.log_map F (leading T hp) (Order.ratio_quiet hP), quotient T hp _ hP]
-- observe commutation with same coupling count. No assumption of sym
omit hp
lemma take_orders (ht:i≤r): observe S r (F P) i=T (observe R r P i):= by unfold observe; simp only [ht,↓reduceDIte,↓reduceIte]; rw [map_smul]; change _ • (sheet S (indices r) _ (F P)) = _ • T (sheet R (indices r) _ _); rw [morph_sheet]
lemma orders_sheet (s : Index r)(p': PTable R): sheet R _ s (series R r p')= (s.val.card.factorial:ℂ) • (PowerSeries.coeff s.val.card p'):= by ext i; rw [attains, polarization, Poly.part_smul]
lemma series_map (p : PTable R): F (Order.series R r p)=series S r (PowerSeries.map T.toRingHom p):= by apply sheet_ext; intro i; rw [morph_sheet,orders_sheet,orders_sheet,PowerSeries.coeff_map, map_smul]; rfl
end Keeper
end YM.Qlocal.Dialect
