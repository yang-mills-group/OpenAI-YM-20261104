import YM.FVA2.XReg.Sight
/-!
# The MS position-frame data after normalization

In the continuum variable g before calibration by the position coupling. We use
`Normalize`'s prepared measurements (also at the various horizons) to obtain a
single, compatible, continuum position-frame array. Proves exact-trace and
leading-order properties as well as convergence from the finite-regulator position
prescription in the MS variable.

`ν` in this file is in the logarithmic convention of `YM/MS`. For example use
`ν = Teller.logNu 1` (see `Teller/Mass.lean`) to assert results at unit MS mass.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Reg.State
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Normalize.Fray Reg.Point Reg.Unique Pivot CoverTest Higher
open scoped Topology ContDiff BigOperators Classical
variable {n d k:ℕ}{G:Gauge}
local notation "Π"=> Press.portDeck G
local notation "ℒ"=> Normalize.Change G d
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
variable (ν:ℝ)(Y:Initialize G)(V:Normalize.Store G)(S: Prescription (Press.portDeck G)){O:Booked (Press.portDeck G)} (T: MS_Data G O)
abbrev kernel (d:ℕ) := Rates ν T d
abbrev root (d:ℕ) := (V.survey d).Lays (V.prepared d) (kernel ν T d)
def chooseL (d:ℕ): Guard G d:= deck (root ν V T d)
abbrev author (d:ℕ): Reports G d:= realm (chooseL ν V T d) (kernel ν T d)
def wall (d:ℕ)(x: Points n): ℕ→ Structure1.Point G d n := status (chooseL ν V T d) (meteor ν T d x)
lemma freeT : kernel ν T d 0= reference G d:= ground ν T
lemma baseL (d:ℕ): constantCoeff (chooseL ν V T d)=1:= by rw [chooseL,const_deck,root,compass _ _ (freeT ν T),stand0]
lemma baseK : root ν V T d 0=0:= compass _ _ (freeT ν T)
lemma success : ( V.survey d ).Executed ( V.prepared d ) (kernel ν T d) := force_title _ _ _ (freeT ν T)
lemma legit : Formal ( chooseL ν V T d ):= ( success (d:=d) ν V T ).1
lemma near_free (R:Pick G d) (h:R 0=0) (hs:( V.measure d ).Solved R (kernel ν T d)): R=root ν V T d:= uniqueness_title _ _ _ (freeT ν T) _ hs h
lemma road (u:Tags G d n)(k:ℕ) : ContinuousOn (fun x=> wall ν V T d x k u) (conf n):= by simp_rw [wall,seen]; exact continuousOn_finsetSum _ (fun i _=> CoverTest.measurable _ T (i none) _)
lemma spirit (x:Points n)(he:x∈conf n): wall ν V T d x 0=scene x d:= by ext1 p; rw [ wall,Silver.status_lead (G:=G), limit_lead ν T he,coeff_zero_eq_constantCoeff_apply, baseL ]; rfl
-- Identification with smeared reports.
lemma in_mem {K:Guard G d}(t: Test n) (p: Tags G d n): t.applyTo (fun x=> status K (meteor ν T d x) k p) = realm K (kernel ν T d) k n t p:=by
    rw [ really ]; unfold kernel; simp_rw [ indicative, seen, Test.applyTo, Finset.mul_sum, integral_finsetSum _ (fun i _=> t.smearing (CoverTest.measurable ν T (i none) (pulseU i K p)) ) ] -- arguments
lemma exact_trace (t:Test n)(p:Tags G d n): author ν V T d k n t p= t.applyTo (fun x=> wall ν V T d x k p):= ( in_mem ν T t p ).symm
-- REAL realm. Compatibility across heights
-- use the Booked optics on this Deck
lemma initial_chain {e:ℕ}(h:d≤e)(x:Points n)(p:Tags G d n): meteor ν T e x k ( up h ∘ p ) = meteor ν T d x k p:= by
    let P:𝒮:=( meteor ν T e x k ).compLinearMap (fun _=> up h); change P p=_; rw [ stencil_he _ p, stencil_he ( meteor ν T d x k ) p ]; apply Finset.sum_congr rfl; intro i _; unfold P; rw [MultilinearMap.compLinearMap_apply]; let t:=fill i; rw [show (fun k=> up h (fill i k))=fill (fun y=> Dframe.enroll h (i y)) from rfl,ribbon,ribbon]; rfl
lemma chain_kernel {e:ℕ}(h:d≤e): recruit ( up h ) (kernel ν T e k)= kernel ν T d k:= by
    ext1 n; ext1 t; ext1 p; rw [recruits]; unfold kernel; simp_rw [indicative, initial_chain]
-- continuum L preserves near-state. Can use uniqueness to push it through all Field horizons.
lemma chain_k : ∀ j,fell d (root ν V T (d+1) j)=root ν V T d j:= by
    suffices he:(fun i=> fell d (root ν V T (d+1) i))=root ν V T d from congr_fun he
    apply near_free ν V T; swap; · rw [show kernel ν T d = (fun i=> recruit ( Normalize.step d ) ( kernel ν T (d+1) i )) from Eq.symm (funext fun i=> chain_kernel ν T (k:=i) ( Nat.le_succ d )) ]; exact Screen.shadow (V.respects d) ( success (d:=d+1) ν V T|>.2.1 )
    rw [baseK,map_zero]
lemma chain_step : ∀ n (p: Sec G d), PowerSeries.coeff n (chooseL ν V T (d+1)) (up ( Nat.le_succ d ) p)=up ( Nat.le_succ d ) (PowerSeries.coeff n (chooseL ν V T d) p):= nest _ _ ( chain_k ν V T )
lemma chainL {e:ℕ}(h:d≤e)(u:Sec G d) : coeff k (chooseL ν V T e) ( up h u )=up h ( coeff k (chooseL ν V T d) u ):= by
    induction e,h using Nat.le_induction with
    | base=> rfl
    | succ e he ih=> rw [show up _ u=up ( Nat.le_succ e ) (up he u) from (rfl: up ( Nat.le_trans he ( Nat.le_succ e ) ) u=_), chain_step,ih]; rfl -- value cast
lemma chain_era {e:ℕ}(h:d≤e)(x:Points n)(p:Tags G d n): wall ν V T e x k (up h ∘ p)=wall ν V T d x k p:= by
    rw [wall, wall, seen,seen]; apply Finset.sum_congr rfl; intro i _; rw [ show pulseU i (chooseL ν V T e) (up h ∘ p) = up h ∘ pulseU i (chooseL ν V T d) p from funext fun y=> chainL ν V T h (k:=i (some y)) (p y), initial_chain]
-- CONCRETE continuity of above conversion to XSpace phases.Detector prep
variable (h:G.Simple)(hs: TaylorOKF T (Press.wickInput Y) S)
local notation "U"=> XSpace.Cirrus.Sample
include h hs
lemma priceL : HasAll Front (posted ν Y S d) (kernel ν T d):= fun _=> CoverTest.covered ν Y S T h hs
lemma chalk_t : Higher.Formulas Front (fun i=> chalk ν Y V S d i) (root ν V T d):= Higher.frames _ _ _ (freeT ν T) _ (priceL ν Y S T h hs)
lemma tea : HasAll Front (coupledBatch ν Y V S d) (author ν V T d):= Higher.acts _ _ _ (freeT ν T) _ (priceL ν Y S T h hs)
lemma dual {x:Points n}(he:x∈conf n): Pieces (Gate x) (fun i=> coupledPoints ν Y V S i d) (wall ν V T d x):= by
    let Z:=fun i:Mesh=> chalk ν Y V S d i; exact Higher.respected₂ (fun i=> Z ( (i: Sample n).F )) _ (fun i=> ( show Tendsto (fun j=> guide G d ( Z j i )) Front (𝓝 (guide G d (root ν V T d i))) from chalk_t ν Y V S T h hs i ).comp (liftG x)) _ _ (fun i p=> tB ν Y S T h hs i p x he)
variable (hr: Favors.Horder S)(hv: Ace.UnitP S)
include hr hv
theorem moveT (p:Tags G d n) (k:ℕ): Senses (conf n) (fun i=> substitute (Dframe.reset ν S i.F) ( Rose.cooked Y V d (i:Sample n) ) k p) (fun x=> wall ν V T d x k p):= by
    intro x hx; apply ( dual ν Y V S T h hs hx k p ).congr'; filter_upwards [(liftG x).eventually (timely (d:=d) ν Y V S T h hs hr hv frontier)] with i hi; rw [whole ν Y V S i hi]
theorem moveR : HasAll Front (fun i=> substitute (Dframe.reset ν S i) (V.opens Y i d)) (author ν V T d):= by intro k n t p; refine ( tea ν Y V S T h hs k n t p ).congr' ?_; filter_upwards [timely (d:=d) ν Y V S T h hs hr hv frontier] with i hi; rw [rulers ν Y V S i hi]
end YM.FVA2.Reg.State
