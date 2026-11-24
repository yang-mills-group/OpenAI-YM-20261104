import YangMills.WilsonProof.GraphOperands
import YM.FVA2.Dframe.Scale
import YM.XSpace.Galop
/-!
# Trace to POINTS on continuum MS G^m

With the initial tangent-power re-expression; before position solve.
This occurs before any position solve and is exactly a realm action *at samples*.
Use explicitly multilinear basis extension even on the continuum side (in the specified
pole conventions `Land.MS_Data`). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Dframe
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
variable {n d k:ℕ}{G:Gauge}
variable (ν:ℝ) (Y:XSpace.Initialize G) (S:Prescription (Press.portDeck G))
local notation "Π"=> Press.portDeck G
local notation "M"=> Toon G
local notation "L"=> M d
local notation "W"=> Fin n
local notation "A"=> Sample n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
-- realmP point arithmetic; arbitrary physical Reports only after testing/smearing separately.
def status (T:Guard G d)(Z:ℕ→Point G d n)(i:ℕ): Point G d n:= ∑ a∈ tally i n,(Z (a none)).compLinearMap (fun j=>PowerSeries.coeff (a (some j)) T)
lemma seen (T:Guard G d)(Z:ℕ→Point G d n)(i:ℕ)(v:Tags G d n): status T Z i v=∑ a∈ tally i n, Z (a none) (pulseU a T v):= by simp only [status,sum_apply]; rfl -- some
abbrev loan (Y:Initialize G) (x:Sample n)(d:ℕ) (k:ℕ): Point G d n:= orderT ν Y S x d k
abbrev postedPoint (ν:ℝ)(Y:Initialize G)(S:Prescription (Press.portDeck G))(d:ℕ)(a:Sample n):= status ( D ν S a.F d ) ( orderT ν Y S a d )
-- tiling.Phase
variable (a: Sample n) (t:Fin n→Toon G d)
abbrev fill (t:Fin n→ Toon G d):= theory ∘ t
lemma w_sc (x:Toon G d)(w:ℕ) : PowerSeries.coeff w (D ν S a.F d) (theory x)= ∑ i:Toon G x.size,PowerSeries.coeff w (allows ν S a.F x i) • up (size_le x) ( theory i ):= by
    rw [pays,w_lit]; unfold story; rw [map_sum]; refine Finset.sum_congr rfl (fun i _=>?_ ); let g:= stake ν S a.F x i w; rw [ allows, coeff_mk ]; exact Eq.trans ( map_smul ( (up (size_le x) (G:=G)).restrictScalars ℝ ) g _ ) ( IsScalarTower.algebraMap_smul ℂ g (_) |>.symm )
private lemma sum_w (Z: Days n)(V:Point G d n): V (pulseU Z (D ν S a.F d) (fill t))=∑ v:Story t,(∏ i:W, coeff (Z (some i)) (allows ν S a.F (t i) (v i))) * V (parent t v):= by change V (fun i=> coeff (Z (some i)) (D ν S a.F d) (theory (t i)))=_; simp_rw [w_sc]; rw [ MultilinearMap.map_sum V (fun i (j:Toon G (t i).size)=> _) ]; apply Finset.sum_congr rfl; intro v _; exact V.map_smul_univ (fun i=> _) (parent t v)
-- exact point expression
lemma meeting : μ (fun i=> postedPoint ν Y S d a i (fill t))= μ (scaled ν Y S a t):= by
    rw [ ← store_s ]; refine PowerSeries.ext fun i=>?_ ; rw [ PowerSeries.coeff_mk, map_sum ]; simp_rw [ postedPoint, seen, Constants.admits, coeff_mk, sum_w ]; rw [ Finset.sum_comm ]; simp_rw [allows, coeff_mk]
theorem reads (k:ℕ) : postedPoint ν Y S d a k (fill t)= Schedule.entries ν Y (flash ∘ t) S Finset.univ k a:= by obtain h:= meeting ν Y S a t; have he:=congr_arg (coeff k) h; simp only [coeff_mk] at he; exact he
-- define Continuum **unconnected** ordered through arity data.Quoting exact MS.D.
variable {O: Booked (Press.portDeck G)}(P: MS_Data G O)
abbrev continuum (t:Fin n→Toon G d)(k:ℕ): Points n→ℂ:= Landing.moondye ν P ( flash ∘ t ) Finset.univ k
def meteor (ν:ℝ){O: Land.Booked (Press.portDeck G)}(P:MS_Data G O)(d:ℕ)(x:Points n)(k:ℕ): Point G d n:= ∑ t:W→ Toon G d, continuum ν P t k x • each t -- arg order?
lemma sift (v:Tags G d n)(t:W→Toon G d): each t v=∏ i:W,(Theater.Daylight Π d).repr (v i) (t i):= rfl
lemma stencil_he (X:Point G d n)(v:Tags G d n): X v=∑ t:W→Toon G d, (each t v) * X (fill t):= by
    have ht:= X.map_sum (fun i (j:Toon G d)=> ( Daylight Π d ).repr ( v i ) j • theory j); simp_rw [all_sig] at ht; rw [ht]; refine Finset.sum_congr rfl (fun j _=>?_); rw [sift]; exact X.map_smul_univ _ (fill j)
lemma title (t y:W→Toon G d): each t (fill y)=if y=t then 1 else 0:= by
    by_cases h:y=t; · subst t; rw [if_pos rfl,sift]; simp [fill, ← theory_sig]
    obtain ⟨i,hi⟩:= Function.ne_iff.mp h; rw [sift,if_neg h]; apply Finset.prod_eq_zero (i:=i) ( Finset.mem_univ _); simp only [fill, comp_apply, ← theory_sig]; simp [hi]
local notation "T"=> postedPoint ν Y S d
lemma ribbon (x:Points n)(k:ℕ) : meteor ν P d x k (fill t)= continuum ν P t k x:= by
    simp_rw [meteor,sum_apply, smul_apply,title,smul_eq_mul, mul_ite,mul_one,mul_zero]; simp
variable (h:G.Simple)(hs:TaylorOKF P (Press.wickInput Y) S)
lemma limit_lead {x:Points n}(hx:x∈conf n) : meteor ν P d x 0=scene x d:= by
 ext1 v; rw [stencil_he _ v, stencil_he ( Normalize.scene x d ) v]; refine Finset.sum_congr rfl (fun i _=>?_ ); congr 1; rw [ ribbon, continuum, Landing.moondye ]; exact Dial.highest_zero P ν x ( flash ∘ i ) hx
include h hs
theorem tB (k:ℕ) (v:Tags G d n): Senses (conf n) (fun i:A=> postedPoint ν Y S d i k v) (fun x=> meteor ν P d x k v):= by
    intro x hx; simp_rw [ stencil_he (postedPoint ν Y S d _ _) v, stencil_he ( meteor ν P d _ _ ) v]; apply tendsto_finsetSum; intro t _; simp_rw [ribbon, reads]; exact (Landing.maturity ν Y P S _ _ _ h hs x hx|>.const_mul _)
-- estimates epsilon Senses.Uniform later, explicitly for all coefficients staffing.
end YM.FVA2.Dframe
