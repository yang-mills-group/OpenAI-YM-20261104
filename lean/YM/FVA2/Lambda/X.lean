import YM.FVA2.Lambda.Parity
/-!
# The first degrees of the X-space running law

 Thus even without scalar parity restrictions on the **position scheme**, its beta generator
 vanishes through quadratic order. Same coefficient at cubic order. Here is a
 FORMAL extraction on the prescribed Wilson coefficients. Numerical value of cubic
 not proven in this module. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.AxisB
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta
namespace Edge
variable {f g h:Cn} (hf:Rooted f)(hg:Tangent g)
lemma compare (n:ℕ)(h0:∀ i<n,coeff i f=0)(ht:Tangent g) : coeff n (f.subst g)=coeff n f:= by
  rw [ ← Constants.actual_subst _ _ ht.start, coeff_mk,rules, Finset.sum_eq_single n ]; · rw [ show Program.cut g n n=1 from (stamp_n _ ht.start n).trans (by rw [ht.lead,one_pow]),one_smul]
  · intro b hb hi; rw [ h0 b (lt_of_le_of_ne (Finset.mem_Iic.mp hb) hi),smul_zero ]
  simp
lemma generator (n:ℕ)(h0:∀ i<n,coeff i f=0)(ht:Tangent g) : coeff n (PowerSeries.derivative ℂ g * f)= coeff n f:= by
  rw [coeff_mul,Finset.sum_eq_single (0,n) ]; · change coeff 0 (PowerSeries.derivative ℂ g) * coeff n f=_ ; simp [ht.lead,coeff_derivative ]
  · intro b hb hi; obtain hL:= Finset.mem_antidiagonal.mp hb; rw [h0 b.2 (by contrapose! hi; exact Prod.ext (by dsimp; omega) (by dsimp; omega)),mul_zero]
  simp
lemma N {k:ℕ}(hG: Tangent h)(he: g.subst h= PowerSeries.derivative ℂ h * f)(hH:∀ i < k, coeff i g=0) : (∀ i<k, coeff i f=0)∧ coeff k g= coeff k f:= by
 have hx i (ht:i≤k): (∀ j < i,coeff j f=0) → coeff i g=coeff i f:= fun H=> by rw [ ← generator i H hG, ← he, compare i (fun j hj=> hH j (hj.trans_le ht)) hG ]
 have hr i (hi:i<k): coeff i f=0:= by
   induction i using Nat.strong_induction_on with
   | _ i ih=> rw [ ← hx i hi.le (fun j hj=> ih j hj (hj.trans hi)) ]; exact hH i hi
 exact ⟨hr,hx k (le_refl _) hr⟩
end Edge
variable {G:Gauge}(ν:ℝ)(Y:XSpace.Initialize G){V:XSpace.Normalize.Store G}(K:XSpace.Rose.Pick V){O: Booked (Press.portDeck G)}(T:MS_Data G O)
variable (S:Prescription (Press.portDeck G)) (t:ℝ)(h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
local notation "χ" => Measure.chi K ν T
local notation "φ"=> Measure.f K ν T
local notation "γ" => Scale.GroupS.ψ K T ν
local notation "π" => Scale.GroupS.Ψ K T ν
local notation "σ" => Program.shift S.team
local notation "Q"=> true_m ν Y K T S h hs hr hu
local notation "B"=> Scale.Beta.beta
include h hs hr hu
lemma first : (∀ i<3, coeff i ( B γ )=0) ∧ coeff 3 ( B π )= coeff 3 ( B γ ):= by
 have ht:= Scale.GroupS.scaleM ν Y K T S h hs hr hu; apply Edge.N (Scale.Specific.vigor_f Y K ν T S h hs hr hu) (Scale.Beta.translated ν Y K T S h hs hr hu)
 intro i hi; interval_cases i <;> first| exact LowBound.beta_parity ν Y K T S h hs hr hu _ (by decide)| exact (warp π (wave ν T) _ ht (Precise.fitM ν Y K T S h hs hr hu)).2
lemma sourced (x:ℝ): coeff 3 (B γ)= -↑((Polynomial.derivative (S.team 3).coupling).eval x):=( (LowBound.pace3 ν Y K T S h hs hr hu x).trans (first ν Y K T S h hs hr hu |>.2) ).symm
end YM.FVA2.Lambda.AxisB
