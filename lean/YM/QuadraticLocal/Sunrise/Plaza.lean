import YM.QuadraticLocal.Sunrise.Campus
/-!
# Period exact rooted-jet from finite aperture
 across all senses preceding `Y` shrinks. Wound lengths charged as TRUE cover.
 No symmetry or positivity assumptions, doesn't compare true step yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise.Plaza
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker AllOrder.Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Kinetic.Port
-- standalone for projections at first mark later.Stays.
variable {G:Gauge}{n m:Side} {α:Type}[Fintype α] {C D A:ℝ}
variable (H:Finset (Point α))(x:Site n)(z:Site m){j k d:ℕ}(f: rule α m→ℝ) (F:rule α n→ℝ)
local notation "Ω"=> rule α n
local notation "T"=> rule α m
local notation "Ξ"=> H
local notation "σ"=> ContinuousLinearMap
set_option quotPrecheck false
local notation "height2" a:max=> stood x (a:Point α)
local notation "hz" a:max=> stood z (a:Point α)
variable (hIn:Set.InjOn (stood (α:=α) z) (↑H)) (hr:∀ u v,(∀ i∈ H,u (stood x i)=v (stood z i))→ F u=f v)
def moves : Ω→L[ℝ] T := ∑ i:H,(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Leaf n α=>ℝ) (stood x i.val)).smulRight (spot (stood z i.val))
lemma moveX (v:Ω): moves H x z v=∑ i:H,v (stood x i.val) • spot (stood z i.val):=by unfold moves; rw [ContinuousLinearMap.sum_apply]; rfl
include hIn hr in
lemma moveValue : f ∘ moves H x z=F:=funext fun u=>by
    symm; apply hr; intro i hi; rw [moveX,Finset.sum_apply]; let I:↥H:=⟨i,hi⟩; rw [sum_eq_single I ?_ (by simp)]; · simp [I,spot]
    intro v _ hv; have he: stood z i≠ stood z v.val:=fun e=> hv ((Subtype.ext (hIn hi v.prop e):I=v).symm); simp [spot,Pi.single_apply,he]
local notation "Θ"=> Tensor.coeff f k 0
variable (k)
abbrev Sign : Type:= Fin k→ H
local notation "J"=> Sign H k
local notation "φ"=> fun (t:J) (j:Fin k)=> stood z ((t j).val)
def fee (i:J):ℝ:= (iteratedFDeriv ℝ k f 0 (fun j=>spot ((φ) i j)))*(k.factorial:ℝ)⁻¹
def labels (i:J):=List.ofFn (fun j=> (i j).val)
-- `Meter` mon rank spectral Local.Render.P.Read.H
lemma money (e:J)(v:Ω): invoice x (labels H k e) v=∏ i,v (stood x (e i).val):=by simp [Ink.invoice,labels,Ink.paid,List.prod_ofFn]
def tile : AllOrder.Ink.Field α where
    Ty := Sign H k
    fee := fee H z k f -- argument order inspect
    slip := labels H k
local notation "Φ"=> tile H z k f
include hIn hr
lemma talks (hp:ContDiffAt ℝ ω f 0): (tile H z k f).site n x=Radial.jet F k:=by
 ext1 v; rw [← moveValue H x z _ _ hIn hr, Kinetic.pivot (moves H x z) f v hp]; unfold Radial.jet; rw [moveX]; change (∑' i:J, fee H z k f i* Ink.invoice x (labels H k i) v) =_; rw [tsum_fintype,ContinuousMultilinearMap.map_sum_finset (iteratedFDeriv ℝ k f 0),Fintype.piFinset_univ]; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; rw [money,ContinuousMultilinearMap.map_smul_univ]; unfold fee; rw [smul_eq_mul]; ring
omit hIn hr
lemma spending (e:J)(hx:∀ i∈H,size i.1≤d) : meter (labels H k e) ≤ k*d:= by
 unfold labels meter; rw [List.map_ofFn,List.sum_ofFn]; exact ((Finset.sum_le_sum (fun i (_:i∈(univ:Finset (Fin k)))=> (show _ from hx _ (e i).prop)))).trans_eq (by simp) -- test unification
lemma burns (he:Allows k f 0 C)(t:J) : ‖fee H z k f t‖≤ C:=by
 have hp:∀ i:Fin k, ‖spot ((φ) t i)‖≤1:=fun i=>by apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j; simp [spot,Pi.single_apply]; split_ifs <;> simp -- likely norm =1
 unfold fee; rw [norm_mul]; have h1 : ‖(k.factorial:ℝ)⁻¹‖≤1:=by rw [norm_inv,Real.norm_of_nonneg (Nat.cast_nonneg _)]; exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos k)
 refine (mul_le_of_le_one_right (norm_nonneg _) h1).trans ((ContinuousMultilinearMap.le_opNorm ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun i _=>hp i))).trans (he.norm_le _ le_rfl)))

lemma pilot (he:Allows k f 0 C)(a:ℝ)(h:0≤a)(hx:∀ i∈H,size i.1≤d) : (tile H z k f).Good a (((↑(H.card^k):ℝ)* (Real.exp (a*(k*d:ℕ)) * C))) k :=by
 constructor; · intro i; change (labels H k i).length≤ _; simp [labels]
 let f':= Real.exp (a*(k*d:ℕ))*C
 change SumBudget (fun i:J=> (Φ).price a i) _; exact budget_finite ( (Φ).price_nonneg _) ((Finset.sum_le_sum (g:=fun i:J=>f') (fun i _=>mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (spending _ _ _ hx)) h)) (burns H z _ _ he i) (abs_nonneg _) (Real.exp_pos _).le)).trans_eq (by rw [Finset.sum_const,card_univ]; rw [show Fintype.card (Sign H k)=H.card^k from by unfold Sign; simp,nsmul_eq_mul]))
end YM.QuadraticLocal.Sunrise.Plaza
