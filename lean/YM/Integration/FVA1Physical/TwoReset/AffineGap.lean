import YM.UVExt.TwoTone
import YM.UVExt.LoopShift
import YM.AllOrder.Floe.Era
import YM.AllOrder.Floe.Crown

/-!
# The affine rank 2 readout for the full regulator family determines Γ

Direct long wave proof. On unmasked tensors only. `Reserved`
exponential width and silence in EACH rank-2 packet are before any
result is priced. In particular avoids reading a periodic clover or
ignoring wrapping E when determining this (formal!) calibration.
A separate numerical estimate needed on actual vacuum and in the paid
marks at reset.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Lattice Wilson RG RG.Supply Gauge Input Org Precision Tree
open AllOrder AllOrder.Floe AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire
open AllOrder.Laplace AllOrder.Laplace.SigmaP Laurent Stationary Pace AllOrder.Ink AllOrder.Ink.Money
open Extra.Iteration Primitives.TwoWave Primitives.TwoWave.RealSlice Finset UVExt.Paths
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G: Gauge}{n : Side}
namespace ReadAffine
open Bid Extra.Iteration Jets
variable {A B C u r h t σ:ℝ}
variable {P Q:Layout G} {T:Finset Age}{q b:Pace.Coin}
variable {i:ℕ}
variable {M N : ℕ → Atom G 2}
set_option quotPrecheck false
local notation "X" c:max => (Link G c)

lemma abs_grad (u : Bid.Dir G n) (b k i x) :
    |Extra.Iteration.grad i (Extra.Iteration.flux u b k) x| ≤ gradD u := by
  let z:= (x,Exterior.plaquette b)
  let V:= Exterior.dColor G n 1 u
  let f : G.Color:= (deltaV i u) z
  have hx : f = V (x+step i,Exterior.plaquette b)-V (x,Exterior.plaquette b) := delta_entry ..
  have hk : Extra.Iteration.grad i (Extra.Iteration.flux u b k) x = f k := by rw [hx]; rfl
  rw [hk]; apply le_trans _ ((norm_le_pi_norm (deltaV i u) z).trans (norm_le_pi_norm (deltaV · u) i))
  simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_mul] using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ k) f

variable {ι : Type*} (Y: ι → Pattern G 2) (x: Bid.Dir G n) (hY : Charged (fun i=>(Y i).atom) σ A) (he:0≤σ) (hQ:∀ i,both (Y i))
include hY he hQ
lemma rivers : |Extra.Iteration.total Y (Extra.Iteration.flux x)| ≤ Fintype.card (Site n) * (gradD x)^2*A := by
  let L:= gradD x
  have hu : SumBudget (fun i=> (Y i).atom.magnitude) A:= by simpa [Charged,Atom.budget] using hY.mono he le_rfl
  let f:= fun i=> ∑ u:Site n, (Y i).sample (Extra.Iteration.flux x) u
  have hm: Summable f:= net_summable _ (Extra.Iteration.flux x) he hY
  have hv:0≤L := norm_nonneg _
  have hh(i:ι) (u:Site n): |(Y i).sample (Extra.Iteration.flux x) u|≤ L^2 * (Y i).atom.magnitude:= by
    rw [Pattern.sample,Atom.magnitude,mul_sum]
    apply (Finset.abs_sum_le_sum_abs ..).trans
    refine Finset.sum_le_sum (fun e _=>?_); rw [abs_mul, Finset.abs_prod,mul_comm (L ^ 2)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (show ∀ j∈(univ:Finset (Fin 2)),|_| ≤ L from fun j _=>?_)).trans_eq (by simp)
    have hx := hQ i j; obtain ⟨l,hl⟩:= Option.isSome_iff_exists.mp hx
    rw [hl]; exact abs_grad x _ _ _ _
  have hb(i:ι): |f i| ≤ ((Fintype.card (Site n):ℝ)*L^2)*(Y i).atom.magnitude:= by
    apply (Finset.abs_sum_le_sum_abs ..).trans
    apply (Finset.sum_le_sum (fun u _=> hh i u)).trans_eq
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
  apply (norm_tsum_le_tsum_norm hm.norm).trans
  apply (Summable.tsum_le_tsum hb hm.norm (hu.2.1.mul_left _)).trans
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hu.2.2 (by positivity)
omit hY he hQ

variable (hw: 0<σ) (hM:StateE.Quoted M σ B)
include hw hM
local notation "f" n:max => (Stationary.turnSeries (m:=n) M)

lemma leading (x:X n) : (PertExtension.Series.Radial.jet (f n) 2) x=
    Patch.average fun s:Signed=> Extra.Iteration.total (plain ∘ M) (Extra.Iteration.flux (pulled (arm G n 1 x) s)) := by
  have h:= Stationary.ray_limit (turns_analytic (m:=n) M hw hM.pay) (turns_low _ hw hM.pay) x
  have hp:= action_limit M hw hM.pay (arm G n 1 x)
  apply tendsto_nhds_unique_of_eventuallyEq h hp
  filter_upwards [] with t
  change (t^2)⁻¹*turnSeries M (t • x) = _
  rw [← map_smul (arm G n 1), div_eq_mul_inv,mul_comm]
  rfl

local notation "Z" => Extra.Iteration.momentPrice 2 (σ-(0:ℝ))*B

lemma pencils (x:X n) (v:Bid.Dir G n) (H:arm G n 1 x=v) :
    |(PertExtension.Series.Radial.jet (f n) 2) x| ≤ Fintype.card (Site n)* (16*gradD v)^2 * (Extra.Iteration.momentPrice 2 σ*B) := by
  rw [leading hw hM,H, Patch.average,abs_mul,abs_of_nonneg (show 0 ≤ (Fintype.card Signed:ℝ)⁻¹ from by positivity)]
  have hp: (Fintype.card Signed:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  let N:= (↑(Fintype.card (Site n)):ℝ)
  let L:= 16*gradD v
  let p:= Extra.Iteration.momentPrice 2 σ*B
  let Y:= Lift.strip M
  have ht: Charged (fun i=>(Y i).atom) 0 p:= by simpa only [p,Y,sub_zero] using (Lift.strip_cost hM.pay (η:=0) le_rfl hw)
  calc
     _ ≤ (Fintype.card Signed:ℝ)⁻¹ * ∑ s:Signed,N*L^2*p:= mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun s _=> by
       rw [← Lift.strip_total hM.pay (η:=0) le_rfl hw (hM.mute rfl)]
       apply (rivers Y (pulled v s) ht le_rfl fun p=> Lift.break_both _ _).trans
       change N*(gradD _)^2*p ≤ _
       exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
         (pow_le_pow_left₀ (norm_nonneg _) (UVExt.Paths.grad_pull v s) 2) (Nat.cast_nonneg _)) (Cost.nonneg ht))) (by positivity)
     _ = N*L^2*p:= by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ hp]
omit hw hM
end ReadAffine
end YM.Integration.FVA1Physical.TwoReset
