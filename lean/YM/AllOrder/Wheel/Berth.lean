import YM.AllOrder.Wheel.Wage
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Wheel
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Catch Catch.Clock Floe StateE Pace Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{L n f : Side}{ι:Type*}{T:Clock ι} {K:KernelChoices}{P:Patch}{σ C b a D η κ:ℝ}{k l p j M:ℕ}
open ConnectedActivityE6.Coat Shellac Work.G05
variable (S:Stage) (R:PathData G) (hG:G.Simple) {Λ:ℝ} (h:R.Bounds S.clip S.width S.paths Λ)
    (x: Apex n G) {β:ℝ} (hp:0<β)
local notation "g"=> gStep β
local notation "L"=> Kinetic.Port.exteriorL G n
local notation "Z"=> staff S.clip R n
local notation "W"=> Precision.loop R ∘ Desk.night (c:=n)
local notation "Tq"=> Shellac.off -- conflicts Clock T. adapt
include h
lemma driftW : drift S.clip R 0 n=W:= funext fun i=>by unfold drift draft; simp only [Function.comp_apply,zero_mul,zero_add]; rfl
lemma center : base S.clip R k n ((L).symm x) = jet Z (k+2) x := by
    let f: Link G n→L[ℝ] Apex n G:= (L).toContinuousLinearMap; let Q:=Classical.choice (BareRates.offered G S.width S.paths k); have ht:ContDiffAt ℝ ω Z 0:= (cursor _ _ 0 h Q _ (mem_ball_self zero_lt_one)).1
    change jet (Z∘f) (k+2) _=_; rw [Kinetic.pivot f _ _ ht]; simp only [f, ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
lemma core : (Coat.clerk (fun _=> Precision.loop R) 0) k n ((L).symm x) = jet W k x := by
    let f: Link G n→L[ℝ] Apex n G:= (L).toContinuousLinearMap; let Q:=Classical.choice (BareRates.offered G S.width S.paths k); have ht:ContDiffAt ℝ ω W 0:= driftW S R h (n:=n) ▸ (cursor S.clip R 0 h Q _ (mem_ball_self zero_lt_one)).2
    change jet (W∘f) k _=_; rw [Kinetic.pivot f _ _ ht]; simp only [f, ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
abbrev adjective (A:Scene G)(c:Side)(β:ℝ): Book (Apex c G) := fun i y=> A i c (bend (gStep β) y)
include hp
lemma oracleB: delay (adjective (Haiku.Coat.clerk (fun _=> Precision.loop R) 0) n β) k (gStep β)=blockTaylor k W:= by
 ext1 z; have hv:= (gS β hp).1; let u:= Plateau.bend (G:=G) (n:=n) (g) z; unfold delay; rw [Finset.sum_apply]; conv_rhs=> rw [← unbend (g) z hv];
 rw [Local.Pure.bill_insert]; apply Finset.sum_congr rfl; intro j _; rw [show (g ^ j • adjective (Haiku.Coat.clerk (fun _=> Precision.loop R) 0) n β j) z=(g^j)*jet W j (L u) from ?_]; rfl
 change g^j*Haiku.Coat.clerk (fun _ => Precision.loop R) 0 j n u=_; rw (occs:=.pos [1])[← (L).symm_apply_apply u, core S R h (L u)]
include hG
lemma oracleA: Tq (delay (adjective (base S.clip R) n β) k (gStep β))= Tq (β • (blockTaylor (k+2) Z)) := by
 let f(q:ℝ):=q; let P:= base S.clip R; let U' v:Apex n G:= g⁻¹ • v; have hv:=gS β hp; have he(v:Apex n G): delay (adjective P n β) k (gStep β) v = β*blockTaylor (k+2) Z v-β*(Z 0):= by
     let y:= U' v; unfold delay; rw [Finset.sum_apply]; conv_rhs=>  enter [1,2]; rw [show v=g • y from (smul_inv_smul₀ hv.1.ne' v).symm]; -- conv syntax
     rw [Local.Pure.bill_insert,sum_range_succ' _ (k+2), sum_range_succ' _ (k+1), show Local.Pure.chip Z 1 y=0 from first_main S.clip R h hG _, show Local.Pure.chip Z 0 y=Z 0 from Tensor.coeff_apply_zero ..]; simp only [mul_zero,pow_zero,one_mul,add_zero,mul_add,add_sub_cancel_right]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; change g^j* P j n ((L).symm y) = β*(g^(j+2)*jet Z (j+2) y); unfold P; rw [center S R h,pow_add]; have hζ:g^2*β=1:=hv.2; linear_combination -g^j*jet Z (j+2) y*hζ
 ext1 i; change delay (adjective P n β) k g i-delay (adjective P n β) k g 0=_; rw [he,he]; simp only [Shellac.off,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; ring
omit hp in

lemma oracleX: blockTaylor 1 (Tq Z)=0 := by
 let X:=Apex n G; ext1 x; rw [taylor_off,blockTaylor]; swap;
 · exact ((cursor S.clip R 0 h (Classical.choice (BareRates.offered G S.width S.paths 0)) _ (mem_ball_self zero_lt_one)).1.of_le le_top)
 have hh(v:X) : Tensor.diagonal (Tensor.coeff Z 1 0) v =0:= first_main _ _ h hG v; have h'(v:X) : Tensor.diagonal (Tensor.coeff Z 0 0) v= Z 0:= Tensor.coeff_apply_zero ..; unfold Shellac.off; simp only [Pi.sub_apply,Finset.sum_apply,sum_range_succ,sum_range_zero]; simp_rw [Pi.add_apply,Pi.zero_apply,hh,h']; abel
end YM.AllOrder.Wheel
