import YM.AllOrder.Fire.Bound
import YM.AllOrder.Response.Vane
/-!
# Booklet for price transfer over angular, lattice legs

Generation formula and improved rank of the actual projected one-step
vacuum polynomial. Period finite *using all levels*, no mirror assumptions.
This file to be used for transmission of the local strip (rank and reach only).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response Module GaussianScore
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] (A: Law Y)
    {ι:Type} [Fintype ι] (B:Basis ι ℝ Y)
local notation "Ω"=>X×Y
section columns
local notation "I₀"=> fun i:ι=>((0:X),Inv A B i)
abbrev rowM (i j:ι) : ℝ:= B.coord j (Inv A B i)
lemma money (v:Ω→ℝ)(i:ι) : diff' (I₀ i) v=∑ j:ι,rowM A B i j • diff' (vec B j) v:= by
 ext1 x; unfold diff'; rw [Finset.sum_apply]; let u:= Inv A B i; have ht : I₀ i=∑ j:ι,rowM A B i j • (vec (X:=X) B j) := by
   change (ContinuousLinearMap.inr ℝ X Y) u=_; conv_lhs => rhs; rw [←B.sum_equivFun u]
   rw [map_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul]; rfl
 rw [ht,map_sum]; simp only [map_smul,Pi.smul_apply]
lemma duplex (v:Ω→ℝ): infinity A B v =∑ i:ι,∑ j:ι,rowM A B i j • diff' (vec B j) (diff' (vec B i) v):= sum_congr rfl fun i _=> money A B _ i
lemma apron (v w:Ω→ℝ): connection A B v w=∑ i:ι,∑ j:ι,rowM A B i j • (diff' (vec B j) v*diff' (vec B i) w):= by unfold connection; apply sum_congr rfl; intro i _; rw [money A B v i]; simp_rw [Finset.sum_mul,smul_mul_assoc]

-- sector preserving commute for Rank proof later
end columns
open Lattice Gauge RG Wilson Pressure Precision Tree Push Push.Uniform
open ConnectedActivityE6 Blaze PhysicalNext Repeat Local.Vote
variable {G:Gauge} {c f:Side}{S:StepData c f}{F:Forest S.ratio}{u:ℝ → Config G f→ℝ}{O:ChartRatio G}{k:S.Choices}
    (D:Desk F O u k)
local notation "K"=> Precision.Key F G
lemma radius (n:ℕ): Rank (Apex c G) (n+2) (ratePlan D n):= by
   let V:= D.hard; let L:= fderiv ℝ D.quiet 0; let U : Apex c G →L[ℝ] Apex c G × Poll.Body (Precision.Key F G):= (ContinuousLinearMap.id ..).prod L; let Q:= Impulse L D.high D.paid; let h:=end_rank (castle D.hard D.quiet D.pay.steer) (EuclideanSpace.basisFun (Precision.Key F G) ℝ).toBasis volume (u:=Q) (win0 _) (impulse_rank L D.high D.paid) n
   refine Rank.add (f:=_root_.YM.AllOrder.Response.wirings (fun x=> preview D-liftQ V L x) n) ?_ h; change Rank _ _ (wirings (fun x=> preview D-liftQ V L x) n); rcases n with _|i; swap;
   · have hh: ∀ (x:Apex c G), wirings (fun x=> preview D-liftQ V L x) (i+1) x=0:= fun x=> by simp [wirings,swap,just]
     exact (funext hh).symm ▸ Rank.nil _ 0
   exact (Rank.nil 2 (preview D)).sub ((Rank.hom U (iteratedFDeriv ℝ 2 V 0)).scal (↑(Nat.factorial 2):ℝ)⁻¹)
end YM.AllOrder.Fire
