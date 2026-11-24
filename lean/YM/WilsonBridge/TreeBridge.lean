import YM.WilsonBridge.ChartJets
import YM.WilsonBridge.Scalar
import YM.PertExtension.OrbLaurent

/-!
# From independent tree Gaussian to MS Swirl superalgebra

Actual normalized quotient Wilson coefficients, not analytic remainder estimates.
The change of gauge is stated so downstream suppliers can use a different based
resolution on *exactly the same* exponent, insertion and tree coefficients.
No connected-subset ambiguity: an insertion may itself be a product or include
contact terms. In this module still in position basis and **based** gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Based.Position
open MS MS.Book MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit
open MS.Book.Convolve Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Puff.Dynamics Orbit.LogReal Orbit.Cog
open PertExtension GaussianScore Orb Function Finset Lattice MeasureTheory WilsonBridge.Polynomial Native Bare Focus
open PertExtension.Series Radial PertExtension.Series.Tested Cylinder.Taylor Precision Filter
open PowerSeries (mk coeff)
open scoped BigOperators ContDiff Classical Topology
variable {G:Gauge}{n:Side} (he:Even n.val)
local notation "P"=> Position.Parity G n
local notation "W"=> actionW G n
local notation "Q"=> FreeBV.interaction (actionW G n) (haarW G n)
local notation "Tτ"=> noFP G he
local notation "π"=> PertExtension.Chart.tangent G (Cotree n)
local notation "H"=> tray G
local notation "Z" => exp0 P Q
local notation "V" => View Tτ
local notation "ℶ" => ℶV Tτ
variable (O:Wilson.Config G n→ℝ)
local infixl:70 " ★ " => Actors.core (PermV P)
local notation "R"=> Position.insertion O

def vacScale (G:Gauge)(n:Side) : ℝ := cJac G n * ∫ x:Dir G n, kernel fiscal x ∂ PertExtension.Chart.tangent G (Cotree n) -- correct
include he
lemma vac_pos : 0 < vacScale G n:= mul_pos cJac_pos (integral_exp_pos (ker_integrable he))
lemma posts (h:germ (charted O)) (i:ℕ): V (numeratorRows O i)= (vacScale G n)⁻¹ * (rows (restrictedO O) i:ℂ) := by
    let z:= (cJac G n)⁻¹
    let a := integrandSeries fiscal (accountingWith H (restrictedO O)) i
    have heq : V (numeratorRows O i)=(gaussian he (z • a):ℂ):= true_mean he (ΤΓ_pair (expΓ master.supported) (FreeBV.basis_level (d:=0) (ink_s _ (Position.glow G n).never h)) i (Set.mem_univ _)) (fun x=> totalRevenue x O h i)
    rw [ heq, ← show (∫ x:Dir G n,kernel fiscal x ∂π)*gaussian he a=rows _ i from rows_gaussian H _ i he];
    have hp: gaussian he (z • a)=z*gaussian he a:= by unfold gaussian Law.average; change (∫ x:Dir G n,z*a x* _ ∂π) / _ = z*((∫ x:Dir G n,a x * _ ∂π) / _); simp_rw [mul_assoc,integral_const_mul,mul_div_assoc]
    rw [hp]; unfold vacScale z; push_cast; 
    let r : ℝ:=∫ x:Dir G n, kernel fiscal x ∂ PertExtension.Chart.tangent G (Cotree n)
    have hz:(r:ℂ)≠0:= by exact_mod_cast (show 0<r from integral_exp_pos (ker_integrable he)).ne'
    field_simp [show ((↑(∫ x:Dir G n, kernel fiscal x ∂π):ℂ)≠0) from hz] -- no need cJac? denominator. proof auto?
omit he in
lemma oneStencil : rankLevel 0 (Position.insertion (1:Wilson.Config G n→ℝ))=(PermV P).unit:= by
    funext i; change mask (i+0:ℤ) (ink _ (fun _=>1))=useN.refineV (coin (1:ℂ)) i; rw [ink_const,Complex.ofReal_one,add_zero]
    by_cases hi:i=0; · subst i; rw [Nat.cast_zero,lone_use]; exact (rank_hat 0).mp (Rails.coin (v:=fun _=>1) (1:ℂ))
    unfold SplitP.refineV; rw [if_neg (show i≠useN.origin from hi)]; exact rank_off (Rails.coin (v:=fun _=>1) 1) (by omega)
lemma vacuum_scaled (i:ℕ): V (Z i)=(vacScale G n)⁻¹ * (rows (1:Observable G n) i:ℂ) := by
    let O:= (1:Wilson.Config G n→ℝ); have ht := posts he (1:Wilson.Config G n→ℝ) contDiffAt_const i
    unfold numeratorRows at ht; rw [oneStencil,(PermV P).identityR] at ht; exact ht

lemma billed_top (h:germ (charted O)) : Endμ Tτ P Q (rankLevel 0 R) (fun i => (Orb.diag (restrictedO O) i:ℂ)):= by
    unfold Endμ; funext i; let V0:=restrictedO O; let M:= (vacScale G n:ℂ)⁻¹
    let w0:=rows (1:Observable G n); let d:=Orb.diag V0
    change V (numeratorRows O i)=∑ j∈antidiagonal i,V (Z j.1)*(d j.2:ℝ)
    simp_rw [posts he O h i,vacuum_scaled, mul_assoc, ← Finset.mul_sum ]; congr 1
    simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum]; apply congr_arg ((↑) : ℝ→ℂ); apply Eq.symm
    have hv: PowerSeries.mk d * PowerSeries.mk w0=PowerSeries.mk (rows V0):= PowerSeries.ext fun i=> by rw [PowerSeries.coeff_mk]; exact congr_fun (rows_with_head (traySpec G) he V0) i
    rw [mul_comm] at hv; obtain hx:= congr_arg (PowerSeries.coeff i) hv; simp_rw [PowerSeries.coeff_mul,PowerSeries.coeff_mk] at hx; exact hx
-- go up once the unstripped match is proved
lemma priced {d:ℕ}(h:germ (charted O)) (hd:From R d) : EndRule.response P Tτ Q (rankLevel d R) = fun i=> (Orb.diag (restrictedO O) (i+d):ℂ) := by
    have ht:= EndRule.unique P Tτ Q _ FreeBV.MasterLaw.initial_zero _ (billed_top he O h); rw [prefactor hd, priceMove, EndRule.natural ] at ht
    funext i; rw [← shifts (EndRule.response P Tτ Q (rankLevel d R)) i d]; exact congr_fun ht (i+d)
lemma prices_zero {d:ℕ}(h:germ (charted O)) (hd:From R d) {i:ℕ}(hx:i < d): Orb.diag (restrictedO O) i=0 := by
    have ht:= EndRule.unique P Tτ Q _ FreeBV.MasterLaw.initial_zero _ (billed_top he O h); rw [prefactor hd, priceMove, EndRule.natural ] at ht
    exact_mod_cast (congr_fun ht i).symm.trans (shifts_zero _ hx)

/-- Finite all order, includes marked operators with external Laurent factor.
    no matching/renormalization assumptions. tree choice and full normalization specified. -/
theorem tree_to_based (d:ℕ) (J:(kinetic G n).Fixing)
    (h:germ (charted O))(ho:Invariant O)(hd:From R d) :
    Endμ J.half P Q (rankLevel d R) (fun i=> (Orb.diag (restrictedO O) (i+d) :ℂ)):= by
    apply (gauge_change blocks master J (treeFix G he) (physical ho h hd) _).mpr
    rw [computed_tree he h, ← priced he O h hd]; exact EndRule.agrees P Tτ Q FreeBV.MasterLaw.initial_zero _
end YM.WilsonBridge.Based.Position
