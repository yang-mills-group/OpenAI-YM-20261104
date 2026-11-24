import YM.QuadraticLocal.Startup.Arbor
import YM.QuadraticLocal.Startup.Load
import YM.QuadraticLocal.Pry
/-!
# Analytic MARK startup with literal unmasked cylinders and packed reserve

 Does not require finite-range coupling moments or positivity-of-chunk.State.K.
 Fill after preserving Origin budgets in model.F.Resource. If fitting.Economy StrongK grants
 arbitrary polynomial room for unmasked overpayments. Use on full mark family simultaneously.Weights
 can restore inverse coupling for installation here, still prior to HOLDER. Discrete labels and
 true cover support including X; help for subsequent re-read at x∉Unit.Test critical.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spes
open Function Filter Finset Wilson Lattice RG Marker Push Push.AbsoluteSums MeasureTheory Animals
open Corrected Hard Kiosk Canopy Ovens Ovens.Pipes Affinity Fusion Fusion.Attached GridRenewal.Rain
open Display Integration.LocalComparison ComparisonDensity.Address Comparison.Density.RenderM
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X Y:Activities G n}{P:Rep G n}
variable {α:Type*}{V ι:Type}[DecidableEq V]{R:Census V}{o:V→Site n}
variable {B s d k:ℕ}{a b f τ c e η q:ℝ}{w:V→ℝ} (hw:∀ i,0<w i)
variable [Fintype ι][Fintype V]
set_option quotPrecheck false
variable (D:V→Orbit)
def ampl : Affinity.Spring ℂ (Lens.portion D) where
   rate i f:= (Lens.adopts D).rate i f
   nonzero i x:= Complex.ofReal_ne_zero.mpr ((Lens.adopts D).nonzero i x)
   level i x h:= (by rw [(Lens.adopts D).level i x h,Complex.ofReal_one])
   accepts i x:=by rw [← Complex.ofReal_inv,Complex.coe_smul]; exact (Lens.adopts D).accepts i x
variable {D} {K:∀ v,Submodule ℂ (D v).Mood} {L:V→ Support n}
local notation "T"=> Affinity.Full (E:=fun v=>(D v).Mood)
local notation "Θ"=> Wallet (Lens.portion D)
local notation "z"=> readBack (Lens.portion D)
local notation "Y₀"=>ampl D
variable (F:Screen D ι R G n)(h: Screen.Rooted K L o F w c d)
variable (g:ℝ) (S:Kiosk.Second P.p X P.activities a b P.p.supportExponent f)(he:Hard.Rent X.forced X.K P.p (P.p.supportExponent+1) a)
local notation "R₀"=> F.render P.p o h g
local notation "Λ"=> F.shift P.p o h g
local notation "Y'"=> Kiosk.Second.canopy (Hard.rent he (o:=o) (R:=R) (α:=Wallet (Lens.portion D))) Λ S
local notation "δ"=> P.p.supportExponent
local notation "F'"=> F.log g
include h
namespace Screen

def furnished : Gallery Θ ι o P R:=⟨ (R₀).pullback z,Y'⟩
local notation "H"=> furnished F h g S he
def full : Gallery T ι o P R := (Y₀).card H
local notation "H'"=> full F h g S he
lemma rainforest : Adult L K H' := by
    refine Spring.employment L K Y₀ H ⟨⟨fun i j hj=> (h.leg i|>.frame j hj),fun i U=> ?_⟩,Affinity.Crown.second _ S Λ ?_ (fun i U=> F.holds P.p o h g i U)⟩
    · exact (F.esteemed P.p o h g i U).restrict _
    refine ⟨fun i U=> Affinity.Stencil.const (Poly.bead R (↑(X.K i U):ℂ)) fun i hi=>?_⟩
    exact (Poly.part_send ..).trans (if_neg hi)
lemma looksLike : (H').E=R₀:= by
   refine Lamps.ext rfl rfl (funext fun t=> funext fun i=> funext fun U=> ?_) rfl
   exact ((Y₀).basisIssue (H).E t U i).trans (congr_fun ((Y₀).determines (F.esteemed P.p o h g i U)) t)
lemma rise (p:BudgetPoint) (t:T)(U:Config G n): (Y₀).program t (F' (z ((Y₀).profile t)) U)= F' t U:= by -- true τ
   unfold log; rw [map_sum]; apply sum_congr rfl; intro i _; ext v; rw [Spring.part]; unfold rawTerms; rw [Poly.part_send,Poly.part_send]; split
   next ht=> subst v; exact congr_fun ((Y₀).determines (F.esteemed p o h g i U)) t -- no p here. supply? lean see. equivalent legal
   next=> simp
variable {v:V→ℝ} (hv:∀ i,0<v i) (hL:(Screen.shift P.p o F h g).Budget v P.p.B (P.p.supportExponent+1) f)
local notation "v'"=> Stoop.radius w e
include he S hv hL
lemma money {w1:V→ℝ}(hw':1 ≤ e)(hk:∀ i:R.Mode,i.val.card ≤ k)(hM: ((R₀).pullback z).Paid w1 P.p.B P.p.supportExponent q)(hY:v=Stoop.radius w1 e): (readH H' z).Pays w1 δ q (e^k*b):=by
   rw [show readH H' z=_ from (Y₀).reverts H]; refine ⟨hM,Stoop.budget («t»:=w1) hk _ ?_ hw' ?_⟩ -- parameters
   · intro i; specialize hv i; rw [hY] at hv; exact pos_of_mul_pos_left (show 0<w1 i*e⁻¹ from (by unfold Stoop.radius at hv; rwa [← div_eq_mul_inv])) (by positivity)
   rw [← hY]; exact (Hard.Rent.instals hv S he Λ P.p.exponent_pos.le hL).1
lemma offered {w₀:V→ℝ}(hs:∀ i,0< w₀ i) (ht:(H).Pays w₀ δ τ η) (t:T) (U:Config G n) : (H').density t U=(↑(P.eval U):ℂ) • Poly.pass (F' t U):=by
   have hh:= (Hard.Rent.instals hv S he Λ P.p.exponent_pos.le hL).2
   let φ:= (Y₀).profile t; let ρ:ℂ:= Real.exp (P.exponent U); let u:ℂ:= P.activities.gas P.p U; let x:T:=z φ; have ho: ( (Λ).log φ U).part R.quiet=0:=by unfold ShiftRows.log; rw [tsum_fintype,Poly.part_sum,sum_eq_zero (fun i _=>(Λ).skip ..)];
   have hV: ((H).E.log φ U).part R.quiet=0:=Lamps.quiet_of_hasSum φ U (ht.budget.sums P.p.exponent_pos.le hs φ U)
   have hz: P.eval U=(Real.exp (P.exponent U))* P.activities.gas P.p U:= rfl
   have hp : (H).density φ U=(↑(P.eval U):ℂ) • Poly.pass (F' x U):=by
       have hh' := (hh φ U).tsum_eq; have ht': F' x U= (H).E.log φ U+(Λ).log φ U:= F.log_io P.p o h g φ U; rw [ht', ← GridRenewal.Rain.passes _ (show _=0 from (by simp only [Poly.part_plus,hV,ho,add_zero])), GridRenewal.Rain.plus,GridRenewal.Rain.passes _ ho,GridRenewal.Rain.passes _ hV,hz,Complex.ofReal_mul, Gallery.density,show (H).gas φ U= _ from hh', mul_smul_comm,smul_smul]
   rw [full,Spring.tariff Y₀ H ht P.p.exponent_pos.le hs,hp,map_smul,Spring.program,ModeWeight.pass,show ModeWeight.turn R ((Y₀).booklet t) (F' x U)=_ from Screen.rise F h g P.p t U] -- final defeq
end Screen
end YM.QuadraticLocal.Spes
