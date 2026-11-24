import YM.MSbar.Lease.Year
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Bulk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {c f:Side} {S:StepData c f} {U:Config G f}{R: Rep G f}{R':Rep G c}{σ C T K B a b v r δ w β u:ℝ}{M k m:ℕ}
open ConnectedActivityE6 Finset RG.PathData Tree Push.Uniform Pressure SectorNext.Vacuum AnalyticBridge.VerifiedReset Next.Scheduling Precision Stock Metric Posture
variable (P:Patch)(D:KernelChoices)(p:Palisade)(J:Voice G) (L L' : Stage) (g : Clear G J)(x c₀:ℝ)
set_option quotPrecheck false
local notation "Ξ"=> tip G P.L
local notation "Kx"=> sizingW D
local notation "q!"=> voyageB (tip G P.L x)
local notation "b!"=> radiusB (tip G P.L x)
local notation "E!"=> skies (tip G P.L x)
local notation "r'"=> rot p (tip G P.L x)
local notation "H!"=> fear -- unused
variable (hc:Season J L L' x R R' S (courage G P.L x)) (A:S.patch=P)(A': S.kernel=D)
variable (X Y:Support f) (F: Forest S.ratio)(i:S.Choices)(W : Positions (Primary c G))
local notation "t!"=> courage G P.L x
local notation "Δ"=> (tip G P.L x)
local notation "R!"=> rot p Δ
local notation "B!"=> radiusB Δ
local notation "M!"=> voyageB Δ
local notation "X!"=> vest (priced F i R.clip R.path) W
local notation "V"=> represent (tint G (Exterior.Body 1 c) W)
local notation "b0"=> base J (tip G P.L x)
local notation "min!"=> pillow Δ
local notation "J!"=> hotel F X Y J V X! (pillow Δ) (room Δ)
local notation "e'"=> chance S R V
--
def curtains (L : Stage)(G:Gauge)(x s:ℝ)(p:Palisade)(B y j t:ℕ) := L.supportExponent *j+(heat L G x y p+leaseScore x B G)+(t:ℝ) -- include B.C exponent separately
local notation "Z'"=> (Y.card:ℝ)
include g hc A
variable (hp: Posture p J F (pillow (tip G P.L x)) (room (tip G P.L x)) (base J (tip G P.L x)) (rot p (tip G P.L x)) (voyageB (tip G P.L x)) (radiusB (tip G P.L x)) X Y W (vest (priced F i R.clip R.path) W) R.p)
    (t:Grants i R F p m)(F':ℝ→ℕ)(k' l:ℕ)(youthFill:(coverNumber R.p.B (youth F Y))≤l)(hy:Y.card≤ F' x) (e:ℝ)
set_option quotPrecheck false
local notation "yB"=> F' x
local notation "yLevel"=> F' x * (4:ℕ)
local notation "Xb"=> X.card
local notation "ψ!"=> Ξ x
local notation "rb"=> (Ξ x)^(-(1:ℝ))
local notation "eps0"=> silkRoad L'.paths L'.width (ability Δ) (lbt Δ) R.beta X.card (M!) R.p B!
local notation "κ!"=> Real.exp (silkRoad L'.paths L'.width (ability Δ) (lbt Δ) R.beta X.card (voyageB Δ) R.p (radiusB Δ))
local notation "Z1"=> youth F Y
local notation "δ'"=> wSize G R.p L'.width L'.paths (ability Δ) (lbt Δ) R.beta (voyageB Δ) Y.card X.card p R! (room Δ)
-- choose margin_G output.B.',charging. size bounds. Need `moss inv ≤ exp(Lease)`

omit g hc A in
def lastY (P:Patch)(n:ℕ):= n*skirt (4*P.L.val+8)
omit g hc A in
def leaseX (L:Stage)(P:Patch)(G:Gauge)(p:Palisade)(s x e:ℝ) (y j:ℕ):= let u:=tip G P.L x; (courage G P.L x)*Real.exp (curtains L G u s p (y*4) y j (lastY P y))*(u^e*2)
include t hp youthFill hy A'
lemma brought (hd: Real.log Δ ≥ 1):
     let c₁:= Real.exp δ'/moss G ((tip G P.L x)^(-(1:ℝ))) (board F X).card
     0 ≤ κ! - 1 ∧ κ! ≤ payRoad L' G P x (F' x) ∧ t!*(R.p.mass (youth F Y) (c₁*(tip G P.L x)^e*2)* Real.exp ((youth F Y).card*(1:ℝ))) ≤ leaseX L' P G p e x e (F' x) l :=by
    let A₀:= heat L' G Δ (F' x) p; let B₀:= (F' x)*4; let J':=L'.supportExponent;let Z:= youth F Y; have hp' := hp.awake; have hr :0 ≤ rot p Δ:= (norm_nonneg _).trans hp'
    obtain ⟨hV,hC,hY⟩:= Era P p J L L' x hc A X Y F i F' t hy hp.extendsX hd hr -- order
    intro c₁; refine ⟨sub_nonneg.mpr (Real.one_le_exp hV),Real.exp_monotone hC, ?_⟩
    have hH:=hc.case_; rw [A] at hH
    have hz:0<tip G P.L x:= zero_lt_one.trans hH.enough; have hB: (board F X).card ≤ B₀:= (boardC F X).trans (Nat.mul_le_mul_right _ ((card_le_card hp.extendsX).trans hy))
    let I₀:= curtains L' G Δ e p B₀ (F' x) l (lastY P (F' x)); let V':= leaseScore Δ B₀ G; have hK : c₁ ≤ Real.exp (A₀+V') := by
        unfold c₁; rw [pine G Δ hz,Real.exp_neg, div_inv_eq_mul,← Real.exp_add]; apply Real.exp_monotone
        apply add_le_add hY;unfold V' leaseScore; refine mul_le_mul_of_nonneg_left (by exact_mod_cast hB) (mul_nonneg ?_ (Nat.cast_nonneg _)); have he:= Real.log_nonneg (show (1:ℝ)≤4 by norm_num); linarith only [hd,he]
    let Jg:=Δ^e; have hw:0 ≤ Jg:=Real.rpow_nonneg hz.le _
    have he: Z.card≤ lastY P (F' x):=by have he:= Corona.halo_size Y (4*S.patch.L.val+8); refine le_trans (show Z.card≤ _ from he) ?_; unfold lastY skirt; rw [A]; exact Nat.mul_le_mul_right _ hy
    have hu : R.p.mass Z (c₁*Jg*2) ≤ Real.exp (J'*l+A₀+V')*(Jg*2):=by
        let H:=Real.exp (J'*l); unfold BudgetPoint.mass; rw [hH.support, add_assoc _ A₀ V',Real.exp_add, mul_assoc c₁]; have hX:=L'.price_pos.le; refine le_trans (b:= Real.exp (J' * l)* (Real.exp (A₀+V')*(Jg*2))) ?_ (le_of_eq (by ring)); apply mul_le_mul _ (mul_le_mul_of_nonneg_right hK (mul_nonneg hw zero_le_two)) _ (Real.exp_pos _).le
        apply Real.exp_monotone; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr youthFill) L'.price_pos.le
        unfold c₁ moss; have hh:0 ≤ rb:=Real.rpow_nonneg hz.le _; positivity
    let W':= Real.exp ((Z.card:ℝ)*1); let a:=courage G P.L x
    have hh : R.p.mass Z (c₁*Jg*2) * W' ≤ Real.exp I₀*(Jg*2) := by
        apply le_trans (mul_le_mul hu (show W' ≤ Real.exp (lastY P (F' x)) from ?_) (Real.exp_pos _).le ?_) (le_of_eq ?_); · unfold W';rw [mul_one]; exact Real.exp_monotone (by exact_mod_cast he)
        · positivity
        unfold I₀ curtains J' A₀ V' B₀; simp_rw [Real.exp_add]; ring
    unfold leaseX; change a *_ ≤ a* _ *_; rw [mul_assoc a (Real.exp _) _]; exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
end YM.MSbar.Heath.Cottage
