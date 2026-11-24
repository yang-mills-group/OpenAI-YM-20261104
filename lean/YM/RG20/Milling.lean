import YM.RG20.Loan
noncomputable section
set_option autoImplicit false
namespace YM.RG20.Loan
open Function Filter Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open MeasureTheory UVExtension Spire Dales Guild Push Oriel Oriel.Charted Camp Camp.Cart Fitted Orchard
set_option quotPrecheck false
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{R : Factor A}(S: Spire.Uses R hG)
    (v : Keys S) {N p i:ℕ}
local notation "T"=> A.B.a
local notation "D"=> (S.fits N p)
local notation "E"=> (S.cart N p)
local notation "α"=> (A.B.kin.alpha N)
local notation "κ"=> (S.grove.coins)
local notation "π"=> (S.grove.pledge)
local notation "s"=> (S.grove.peak)
local notation "rp" i=> (D).W (i)
local notation "ß"=> (money S v N p)
local notation "ℒ"=> (actual S v N p)
local notation "℃"=> (scalarBook S v N p)
local notation "s!"=> (levelPlot S v N p)
local notation "τ"=> S.token N p
local notation "Y" i=> ((Loan.H S v).rep N p (i))
local notation "Ψ" i=> sitecharge S N p (i)
local notation "δ"=> A.B.a.clock
local notation "∆" i=> ζnorm S N p (i)
local notation "δE"=> A.B.a.clock.allowance
local notation "δK"=> A.B.a.clock.forcedAllowance
/-! # Finite-width ultraviolet preview and roll/update of ACTUAL data
Credit on λ accrues at the true incoming rows; we don't try to iterate an
illegal `valid` perturbed set of measures or approximate the extensive scalar,
which we leave alone. The new inhomogeneous (actual-ε mentees) along adjacent
levels is priced, *including* those K data whose masks make them invisible near
flat configurations. The model does not omit any actual masking errors for free.
This supplies a fixed-order-window (log width in NUMBER OF LEVELS) repeatable
*physical* vacuum approximation in the same exact normalized Banach currency,
under all sectors, not Taylor/log-of-K approximation and not claiming independent
PT identification. It allows the actual kernel of every scale to be evaluated in
supported-local tests even after discarding all farther E & K at the far-mesh
start. A local model of another kind still has to pay the displacement cost of
adapting to these same rays. -/
variable {j e d:ℕ}
local notation "T'" i => A.B.a.clock.hatBeta (i)
local notation "ζ!" => Oriel.rim
local notation "s*" => Camp.soft
local notation "Q*" i => (sitecharge S N p (i))
lemma fall_g : 0< Camp.soft ∧ Camp.soft ≤ 1/2 ∧ Camp.soft<Oriel.rim:= by norm_num [Camp.soft,Oriel.rim]
omit v
lemma duelcharge (x y z:vertex S N p i): sitecharge S N p i (x-y) ≤ sitecharge S N p i (x-z) + sitecharge S N p i (z-y):=by
   unfold sitecharge; simp_rw [map_sub]; exact norm_sub_le_norm_sub_add_norm_sub ..
include v
-- no `a_i/a_j` claims
/-- Surrogate *real*, in the chosen supported metric. Re-use readings only;
reflush true coupled-trajectory while walking. Don't touch masks. -/
def accrual (N p e:ℕ)(A:vertex S N p e)(i)(he:i≤ e)(hN:e ≤ N): vertex S N p i:= Nat.decreasingInduction (motive:=fun i _=> vertex S N p i)
    (fun i h V => roller S v N p i (h.trans_le hN) V) A he
local notation "Q'"=> accrual S v N p e
variable {V:vertex S N p e}
lemma pitch (hi:i< e)(hN:e≤N): accrual S v N p e V i hi.le hN=roller S v N p i (hi.trans_le hN) (accrual S v N p e V (i+1) hi hN):=Nat.decreasingInduction_succ_left _ _ _ _
lemma pitch_top (hN:e≤N): accrual S v N p e V e le_rfl hN=V:= Nat.decreasingInduction_self ..

lemma constantR (hi:i≤ e)(hN:e≤N): accrual S v N p e (actual S v N p e) i hi hN=actual S v N p i:=by induction hi using Nat.decreasingInduction with
    | self=> exact pitch_top S v hN
    | of_succ i hi ih=> rw [pitch S v hi hN,ih]; exact (summitBill S v (hi.trans_le hN)).1.symm
lemma tram (hi:i ≤ e)(hN:e≤N)(hp:sitecharge S N p e V ≤ Camp.soft):
    let Q:= accrual S v N p e V i hi hN; sitecharge S N p i Q≤ Camp.soft ∧ sitecharge S N p i (actual S v N p i-Q)≤ Camp.soft^(e-i)*sitecharge S N p e (actual S v N p e - V):=by
    induction hi using Nat.decreasingInduction with
    | self => rw [pitch_top S v]; intro Q; rw [Nat.sub_self,pow_zero,one_mul]; exact ⟨hp,le_rfl⟩
    | of_succ i hi ih =>
       intro Q; let P':= accrual S v N p e V (i+1) hi hN; let H:= (ℒ (i+1)); have hx:0<s*:=fall_g.1; have he':s* < ζ!:= fall_g.2.2
       let h := hi.trans_le hN
       have hQ:Q=roller S v N p i h P':= pitch S v hi hN
       obtain ⟨h₁,h₂,-⟩:=shore S v h P' H (ih.1.trans_lt he') ((pricelist S v h).trans_lt he'); refine ⟨hQ.symm ▸ h₁, ?_⟩;
       have hf(x y:vertex S N p i): sitecharge S N p i (x-y)=sitecharge S N p i (y-x):=by unfold sitecharge; simp_rw [map_sub]; exact norm_sub_rev ..
       have hz(x y:vertex S N p (i+1)): sitecharge S N p (i+1) (x-y)=sitecharge S N p (i+1) (y-x):=by unfold sitecharge; simp_rw [map_sub]; exact norm_sub_rev ..
       -- rw hazard changing actual e via projection? e independent
       rw [← hQ, ← (summitBill (p:=p) S v h).1, hf, hz] at h₂
       rw [show e-i=e-(i+1)+1 by omega, pow_succ',mul_assoc]; exact h₂.trans (mul_le_mul_of_nonneg_left ih.2 fall_g.1.le)

-- at cutoff itself use actual root Wilson seed instead of omitting any data
-- enough finite width L(r)=⌈q*log(beta)/log2⌉ ahead. no assumptions on window spacing/duration.
omit v
def preWidth (B: Levels G)(k d:ℕ) := Nat.ceil ((d:ℝ)*Real.log (B.clock.hatBeta k)/Real.log 2)
abbrev capSphere (N i d:ℕ) := min N (i+preWidth (A.B.a) i d) -- args S implicit? levels uses A, C.
lemma optimistic (hi:i≤N) : i≤ capSphere (A:=A) N i d := le_min hi (Nat.le_add_right ..)
local notation "K" i d=> capSphere (A:=A) N (i) (d)
lemma aft (B:Levels G) (i d:ℕ) : Camp.soft^(preWidth B i d) ≤ (B.clock.hatBeta i^d)⁻¹:=by
    let x:= B.clock.hatBeta i; let u:= Real.log 2; let j:= preWidth B i d; have h:0 < x:= zero_lt_one.trans (B.fits.delayed _); have hh:0<u:= Real.log_pos one_lt_two
    refine (pow_le_pow_left₀ fall_g.1.le (show Camp.soft ≤ (2:ℝ)⁻¹ from one_div (2:ℝ) ▸ fall_g.2.1) _).trans ?_; change (2:ℝ)⁻¹^j ≤ (x^d)⁻¹; rw [inv_pow]; apply inv_anti₀ (pow_pos h _) ; rw [← Real.exp_log h, ← Real.exp_log (show 0<(2:ℝ) by norm_num),← Real.exp_nat_mul,← Real.exp_nat_mul]; apply Real.exp_monotone; exact (div_le_iff₀ hh).mp (Nat.le_ceil _)
lemma width_limited (B:Levels G)(i d:ℕ) : (preWidth B i d:ℝ)≤ (d:ℝ)*Real.log (B.clock.hatBeta i)/Real.log 2 +1:= (Nat.ceil_lt_add_one (div_nonneg (by positivity [Real.log_nonneg (B.fits.delayed i).le]) (Real.log_pos one_lt_two).le)).le

/-- Didn't assume perturbed measures were actual, don't interpret their partition if standing in for vacuum!
 Transcribe step in the same address chart + reset to true beta.
 -/
def ranger (N p i d:ℕ) : vertex S N p i:=
   if hi:i≤N then accrual S v N p (capSphere (A:=A) N i d) (if capSphere (A:=A) N i d=N then actual S v N p (capSphere (A:=A) N i d) else 0) i (optimistic (A:=A) hi) (min_le_left ..) else 0
local notation "Λ" d=> ((T' i)^ (d))⁻¹

include v
lemma slap (hi:i≤ N): sitecharge S N p i (ranger S v N p i d)≤ Camp.soft ∧ sitecharge S N p i (actual S v N p i-ranger S v N p i d) ≤ ((A.B.a.clock.hatBeta i)^d)⁻¹:=by
    let x:= T' i; have hp:1<x:=(T).fits.delayed i; let a:= i+preWidth (T) i d; let j:=capSphere (A:=A) N i d; have hh:j≤N:= min_le_left ..; have hs:s*≤1:= fall_g.2.1.trans (by norm_num); have hz(i): sitecharge S N p i 0=0:= by simp only [sitecharge,map_zero,norm_zero]; -- eta k arbitrary
    unfold ranger; rw [dif_pos hi]; split; next h=>
       rw [constantR]; rw [sub_self,hz]; exact ⟨pricelist S v hi, inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hp).le _)⟩
    next h=>
       obtain ⟨hf,H'⟩:= tram S v (optimistic (A:=A) hi) (show capSphere (A:=A) N i d ≤N from hh) (show sitecharge S N p (capSphere (A:=A) N i d) 0≤ s* from (hz _).trans_le fall_g.1.le)
       refine ⟨hf,H'.trans ?_⟩; rw [sub_zero]
       apply le_trans (mul_le_of_le_one_right (pow_nonneg fall_g.1.le _) ((pricelist S v hh).trans hs))
       have ht:a < N:= lt_of_not_ge fun he=> h (min_eq_left he); change s*^(min N a-i) ≤ _; rw [min_eq_right ht.le, show a-i=_ from Nat.add_sub_cancel_left i (Loan.preWidth (T) i d)]; exact aft (T) i d

end YM.RG20.Loan
