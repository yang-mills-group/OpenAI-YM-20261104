import YM.RG20.Milling
import YM.RG20.Window
import YM.UVExtension.Mast.Rig
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
/-! # Expose complete budget for next real steps WITH approximate preview. β forecast at true
 β, alpha and Cart. Weighted losses at every step and concrete estimate summed from true collar. -/
local notation "B" i => A.B.a.clock.hatBeta (i)
local notation "z" => Oriel.rim
local notation "c*" => Camp.soft
local notation "x*" i:max => actual S v N p i
variable {d:ℕ}
local notation "V" i:max => ranger S v N p i d
local notation "P'" i:max => ((A.B.a.clock.hatBeta i)^d)⁻¹
variable {e:ℕ}
include hG
lemma currents (T:Levels G) : ∀ i,T.clock.hatBeta i+tom G≤T.clock.hatBeta (i+1):=by -- rename parameter
  intro i; unfold Calendar.hatBeta tom; rw [Schedule.scale_succ,mul_add,← add_assoc]; apply add_le_add_right; exact mul_le_mul_of_nonneg_left (Real.log_le_log two_pos (show (2:ℝ)≤ ((T.S).block i).val from by exact_mod_cast (show 2 ≤ ((T.S).block i).val from Nat.le_trans (by norm_num : 2 ≤ 3) ((T.S).block_large i)))) (Gauge.slopeConstant_pos hG).le
-- generalize Window.stride_gain to Levels
lemma climbs (T: Levels G) : Monotone T.clock.hatBeta := monotone_nat_of_le_succ fun i=> (le_add_of_nonneg_right (tom_pos hG).le).trans (currents (hG:=hG) T i)
lemma refund (T: Levels G) (i d:ℕ): ((T.clock.hatBeta (i+1))^(d+2))⁻¹ ≤
    (tom G)⁻¹ * (((T.clock.hatBeta i)^(d+1))⁻¹- ((T.clock.hatBeta (i+1))^(d+1))⁻¹):= by
   have hv := currents (hG:=hG) T i; let x:=(T.clock.hatBeta i); let y:= (T.clock.hatBeta (i+1)); let c:=tom G
   have hr:0 < x:=zero_lt_one.trans (T.fits.delayed _); have hx:x≤ y:= climbs (hG:=hG) T (Nat.le_succ i); have hs: x+c ≤ y:= hv; have he:0<c:=tom_pos hG
   have hy:= hr.trans_le hx; rw [inv_mul_eq_div,le_div_iff₀ he]; simp only [← inv_pow]
   have hδ: y⁻¹+y⁻¹^2*c≤ x⁻¹ :=by field_simp; nlinarith only [mul_le_mul_of_nonneg_left hs hy.le,mul_le_mul_of_nonneg_right hx he.le]
   have hT:= mul_le_mul_of_nonneg_right hδ (show 0≤ y⁻¹^d from by positivity)
   have hB:= pow_le_pow_left₀ (show 0≤ y⁻¹ by positivity) (inv_anti₀ hr hx) d
   change y⁻¹^ _ *c ≤ x⁻¹^_ - y⁻¹^_
   have ho:=hT.trans (mul_le_mul_of_nonneg_left hB (inv_pos.mpr hr).le)
   rw [le_sub_iff_add_le]; exact Eq.trans_le (show y⁻¹^(d+2)*c+y⁻¹^(d+1)=(y⁻¹+y⁻¹^2*c)*y⁻¹^d from by ring) (ho.trans_eq (by ring))

abbrev hollow (N p i d:ℕ):= actual S v N p i-ranger S v N p i d
abbrev preRoll (N p i d:ℕ)(hi:i<N):= roller S v N p i hi (ranger S v N p (i+1) d)
abbrev preSpend (N p i d:ℕ):= if H:i<N then coins S v N p i H (ranger S v N p (i+1) d) else 0
local notation "ρ"=> sitecharge S N p
local notation "u*" i:max => ((A.B.a.clock.hatBeta i)^(d+1))⁻¹
lemma cycle (hi:i<N):
    let a:= (A.B.a.clock.hatBeta i^d)⁻¹; let b:=(A.B.a.clock.hatBeta (i+1)^d)⁻¹
    let q:= preRoll S v N p i d hi
    (etaPack S N p i (hollow S v N p i d)).Valid (A.B.a.budget i) (a*(δE) i) (a*(δK) i)∧
    (etaPack S N p i (actual S v N p i - q)).Valid (A.B.a.budget i) ((c*)*b*(δE) i) ((c*)*b*(δK) i)∧
    (etaPack S N p i (V i - q)).Valid (A.B.a.budget i) ((1+(c*))*a*(δE) i) ((1+(c*))*a*(δK) i)∧
    |ß i- (ß (i+1)+A.B.kin.alpha N i+preSpend S v N p i d)| ≤ b:=by
   intro a b q; have hz:= fall_g
   have ht : ℒ i=roller S v N p i hi (ℒ (i+1)):= (summitBill S v hi).1; obtain ⟨h₁,h₂,h₃⟩:=shore S v hi (x* (i+1)) (V (i+1)) ((pricelist S v hi).trans_lt hz.2.2) ((slap S v (p:=p) (d:=d) hi|>.1).trans_lt hz.2.2); obtain ⟨h,hq⟩:= slap S v (p:=p) (d:=d) hi; have hx:= (slap S v (p:=p) (d:=d) hi.le).2
   have hL:sitecharge S N p i (actual S v N p i - q) ≤ (c*)*b:= by rw [ht]; exact h₂.trans (mul_le_mul_of_nonneg_left hq hz.1.le)
   refine ⟨(price_charge ..).1 hx, (price_charge ..).1 hL, (price_charge ..).1 ((duelcharge S _ _ (ℒ i)).trans ?_),?_⟩
   · have he : b≤a:= inv_anti₀ (pow_pos (zero_lt_one.trans ((A.B.a).fits.delayed _)) _) (pow_le_pow_left₀ (zero_le_one.trans ((A.B.a).fits.delayed i).le) (climbs (hG:=hG) A.B.a (Nat.le_succ _)) _)
     have hg(x y:vertex S N p i): sitecharge S N p i (x-y)=sitecharge S N p i (y-x):=by unfold sitecharge; simp_rw [map_sub]; exact norm_sub_rev ..
     rw [hg (V i) (x* i), add_mul,one_mul]; exact add_le_add hx (hL.trans (mul_le_mul_of_nonneg_left he hz.1.le))
   unfold preSpend; rw [dif_pos hi,(summitBill S v hi).2,add_sub_add_left_eq_sub]; exact h₃.trans ((mul_le_of_le_one_left (norm_nonneg _) (show Yard.rake (B (i+1)) ≤1 from Real.rpow_le_one_of_one_le_of_nonpos ((A.B.a).fits.delayed (i+1)).le (by norm_num))).trans hq)
-- full reconstruction including chosen path and density, NOT dropping old flags/labels
lemma screen_page (hi:i≤N) (d:ℕ): (etaPack S N p i (hollow S v N p i d)).Valid (A.B.a.budget i) (((A.B.a.clock.hatBeta i)^d)⁻¹*(δE) i) (((A.B.a.clock.hatBeta i)^d)⁻¹*(δK) i)∧
     Dales.mount R N i p (hollow S v N p i d + ranger S v N p i d).val (money S v N p i) (scalarBook S v N p i) = (Loan.H S v).rep N p i :=by
   refine ⟨(price_charge ..).1 (slap (d:=d) S v hi|>.2),?_⟩; unfold hollow; rw [sub_add_cancel]; rfl
-- forward finite beta ledger beginning coarse i and read as far as e. use sum over finrange
variable (hi: i ≤ N)
abbrev coinLine (d N p i:ℕ):= A.B.kin.alpha N i + preSpend S v N p i d
lemma spending (hi:i<N) : |ß i - ß (i+1) - coinLine S v (d+2) N p i| ≤ ((A.B.a.clock.hatBeta (i+1))^(d+2))⁻¹:=by
   rw [sub_sub,← add_assoc]; exact (cycle S v hi (p:=p) (d:=d+2)).2.2.2 -- ABS multiplication
lemma statement (hN:i+e ≤ N) : |ß (i+e) - (ß i - ∑ l∈Finset.range e, coinLine S v (d+2) N p (i+l))| ≤ (tom G)⁻¹ * (((A.B.a.clock.hatBeta i)^(d+1))⁻¹ - ((A.B.a.clock.hatBeta (i+e))^(d+1))⁻¹):=by
   induction e with
   | zero=> simp
   | succ e ih=>
      let l:= i+e; have hi:l<N:= hN; set t:= (tom G)⁻¹; have h:= refund (hG:=hG) A.B.a l d; set m:= ∑ j∈Finset.range e,coinLine S v (d+2) N p (i+j); let w:=coinLine S v (d+2) N p l
      have ht: ß (l+1) - (ß i-(m+w))= ß l-(ß i-m)-(ß l - ß (l+1) - w):= by ring
      rw [Finset.sum_range_succ]; change |ß (l+1)-(ß i-(m+w))|≤ _; rw [ht]; apply (abs_sub _ _).trans; exact (add_le_add (ih (Nat.le_of_succ_le hN)) ((spending S v (p:=p) hi).trans h)).trans_eq (by change t*(u* i - u* l)+t*(u* l - u* (l+1))=t*(u* i-u* (l+1)); ring)
end YM.RG20.Loan
