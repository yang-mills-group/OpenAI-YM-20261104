import YM.SignedWilsonExpansion.F9.Trek
/-!
# K intake formal votes and their steep rank decomposition

Full unit price. No Wick drop. Reconstruct oriented seat clock projection there. At cap
zero ensure symbol includes the true WCU unit (lane will need concrete `Auth` and
 rank from Pare). Root widths in actual K thermal ledger unresolved here.
-/
set_option autoImplicit false
set_option maxHeartbeats 780000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r p u n :ℕ}
variable {B Q D Z X Y η t a ρ d:ℝ}{E W U V:Credit}
variable {P:Era G ℝ}{R:Realm G (e+1) E}
local notation "Fz"=> PowerSeries.X
section
variable (F:Frame G h)(f:BankP F p)
def stamps (i:F.Index): Cost:= ∑ j:Fin (p+1), f (i,j) • (PowerSeries.X^j.val)
lemma stampsFee (t:ℕ)(w:t≤p)(i:F.Index): coeff t (stamps F f i)= f (i,⟨t,by omega⟩):=by
    unfold stamps; rw [map_sum,Finset.sum_eq_single (⟨t,by omega⟩:Fin (p+1))]; · rw [map_smul,coeff_X_pow]; simp
    intro i h v; rw [map_smul, coeff_X_pow,if_neg (fun h=>v (Fin.ext ?_)),smul_zero]; exact h.symm
    simp
lemma rack_as (P:SourceP F): rack F P f=∑ i,trim (stamps F f i) (P i):=by
   unfold rack stamps; rw [Fintype.sum_prod_type]; simp_rw [trim_lot,trim_lib]; rfl
end
/- Deck on PURCHASED schedule. Notation:
  m front,a₀; b f; v K; c inversion top; N actual cutoff or inversion top (`=c`).
 Calendars priced there.
-/
structure MergeTrip {F:Frames G}(A':Council F)(T:TowerP F)(A:Levels G)(Ñ:ChartRatio G)(m b v c N h e k u:ℕ)(Z:ℝ): Prop where
    cohort: Stair A' T A Ñ m c N h e k u Z
    berth : m≤b
    walk : b≤ v
    west : v≤ c
variable {F:Frames G}{A':Council F}{T':TowerP F}
namespace MergeTrip
local notation "Fι"=> (F.level h)
variable (H:Hol G) (q:MergeTrip A' T' A Ñ m b v c N h e k u Z)
noncomputable abbrev tieU : Palette (F.level h) (q.cohort.ladder v) k u e ((Stair.lightFee H F A' h k u e).buy Z):= q.cohort.budget H (q.berth.trans q.walk) q.west
include q in
lemma reserve : Chartage (A' h) A Ñ b v N k u e ((Stair.lightFee H F A' h k u e).buy Z):=by
    let T:= q.cohort.charm h le_rfl; exact climbs (T.clip q.berth q.walk q.west) ((le_of_eq (Credit.lean_cost Z).symm).trans (Credit.thickened _ T.pos))
def lightP (P:Era G ℝ): BankP (F.level h) e:= solve (q.tieU H) (q.reserve H) P 0
def extractR (P:Era G ℝ):= rack Fι (q.cohort.ladder v) (q.lightP H P)
def openX (P:Era G ℝ):= -(q.extractR H P) -- deployed counterpart palette at K, the rest Y+extracted
include q
protected lemma validated (P:Era G ℝ): Auth k (q.openX H P):=by unfold openX; rw [←zero_sub]; exact (silent G k).sub ((q.tieU H).mix _)
omit q in
def shelterC (H:Hol G)(F:Frames G)(A':Council F)(h k u e:ℕ):Credit:= (Enough (F.level h) e u k).usingC (Stair.lightFee H F A' h k u e)
lemma capBill (P:Era G ℝ)(f:Respect k e u 1 P B):
    let U:=(shelterC H F A' h k u e).buy Z;
    (∀ i, ‖q.lightP H P i‖ ≤U*B) ∧∀ i,b≤ i → i≤v → Respect k e u 1 (pier A Ñ N h k v i (P-q.openX H P)) (U*B):=by
    intro U; have hv:U= (Enough Fι e u k).buy ((Stair.lightFee H F A' h k u e).buy Z):= Credit.stock_up ..; rw [hv]; obtain ⟨H0,H1⟩:=solve_bounds (q.tieU H) (q.reserve H) 0 f.auth f.nn f.anchor (fun i=>by rw [Pi.zero_apply,norm_zero]; exact f.nn); refine ⟨H0,fun i h' v'=>⟨piered (q.reserve H).simple (q.reserve H).ratios v' (q.reserve H).cap (f.auth.sub (q.validated H _)),?_⟩⟩; rw [openX,sub_neg_eq_add]; exact fun e p r _=>H1 i h' v' e p r
-- coefficients AFTER!
def pen (P:Era G ℝ)(ρ:ℝ)(i:(F.level h).Index): Cost:= -(sizeT A ρ v ^ wt Fι i) • stamps Fι (q.lightP H P) i
lemma pen_paid (f:Respect k e u 1 P B)(i:(F.level h).Index)(hρ:0<ρ):
     FitS e (q.pen H P ρ i) ((shelterC H F A' h k u e).buy Z*(B*(sizeT A ρ v)^(wt Fι i))):=by
    let U:=shelterC H F A' h k u e; intro a t; unfold pen; rw [map_smul,norm_smul,stampsFee Fι _ a t,norm_neg, Real.norm_of_nonneg (pow_nonneg (sizeT_pos A hρ v).le _)]; refine le_trans (mul_le_mul_of_nonneg_left ((q.capBill H P f).1 _) (pow_nonneg (sizeT_pos A hρ v).le _)) (le_of_eq (by ring))
lemma opening (P:Era G ℝ)(hρ:0<ρ): q.openX H P= ∑ i: (F.level h).Index, trim (q.pen H P ρ i) (q.cohort.tab ρ v i):=by
    unfold openX extractR; rw [rack_as, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; unfold pen Stair.tab; rw [trim_lib,trim_μ,smul_smul,neg_mul, mul_inv_cancel₀ (pow_ne_zero _ (sizeT_pos _ hρ _).ne'), neg_smul,one_smul]
/- unencoding excess prices small -/
lemma missing (f:Respect k e u 1 P B)(z:b≤ i)(w:i≤v):
    Respect k e u 1 (cruises A Ñ N k v i (P-q.openX H P)) ((shelterC H F A' h k u e).buy Z*(paceT A.S i v^h*B)):=by
    let p:= q.capBill H P f; let Fv:= cruises A Ñ N k v i (P-q.openX H P); let K:=paceT A.S i v; let V:=(shelterC H F A' h k u e).buy Z; have hk:0<K:=pace_pos ..; have hx:linkL A i v= K⁻¹:=by unfold K paceT; rw [inv_div]
    have hr : Fv= K^h • pier A Ñ N h k v i (P-q.openX H P):=by unfold pier; rw [smul_smul,hx, inv_pow,mul_inv_cancel₀ (pow_ne_zero _ hk.ne'),one_smul]
    change Respect k e u 1 Fv _; rw [hr]; exact (((p.2 i z w).series (K^h)).rise (le_of_eq (by rw [abs_of_nonneg (pow_nonneg hk.le _)]; ring)))
end MergeTrip
end YM.WilsonCoeffUV.Mer.Xa
