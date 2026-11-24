import YM.SignedWilsonExpansion.F9.Meringue
import YM.WilsonCoeffUV.Root.Step.Covariance
/-!
# Actual run probe on every horizon. Keep HOLES orientation with Signed & Buds.
Relevant at K in Phase estimator prices; `flash` cert on every n, so
 honor turns with links not skipping any order & equation projection.
-/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M i j l r d u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace Looms
variable {F' : Frame G d} (T:SectionData F') (p: Bid.pop T) (hq:T.Sound H)
abbrev literal (T:SectionData F')(i:F'.Index) := Probe T (d+1) d.lt_succ_self i
include p hq
lemma strength {x:F'.Index} (h:d≤k) : Auth k (literal T x):=(probed H T (d+1) _ x hq p).tall ((value_le F' x).trans h) -- def
lemma mantel (i:F'.Index)(n:Side) : PowerSeries.X^(wr F' i) * flash ((literal T i).1 n)=jet (Plies T i n):=by
    have he:= herald_lit T d.lt_succ_self (Xa.seat F' i) n (brow _ (Xa.seat F' i) (d+1)) p H hq; rw [packBloom,if_pos rfl,one_smul] at he; exact he
lemma unity : literal T 0=Wheel.Mark.pieceO G:=by
    apply flash_recover ((strength T p hq (k:=d) le_rfl)) ((Wheel.Mark.piece_auth (j:=0)).tall (Nat.zero_le d)); intro n
    have hx:= mantel T p hq 0 n; rw [wr_unitH,pow_zero,one_mul] at hx; rw [hx,show Plies T 0 n=fun _=>1 from funext (fun Y=>by unfold Plies SectionData.places; rw [show Pi.single _ _=F'.e0 from rfl, hq.unit,Pi.one_apply,Complex.one_re]),jet_const]; change _= flash (uband 1); rw [uband_flash,map_one,map_one]
-- Real columns (Probe through any d) keep SAME `hol`s, no Gauge Quotient assume
lemma literal_roll (s:Signed) : MotionP F' s (literal T):=by
    intro i n X I x A B E
    let f(j:F'.Index):= bleached F' s.ortho j i; let J:= wr F' i; let U:= literal T; let V:= Finset.univ.filter fun j:F'.Index=> wr F' j=J
    have hv j (H':wr F' j≠ J) : f j=0:= bleach_sparse _ _ _ _ (fun t=> H' ((congr_arg Prod.snd t).symm))
    let Y j:= Plies T j n ∘ A; let S:=Plies T i n ∘ B
    have he(j): Green (Y j):=ContDiffAt.comp (g:=Plies T j n) _ (E.f₀.symm ▸ (innu T H hq j n)) E.g₀
    have hb : S=ᶠ[𝓝 0] ∑ j, f j • Y j:=by
       filter_upwards [E.shift] with z hz
       change (T.places _ 0 (mantle (B z))).re=_; rw [hz,T.placed_invariant hq _ _, T.placed_signed hq s, show affine s (0:Site n) 0=0 from by simp [affine], shadePlies,Finset.sum_apply]; rfl
    have he':=jet_congr hb; rw [jet_sum _ _ (fun j _=> show Green (f j • Y j) from ContDiffAt.const_smul (f j) (he j))] at he'; have ht j: jet (f j • Y j)=f j • jet (Y j):=by rw [show f j • _=(fun _:Lawn X=> f j)* Y j from rfl,jet_mul _ (he j),jet_const,← real_alg,Algebra.smul_def]; exact contDiffAt_const
    simp_rw [ht] at he'; have hu j : Auth d (U j):= strength T p hq le_rfl
    have hei j (G': Lawn X→ Lawn (Woods G n)) (hA:Green G')(hx:G' 0=0): PowerSeries.X^wr F' j*train (spool G') (flash ((U j).1 n)) = jet (Plies T j n ∘ G'):=by
       conv_lhs => arg 1; rw [←train_X (spool G'),← map_pow]
       rw [←map_mul,mantel T p hq j n,traveling G' hA hx _ (innu T H hq _ _)]
    apply mul_left_cancel₀ (a:=PowerSeries.X^J) (pow_ne_zero _ X_ne_zero); simp only [Prod.fst_sum,Prod.smul_fst,Pi.smul_apply,Finset.sum_apply]; rw [flash_term _ (fun j _=> (show shellK d (f j • (U j).1 n) from ((hu j).μ _).span _)),map_sum, Finset.mul_sum,hei i B E.g₁ E.f₁,he']; refine Finset.sum_congr rfl fun j _=> ?_; rw [flash_mu _ ((hu j).span n),train_smul,mul_smul_comm]; by_cases h: wr F' j=J; · rw [← h,hei j A E.g₀ E.f₀]
    change f j • _= f j • _; rw [hv j h,zero_smul,zero_smul]
end Looms
end YM.WilsonCoeffUV.Mer.Xa
