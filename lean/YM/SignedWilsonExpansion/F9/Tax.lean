import YM.SignedWilsonExpansion.F9.Proto
/-! # Point arm fees in path letter. K probe from REAL section then linear on color sums. -/
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
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
lemma toward_multi (x:ℝ)(Q:Cost): toward A Ñ N l v (x • Q)= x • toward A Ñ N l v Q:=by rw [Algebra.smul_def,Algebra.smul_def,map_mul,show toward _ _ _ _ _ (algebraMap ℝ Cost x)=_ from reel_C ..]; rfl
namespace MergeTrip
open Looms
variable {Ω:Council F}{W':TowerP F}{K':∀ h,Survey G H h}{Pk:∀h,Rays G h H}{F':Frame G d}
local notation "Lι"=> (F.level d)
-- use actual physical SectionData F', not K'.
variable (Q':MergeTrip Ω (launch F H K' Pk k) R.draws R.paid m b v c c h e k u X) (T:SectionData (F.level d))(ht:T.Sound H)(Pp:Bid.pop T) (hx:d≤h) -- Sound of hol P.Bold; need allow physical holistic ≠ H
abbrev tax (α:(F.level d).Index) (β:(F.level h).Index) : Cost:= Q'.cFees H ρ l (literal T α) β
-- split: Sound Hx' separately from launch H, Roll only needs H for latter.
variable {P':Hol G}(ht':T.Sound P')
include ht' Pp
-- bidegree torsion, no derivative on ports
theorem rankExact (α:(F.level d).Index) (β:(F.level h).Index) (w:h≥d) (hp:wr (F.level d) α<wr (F.level h) β): coeff 0 (tax (l:=l) (ρ:=ρ) Q' T α β)=0:=by
    let Z:=SolveCorner.proto (Q'.tieU H) (Q'.reserve H); let P:=literal T α; let τ:=Z P; let J:=wr (F.level d) α; have hm:Auth k P:= strength T Pp ht' (w.trans (Q'.reserve H).order)
    have hw:= probed P' T (d+1) d.lt_succ_self α ht' Pp; have hb:(τ (β,0))=0:= (SolveCorner.aim (Q'.tieU H) (Q'.reserve H) hm hp (by intro r hr; exact hw.coverN 0 _ (by change wr (F.level d) α+0<r; omega))).2 (⟨β,rfl⟩:TagIx (F.level h) (wr (F.level h) β))
    unfold tax cFees toward pen; rw [reelQuote]; simp only [zero_add, Finset.range_one,Finset.sum_singleton,Nat.sub_self,pow_zero,coeff_one, if_true, mul_one,map_smul,stampsFee (F.level h) _ 0 (Nat.zero_le e)]; exact (congr_arg (fun x:ℝ => -(sizeT R.draws ρ v ^ wt Rι β) • x) hb).trans (smul_zero ..)
-- For NO weight > processed lane costs. diagonal through ITS weight at rank wr.
theorem massExact (α:TagIx (F.level d) r)(β:TagIx (F.level h) r)(w:h≥d)(hi:wT (F.level h) β≤wT (F.level d) α):
    coeff 0 (tax (l:=l) (ρ:=ρ) Q' T α β)= if upT F w α=β then sizeT R.draws ρ v ^ wT (F.level h) β else 0:=by
    let Z:=SolveCorner.proto (Q'.tieU H) (Q'.reserve H); let P:=literal T α; let τ:=Z P; let x:= upT F w α; have hm:Auth k P:= strength T Pp ht' (w.trans (Q'.reserve H).order); have hw:Auth r P:= marks T ht' Pp α; have hz:= up_w F w α
    have hp(j:TagIx (F.level h) r)(hj:wT (F.level h) j≤ wT (F.level h) x): row (F.level h) (P.2 0 r) j=if x=j then 1 else 0:=by
       have hj':wT (F.level h) j≤d:=(hj.trans (hz.trans_le ((F.level d).bound α))); let y:=downT F w j hj'; have hv:upT F w y=j:= up_downT F w j hj'; have hf : row (F.level h) (P.2 0 r) j =row (F.level d) (P.2 0 r) y:=by rw [row_handed H F hm _ w,hv]
       have hg: α=y ↔x=j:=⟨fun h=> (congr_arg (upT F w) h).trans hv,fun h=>upT_faith F w α y (h.trans hv.symm)⟩; rw [hf,direct P' T _ _ ht' Pp]; by_cases h:x=j <;> simp only [hg,h,if_true,if_false]
    have he : τ (β,0)=if x=β then -1 else 0:=SolveCorner.basisLead (Q'.tieU H) (Q'.reserve H) hm (fun i hi=>hw.coverN 0 i (by omega)) x hp _ (hi.trans (hz.symm.le))
    unfold tax cFees pen toward; rw [reelQuote]; simp only [zero_add, Finset.range_one,Finset.sum_singleton,Nat.sub_self,pow_zero,coeff_one, if_true, mul_one,map_smul,stampsFee (F.level h) _ 0 (Nat.zero_le e)]
    change -(sizeT R.draws ρ v ^ wT (F.level h) β) *τ (β,0)=_; rw [he]; by_cases u:x=β; · rw [if_pos u, if_pos u, neg_mul_neg,mul_one]
    rw [if_neg u,if_neg u,mul_zero]
-- unit pricetag on mentor. literal ONE
lemma unity_tax (β:(F.level h).Index): tax (l:=l) (ρ:=ρ) Q' T 0 β = if β=0 then 1 else 0:=by
    let P:= Wheel.Mark.pieceO G; unfold tax; rw [unity T Pp ht']; let F:=F.level h; let Z:= pureF F 0 e; let T:= Q'.reserve H
    have hb : rack F (Q'.cohort.ladder v) Z=P:= by rw [rack_sample _ _ _, stair_unit H Pk K' Q'.cohort Q'.west]
    have hz := (neg_one_smul ℝ Z).symm; have hc: Q'.lightP H P= -Z:=by
        have hu:Auth k P:= Wheel.Mark.piece_auth; apply Eq.symm; apply solve_unique (Q'.tieU H) (Q'.reserve H) hu; rw [hz,rack_μ,hb, neg_one_smul,add_neg_cancel]; unfold heard; rw [pier_nil T.simple T.ratios T.length T.cap,output_nil]
    have hm(j:Fin (e+1)) (u:j≠0): (-Z) (β,j)=0:=by unfold Z pureF; simp [u]
    unfold cFees pen; rw [hc,stamps,Finset.sum_eq_single (0:Fin (e+1))]; swap; · intro i _ hi; rw [hm i hi, zero_smul]
    swap; · simp
    by_cases u:β=0; · subst β; rw [wt_zeroH,if_pos rfl]; simp [Z,pureF]
    rw [show (-Z) (β,0)=0 from (by unfold Z pureF; simp [u]),if_neg u,zero_smul,smul_zero,map_zero]
end MergeTrip
end YM.WilsonCoeffUV.Mer.Xa
