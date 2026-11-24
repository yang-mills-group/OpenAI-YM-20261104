import YM.SignedWilsonExpansion.F9.Tax
/-! # Tax equivariance -/
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
section general
variable {Y:TowerP F}{Ω:Council F} (t':MergeTrip Ω Y A Ñ m b v c c h e k u X) (H:Hol G)
lemma MergeTrip.sum_bill (S:Finset J)(a:J→Era G ℝ)(t:J→ℝ)(ha:∀ i∈S,Auth k (a i)) : t'.lightP H (∑ i∈S,t i • a i)=∑ i∈S, t i • t'.lightP H (a i):=by
    let U:=t'.reserve H
    have hf: output Rι e (∑ i∈S,t i • pier A Ñ c h k v b (a i))= ∑ i∈ S,t i • output Rι e (pier A Ñ c h k v b (a i)):=by
        funext i; rw [Finset.sum_apply]; exact row_summed _ _ (fun i h=>piered U.simple U.ratios U.length U.cap (ha i h)) (e:=i.2.val) (⟨i.1,rfl⟩:TagIx _ (wr Rι i.1)) t
    unfold lightP solve; simp only [zero_sub,heard]; rw [pier_sum U.simple U.ratios U.length U.cap _ t a ha, hf]; simp only [Finset.sum_neg_distrib, map_sum, smul_neg, map_neg,map_smul]
end general
namespace MergeTrip
open Looms
variable {Ω:Council F}{Kt:∀h,Survey G H h}{P':Hol G}
variable (Q':MergeTrip Ω (launch F H Kt K k) R.draws R.paid m b v c c h e k u X)
variable (T:SectionData (F.level d)) (Pp:Bid.pop T)(ht:T.Sound P')(w:h≥d)(s:Signed) (α:(F.level d).Index) (β:(F.level h).Index)
include Pp ht w
def pager (ρ:ℝ)(l:ℕ):= Q'.tax T (ρ:=ρ) (l:=l) α β -- exists for no th? include Pp ht not inserted defs
lemma light_spin (k':Fin (e+1)): ∑ i:(F.level d).Index, bleached (F.level d) s.ortho i α * Q'.lightP H (literal T i) (β,k')= ∑ j:(F.level h).Index, bleached Rι s.ortho β j * Q'.lightP H (literal T α) (j,k'):=by
   let f:=literal T; let L:= Q'.tieU H; let V:= Q'.reserve H; let b:=fun i:(F.level d).Index=>bleached (F.level d) s.ortho i α; have hp(i): Auth k (f i):= strength T Pp ht (w.trans V.order); have hh:MotionP Rι s (Q'.cohort.ladder v):=Q'.cohort.rotated (fun d x=>manifest H F Kt K s (x.trans V.order)) H (Q'.berth.trans Q'.walk) Q'.west; have hv:= literal_roll T Pp ht s α
   have he:= solve_roll H L V hh hv (hp α) (Auth.sum (P:=fun i=>b i • f i) (fun i _=> (hp i).μ (b i))) 0
   rw [map_zero] at he; change Q'.lightP H (∑ i,b i • f i)= _ at he; rw [Q'.sum_bill H _ _ b (fun i _=> hp i)] at he; have hc:= congr_fun he (β,k'); rw [Finset.sum_apply] at hc; exact hc
lemma spin_tax : ∑ i:(F.level d).Index, bleached (F.level d) s.ortho i α • Q'.tax T (ρ:=ρ) (l:=l) i β= ∑ j:(F.level h).Index,bleached Rι s.ortho β j • Q'.tax T (ρ:=ρ) (l:=l) α j:=by
   let L:=(F.level d); let V:=(F.level h); let d:= bleached L s.ortho; let c:= bleached V s.ortho; let K:=sizeT R.draws ρ v; let xT(i):=Q'.lightP H (literal T i); let E(i:V.Index):= -(K^wt V i)
   -- avoid shadow T
   have he(j:V.Index) : c β j • ( E j • stamps V (xT α) j)= E β • ( c β j • stamps V (xT α) j):=by
       rw [smul_comm]; by_cases h: wt V β= wt V j; · unfold E; rw [h]
       rw [show c β j=0 from bleach_sparse V _ _ _ (fun t=> h ((congr_arg Prod.fst t).symm)), zero_smul]; simp
   unfold tax cFees pen; simp_rw [← toward_multi]; rw [← map_sum,← map_sum]; apply congr_arg; change (∑ i:L.Index,d i α • (E β • stamps V (xT i) β))=∑ j:V.Index,c β j • (E j • stamps V (xT α) j); simp_rw [he, smul_comm (d _ α) (E β),← Finset.smul_sum]; apply congr_arg; unfold stamps; simp_rw [ Finset.smul_sum,smul_smul]; rw [Finset.sum_comm ]
   conv_rhs=> rw [Finset.sum_comm]
   simp_rw [← Finset.sum_smul]; refine Finset.sum_congr rfl (fun i _=> congr_arg (fun x:ℝ=> x • _) (light_spin Q' _ Pp ht w s α β i))
end MergeTrip
end YM.WilsonCoeffUV.Mer.Xa
