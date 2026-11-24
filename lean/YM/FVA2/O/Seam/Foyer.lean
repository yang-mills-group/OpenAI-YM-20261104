import YM.FVA2.O.Seam.Fare
/-!
# Bundling the candidate OPE expansion also after spectator insertion

Weighted sum of physical fields. `FrameZ` for extending to the associated families;
use the `Valid` pricing of the coefficients and `Chaff` estimates before
passing the seam. See `O/Seam/Finish`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse
open scoped Topology ContDiff Interval
variable { I W : Type } { G:Gauge }{B:Deck G}
variable {P:Geo I}{K:Booked B}{M:MS_Data G K}{ X Y F: T ( Glade G I )}{p:I→ℝ}{n k d:ℕ}
local notation "S"=> deckB P
lemma timeFee (h:Profit (Station P).dawn p): paid (deckB P).toScale ( fun i=> ‖( p i.fst :ℂ )‖ ) 1:= by
    obtain ⟨C,hC,k,h⟩:=h; refine ⟨C,hC,k,fun i=>?_⟩; dsimp only; rw [ Complex.norm_real ]; apply ( h i.1 ).trans; rw [Pi.one_apply,Pi.one_apply,mul_one,mul_one ]; gcongr; exact (( Station P ).dawn.basic_pos i.1).le; change habitat P _*(1+0) ≤ habitat P _*(1+|Belt.tstart i|); have hp : 0 <habitat P i.fst:= (by unfold habitat; positivity); exact mul_le_mul_of_nonneg_left (by simp) hp.le
lemma Chaff.seated (hp: Profit ( Station P ).dawn p)(hx: Chaff ( deckB P ) P X): Chaff (deckB P) P ( Hue.seat p X ):= fun i q=> FormP.money _ (timeFee hp) ( hx i q )
lemma Chaff.project (h:Chaff S P X): Chaff S P ( hold0 n X ):= by intro k; by_cases hv:n≤ k; rw [hx_holder hv]; exact h _; rw [low_hold (by omega)]; exact ThinAt
variable {p':T ( I→ℝ )}
lemma Chaff.fromH (h:Chaff S P X)(he:∀ n,Profit (Station P).dawn (p' n)): Chaff S P ( entrance p' X ):= by intro i; exact Tiny.sum ( Finset.range (i+1) ) (fun j _=> Chaff.project ( Chaff.seated ( he j ) h ) i )
lemma joinCash : joint G I (X k) (Hue.seat p F n)= Hue.seat p (fun _=> joint G I ( X k ) ( F n )) n := by
    funext i t; exact map_smul ( ( product (field parity) ) ( X k i t ) ) _ _
lemma bondCash (p:I→ℝ): bond G I X ( Hue.seat p Y ) = Hue.seat p (bond G I X Y):= by funext k; rw [bond,paired]; simp_rw [joinCash]; unfold Hue.seat Lives.pay; rw [paired]; funext i; simp_rw [ Finset.sum_apply, Finset.smul_sum ]
lemma priceBranches (p:T (I→ℝ)) : bond G I X (entrance p F)= entrance p (bond G I X F):= by
    let H:=bond G I X; have ht(n:ℕ): H (hall p F n)=hall p ( H F ) n:= by unfold H hall bond; simp_rw [map_sum,split_h (joint G I), show ∀ i, pairW ( joint G I ) X (Hue.seat ( p i ) F)=_ from fun i=> bondCash ( X:=X ) ( Y:=F ) (p i)] -- typo
    funext i; calc
       _ = H ( hall p F i ) i:= (pairΛ (joint G I) X (fun _ h=> hereΛ h) i (le_refl i)).symm
       _ = _ := by rw [ ht i ]; exact hereΛ (le_refl i)
lemma marked_diff (p:T ( I→ℝ )): entrance p (F-Y)= entrance p F-entrance p Y:= by
    funext i; unfold entrance; rw [Pi.sub_apply, ← Finset.sum_sub_distrib ]; apply Finset.sum_congr rfl; intro j hj; obtain he : j ≤ i:=by simp only [ Finset.mem_range ] at hj; omega
    rw [ hx_holder he,hx_holder he,hx_holder he ]; funext i; unfold Hue.seat Lives.pay; simp only [ Pi.sub_apply,smul_sub ]
abbrev actor (x:Counter B k): Label B:= ⟨ x.1.val,x.2 ⟩
abbrev FrameZ (p:Details B I k)( F: Counter B k→ T ( Glade G I ) ):= ∑ i:Counter B k, entrance ( p i ) ( F i )
variable {Ω:Counter B k→ T ( Glade G I )}{p:Details B I k}
lemma Frame_r (h:∀ i,Certified ( Ω i ) M P.η 0) : Certified ( FrameZ p Ω ) M P.η 0:= C_ο _ (fun i _=> entrance_C _ ( h i ))
variable [LinearOrder W]{x:Position W I}{R: W→ Label B}{s:Finset W}
lemma Frame_join : rootT P M x R s ( Physical P.η M p )= FrameZ p (fun i=> rootT P M x R s (rowM P M ( actor i ))):= by unfold Physical FrameZ; rw [map_sum]; exact Finset.sum_congr rfl fun i hi=> priceBranches _
lemma Frame_v (hp:Mesh P x)(ht:∀ i,CoverSep P ( x i ))(he:∀ i,Response ( Ω i ) M P.η 0)(hx: ∀ i n,PastPoint ( ( Ω i - rootT P M x R s (rowM P M ( actor i )) ) n ))(hr: Valid ( Station P ) p) : Chaff S P ( FrameZ p Ω-rootT P M x R s ( Physical P.η M p ) ):= by
    rw [Frame_join]; unfold FrameZ; rw [ ← Finset.sum_sub_distrib ]; apply Chaff.sums; intro i hi; rw [ ← marked_diff ]; exact Chaff.fromH ( single_gap hp ht ( he i ) ( hx i ) ) (hr i)
end YM.FVA2.O.Seam
