import YM.SignedWilsonExpansion.F9.Hunker
/-! # Same-rank tie law at launch.H weight of actual physical horizon d -/
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
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MarqueQ
namespace PorchK
open SignedWilsonExpansion.Commission Method Method.Epic Asymptotics Stair MergeTrip Looms
open Normalize (Sec)
open XSpace.Cirrus
variable {W':Initialize G}{Q':∀ h,Rays G h W'.hol}{Ω:Council F}
variable {P':Hol G}{ι:Type}
variable (x:PorchK W' F Q' Ω R h k u)(q:ι→PorchK W' F Q' Ω R h k u)(Wn:Normalize.Store G)
variable {Y B:ι→ℝ}{L:Filter ι}(hQ:Annual q L Y)(hs:Expense.Stretched L (fun i=>(q i).mesh))(Pp:∀ i≤e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' Wn i))
variable (S:SectionData (F.level d))(hS:S.Sound P')(p0:Bid.pop S)(v₀:d≤h)
variable (α:(F.level d).Index)(β i:(F.level h).Index)
-- observe bidegree (from same floor) response using ζ.Insert (formerly called palette.P)
include p0 hS v₀
lemma tap_solo (u':wr Rι β=wr (F.level d) α) (he:wt Rι β≤wt (F.level d) α) : coeff 0 (x.tap S α β) = if upL F v₀ α=β then (x.markW:ℂ)^wt Rι β else 0:=by
    let M:= wr (F.level d) α; let X: TagIx (F.level d) M:= ⟨α,rfl⟩; let V:TagIx Rι M:=⟨β,u'⟩; unfold tap; rw [x.canv.push_first W' S α β, x.canv.massExact S p0 hS (α:=X) (β:=V) v₀ he]; by_cases H: upL F v₀ α=β
    · rw [if_pos H, if_pos (show upT F v₀ X=V from Subtype.ext H)]; push_cast; rfl
    rw [if_neg H,if_neg (show upT F v₀ X≠ V from fun h=> H (Subtype.ext_iff.mp h)),Complex.ofReal_zero]
private lemma smaller (hp:wr (F.level d) α< wr Rι β): coeff 0 (x.tap S α β)=0:=by unfold tap; rw [x.canv.push_first W' S α β, x.canv.rankExact S p0 hS α β v₀ hp,Complex.ofReal_zero]
include hQ hs Pp hS p0 v₀
lemma lamp_equal (ha:wt (F.level d) α=d) (hd:wt Rι i=d)(hi:wr (F.level d) α=wr Rι i) : Wage L Y (remitW q (d+1)) (fun j=> sonar Rι i ((q j).sober Wn S α 0)- ((q j).markW:ℂ)^d * sonar Rι i (vista F (upL F v₀ α))):=by
    set z:= upL F v₀ α; let P(x:ι):= ((q x).markW:ℂ)^d * sonar Rι i (vista F z); let Tk(j:ι)(k:(F.level h).Index) := if z=k then P j else 0; let L'(j:ι)(k:(F.level h).Index):= (q j).listen0 Wn S α i k
    have hu(j:ι): P j=∑ k,Tk j k:=by simp [Tk]
    have ht:wt Rι z=d:= (congr_arg Prod.fst (up_grade F v₀ α)).trans ha; have hr:wr Rι z=wr Rι i:= (congr_arg Prod.snd (up_grade F v₀ α)).trans hi
    unfold sober shapeD; simp only [map_sum,Finset.sum_apply]; change Wage L Y _ fun j=> (∑ k:(F.level h).Index,L' j k)-P j; simp_rw [hu, ← Finset.sum_sub_distrib]; apply Wage.sum hQ.1; intro k hk
    by_cases v: z=k; · unfold Tk; subst k; simp only [if_true]; have he:=ear0_bias q Wn hQ hs Pp S hS p0 v₀ α z i hr.le; simp_rw [tap_solo _ S hS p0 v₀ α z (hr.trans hi.symm) (ht.trans_le ha.symm.le), if_pos (show upL F v₀ α=z from rfl), ht] at he; exact he
    unfold Tk L'; simp only [if_neg v,sub_zero]; rcases lt_trichotomy (wt Rι k) d with v'|v'|u; · simp_rw [blank (β:=k) (u_:=v'.trans_eq hd.symm)]; exact Wage.nil
    · rcases lt_trichotomy (wr Rι k) (wr Rι i) with t|t|x
      · simpa only [mote i _ (vista_rank (F:=F) k t) le_rfl, mul_zero,sub_zero,v'] using ear0_bias q Wn hQ hs Pp S hS p0 v₀ α k i t.le
      · exact Wage.fix Wage.nil (Eventually.of_forall fun j=> by change (0:ℂ)= (q j).listen0 Wn S α i k; rw [ear0, tap_solo _ S hS p0 v₀ α k (t.trans hi.symm) (v'.trans_le ha.symm.le), if_neg v,zero_mul]) (.refl ..)
      simp_rw [ear0,smaller _ S hS p0 v₀ α k (hi.trans_lt x),zero_mul]; exact Wage.nil
    exact hear_large q Wn hQ hs Pp S hS p0 v₀ α k i u
-- approximate all Gram closure uses only these. Keep slots preserving rank, not parity.
end PorchK
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa
