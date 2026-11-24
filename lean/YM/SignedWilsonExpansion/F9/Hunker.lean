import YM.SignedWilsonExpansion.F9.SonarQ
/-! # Ground orthro on exact bidegree observations. No Wick transport on interiors needed. -/
set_option autoImplicit false
set_option maxHeartbeats 160000
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
abbrev shot (i:(F.level h).Index):= x.paid.originalT W' x.mesh x.ρ 0 ((F.level h).basis i)
abbrev listen0 (α:(F.level d).Index)(i:(F.level h).Index)(β:(F.level h).Index): ℂ:= sonar Rι i (x.booth Wn S α β 0)
abbrev remitW (n:ℕ): ι→ℝ:= (fun i=> ((q i).markW)^n)
variable (α:(F.level d).Index)(β i:(F.level h).Index)
theorem ear0 : x.listen0 Wn S α i β = coeff 0 (x.tap S α β) * sonar Rι i ( x.toEpic.tenor W' Wn 0 ((F.level h).basis β)):=by
    rw [listen0,show x.booth Wn S α β 0=coeff 0 (x.tap S α β) • (x.canv.boots W' Wn x.mesh β x.l x.r x.ρ 0) from (?_),map_smul,x.canv.boots_at]; rfl
    simp [PorchK.booth,Tape.starE,Tape.pep]
theorem shot_below (f:wr Rι β ≤ wr Rι i): sonar Rι i (x.shot β)=sonar Rι i (vista F β):= by -- x.shot Wn? yes used W'? Wn not x.shot doesn't require Wn!
    apply sub_eq_zero.mp; rw [←map_sub]; have ht:= x.paid.radical_down W' x.mesh x.ρ x.align β; rw [LinearMap.sub_apply, ← carried] at ht; exact mote i _ ht f
theorem blank (u_:wt Rι β< wt Rι i): x.listen0 Wn S α i β=0:= nearer i ((F.level h).bound β) _ u_ (x.goesPart Wn S α β 0)
include hQ hs Pp hS p0 v₀
lemma ear0_bias (hv:wr Rι β≤wr Rι i): Wage L Y (remitW q (wt Rι β +1)) (fun j=> (q j).listen0 Wn S α i β- coeff 0 ((q j).tap S α β)* sonar Rι i (vista F β)):=by
    simp_rw [ear0,← mul_sub]; let p:= sonar Rι i; apply (Wage.mul (tap_charge q hQ S hS p0 v₀ α β 0 (Nat.zero_le _)) (Y:=(fun i=> (q i).markW)) (?_)).fix (.refl ..) (Eventually.of_forall fun j=> (?_)) -- apply
    · apply Wage.fix (slides_mark q Wn hQ hs Pp β p) ?_ (.refl ..); exact Eventually.of_forall fun j=> by dsimp only; unfold p; rw [map_sub, boots_at, (q j).shot_below β i hv] -- check `shot` defeq
    exact (show ((q j).markW)^_ * (q j).markW=((q j).markW)^(_+1) from (pow_succ ..).symm)
lemma hear_large (p:d< wt Rι β): Wage L Y (remitW q (d+1)) (fun j=> (q j).listen0 Wn S α i β):=by
    apply Wage.clip (booth_paid q Wn hQ S hS p0 v₀ α β Pp (j:=0) (Nat.zero_le _) (sonar Rι i)); exact (IsBigO.of_bound' (Eventually.of_forall fun x=> by let t:=(q x).markW; have ht:0≤t:= (sizeT_pos _ (q x).pos _).le; rw [Real.norm_of_nonneg (pow_nonneg ht _), Real.norm_of_nonneg (pow_nonneg ht _)]; exact pow_le_pow_of_le_one ht (q x).small p))
lemma lamp_small (hd:wt Rι i=d)(hi:wr (F.level d) α<wr Rι i) : Wage L Y (remitW q (d+1)) (fun j=> sonar Rι i ((q j).sober Wn S α 0)):=by
    unfold sober shapeD; simp only [map_sum, Finset.sum_apply]; change Wage L Y _ (fun j=> ∑ β,(q j).listen0 Wn S α i β); apply Wage.sum hQ.1; intro k _; rcases lt_trichotomy (wt Rι k) d with e'|v|t; · simp_rw [blank (β:=k) (u_:=e'.trans_eq hd.symm)]; exact Wage.nil -- choose
    · by_cases u':wr Rι k< wr Rι i
      · have hv:= vista_rank (F:=F) k u'; have p:= ear0_bias q Wn hQ hs Pp S hS p0 v₀ α k i u'.le; simpa only [mote i _ hv le_rfl, v, mul_zero,sub_zero] using p -- rw simplifies mul?
      exact Wage.fix Wage.nil (Eventually.of_forall fun j=> by change (0:ℂ)=(q j).listen0 Wn S α i k; rw [ear0,show coeff 0 ((q j).tap S α k)=_ from (( q j ).canv.push_first W' S α k), (q j).canv.rankExact S p0 hS α k v₀ (by omega),Complex.ofReal_zero,zero_mul ]) (.refl ..)
    exact hear_large q Wn hQ hs Pp S hS p0 v₀ α k i t
-- include height d case exact diag not tilt-free. Need later.
end PorchK
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa
