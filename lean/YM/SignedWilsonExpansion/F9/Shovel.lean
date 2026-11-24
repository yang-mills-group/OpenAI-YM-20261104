import YM.SignedWilsonExpansion.F9.Tenancy
/-! # Tax conversion Hook actual to Sec h for EVERY pair of caps. -/
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
variable {F:Frames G}{H:Hol G}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MergeTrip
open Stair Tape
open Normalize (Sec)
-- all real columns; numerical argument from x.th recommended unnormalized K vectors, so factor δ^−d, ψ-ready etc handled outside.
variable (W':Initialize G){Ki:∀ h,Rays G h W'.hol}{Ω:Council F}
local notation "Rθ"=> (F.level h)
variable (Q':MergeTrip Ω (launch F W'.hol W'.surveys Ki k) R.draws R.paid m b v c c h e k u X)
variable (A':SectionData (F.level d)) (S:Normalize.Store G) (t': Mesh) -- mesh projection not tied except in radical change at ground
-- decomposed. Preserve grades before applying increases from pen. This is ψ coupled to HOOK publisher clocks.
abbrev boots (β:(F.level h).Index)(l r:ℕ)(ρ:ℝ): Tape (Sec G h):= Tape.tempo (starFlight (relativeC R.draws R.paid c l (r-l))) (Q'.cohort.lineTape W' S t' l ρ β)
def pushTax (α:(F.level d).Index)(β:(F.level h).Index)(l r:ℕ)(ρ:ℝ): InkQ:= northQ R.draws R.paid c l r (insertQ (Q'.tax (l:=l) (ρ:=ρ) A' α β))
def shapeD (α:(F.level d).Index)(l r:ℕ)(ρ:ℝ): Tape (Sec G h):= ∑ β:(F.level h).Index,starE (Q'.pushTax W' A' α β l r ρ) (Q'.boots W' S t' β l r ρ)
local notation "Yι" => (F.level d)
lemma shape_alpha (α:(F.level d).Index): Q'.yank W' S l r t' ρ (Looms.literal A' α)=shapeD W' Q' A' S t' α l r ρ:=by
    unfold yank Zed shapeD boots pushTax northQ; rw [map_sum]; exact Finset.sum_congr rfl (fun i _=>by rw [flight_sub, tempo_south (flight_zero _)])
-- leg map on actual K unencoded coefficients normalized in thermal sales
noncomputable def snapD (l r:ℕ)(ρ:ℝ) : (F.level d).Coeff→ₗ[ℂ] Tape (Sec G h) where
    toFun x:= ∑ α:(F.level d).Index,x α • Q'.shapeD W' A' S t' α l r ρ
    map_add' x y:= by simp only [Pi.add_apply, add_smul,Finset.sum_add_distrib]
    map_smul' f x:= by simp only [Pi.smul_apply, Finset.smul_sum, smul_smul]; rfl
variable {x:(F.level d).Coeff}{Hs:Hol G} (hA:A'.Sound Hs)(ha:Bid.pop A') (hp:d≤h) (α:(F.level d).Index) (β:(F.level h).Index)
lemma boots_at : Q'.boots W' S t' β l r ρ 0= Q'.cohort.publish W' t' ρ S l 0 ((F.level h).basis β):=by rw [boots,tempo_first (flight_zero ..), published]
lemma boot_rank (k:ℕ): Q'.boots W' S t' β l r ρ k∈Folia G (wt Rθ β) h:=by
   unfold boots tempo; refine Submodule.sum_mem (Folia G (wt Rθ β) h) (fun j _=>Submodule.smul_mem (Folia G (wt Rθ β) h) _ ?_); unfold lineTape; exact frame_height _ (guardH W' _ _) _ (Q'.cohort.tape_permit W' t' ρ β) ((F.level h).bound _) _ _
lemma layer_tempo (R:InkQ)(L:Module.End ℂ (Sec G h))(p:Tape (Sec G h)): Tape.layer L (tempo R p)= tempo R (Tape.layer L p):= by funext i; simp only [Tape.layer,tempo,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul]
lemma layer_star (R:InkQ)(L: Module.End ℂ (Sec G h))(p:Tape (Sec G h)): Tape.layer L (starE R p)=starE R (Tape.layer L p):=by funext i; simp only [Tape.layer,starE,LinearMap.coe_mk,AddHom.coe_mk,pep,map_sum,map_smul]
lemma port_spin (s:Signed): Tape.layer (Normalize.ori s.ortho h) (Q'.boots W' S t' β l r ρ)=∑ j:(F.level h).Index,(↑(bleached Rι s.ortho j β):ℂ) • Q'.boots W' S t' j l r ρ:=by
   unfold boots; rw [layer_tempo]; simp_rw [lineTape,tempo_spin _ _ (guardH W' (_:Mesh) h),bare_spin]; simp_rw [map_sum,map_smul]
private lemma stars_sum (x: Finset J)(y:J→ InkQ)(u:Tape (Sec G h)): ∑ i∈x,starE (y i) u=starE (∑ i∈ x,y i) u:=by
    induction x using Finset.induction_on with
    | empty=> ext1 i; simp only [Finset.sum_empty,starE,LinearMap.coe_mk,AddHom.coe_mk,pep,map_zero,zero_smul,Finset.sum_const_zero,Pi.zero_apply]
    | insert _ _ v ih=> rw [Finset.sum_insert v,ih,Finset.sum_insert v,stars_left]
private lemma stars_μ (c:ℂ)(R:InkQ)(u:Tape (Sec G h)): starE (c • R) u=c • starE R u:=by funext i; simp only [starE,LinearMap.coe_mk,AddHom.coe_mk,pep,map_smul,Pi.smul_apply,smul_assoc,Finset.smul_sum]
lemma push_first : coeff 0 (Q'.pushTax W' A' α β l r ρ)= ((coeff 0 (Q'.tax (l:=l) (ρ:=ρ) A' α β):ℝ):ℂ):=by unfold pushTax northQ; rw [flyh,inked,reelQuote]; simp
-- build accepted color/orientation Direction. Leg.Re.Seat
lemma bootreal : WReal (Q'.boots W' S t' β l r ρ):= tempoF_real _ (tempoF_real _ (frame_real _ (guardH W' _ _) _ (Q'.cohort.bare_real W' _ _ β)) _ (realZx _)) _ (realZx _)
lemma push_real : realInk (Q'.pushTax W' A' α β l r ρ):= realH _ (realZx _)
lemma shape_real : WReal (Q'.shapeD W' A' S t' α l r ρ):=by
    intro i; unfold shapeD; rw [ Finset.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro j _; unfold starE; simp only [LinearMap.coe_mk,AddHom.coe_mk,pep,map_sum,(Normalize.reel h).map_smulₛₗ]; exact Finset.sum_congr rfl fun t _=> by rw [show ∀ k,starRingEnd ℂ (coeff k _)=_ from (fun k=>realLevel _ (Q'.push_real W' A' α j (l:=l) (r:=r) (ρ:=ρ)) k),bootreal]
include hA ha hp
-- proper group motion
lemma push_spin (s:Signed): ∑ i:(F.level d).Index, (↑(bleached Yι s.ortho i α):ℂ) • Q'.pushTax W' A' i β l r ρ=∑ j:(F.level h).Index,(↑(bleached Rι s.ortho β j):ℂ) • Q'.pushTax W' A' α j l r ρ:=by unfold pushTax; simp_rw [← map_smul, ← Stair.realM_of]; simp_rw [←map_sum]; exact congr_arg _ (congr_arg insertQ (spin_tax Q' A' ha hA hp ..))
lemma shape_spin (s:Signed): Tape.layer (Normalize.ori s.ortho h) (Q'.shapeD W' A' S t' α l r ρ)=∑ j:(F.level d).Index,(↑(bleached Yι s.ortho j α):ℂ) • Q'.shapeD W' A' S t' j l r ρ:=by
    unfold shapeD; rw [map_sum]; simp_rw [layer_star,port_spin,map_sum,map_smul,Finset.smul_sum,←stars_μ]; rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _=>?_ ; rw [stars_sum,stars_sum]; exact congr_arg (fun k=>starE k _) (push_spin W' Q' A' hA ha hp α i s).symm
omit hp in
lemma shape_unit : Q'.shapeD W' A' S t' 0 l r ρ = Tape.side (Normalize.leaf G h) 1:=by
   unfold shapeD; rw [Finset.sum_eq_single 0]; · rw [pushTax,Q'.unity_tax A' ha hA _,if_pos rfl,map_one,map_one,Tape.star_one]; rw [boots,Q'.cohort.line_unit W',side_tempo (flight_zero _),← flight_sub,map_one]
   · intro i _ hi; rw [pushTax,Q'.unity_tax A' ha hA _,if_neg hi,map_zero,map_zero]; funext j; simp [starE,Tape.pep]
   simp
end MergeTrip
end YM.WilsonCoeffUV.Mer.Xa
