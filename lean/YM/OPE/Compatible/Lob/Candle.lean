import YM.OPE.Compatible.Karu.Spring
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
open PriceZ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Y"=> solar G d τ
open JetS
variable (h:Aware d τ)
-- Tower τ op
noncomputable def armP (G:Gauge)(h:Aware d τ)(i j:Phase)(hp:i ≤ j): Seat (d+i.val) (τ i) (Shade G)→L[ℝ] Seat (d+j.val) (τ j) (Shade G):= glasses (Shade G) _ (τ i) _ (h.mono hp) ∘L kindle G _ _ _ (by have he: i.val≤ j.val:=hp;omega)
lemma armL (i j:Phase)(hp:i≤j)(x:Seat (d+i.val) (τ i) D!): lilies (τ j) (d+j.val) _ (armP G h i j hp x)=lilies _ _ _ x:=by unfold armP; rw [ContinuousLinearMap.comp_apply,putG,forgets]; exact kindle_eq _ _
def Candy (G:Gauge)(h:Aware d τ): Tower (Shade G) d τ→L[ℝ] Tower (Shade G) d τ:= ContinuousLinearMap.pi (fun i=> if ht:i<1 then 0 else
     let j:Phase:=⟨i.val-1,by have h:= i.isLt;omega⟩; armP G h j i (by unfold j; change i.val-1 ≤ i.val;omega) ∘L ContinuousLinearMap.proj j)
lemma pal (x:L!)(i:Phase)(hp:i<1):Candy G h x i=0:=by simp only [Candy,ContinuousLinearMap.pi_apply,dif_pos hp,_root_.zero_apply] -- if not dite
lemma glee (x:L!)(i j:Phase)(hp:i.val=j.val+1):Candy G h x i=armP G h j i (by change j.val ≤ i.val;omega) (x j):=by
     unfold Candy; rw [ContinuousLinearMap.pi_apply,dif_neg]; swap; · have ht:i.val≥1:=(by omega); exact not_lt.mpr ht
     have ht:i.val-1 <3:=by have hv:=i.isLt;omega
     have hv : j=(⟨i.val-1,ht⟩:Phase):=by apply Fin.ext; change j.val=_-1;omega
     subst j;rfl
lemma slideP (x:L!):spread G d τ (Candy G h x)=Drift.glide (spread G d τ x) 1:=by
    funext i; fin_cases i
    · change lilies (τ 0) (d+(0:Phase).val) _ (Candy G h x 0)=0; rw [pal h _ _ (by decide),map_zero]
    · change lilies (τ 1) (d+(1:Phase).val) _ (Candy G h x 1)= lilies (τ 0) (d+(0:Phase).val) _ (x 0); rw [show Candy G h x 1 = _ from glee h x 1 0 rfl]; exact armL ..
    change lilies (τ 2) (d+(2:Phase).val) _ (Candy G h x 2)= lilies (τ 1) (d+(1:Phase).val) _ (x 1); rw [show Candy G h x 2=_ from glee h x 2 1 rfl]; exact armL ..
lemma flairS_eq (x:L!)(i:Phase)(t:Bid.Dir G n)(p:Site n): Flair ((Drift.spread G d τ x) i) (d+1+i.val) (spool G n t) p=Flair ((Drift.spread G d τ x) i) (d+i.val) (spool G n t) p:=by
     unfold Flair; rw [show d+1+i.val=d+i.val+1 from by omega, Finset.sum_range_succ,show Drift.spread G d τ x i (d+i.val+1) =0 from (resin x (m:=0) (fun _=> Nat.zero_le _) i).1 _ (by omega)]; simp [Flume.Script.value,scribe] -- f doesn't appear.
lemma Speel (x:L!)(p:Site n): Vtap (Candy G h x) p=fun i=> Ū* Vtap x p i:=by
     funext i; unfold Vtap; rw [slideP h,Drift.baton]; change Ū^1*_= _; rw [pow_one]; apply congrArg (Ū*·); apply JetS.eta<;>first|exact flairS_eq x 0 i p|exact flairS_eq x 1 i p|exact flairS_eq x 2 i p
lemma sailV (p:Y): Candy G h p.val∈solar G d τ:=by
     refine ⟨fun i j=>?_,fun n x=>?_⟩; swap
     · change (tor n).Marbles (Vtap _ x); rw [Speel]; exact prodMar (tor n) (staysP ..) (p.property.2 ..)
     rw [slideP]; fin_cases i; rw [Drift.glide_nil _ (by decide)]; exact fun _=>rfl; exact p.property.1 0 j; exact p.property.1 1 j
noncomputable def trellisA (G:Gauge)(h:Aware d τ): solar G d τ→L[ℝ] solar G d τ:= (Candy G h∘L (solar G d τ).subtypeL).codRestrict _ fun x=>sailV h x
lemma gaze (p:L!)(u:ℝ) : Candy G h (rebase G h u p)=rebase G h u (Candy G h p):=by
    funext i; by_cases hz:i<1; · rw [sail _ i _ _ (by intro hx; rw [hx] at hz; exact lt_irrefl _ (lt_of_le_of_lt (show (1:Phase)≤2 by decide) hz)),pal h _ i hz,pal h _ i hz]
    fin_cases i; simp at hz
    · change Candy G h _ 1= rebase G h _ _ 1; rw [glee h _ 1 0 rfl,sail _ 0 _ _ (by decide),sail _ 1 _ _ (by decide)]; exact (glee h _ 1 0 rfl).symm
    change Candy G h _ 2=rebase G h _ _ 2; rw [glee h _ 2 1 rfl, sail _ 1 _ _ (by decide), Drift.sip,pal h p 0 (by decide),map_zero,smul_zero,add_zero]; exact (glee h _ 2 1 rfl).symm
end YM.OPE.Quit.Jac
