import YM.RG12.Burst.Vertex
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Blush
open Function Filter Lattice RG Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Daisy Daisy.Charity Mallow Lotus
open PowerSeries Extra.Histories Progress.DirectedRecipe Next.Foundations Precision
open Blaze Blaze.March Poll Pond Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f n: Side}
variable {i j:ℕ} {o: Site n}{S:Support n}{B : BudgetPoint}
open Pressure Push.SectorMeasure Greenbelt Refrain
variable {S:StepData c f}{T: Tube G S}{L:Side}{P:Teller G} {Q: ConnectedActivityE6.Target G P}{W x μ C : ℝ}{o':Target.Order G W}{R:RG.Rep G f}
variable (H:Cash W x μ L Q o' C T R) (r : Cloud R) (o : Site c)
local notation "hd"=> r.live
local notation "hd'"=> r.pale
local notation "χ"=> Chi.canonical
variable (K R' : ℝ → Code G c)
variable (v: ℂ)
variable (F : YM.Labels.Frame G j)
section prices
local notation "M" => Blush.screen H r K R' v F
variable {R2 : Rep G c} (he:R2.p=B)
variable {A b q t d Y f₀ α k β e w t':ℝ}{n' ℓ:ℕ}(N: Captain H n' q t d Y A b t' f₀ k ℓ Chi.canonical)
namespace Burst10
open Daisy.Charity.RG12 Matter Height Shield Stained
-- Drop packets by markSeed(derived on algebra not parity). Drop K explicitly because roster incidence. No generic subtraction. Then in warm molecules only Miniature and Signed Cubic. Horn criterion employed.
section masks
open Source Labels
variable (g:Hol G)
set_option quotPrecheck false
local notation "u" => rows10 (B:=B) H r o v F g
local notation "w" => warm11 (B:=B) H r o v F g
local notation "Tag" => r.live.turn.badge S

-- residual slot. Direct stencil exactly defined on the basis. turn-unit not required.Pay for entire histories. Matrix precision still needs those residuals & nonvaning stable analyses.
def tendrils (k:ℕ)(i:H.fragrances):= if i=Brim.icon H k then 0 else w i
protected def lots (k:ℕ):= ∑' i,tendrils (B:=B) H r o v F g k i
lemma duplex (hs:Summable w){k:ℕ}(hk:r.live.turn=.logKey k): chart11 (B:=B) H r o v F g= (Local.weighted g F o (Brim.plate H k).support B.threshold (pane H r v (Brim.icon H k)))+ Burst10.lots (B:=B) H r o v F g k ∧ Summable (tendrils (B:=B) H r o v F g k) ∧ ∀ i:H.fragrances, ¬ Duo H r i→ tendrils (B:=B) H r o v F g k i=0:=by
   let L:= Brim.icon H k; let z:=w L; let f (i:H.fragrances):= if i=L then z else 0
   have hx:w-f=tendrils (B:=B) H r o v F g k:=by
       funext i; by_cases h:i=L; · subst i; simp [z,tendrils,L,f]
       change w i-f i=(if _ then _ else _); rw [show f i=0 from if_neg h, if_neg (show i≠Brim.icon H k from h),sub_zero]
   have hh : HasSum f z:= hasSum_ite_eq _ _
   refine ⟨?_, hx ▸ hs.sub hh.summable,fun i hi=> ?_⟩
   · unfold Burst10.lots; rw [←hx]; change (∑' i,w i) = _+∑' i,(w-f) i; simp_rw [Pi.sub_apply,Summable.tsum_sub hs hh.summable,hh.tsum_eq,(show Local.weighted g F o _ _ _= z from (warming (B:=B) H r o v F g hk).symm)]; abel
   unfold tendrils; split; rfl
   next h=> exact not_not.mp (fun h'=> hi (twigs11 H r o v F g k hk i h h'))
lemma gasEra {k:ℕ}(hg:r.live.turn=.gasKey k):chart11 (B:=B) H r o v F g=0:=by
   unfold chart11; rw [show (fun i=>w i)=fun _=>0 from ?_,tsum_zero]
   funext i; by_contra h; obtain ⟨j,hj⟩:=(guides11 H r o v F g (B:=B) h).notPetrol; rw [hg] at hj; cases hj
end masks
end Burst10
end prices
end YM.PhysicalNext.Repeat.Blush
