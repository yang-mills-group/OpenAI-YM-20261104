import YM.MS.Echo.Bare
/-!
Lift to actual Ward-label. Supports can be established through order n only (may wrap
on farther orders). Distinguish n indices from engineering grades.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Echo
open Set Filter Function Finset Metric
open Koszul Plane Landau Detect Tone Momentum Heat Osc Native
open Lattice Book Convolve Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Puff Puff.SplitP Puff.Engine Puff.Actors Fleet
open scoped Topology ContDiff Interval
variable {G:Gauge}{n:ℕ}{p:Team}{x:ℝ}{F H X:NatK G}{h k u:ℤ}{s t:Finset Cover}
local notation "B"=> Spectrum G
local notation "Θ"=> DotFlip (G:=G)
-- harmonic dependencies.
local infixl:70 " ⋄ "=> couple DotFlip
set_option quotPrecheck false
local infixl:70 " ⋆ "=> (native G).core
lemma toeLeib (hx:∀ i,Tuned ( X i ) 0)(hF:∀ i,Tuned ( F i ) 0) : blocks B X ( F ⋆ H )=( blocks B X F ) ⋆ H+ F ⋆ ( blocks B X H ):= by
    funext n; change Mom.useN.Lift (B).touch _ ( Mom.useN.Lift ( couple DotFlip ) F H ) n=Mom.useN.Lift ( couple DotFlip ) ( Mom.useN.Lift (B).touch X F) H n+ Mom.useN.Lift (couple DotFlip) F ( Mom.useN.Lift (B).touch X H ) n; simp_rw [loan,map_sum,pulseLeib (hF _) (hx _), Finset.sum_add_distrib, LinearMap.sum_apply ]; refine congr_arg₂ (·+·) ( nat.trip _ n (fun i j k=> (B).touch ( X i ) ( F j ) ⋄ H k )) ( rewrap nat _ (fun i j k=> F j ⋄ ( (B).touch ( X i ) ( H k ) )) n ) -- nat = rfl
lemma LapLeib (hF:∀ i,Tuned ( F i ) 0)(hx:∀ i≤n,Pieces ( F i ) s)(hv:∀ i≤n,Pieces ( H i ) t)(hp:Disjoint s t): steadyE B ( style G p x ) ( F ⋆ H ) n=( steadyE B (style G p x) F ⋆ H + F ⋆ steadyE B (style G p x) H ) n:= by
   let S:=style G p x; have ht : ∀ i, Tuned ( S i ) 0:= fun _=> (core_circle G p).actual ..; change actB B _ n+ blocks B S _ n=(((actB B F+blocks B S F) ⋆ H) + F ⋆ (actB B H+blocks B S H)) n
   have Hx : ( actB B ( F ⋆ H ) n )=( actB B F ⋆ H ) n + ( F ⋆ actB B H ) n:= by
      change ( B ).Lap ( Mom.useN.Lift (couple DotFlip) F H n )= Mom.useN.Lift ( couple DotFlip ) ( actB B F ) H n+ Mom.useN.Lift (couple DotFlip) F ( actB B H ) n; rw [ loan,loan,loan,map_sum,← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun i hi=>?_ ; obtain he:= Mom.useN.pays hi;
      change _=_ at he; refine lap_sep ( hF _ ) ( hx _ ?_ ) ( hv _ ?_ ) hp <;> (change i.1+i.2=n at he; omega)
   rw [ Hx, toeLeib ht hF ]; simp only [ map_add,LinearMap.add_apply,Pi.add_apply]; abel
lemma shiftX (x:Cover)(Q H:NatK G): promote ( Lab.Shift x ) (steadyE B Q H )= steadyE B Q ( promote ( Lab.Shift x ) H ):= by funext t; unfold steadyE actB blocks; simp only [Pi.add_apply,promised, paired,map_add,map_sum,lap_dens,touch_dens] -- normalized shift
def NoWeight (n:ℕ)(F X:NatK G): Prop:= ∀ i≤ n,steadyE ( Spectrum G ) X F i=0
end YM.MS.Echo
