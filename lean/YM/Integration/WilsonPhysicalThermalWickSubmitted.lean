import YM.Integration.WilsonPhysicalThermalWickSurplus
import YM.TraceExtension.Prom.Front.West.Mooncake

/-! The actual untrimmed posted Wilson group, at every cutoff and period.
Both the Schur correction and the earned variation on the clipped source
stay on their original sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickSubmitted
open Lattice Wilson RG Labels Function Filter
open Next.Rank Next.Rank.Atlas Next.Rank.Station Next.Rank.Perch Next.Rank.Glimmer
open Next.Rank.Prayer Next.Rank.Beamer Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal
open Marker Glyph Exponential Cells
open scoped BigOperators Classical Topology
variable {G:Gauge}{C:Family G}{d k N p:ℕ}{x:Points 2}{b:ℝ}{Y:AtlasData G C.S p}
    {d0:Fin 2→ℕ}(v:(i:Fin 2)→C.label (d0 i))(hY:∀i,d0 i≤d)(g:FitSky C.path.levels b k x)
    (degree:ℕ)(h:BellSky C.path.levels Y d degree g)
local notation "A"=>C.path.levels
local notation "s"=>clim A k
variable {Z:(i:Fin 2)→Heater C k (d0 i)}{T:(i:Fin 2)→Module.End ℂ (C.label (d0 i))}

include h in
theorem original (u:(i:Fin 2)→C.label (d0 i))(rpos:0<mag A b k)
    (m:Chamber G C.S (middleSky A b k) p→ℝ)(hm:Wind A m (fraction 2 degree s))(mode:modes (Fin 2)):
    let w:=choose A b k x
    let I:trimV (lengthW s) G→Address G:=Subtype.val
    let r:=mag A b k
    let Γ:=Γre C.path.levels.S Y w (beforeSky A b k)
    let μ:=μre C.path.levels.S Y w (beforeSky A b k) (fun U=>(m U:ℂ))
    let Q:=primary d I r Γ (Γs A Y w (beforeSky A b k))
    let z:=Beamer.seen d I r μ
    let M:=fun _:Fin 2=>features d I r
    let P:=fun i=>Z i (u i)
    (Answer Y w (beforeSky A b k) P (fun U=>(m U:ℂ))).part mode=blend Q z (pot mode.val (Particle.cast M P)):=by
  intro w I r Γ μ Q z M P
  let f:=fun i:Fin 2×trimV (lengthW s) G=>(i.1,i.2.val)
  let base:=Qmarks Y w (beforeSky A b k)
  let mean:=noise Y w (beforeSky A b k) (fun U=>(m U:ℂ))
  have radius:0<r:=rpos
  have cert:scope (fun i=>Finsupp.single (f i) 1) base=scope (perSlot M) Q:=by
    have ht:scope (perSlot M) Q=prize I Γ (Γs A Y w (beforeSky A b k)):=shaped d I r Γ _ radius
    rw [ht]
    apply Symmetric.ext
    funext i j
    rw [match_name f]
    exact (h.validQ ..).symm
  have eval:mean∘f=reads (perSlot M) z:=by
    funext i
    rw [show reads (perSlot M) z i=_ from scanned d I r μ i radius]
    exact (h.validM m hm _).symm
  rw [Answer_part,cert,eval,←wets]
  apply congrArg
  unfold pot
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _=>posts M i (P i)

end YM.Integration.WilsonPhysicalThermalWickSubmitted
end
