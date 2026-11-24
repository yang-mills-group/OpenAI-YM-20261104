import YM.SignedWilsonExpansion.Public.Dazzle
import YM.SignedWilsonExpansion.Museum.Anchor
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Answer.ContinuumLimit
open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open PowerSeries XSpace.Cirrus Entree Future
open scoped BigOperators Classical ContDiff Topology
universe u
namespace Vision
variable {G:Gauge}{H:G.Simple}{e:Axis}{ε:ℝ}{O:OrderS G}{E:Construction.{u} H ε e O}{ξ:Extraction.Order}{V:Vision E ξ}
variable {Z:WilsonPrescription G}{dial:Bool}(Q:Perspective H Z dial)
open Frames Frames.Cortex -- order check
open Dancer Entree.Cup -- remove if trouble
open PowerSeries Scale Jury WilsonCoeffUV.Mer.Xa MarqueQ Crops
variable {Q} (M:Garnishes V Q)
variable {α ι:Type}{l:Filter ι}{r:ι→ℝ}
variable (p:Tendsto r l trail){a:Bool} {n d:ℕ} {u:α→ι→Tags G d n} {b:ℕ} {U:Set (Points n)}
include M
local notation "Ξ₀"=> ( V.T Z ∘ r )
local notation "Θ"=> ( Lamplight Z a d )
local notation "Ω"=> ( slotW Z V a )
local notation "𝕎"=> ( V.pupil )
local notation "Ω₀"=> ( V.pupil.last )
variable (t:Taster α) (B:Roi U) (P : ∀ i:α,∀ j: Fin n,SeatsW.Salary ℂ l 1 (fun v=> u i v j) )
local notation "K*"=> (fun i j=> u j i)
include B p P
local notation "ℓ" => ( fun i s=> costumes E.paths V.pupil.last V.colours (slotW Z V a) ( r i ) d (u s i) )
local notation "f₀" => ( V.pupil.f )
local notation "s₀" => ( fun i=> bakes Ω₀ t Ω none (r i) (K* i) )
local notation "Λ" => ( fun i : ℕ => E.paths.family.S.a i ) -- not needed
local notation "P*" => ( fun i=> fulfills (Y':= Θ) t (Ξ₀ i) b ( K* i ) )
abbrev cutoffPoints (Z:WilsonPrescription G)(V: Vision E ξ)(a:Bool)(r:ι→ℝ)(u:α→ι→Tags G d n)(i:ι)(y:ℕ×ℕ):= cafe E.paths.family (r i) (fun x=>Cup.dispense x t) ( fun s=> costumes E.paths V.pupil.last V.colours (slotW Z V a) ( r i ) d (u s i) ) y.1 y.2 -- need infer n
abbrev cutoffProfile (Z:WilsonPrescription G)(V:Vision E ξ)(a:Bool)(r:ι→ℝ)(u:α→ι→Tags G d n)(φ: Test n)(i:ι)(y:ℕ×ℕ):= summit E.paths.family φ (r i) (fun x=>Cup.dispense x t) ( fun s=> costumes E.paths V.pupil.last V.colours (slotW Z V a) ( r i ) d (u s i) ) y.1 y.2
local notation "Xc" => (cutoffPoints t Z V a r u)
local notation "Yc" => ( cutoffProfile t Z V a r u )
lemma curtains : ∃ C:ℝ,0<C ∧ ∀ᶠ i in l,∀ᶠ y:ℕ×ℕ in (Homes.track f₀).fuse,(∀ x∈ U, ‖Xc i y x-P* i x‖≤ C*‖Ξ₀ i ^(b+1)‖) ∧ (∀ f:Test n, tsupport f⊆ U→ ‖Yc f i y- f.applyTo ( P* i )‖≤ (∫ x:Points n,‖f x‖)*( C * ‖Ξ₀ i ^(b+1)‖)):=by
      obtain ⟨⟨c,hc,w⟩,d₀,hd,z⟩:=stagewide M p t B (b:=b) (a:=a) P; let D(i):= ‖Ξ₀ i ^(b+1)‖; have hd':∀ᶠ i in l,0<D i:= ( p.eventually M.accounts.calibrated.calendar.clock.positive ).mono fun i h=> norm_pos_iff.mpr ( pow_pos ( show 0 < Ξ₀ i from h ) (b+1) ).ne'; let χ(x:α→ℂ):ℂ:= Cup.dispense x t; let T':= anchorF (p.eventually self_mem_nhdsWithin) E.paths V.pupil.last V.colours Ω χ H B ( continuousOn_univ.mp ( Cup.garage (X:=fun x:α→ℂ=>x) (fun i=> ( continuous_apply (A:=fun _:α=>ℂ) i ).continuousOn ) t ) ) u V.pupil.trackV D hd'; refine ⟨ 1+c+d₀, by linarith,?_ ⟩; filter_upwards [z,w,hd',T'] with i hz hw hf ht; filter_upwards [ht] with j hj
      let S':= s₀; let P'':= P*; refine ⟨ fun x hx=>?_,fun φ hφ=>?_ ⟩
      · have he: ‖Xc i j x- S' i x‖≤D i:= hj.1 x hx; have hy: ‖S' i x-P'' i x‖≤ c* D i:= hw none x hx; exact ( norm_sub_le_norm_sub_add_norm_sub _ _ _ ).trans ( ( add_le_add he hy ).trans (by change D i+c*D i ≤ (1+c+d₀)*D i; nlinarith only [hf,hd]) ) -- norm & ζ unfolding maybe
      have he: ‖Yc φ i j- φ.applyTo ( S' i )‖≤ (∫ x:Points n,‖φ x‖)* D i := hj.2 φ hφ; have hy:= hz none φ hφ; change ‖φ.applyTo ( S' i )- φ.applyTo ( P* i )‖≤ _*( d₀* D i ) at hy; refine ( norm_sub_le_norm_sub_add_norm_sub _ _ _ ).trans ( ( add_le_add he hy ).trans ( ?_ ) ); set A:= ( ∫ x:Points n,‖φ x‖); have ha: 0 ≤ A:= integral_nonneg fun _=> norm_nonneg _; rw [ ← mul_add ]; exact mul_le_mul_of_nonneg_left ( by change D i + d₀ * D i ≤ ( 1+c+d₀ ) * D i; nlinarith only [hf,hc] ) ha
end Vision
end YM.Answer.ContinuumLimit
