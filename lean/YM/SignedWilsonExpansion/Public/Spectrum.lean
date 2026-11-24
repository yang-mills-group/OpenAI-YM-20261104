import YM.SignedWilsonExpansion.Public.Eventide
/-! # All characters of the SAME compression. Includes full-support measure, no phase
  reselection of finite measures. Continuum character price then shows that one may with
  ordered regulator estimates PRICE with ANY such continuum character as well, using the
  actual unselected cutoff words at fixed r, health margin in α. Masks may be chosen freely
  as usual (the subtraction takes place within each character). Mixture identity here is for
  complete moments (& each face), not declaring mixture of *cumulants* or a factorization.
-/
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

local notation "Ξ₀"=> ( V.T Z ∘ r )
local notation "Θ"=> ( Lamplight Z a d )
local notation "Ω"=> ( slotW Z V a )
local notation "𝕎"=> ( V.pupil )
local notation "Ω₀"=> ( V.pupil.last )
variable (t:Taster α) (B:Roi U) (P : ∀ i:α,∀ j: Fin n,SeatsW.Salary ℂ l 1 (fun v=> u i v j) )
local notation "K*"=> (fun i j=> u j i)

local notation "ℓ" => ( fun i s=> costumes E.paths V.pupil.last V.colours (slotW Z V a) ( r i ) d (u s i) )
local notation "f₀" => ( V.pupil.f )
local notation "s₀" => ( fun i=> bakes Ω₀ t Ω none (r i) (K* i) )
local notation "Λ" => ( fun i : ℕ => E.paths.family.S.a i ) -- not needed
local notation "P*" => ( fun i=> fulfills (Y':= Θ) t (Ξ₀ i) b ( K* i ) )
local notation "A₀"=> ( V.pupil.last.α.unselected )
local notation "R₀"=> ( V.pupil.last.α.space )
attribute [local instance] OS.Spread.Resolution.metric OS.Spread.Resolution.compact OS.Spread.Resolution.borel
variable (V) -- Q? core
lemma groundFile : (R₀).Out:= (Ω₀).phase.phase.decomposition
lemma everySingle (χ:(A₀).algebra →⋆ₐ[ℂ] ℂ): ∃! z:(R₀).X,(R₀).character z=χ:=
    Function.Bijective.existsUnique (groundFile V).onto χ -- possible lemma?
lemma phasesCompleted : EveryPhase.Completed (Ω₀) (𝕎).L:= (𝕎).phase
lemma groundMean {τ:ℝ}(Z:WilsonPrescription G)(p:0<τ){w:Caps n}(u:∀ j,Sec G ( w j ))(a:Bool)(x:Scale.Stage n): Continuous (fun t:(R₀).X=> Life Z V a τ w u x.val (some t) ) ∧ ( ∫ t:(R₀).X, Life Z V a τ w u x.val (some t) ∂( (R₀).μ ) ) = Life Z V a τ w u x.val none :=by
    let f:=word Z V a τ w u; let y:= τ • x.val; have hy:= Work.A05.smul_conf p x.property; let P':= viewing Ω₀ y.ofLp f; let Y':= groundFile V; have he(q:Peers V): Life Z V a τ w u x.val q=( glance Ω₀ q ) P':= applause E.paths Ω₀ V.colours _ τ w u q x.val hy
    simp_rw [he]; exact ⟨ Y'.weak _, Y'.ground _ ⟩
variable {V}
include M B p P
abbrev onCost (V:Vision E ξ)(Z: WilsonPrescription G)(a:Bool)(t:Taster α)(u:α→ι→Tags G d n)(r:ι→ℝ)(i)(x:Viewers V.pupil.last):= bakes V.pupil.last t (slotW Z V a) x (r i) (fun j=> u j i)
local notation "φ*"=> ( onCost V Z a t u r )
local notation "X*" => (cutoffPoints t Z V a r u)
local notation "Y*" => ( cutoffProfile t Z V a r u )
lemma underRainbow : ∃ C:ℝ,0<C ∧ ∀ᶠ i in l,∀ᶠ y:ℕ×ℕ in (Homes.track f₀).fuse, (∀ v:Peers V,∀ x∈U, ‖X* i y x- φ* i v x‖≤ C*‖Ξ₀ i^(b+1)‖) ∧ (∀ v:Peers V,∀ f:Test n, tsupport f⊆U→ ‖Y* f i y- f.applyTo ( φ* i v )‖≤ (∫ x:Points n,‖f x‖)*( C*‖Ξ₀ i^(b+1)‖)):=by
    obtain ⟨⟨c,hc,w⟩,d₀,hd,z⟩:=stagewide M p t B (b:=b) (a:=a) P; obtain ⟨K,u₀,U'⟩:= curtains M p (a:=a) t B P (b:=b); let D(i):= ‖Ξ₀ i ^ (b+1)‖; refine ⟨K+c+d₀,by linarith,?_⟩; filter_upwards [ z, w, U' ] with i hz hw hF; have h:0≤D i:= norm_nonneg _; filter_upwards [ hF ] with i' hj; refine ⟨ ?_, fun v f hf=>?_ ⟩
    · intro v x hx; have he: ‖X* i i' x- P* i x‖≤ K * D i:= hj.1 x hx; have ht: ‖P* i x- φ* i v x‖≤ c*D i:=( norm_sub_rev (P* i x) _ ).le.trans ( hw v x hx ); exact ( norm_sub_le_norm_sub_add_norm_sub _ _ _ ).trans (( add_le_add he ht ).trans (by change K * D i+c*D i≤(K+c+d₀)*D i; nlinarith only [hd,h]))
    let H':= (∫ x:Points n,‖f x‖); have hu: 0≤ H':=integral_nonneg fun _=> norm_nonneg _; have he: ‖Y* f i i'- f.applyTo ( P* i )‖≤ H'*(K * D i):= hj.2 f hf; have hy: ‖f.applyTo ( P* i )-f.applyTo ( φ* i v )‖≤H'*( d₀*D i ):= ( norm_sub_rev (f.applyTo ( P* i )) _ ).le.trans ( hz v f hf ); refine ( norm_sub_le_norm_sub_add_norm_sub _ _ _ ).trans ( ( add_le_add he hy ).trans ?_ ); rw [ ← mul_add ]; exact mul_le_mul_of_nonneg_left (by change K * D i + d₀* D i≤ ( K+c+d₀ )*D i; nlinarith only [h,hc] ) hu
end Vision
end YM.Answer.ContinuumLimit
