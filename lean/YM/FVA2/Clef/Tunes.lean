import YM.FVA2.Clef.Optional
import YM.FVA2.Notch.Sales
/-!
 # Optional within-grade final read on the **same regulators**
 Already makes sense once at all horizons, then even after each finite criterion clearance, no
 derivative on test needed besides same first-order bound. Completes allowance for converter of
 §ms-alignment with an optional final *within-grade* basis adjustment preserving real and unit.
 Do not introduce any horizon/order-dependent truncated matrix approximation.$ν log.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Clef.Tunes
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta Generator.Der Generator.Drive
variable {G:Gauge}{d n i j:ℕ}
open Speed Notch Reg Dframe
variable (ν:ℝ)(Y: Initialize G){V:Normalize.Store G}(K:Rose.Pick V)
variable (T: MS_Data G (Position.OpenAxis.Plot ( Press.portDeck G))) (M:Prescription (Press.portDeck G))
variable (D:Frames G)(p: Tags G d n)
local notation "ϑ"=> Scale.Measure.outlook Y K
-- repeated notation to ease reflexive proof.Civil not needed on these.
def charged (A:Frames G)(d:ℕ)(v:Sample n):= status (A d) (Speed.forms_t Y K v d)
def orders (A:Frames G)(d:ℕ)(v:Mesh): Reports G d:= realm ( A d ) (Scale.System.positions Y K d v)
def rep (A:Frames G)(d:ℕ)(x:Points n):= status (A d) (Speed.MeasureAt ν Y K T x d)
def incurred (A:Frames G) (d:ℕ): Reports G d:= realm ( A d ) ( Scale.System.Readout Y K T ν d )
lemma smears (k:ℕ)(φ:Test n) (x:Mesh) : orders Y K D d x k n φ p= Deposit x (fun i=> charged Y K D d i k p) φ:= by
    exact CoverTest.forms x _ _ p (fun _=>D d) φ (fun _ u => CoverTest.forms x ( fun m=> Rose.proposed Y K m d ) ( fun i=> Rose.measureₓ Y K d i ) u (fun _=> Scale.Measure.adjust Y K d ) φ ( fun _ _=> Rose.represents Y K x d _ _ ) ) -- may unify
variable (h:G.Simple)(H: Speed.Quoted Y K T M)
include h H
lemma mouth (x:Points n)(h':x∈conf n): rendition ϑ D d n ⟨x,h'⟩=rep ν Y K T D d x:= by
    obtain H0:= H.toContract.toMission.born;
    apply congr_arg (Dframe.status ( D d ) ); exact ( Speed.now ν Y K M T h H0.Taylor H0.still H0.base x h' )
omit h in
lemma proper (d:ℕ): Scale.Jury.Orders (rendition ϑ D d) ( incurred ν Y K T D d ):= ( H.toContract.smear ν d ).1.specify _
lemma tested (k:ℕ)(φ:Test n): incurred ν Y K T D d k n φ p= φ.applyTo (fun x=> rep ν Y K T D d x k p):= by
    rw [ ( proper ν Y K T M D H _ ).exact n k ]; apply Test.apply_eq; intro x hx; dsimp only; unfold fxt; rw [dif_pos hx,mouth ν Y K T M D h H]
omit h H in
lemma rolling (k:ℕ)(x: Points n)(hx:x∈conf n): ContDiffAt ℝ ∞ (fun x=> rep ν Y K T D d x k p) x:= by simp_rw [rep,Dframe.seen ( D d ) ]; exact ContDiffAt.sum fun _ _=> Speed.notice _ _ _ _ _ _ hx _
variable {U:Set ( Points n )}(hu:IsCompact U)(hx:U⊆conf n) (k:ℕ)
include hu hx
omit h in
lemma steady : Strength U (fun v=> charged Y K D d v k p ) (fun x=> rep ν Y K T D d x k p):= by
    rw [ cartel ]; simp_rw [ charged,rep,Speed.Contacts,Function.comp_def,Dframe.seen ( D d ) ]; exact Fast.sum _ _ _ ( fun i _=> ( Speed.cartel.mp (( H.funds ( XSpace.Normalize.pulseU i ( D d ) p ) ν U hu hx ).checks (i none)).1 ) )
lemma posted (r:ℝ)(hr:0<r): ∃ C:ℝ,0<C ∧ ∀ᶠ m in Front,∀ v:Sample n, grab v=m→ Entry r v → familiar v ∈ U → ‖charged Y K D d v k p- rep ν Y K T D d (familiar v) k p‖ ≤ C*Speed.chip v.F:= by
    apply ( Notch.Pitch.specialize ( V:= fun x=> rep ν Y K T D d x k p ) ).mp; obtain H0:=H.toContract.toMission.born; simp_rw [ charged,rep,Dframe.seen ( D d ) ]; exact Fast.sum _ _ _ (fun i _=> ( Notch.Pitch.pose ν Y K M r ( pulseU i ( D d ) p ) T H0.Taylor h H0.still H0.base (i none) hu hx hr ))
lemma cost : Labor U (fun x φ=> orders Y K D d x k n φ p) (fun φ=> incurred ν Y K T D d k n φ p):= by
    simp_rw [ smears, tested ν Y K T M _ p h H ]; exact Speed.ahead ( steady ν Y K T M D p H hu hx k ) hu hx ( fun v hv=> rolling _ _ _ _ _ _ _ _ hv ) (fun _ _ _=> rfl)
omit hu hx h in
lemma exactly (d:ℕ) : Reg.Higher.HasAll Front (fun x=> Clef.Tunes.orders Y K D d x ) ( Clef.Tunes.incurred ν Y K T D d ):= by intro i n t v; let Q:=H.toContract; change Tendsto ( fun x=>_ ) Front _; unfold Tunes.orders Tunes.incurred; simp_rw [ XSpace.Normalize.really (D d) ]; exact tendsto_finsetSum _ fun j _=> (Q.smear ν d).2 (j none) n t ( Normalize.pulseU j ( D d ) v )
-- same operation order with Z'
omit h H hu hx in
lemma character (A:Frames G) ( t:ℝ ) (d:ℕ): realm ( Scale.Measure.Z Y K t T d * A d ) (substitute ( Scale.Measure.f K t T ) ( State.kernel t T d )) = incurred t Y K T A d:= ( Normalize.parlance _ _ _ ).symm -- orientation check
end YM.FVA2.Clef.Tunes
