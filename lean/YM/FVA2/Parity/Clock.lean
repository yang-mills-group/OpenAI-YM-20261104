import YM.FVA2.Parity.Toll
import YM.FVA2.Generator.Cycle
/-!
# $J_0$ parity through scale transformations

Theorem `measured`. `Presence` for the entire tower of operators, including on
`Measure.Z`, and on the `β` in both variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Parity.Clock
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta Invol Generator.Drive
open Hue.Agent Hue.Agent.Kappa
variable {d n m k e i j:ℕ}{G:Gauge}
local notation "σ"=> Hue.σ
local notation "ς"=> Screen.sigma
local notation "℘"=> Press.portDeck G
-- modest declaration.In presence true shapeV for H-law. Witness for any eligible Finish.b.
variable (ν:ℝ)(W: XSpace.Initialize G){P:Booked (Press.portDeck G)}{V: Store G}(K:Rose.Pick V)(T:MS_Data G P)
variable (S:Prescription (Press.portDeck G)) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput W) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
local notation "L"=> Measure.liftT K ν T
local notation "χ"=> Measure.chi K ν T
local notation "φ"=> Measure.f K ν T
include h hs hr hu
lemma odd_χ : Anti (Measure.chi K ν T):= by
    have hp (m:Mesh) (hv: V.Meets W m 6): Anti (prospects ν W K S m):= Anti.compose ( Invol.t.mpr ( Rose.odd_c W K m hv )) ( show Anti (Dframe.reset ν S m) from Lambda.Pen.shifted S.team _ ( standardF h hs ) ) (share ..)
    apply Invol.t.mpr; apply PowerSeries.ext; intro i; have hm:= Reg.Choice.forecast ν W K S T h hs hr hu i; rw [Rose.inversion,coeff_rescale, map_neg]; apply tendsto_nhds_unique ( hm.const_mul (σ i) ) -- g bad
    refine hm.neg.congr' ?_; filter_upwards [ ( V.nested_solution W 6 frontier ).2 ] with x hx; rw [ ← coeff_rescale, show rescale (-1:ℂ) (prospects ν W K S x)=_ from Invol.t.mp ( hp x hx.1 ), map_neg]
lemma odd_f : Anti ( Measure.f K ν T ):= by obtain hx:= (Select.vigor W K ν T S h hs hr hu); exact ( odd_χ ν W K T S h hs hr hu ).pack hx.left hx.right hx.own
lemma odd_ψ (t:ℝ) : Anti (GroupS.ψ K T ν t):= Anti.compose ( odd_χ (ν-t) W K T S h hs hr hu ) ( odd_f ν W K T S h hs hr hu ) (Specific.vigor_f W K ν T S h hs hr hu).start
lemma odd_Ψ (t:ℝ) : Anti ( Scale.GroupS.Ψ K T ν t ):= Lambda.LowBound.turns ν W K T S t h hs hr hu 0
local notation "Tg"=> odd_ψ ν W K T S h hs hr hu
local notation "Z_"=> Scale.Measure.Z W K ν T
local notation "Lo"=> GroupS.gaugeB K T ν
local notation "U"=> GroupS.gaugeN W K T ν
local notation "M"=> GroupS.gaugeM W K T ν
lemma presence_l : Facing ( L d ):= Facing.substR ( frameForms ν W S T h hs V ) _ ( odd_f ν W K T S h hs hr hu )
lemma presence_Z : Facing ( Z_ d ):= by rw [ equator W K ν T S h hs hr hu ]; exact ( presence_l ν W K T S h hs hr hu ).keeps
lemma presence_B (t:ℝ): Facing ( Lo t d ):= Facing.mul ( ( presence_l ν W K T S ( d:=d ) h hs hr hu ).sacr t|>.reflects ) ( ( presence_l (ν-t) W K T S h hs hr hu ).substR _ (Tg t) ) -- arg order
lemma presence_N (t:ℝ): Facing ( U t d ):= Facing.mul ( Facing.reflects (presence_Z ν W K T S h hs hr hu) ) ( Facing.substR ( presence_Z (ν-t) W K T S h hs hr hu ) _ (Tg t))
include ν
lemma adjusted : Facing (Measure.adjust W K d):= by obtain he:= ( presence_l ν W K T S ( d:=d ) h hs hr hu ); rw [ Measure.matchU W K ν T S h hs hr hu _ ( adj W K ν T S h hs hr hu ) ]; exact Facing.mul ( he.reflects ) ( he.keeps )
lemma presence_M (t:ℝ): Facing ( M t d ):= by
    have hx:= presence_Z ν W K T S (d:=d) h hs hr hu; exact Facing.substR ( ( hx.mul ( presence_N ν W K T S h hs hr hu t ) ).mul (( hx.substR _ (Tg t) ).reflects) ) _ ( odd_χ ν W K T S h hs hr hu )
lemma aligns (d n:ℕ)(x:Stage n) : Relays (wave ν T d n x) ∧ Relays ( Measure.start W K d n x ) ∧ Relays (Measure.outlook W K d n x):= by
    rw [← together W K ν T S h hs hr hu d]; obtain ht:Relays (wave ν T d n x):= Invol.earns ν W S T h hs x.property; have hp: Relays (pupil K ν T d n x):= Relays.meet ( ht.pay _ ( odd_f ν W K T S h hs hr hu ) ) ( presence_l ν W K T S h hs hr hu); unfold Measure.outlook; rw [← together W K ν T S h hs hr hu d ]; exact ⟨ ht,hp,hp.meet ( adjusted ν W K T S h hs hr hu ) ⟩
omit h hs hr hu ν
lemma justified {B:ℝ→ Guard G d}{A:Guard G d}(i:ℝ)(hp: Generator.Der.Instant B A i)(hb:∀ v,Facing (B v)): Facing A:= by
    intro j p; let b:=Module.finBasis ℂ (Sec G d); apply b.equivFun.injective; funext k; let Worker(v:Sec G d):= LinearMap.applyₗ (R:=ℂ) (M₂:=Sec G d) v;
    obtain hv:= hp j ( b.coord k ∘ₗ Worker ( hinge d p )); simp_rw [LinearMap.comp_apply] at hv; change HasDerivAt (fun t=> b.coord k ( coeff j (B t) (hinge d p))) _ i at hv; simp_rw [hb] at hv; exact hv.unique ( hp j ( b.coord k ∘ₗ (σ j • hinge d) ∘ₗ ( Worker p ) ) )
structure Presence (ν:ℝ) : Prop where
    meters : Anti ( Measure.chi K ν T ) ∧ Anti ( Measure.f K ν T ) ∧ ∀ t, Anti ( GroupS.ψ K T ν t ) ∧ Anti (GroupS.Ψ K T ν t)
    fields d: Facing (Measure.liftT K ν T d) ∧ Facing (Measure.adjust W K d) ∧ Facing (Measure.Z W K ν T d) ∧ ∀ t,Facing ( GroupS.gaugeB K T ν t d ) ∧ Facing ( GroupS.gaugeN W K T ν t d ) ∧ Facing (GroupS.gaugeM W K T ν t d)
    points (d n:ℕ)(x:Stage n): Relays (wave ν T d n x) ∧ Relays ( Measure.start W K d n x ) ∧ Relays (Measure.outlook W K d n x)
    beta4 (i:ℕ)(he:Even i): coeff i ( Beta.beta (GroupS.ψ K T ν))=0 ∧ coeff i (Beta.beta ( GroupS.Ψ K T ν ))=0
    engraves d: Facing (Generator.Drive.engraving ( GroupS.gaugeN W K T ν ) d) ∧ Facing ( Generator.Drive.engraving ( GroupS.gaugeM W K T ν ) d )
variable (p:ℝ→Cn)
lemma beta4 (he:Clear p)(k:ℕ)(hf:Even k)(h:∀ t, Anti (p t)) : coeff k ( Beta.beta p )=0:= by
    obtain hp:= origin p he k; simp_rw [ show ∀ t,coeff k (p t)=0 from fun t=> Anti.wipe (h t) k ( Nat.even_iff.mp hf ) ] at hp; exact hp.unique (hasDerivAt_const ..)
include ν h hs hr hu
-- any TaylorOKF; any $T$; irrespective of Right policy.
theorem measured : Presence W K T ν := by
    let C:= Precise.mainN ν W K T S h hs hr hu; let D:= Precise.mainM ν W K T S h hs hr hu; exact ⟨ ⟨ odd_χ ν W K T S h hs hr hu, odd_f ν W K T S h hs hr hu, fun t=>⟨ Tg t, odd_Ψ ν W K T S h hs hr hu t ⟩ ⟩, fun d=>⟨ presence_l ν W K T S h hs hr hu,adjusted ν W K T S h hs hr hu,presence_Z ν W K T S h hs hr hu,fun t=>⟨ presence_B ν W K T S h hs hr hu t,presence_N ν W K T S h hs hr hu t,presence_M ν W K T S h hs hr hu t ⟩ ⟩, aligns ν W K T S h hs hr hu, fun i he=>⟨ beta4 _ C.smooth i he ( odd_ψ ν W K T S h hs hr hu ),beta4 _ D.smooth i he ( odd_Ψ ν W K T S h hs hr hu ) ⟩, fun d=>⟨ justified 0 ( Generator.Der.walks C d ) ( presence_N ν W K T S h hs hr hu ),justified 0 ( Generator.Der.walks D d ) ( presence_M ν W K T S h hs hr hu ) ⟩ ⟩
-- use with contract later
end YM.FVA2.Parity.Clock
