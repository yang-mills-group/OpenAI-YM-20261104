import YM.FVA2.Removal.Platter
/-!
# Expand the intermediate kernel estimates

See `Full/Images` for their production (using `Vista`). Here the powers-of-$g$
index, wire and derivative order are *fixed before* choosing the constant. Expand
the costs on Mid (so `tstart i` is the log-time at sample `i`, `Len i` here is
`exp (tstart i) - 1` clamped to at least 1, smoothing length in lattice-space
units for costing; `tickA L i.1` counts the actual lattice-unit side length,
**physical** length divided by spacing). This is **all Mid at once**, arbitrarily large
powers of `Len/tickA` as shown; no limiting relation between mesh and side
needed here. For the final scalar rates (using also tail estimates from `Period`
etc. along the way), see `Removal/{Two,Rates}`. Note the gain at *that* stage is
with a fixed small positive exponent.

The Mark estimate `scales_at`/`insertions` below is for every indicated wire
(`Chart` of the linear inputs into real momentum space in the MS convention). This is
*differentiation along the wire*, not in the external insertion positions.
`Body_frame` includes the estimate also on the positive-order unmarked bulk
parts, **in the same estimates**, on the momentum-conserving sector &
positive-length wires (in `Rake.Site` with `χ` for the unmarked
bulk cover, see `bulk_frame`). Also retain `Period`, hence the defect bounds
(`Period.ends` etc.).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Removal
open Function Set Filter Finset Metric MeasureTheory Real
open MS MS.High MS.Koszul MS.Plane MS.Landau MS.Landau.Detect MS.Tone Lattice MS.Land MS.Tide MS.Latch MS.Latch.Job MS.Heat MS.Book MS.Book.Convolve Program
open MS.Latch.Job.Belt
set_option quotPrecheck false
open Native Wilsonian MS.Wind MS.Rake MS.Rake.Geo MS.Vista MS.Vane MS.City MS.Orbit Cog MS.Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom MS.Echo
open MS.Fleet MS.Swirl MS.Swirl.Near MS.Menus MS.SpaceOut MS.Dial
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W E:Type}[LinearOrder W] [NormedAddCommGroup E] [NormedSpace ℝ E]
   {S P:Rake.Site G I}{ Q:Seeds G I W}{A:I→ Lattice.Cover}{L:I→Side}{η:I→ℝ}
   {t:Team}{V: MS.Vista.Visa I}{S0:Rake.Site G I}{h: High.Recount G}
local notation "ιW"=> ( Orbit.uniform G I )
local notation "χ"=> Scope G (Wind.skyline G t) η
local notation "Π"=> midpoint V L
local notation "Σ_"=>outside L
variable {X U:Rake.Dance G I W}
local notation "Μ"=> Mid V L
local notation "Z"=> enterV L true
local notation "Ω"=> lampV G L
-- keep additionally bulk & defect bounds in the description
include E
omit E [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem Body_frame
      (H: Images G V L η A Q t true X U)(hK:FlowSet V Q)
      (B: High.Knobs.Fixed (  MS.Wind.col ( MS.Wind.skyline G t )) h true 4 1)
      (hr:warmV η V)
      : ∃ b d,
      (∀ i, Portrait G η t A L true Q i (Valve L true b d i) (Vision L true U i A)) ∧
      Circuit (enterV L true) (lampV G L) (TokenB G t η) A Q b d U
      ∧ (Period Μ Z Ω b d U A 1 ∧ Period (After V L) Z Ω b d U A (Tail V L))
      ∧ (∀ i:ℕ,0< i → DoubleB V L true true (b i - χ i))
 := by
 obtain ⟨b,d,hY,hB,h'⟩:= H.runs; let u:= Doors G V L; have hm : MS.Vista.Gate V χ Q:= ⟨ sky_budget hr ( skyPC G t ) B, fun s=> ( hK s ).2 ⟩
 refine ⟨ b,d,?_,hY,⟨ hB,h'⟩,fun i hi=>?_⟩
 · intro i; unfold Portrait LedgerB; rw [ ← traveller G L true i ]; exact C_to i (health G L) hY (guarding G t η L i)
 exact (Mundane ( show MS.Vista.Core Z Ω b (TokenB G t η) from ⟨ u.fix,hY.action,hY.finances⟩) ⟨ u.logw,H.tower.action,H.tower.finances⟩ u.meet (cap_B hm) u.twin hi)|>.2
-- expanding the price in Mid
local notation "S₀"=> (Mid V L).price
local notation "Len"=> (Mid V L).price.length
variable (w:Wire ( MS.City.BH G) E QP){F:  MS.Rake.Glade G I}
omit [LinearOrder W] in
lemma scales_at {μ:ℝ}{k:ℕ}(b c:Bool)
      (H: WarpHere b c Μ F ( goodM Μ μ * gainQ Μ L k ))
      (hp:Course b w)(hh: fig c w.length) (r:ℕ)
      : ∃ C:ℝ,0<C∧∃ m:ℕ,∀ i: (Mid V L).time,∀ x:E,
      ‖iteratedFDeriv ℝ r ((Plane.Chart ( plug ( J:= (Mid V L).slot ) ( warp0 G I F )) w ) i ) x‖
       ≤ C*( V.bank i.1 * (1+tstart i) * (1+ Len i * ‖x‖) )^m *
          (Len i ^ ( (pitch w:ℝ)-μ+(r:ℝ)) * (Len i/(tickA L i.1))^k):= by
 obtain ⟨C,hC,v,hV⟩:= ( H E w hp hh ).quoted r; refine ⟨ C,hC,v,fun i x=> ( hV i x ( Set.mem_univ _ ) ).trans_eq ?_⟩; let s:= Len i; let u:=V.bank i.1; let Y:= tstart i; change C * (_ *(1+s*‖x‖))^v * ( ( _ ^ pitch w )*(s^(-μ) *(s/tickA L i.1)^k)* s^r)= _; have hz:0<s:= (Mid V L).price.pos _; change C*( (u*(1+|Y|))*(1+s*‖x‖))^v*_=_; have ht:0≤Y:= ( midT i ).1; rw [ abs_of_nonneg ht,← Real.rpow_intCast, Real.rpow_add hz, sub_eq_add_neg, Real.rpow_add hz, Real.rpow_natCast ]; unfold s; ring
lemma insertions {k r:ℕ}
      (H: Images G V L η A Q t true X U)(a:Finset W)
      (ha:a.Nonempty) (u:ℕ)
      : ∃ C:ℝ,0<C∧∃ m:ℕ,∀ i: (Mid V L).time,∀ x:E,
      ‖iteratedFDeriv ℝ r ((Plane.Chart
        ( plug ( J:= (Mid V L).slot ) ( warp0 G I ( U a u-X a u ) )) w ) i ) x‖
       ≤ C*( V.bank i.1 * (1+tstart i) * (1+ Len i * ‖x‖) )^m *
          (Len i ^ ( (pitch w:ℝ)-eps_gain+(r:ℝ)) * (Len i/(tickA L i.1))^k):=
      scales_at w false false (H.small a ha u k) (fun x=> Bool.noConfusion x) (fun x=>Bool.noConfusion x) r
omit [LinearOrder W] in
lemma bulk_frame {k r n:ℕ} {X Y:Rake.Site G I}
      (B: DoubleB V L true true ( X n-Y n ))
      (h: net w=0)(ht:0<w.length)
      : ∃ C:ℝ,0<C∧∃ m:ℕ,∀ i: (Mid V L).time,∀ x:E,
      ‖iteratedFDeriv ℝ r ((Plane.Chart
        ( plug ( J:= (Mid V L).slot ) ( warp0 G I ( X n-Y n ) )) w ) i ) x‖
       ≤ C*( V.bank i.1 * (1+tstart i) * (1+ Len i * ‖x‖) )^m *
          (Len i ^ ( (pitch w:ℝ)-4+(r:ℝ)) * (Len i/(tickA L i.1))^k):= by
 refine scales_at w true true ?_ (fun _=> h) (fun _=> ht) _; rw [good_η]; exact B k
end YM.FVA2.Removal
