import YM.FVA2.Inked.Combined
import YM.FVA2.Notch.Finish
/-!
 # Quotes for the physical prescription in wider regulator tests

 Same `Y` orientation on all `Orbit`: fixed calibration and position
 normalization, initial field fees as in `Served`. Strengthen beyond 1/16 clearance,
 all moment *orders*, any fixed list of `Label`s, preservation
 of the unmarked error budget, no hidden period upper (or lower-growth) price before
 linking to Front to obtain the pure-spacing cost. Claims about proof of Estimates are
 exactly through the ports of `MenuCost`: `Images` and `PeakT` etc (derivatives of
 internal/momentum glade kernels before external point projection). Not differentiating
 discrete point kernels with respect to positions. `Mesh` fixed stencil inputs as supplied.
 Fits omitted center complexity by wrapping to a nearest shift. For expansion interpretation see
 `Notch/Finish.lean`, `Removal.Wires`, `Speed.Distill`.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Removal
open Function Set Filter Finset Metric MeasureTheory Real
open MS MS.Koszul MS.Plane MS.Landau MS.Tone Lattice MS.Land MS.Latch MS.Latch.Job MS.Tide MS.High
open MS.Vane MS.Rake MS.Rake.Geo MS.Vista MS.Vane MS.Fleet MS.Dial
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Swirl
open scoped Topology ContDiff Interval
open PeakT (ordZ)
variable {I W:Type}{l:Filter I}{μ:ℝ}{T:Trial I W}{G:Gauge}{K: Land.Booked (Press.portDeck G)}{S: MS_Data G K}{Y:XSpace.Initialize G}
variable [LinearOrder W] {A:Land.Prescription (Press.portDeck G)}{u : W→Label (Press.portDeck G)}{f z: MS.Fleet.Terrify W I}
lemma MenuCost.finFields (H:Spots T μ)(hs:MenuCost S Y T A u μ l f z)(s:Finset W)(n:ℕ) : Fraction l T.profile T.side (fare (Label.h∘u) T.profile ( ordZ f ) s n) (fare (Label.h∘u) T.profile ( ordZ z ) s n) (fun i=> tour S u μ ( testP T i ) s n ):= by
 obtain ⟨_,_,_,_,B,_,_,_,_,_,hB,_⟩:= hs.fabric
 have hp:=posed (μ:=μ) T.off H.knit
 have h0(s:Finset W)(n:ℕ) : Fleet.toZ B s n= (fun i=> book S u μ ( testP T i ) s n ):= funext fun i=> Point_t S u μ hp hB i s n
 rw [ ← show ordZ (Fleet.toZ B) s n=(fun i=>tour S u μ ( testP T i ) s n) from funext fun i=> shape_f S u μ hp hB i s n ]; let x:= Label.h ∘ u
 change Fraction l _ _ ( fare x _ _ _ _ ) (fare x _ _ _ _) _
 rw [ ← funext (fun i=> PeakT.ν_norm x (s:=s) ( n:=n ) ( P:=T.profile ) i f ), ← funext (fun i=> PeakT.ν_norm x (s:=s) ( n:=n ) ( P:=T.profile ) i z ) ]; exact Budget.runs _ _ _ (fun s n=> ⟨(h0 s n).symm ▸ ( hs.reaches s n |>.1 ),hs.reaches s n|>.2.2 ⟩ ) s n
end YM.FVA2.Removal
namespace YM.FVA2.Notch
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Koszul MS.Dial
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe Expense
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Theater PowerSeries
open Normalize.Fray Reg Reg.Pivot Reg.Point Reg.Unique CoverTest Photo Higher State Reg.Choice
open scoped Topology ContDiff BigOperators Classical
open Speed Speed.Star Asymptotics Finset Speed.Clock Speed.Timeframe Arrival.Episodic FVA2.Scale.System
open Register Register.WilsonPrescription Removal Press
open PeakT (ordZ)
variable {n d k:ℕ}{G:Gauge} (N:Register.WilsonPrescription G)
variable (T:MS_Data G ( Position.OpenAxis.Plot (Press.portDeck G) ))
variable (M:Land.Prescription (Press.portDeck G)) (h:G.Simple) (H: Served N T M)
local notation "Y"=> Register.WilsonPrescription.scheme N
local notation "K"=> Register.WilsonPrescription.criterion N
structure Poise : Prop where
    passengers (I W:Type) [LinearOrder W] (l:Filter I) (U:Trial I W)
            (p:W → MS.Rake.Label (Press.portDeck G)) (ν:ℝ) (hK:Spots U ν)
            (ht:Tendsto U.profile.θ l atTop) :
        ∃ f z, MenuCost T Y U M p ν l f z ∧ ∀ s k,
          Vol l U.profile U.side (fare (MS.Rake.Label.h ∘ p) U.profile (ordZ f) s k -
                                  fare (MS.Rake.Label.h ∘ p) U.profile (ordZ z) s k)
    /-- Two-cutoff bounds, even before imposing a relationship between them. -/
    pre_position (n:ℕ) (u:Fin n → MS.Rake.Label (Press.portDeck G)) (s:Finset (Fin n))
            (A:Set (Points n)) (k:ℕ) (ν r:ℝ) (hr:0<r) (ht:IsCompact A) (hp:A⊆ conf n) :
        ∃ (C:ℝ) (m:ℕ) (d:ℝ), 0<C ∧ ∀ i:XSpace.Cirrus.Sample n,
          Entry r i → familiar i∈A → 16 ≤ i.F.p.side.val → i.F.spacing≤1 →
          d ≤ - Real.log i.F.spacing →
            ‖Arrival.Schedule.entries ν Y u M s k i - Arrival.Landing.moondye ν T u s k (familiar i)‖ ≤
              C*( Speed.chip i.F + ( i.F.spacing ^ m )⁻¹*i.F.size^(-mildG) )
    after (n d k:ℕ) (p:Tags G d n) (A:Set (Points n)) (ν r:ℝ) (hr:0<r) (hc:IsCompact A)
            (hp:A⊆ conf n) :
        ∃ C:ℝ, 0<C∧∀ᶠ m in Front,∀ i:Sample n,grab i=m → Entry r i → familiar i ∈ A →
            ‖Speed.forms_t Y K i d k p- Speed.MeasureAt ν Y K T ( familiar i ) d k p‖ ≤ C*Speed.chip i.F
include H h
lemma coverage : Poise N T M := by
 obtain hM:= H.toPosted.toQuoted.toContract.toMission.born; refine ⟨ ?_, fun n u s A k ν r hr ht hp=> Flight.mesh_gain Y u M ν s k T h hM.Taylor ht hp hr,fun n d k p A μ r hr hu hh=> ?_ ⟩
 · intro I W u L Z p ν hK ht; obtain ⟨f,z,H⟩:= tabulate_ge T Y Z M p hK ht hM.Taylor h; exact ⟨ f,z,H, fun s k=> ( H.finFields hK s k ).volume⟩
 exact Notch.Pitch.specialize ( V:=fun x=> Speed.MeasureAt μ Y K T x d k p )|>.mp ( Notch.Pitch.pose μ _ _ _ _ _ _ hM.Taylor h hM.still hM.base k hu hh hr ) -- K
end YM.FVA2.Notch
