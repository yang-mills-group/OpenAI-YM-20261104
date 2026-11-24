import YM.FVAAlt2.Mass.Choice
import YM.FVAAlt2.Convert.Stages
/-!
# Position-WilsonX to MS, on the specified inversion regulator
Summarize the supplier results to date.

Notation: `Pose Plan.begins` is the still unnormalized REAL moment, i.e. unnormalized as to prescription of operators and coupling. Includes the partition (vacuum) normalization. Wilson **physical constructed bare columns** from the `S,H` Launch (geometry.W_N plus $g_N^{-slot}$, with engineering power separated in `Lobby`), not formal representatives recovered from the MS answer. Requirement here any one frozen Plan as in RG10 with the PP Loft (full orthogonal lift on free symbols) and coherent official test sets (both supplied choices). No hypothesis identifying those bare columns with cubic-calibration probe prescription on Pert.Full.

`Room.stage` includes genuine cutoff PhysicalSum/Dial comparisons with `Lobby.WilsonPoint`,
 with uniform error & convergence in point shops before physical position conversion. Rate there is
 `a^mildG` on every Uses shape, mixed correction BEFORE estimating. Contains `steps_go` for the specific constant-L presentation of position scheme used (theorem actually for any fixed positive q>1, e.g. arbitrarily large powers of 3). Includes regulator Peal/frame solve. NOT estimating the parent `ActualDensity` or using it to compute perturbative coefficients. No diagonal limit in variables `(q,n)` **asserted** here.

`Y`-witness (Drivers,Patience) determines `Plan.Yield`. `Framed P Y Z`:
 the `I+strict-height-lowering corrections` with real H/Upright/unit,
 horizontal weight-horizon-compatible, uniquely fixed by simultaneous scaling behavior on the continuum **Wilson** arrays. Agrees with mass-independent `Passe.book`/`Rails.adjust` also if using the stronger requirements (see `Mass.rail_form`). This does not compare perturbative N's where different milk-ticket covariantization choices are made; doesn't compute extra beta/gamma from MS. $ζfinal$ fields exactly preserve engineering weights (not saying no rank/slot mix). In all theorems `Y.ages` and `q Side` use positive integers per source. Need separate suppliers for (a) local Fk germs/unit steps, and (b) final quantitative estimates if working on other e.g. moving-block or submesh scopes. And no assertions on OPE (closure with exterior not proved here).

Read e.g. `Billing.topMatch` (for the older LitBook), `Lobby.top_comparison` & `paysHere` & `Choose`: the latter unifies `Tide.removePl`/`LPT_to_MSPl` through **the same** engine, not employing Legacy/simpleL.
 This is the match to the specified Lean reference: no assertion that the Legacy moments agree with it or that changing its defining convention (e.g. momentum cutoff profile or dimensional lift) wouldn't affect positive coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Top
open Finset Filter Set Function Lattice
open Precision Labels Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10 RG10.Position RG10.Position.Grade RG10.Gazebo RG10.Carryon
open PertExtension PertExtension.Chart PertExtension.Position PertExtension.Position.Triangle
open MS MS.Land MS.Book MS.Menus MS.Fleet MS.Dial MS.Local.Physical
open Home Home.Report Matrix Home.Profiles Convert Mass
open PowerSeries (C coeff constantCoeff)
open scoped Topology BigOperators PowerSeries ContDiff Classical Matrix
variable {G:Gauge}{F:Frames G}{d k m:ℕ}(Q:ChartRatio G)(hQ:LocalRatio Q)
variable (P: RG10.Position.Plan F)(hg:G.Simple)(hO:Official P.stock)(hP:P.liftOff=LoftPP F)
local notation "B"=> seats P.liftOff P.certified
local notation:max "V_" n:max=> RG10.Position.Deck F n
local notation "L"=> Lobby.Table (nativeR P) B
set_option quotPrecheck false
variable {A:Booked (seats P.liftOff P.certified)} (X:MS_Data G A)(Ξ:Prescription (seats P.liftOff P.certified))(μ:ℝ)
local notation "κM"=> f P μ X
local notation:max "Ζ" i:max=>ζfinal P μ X i
local notation "Qξ"=> Launch (F:=F) L X Ξ
structure Output (μ:ℝ) : Prop where
    draw : Launch (F:=F) (Lobby.Table (nativeR P) (seats P.liftOff P.certified)) X Ξ
    regular (I W:Type)(_ : LinearOrder W)(_ : Fintype W)(T:Trial I W)(l:Filter I)(p:W→MS.Rake.Label (seats P.liftOff P.certified)): Uses T l μ→ Lobby.RangePl (nativeR P) X Q Ξ W I T l μ p
    hot : Peaked P X μ
    proper : coeff 1 ( f P μ X ).x=1
    credit (W:Drivers): Patience P W
    exactL (q:Side)(hq:1<q.val)(i:ℕ): ∀ᶠ m:ℕ in atTop, Row ( employed P q m μ Ξ ) P.stock i=rates (X:=Ξ) μ q P m i
    yieldL (W:Drivers)(q:Side)(hq:1<q.val)(d:ℕ)(v:Datum (RG10.Position.Deck F d)) (C:Patience P W): AlignSeries atTop (fun i=> RG10.Position.Plan.collect F P q i d v) (C.Yield v) -- need `d` binder
    tilt (W:Drivers)(C:Patience P W): ∃! N,Framed P C N
    funds (d:ℕ) : Layer ( Deck.price F d ) ( Mass.ζfinal P μ X d ) ∧ Weight ( Mass.ζfinal P μ X d ) -- det certified
    tower {d k:ℕ}(h:d≤k): ( Mass.ζfinal P μ X k ).submatrix ( Deck.climb F h ) ( Deck.climb F h )= Mass.ζfinal P μ X d
    msbar (W:Drivers)(C:Patience P W)(d:ℕ) {Z:∀ i:ℕ,Matrix ( RG10.Position.Deck F i ) ( RG10.Position.Deck F i ) fps} (h:Framed P C Z): CheckG C Z d=mix (( f P μ X ).charge ∘ science μ X F d) ( Mass.ζfinal P μ X d )
-- controller existence (not essential to quantified output). powers of 3 possible.
private def ind (i:ℕ): Side:= ⟨2*i+3,by omega⟩
private lemma ripe : Tendsto ind atTop atTop:=tendsto_atTop.mpr (fun i=> ( eventually_ge_atTop i.val ).mono fun j hj=> by change i.val ≤ 2*j+3; omega)
def age : Drivers where
 ages:= Filter.map ind atTop
 ne:= inferInstance
 cofinal:= ripe
 big:= eventually_map.mpr (Eventually.of_forall (by intro i; change 1<2*i+3; omega))
 odd:= eventually_map.mpr (Eventually.of_forall (by intro i; change Odd (2*i+3); exact ⟨ i+1,by ring⟩ ))
include hQ hP hO hg
theorem customer (H:Qξ): Output Q P X Ξ μ:= by
 refine ⟨ H, fun I W _ _ T l w h=> Lobby.pays_all Q (nativeR P) Ξ w X hQ h hg H.high,peal_hot P hP hQ μ X hg hO H.money, funding_one P hP hQ Ξ μ X hg hO H, horizon_paid P hP hQ Ξ μ X hg hO H, fun q h i=>visible μ P Q hg hQ H q h hO i, fun W q h d v C=> steps_go P hP C Q hQ hg μ X Ξ H q h v, fun W C=>Mass.workflow P C Q hP hQ hg μ X H , fun i=>⟨ tile_layer, ( paidZX P (horizon_paid P hP hQ Ξ μ X hg hO H age ) μ X ).2 ⟩, fun {_ _} h=> ζ_tower P (horizon_paid P hP hQ Ξ μ X hg hO H age ) μ X h, fun W C i {Z} HZ=> Mass.equality P C Q hP hQ hg μ X H HZ ⟩

-- canonical choices. `horizon` ℝ-real position arrays of `Plan.begins`,
-- no requirement of a projective analytic background other than the common Hol germ of those stencils.
theorem choose_inputs : ∃ A:Booked B,Spect F A ∧ ∀ X:MS_Data G A,∃ Ξ:Prescription B,∀ μ:ℝ, Output Q P X Ξ μ:= by
 obtain ⟨K,hK,H⟩:= seats_launch P hg -- inspect
 exact ⟨K,hK,fun X=> let ⟨Ξ,hΞ⟩:= H X; ⟨ Ξ, fun μ=> customer Q hQ P hg hO hP X Ξ μ hΞ ⟩⟩
-- arbitrary concrete S supplier with Official (using Gauge.Check).
omit hQ hO hP
variable {H:Source.Hol G} (R:Lobby.Registry F H)
private def dummy_stock (F:Frames G): Stock F:= fun _=> ⟨ ⊥,∅,0, 0,0⟩
def outdoor (H:Source.Hol G) (R:Lobby.Registry F H) : Plan F:= appoint ⟨ R.use,H,R.owns,R.bid,LoftPP F,readyPP (F:=F),dummy_stock F ⟩
theorem admitted : Official (outdoor H R).stock∧ ( outdoor H R ).liftOff=LoftPP F∧ Profiles.nativeR (outdoor H R) = R:=
 ⟨(host _ hg ).1,rfl,rfl⟩
include hQ
-- Existential package.Ref.Pass.H. Use this one before requests -- not per arity/per phase.
theorem in_room : let P := outdoor H R
    ∃ A: Booked (seats P.liftOff P.certified),∃ (X:MS_Data G A)(Ξ:Prescription (seats P.liftOff P.certified)), ∀ μ:ℝ, Output Q P X Ξ μ:= by
 obtain ⟨he,hv,-⟩ := admitted hg R; obtain ⟨A,h,X⟩:= choose_inputs Q hQ _ hg he hv; obtain ⟨Z⟩:= bookedMS A; exact ⟨A,Z,X Z⟩
end YM.FVAAlt2.Top
