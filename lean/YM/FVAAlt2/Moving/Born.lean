import YM.FVAAlt2.Moving.Program
/-!
# Stamps & requests across Horizon
Final form of CheckG inputs by one real Reader. Doesn't depend
 on $setup nuisance even with infinite-horizon normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Moving.ProgramT
open Function Set Filter MeasureTheory Topology
open Lattice Precision RG PhysicalNext.Repeat.Legato Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field Sound CalendarT Pegs
open MS MS.Land MS.Menus MS.Dial MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open Integration RunFormalChain Pipeline Pipeline.See Figure
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles YM.FVAAlt2.Home YM.FVAAlt2.Home.Report
open Labels Extra.FD Maxwell Source Extraction FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop Perot Study
open RG10 RG10.Position RG10.Carryon YM.FVAAlt2.Moving.Budget
open PowerSeries (C coeff constantCoeff)
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{K:KernelChoices}{X:Type}
variable (Y:Oracle.Program K)(Z:∀ B:Patch,B.Branches K G)(C:Run G)(R:Lodge.Contract C Y Z) (t:X→ℕ)(ht:∀ x,R.floor Y Z C ≤ t x)
local notation "B"=> (R.profile Y Z C t ht)
local notation "P"=> (Period.Field.LodgeT.instance_real Y Z C R t ht)
local notation "Γ"=> C.family.path
local notation "Φ"=> Study.Plan C
set_option quotPrecheck false
variable (F F':Calibration.Tent ( ( R.profile Y Z C t ht ).entire )){g g':G.ColorIndex} (p s:ℕ) (Λ:X→ℕ) (a:X→ Cover)
variable (h:Notebook (R.profile Y Z C t ht).desk Y G Z g (Rocket.native _) F p) (h':Notebook ( R.profile Y Z C t ht ).desk Y G Z g' ( Rocket.native _ ) F' s)
variable {I:Type}[Fintype I][DecidableEq I](S: Marker.Census I)(i:I) (x:X)
variable (hG:G.Simple)(T:ProgramT.Stamp Y Z C R t ht F p a S i) (T':ProgramT.Stamp Y Z C R t ht F' s a S i)
variable {N: Drivers}(D:Patience ( Study.Plan C ) N)
local notation "L"=> sheet F
variable (μ:ℝ) {J':Booked (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified)} {H:MS_Data G J'} (τ:MS.Land.Prescription (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified))(hT:Top.Output C.metals.O (Study.Plan C) H τ μ)
variable (W:∀ i:ℕ,Matrix ( RG10.Position.Deck C.family.labels i ) ( RG10.Position.Deck C.family.labels i ) (PowerSeries ℝ))
    (he:Mass.Framed (Study.Plan C) D W)
variable (d:ℕ) (v:Home.Datum (Deck C.family.labels d))
section Truth
-- coherence. assigned through p resources
include h h' hG
lemma loyal (e:ℕ)(he:e≤p)(hs:e ≤ s) : Through e ( Study.Rack₁ Y Z C R t ht F Λ a x d v ) ( Study.Rack₁ Y Z C R t ht F' Λ a x d v ):=by
 intro k hk; unfold Study.Rack₁; simp_rw [ Function.comp_apply,takeReal,PowerSeries.coeff_mk]; apply congr_arg; refine ProgramT.perotE e ?_ v k hk
 let U:= Study.ledgerL Y Z C R t ht F Λ a x; let U':= Study.ledgerL Y Z C R t ht F' Λ a x
 intro n b d t' k hk
 change coeff k ( Figure.perRead _ _ _ _ _ _ _ _ _ )= coeff k (Figure.perRead _ _ _ _ _ _ _ _ _ ); unfold Figure.perRead; -- use component fact w.Anchor. κ.Frame.Hold.
 have hl:= Sound.recognizes Z (fromRun C) P ( Figure.prop C (ProgramT.spend Y Z C R t ht a x n b) d t' ) ( sheet F ) (Λ x) (sheet F') ( Figure.prop C (ProgramT.spend Y Z C R t ht a x n b) d t' ) ( Calibration.recognized (B).desk Y G Z g (Calibration.shrinks _ _ _ _ _ h he) (Calibration.shrinks _ _ _ _ g (Calibration.coloring _ _ _ _ g' h' hG g) hs) ) ((B).stop.choose x) rfl k hk
 rw [Sound.money, PowerSeries.coeff_mk,Sound.money,PowerSeries.coeff_mk] at hl; simp_rw [ PowerSeries.coeff_mk ]; exact congr_arg Complex.ofReal hl
noncomputable abbrev sourceRead x:= ProgramT.Alive Y Z C R t ht F p Λ a S i T x
-- preserves normalization/coupling flats EXPECT branches through min
lemma established (e:ℕ)(he:e≤p)(hs:e ≤ s) : Through e (ProgramT.sourceRead Y Z C R t ht F p Λ a S i T x d v ) ( ProgramT.sourceRead Y Z C R t ht F' s Λ a S i T' x d v) :=by
 have ht'(k)(hk:k≤e) := ProgramT.congr (T:=Study.Rack₁ Y Z C R t ht F Λ a x) (D:=(Φ).stock) e (U:=Study.Rack₁ Y Z C R t ht F' Λ a x) (fun d' v=> loyal Y Z C R t ht F F' p s Λ a h h' x hG d' v e he hs) d v k hk
 intro k hk; exact (chosen Y Z C R t ht F p Λ a S i h T d v x k (hk.trans he)).trans ( ( ht' k hk ).trans (chosen Y Z C R t ht F' s Λ a S i h' T' d v x k (hk.trans hs)).symm )
end Truth
local notation "A"=> ProgramT.Stamp Y Z C R t ht F p a S i
noncomputable def Matter (x:X): Rack C.family.labels := fun d=> Home.mix ( ProgramT.sourceRead Y Z C R t ht F p Λ a S i T x d ) ( W d )
variable (l:Filter X)[l.NeBot] [l.IsCountablyGenerated]
variable (hV:Tendsto t l atTop) (Hq:∀ x,p≤t x)(hx:Study.Holding Y Z C R t ht F p τ μ Λ l) (hv:(R.profile Y Z C t ht).VenueT a)
include hG h he hT hV hx Hq hv
lemma dataLimit (hp:0<p) : Nice p l (fun x=> ProgramT.Matter Y Z C R t ht F p Λ a S i T W x d v ) ( mix ( (Convert.f ( Study.Plan C ) μ H ).charge ∘ Home.Report.science μ H C.family.labels d ) ( Mass.ζfinal ( Study.Plan C ) μ H d ) v ):=by
    apply ( Study.checkG Y Z C R t ht F p μ Λ a l hV hG τ hT h Hq hv hx hp N D he d v ).edit; intro w; apply RG10.Through.symm; exact Sync.send (hP:=fun t'=> ProgramT.chosen Y Z C R t ht F p Λ a S i h T d ⟨v.1,t'⟩ w) (hK:= fun _ _=> Through.refl _) v.2 -- Through namespace?
end YM.RegulatorIR.FVAAlt2.Moving.ProgramT
