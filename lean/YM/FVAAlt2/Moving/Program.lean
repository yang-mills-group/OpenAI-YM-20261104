import YM.FVAAlt2.Moving.Regular
/-!
# Genuine stamps where the local calculus **is read only at assigned finite cutoff**.

These are alternative computations of the same standard $Study.Normal$ approximation. 
 No other operator convention of Frame/Setup.Step. Compat proofs with MS-procured clocks & shifting passport.
 Scope.S.Pl.Response.Field.T. In particular hσ growth may depend entire arity cap but not Frame.Business after
 purchases. At a fixed station finite, higher orders need not realize same price Witness trajectory for W; require only through these finite instructions.
-/
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
variable (F:Calibration.Tent ( ( R.profile Y Z C t ht ).entire )){g:G.ColorIndex} (p s:ℕ) (Λ:X→ℕ) (a:X → Cover)
variable {I:Type}[Fintype I][DecidableEq I](S: Marker.Census I)(i:I) (x:X)
local notation "L"=> sheet F
abbrev spend (x:X)(n:ℕ)(v:Motor B n x) : X→Fin n→ Cover:= fun _ j=> a x+ Lattice.lift (v j)
-- time stamps common before period target requests. Aura logs.
structure Stamp where
    menu : See.Times ( sheet F ) p
    traces(x:X)(n:ℕ)(k:ℕ)(v: Pegs.Motor (R.profile Y Z C t ht) n x): Activation (I:=Fin n) C (Period.Field.LodgeT.instance_real Y Z C R t ht) k S
    laws(x:X)(n k:ℕ)(v:Pegs.Motor ( R.profile Y Z C t ht ) n x): Figure.Course C ( P ) (spend Y Z C R t ht a x n v) ( sheet F ) k i S p menu ( traces x n k v )
variable (h:Notebook (R.profile Y Z C t ht).desk Y G Z g (Rocket.native _) F p)(T:ProgramT.Stamp Y Z C R t ht F p a S i)
local notation "ρ" x:max=> ( terms x ) -- remove
include h
lemma funds : Nonempty (Stamp Y Z C R t ht F p a S i):=by
 have h0:= Sound.flatTop Y Z h
 obtain ⟨U,-⟩:= See.prices L p h0; choose V hw using fun i' n k l=> Figure.universal C Z Y P (spend Y Z C R t ht a i' n l) (sheet F) k i S p U h0; exact ⟨⟨U,V,hw⟩⟩ -- symbols omitted lean variables in implicit.Nonempty etc
-- ABC unprocessed reading. Higher beyond cutoff at Stamp.Scope deliberately zero in R.inputs via packing into WarmRead.
local notation "F!"=> ( Study.ledgerL Y Z C R t ht F Λ a x )
noncomputable def Ink (x:X):Perot.Exhibit (B) x C.family.labels:=fun n v=> Figure.spoken C P L (Λ x) i S p T.menu ( T.traces x n (Λ x) v ) (( B ).stop.choose x)
local notation "vT"=> ( ProgramT.Ink Y Z C R t ht F p Λ a S i T ) -- Θ through.H.P.Price.Prum
lemma coinRead (n:ℕ)(v:Motor B n x)(c t'): Sound.Formal.Told p (( vT x ) n v c t' ) (( F! n v c t')) := by
    intro e he; change coeff e _= coeff e (PowerSeries.mk _); rw [PowerSeries.coeff_mk]; exact Sound.gold Y Z (fromRun C) P (Figure.prop C _ c t') L (Sound.flatTop Y Z h) (Λ x) S i _ _ _ ( T.laws x n (Λ x) v c t' ) e he
omit h
section algebra
variable {A:Lodge.Track X}{v:X}{F': Frames G}{r d:ℕ} {U U':Perot.Exhibit A v F'}{P': FormalOPE.RG10.Position.Plan F'}
def BillingOK (A:Lodge.Track X)(v:X) (p:ℕ) (U V:Perot.Exhibit A v F'):Prop:=∀ n x h k,Sound.Formal.Told p (U n x h k) (V n x h k)
lemma perotE (H:BillingOK A v p U U')(b:Home.Datum (Position.Deck F' d)): Sound.Formal.Told p ( Perot.Raw A v U P' d b ) ( Perot.Raw A v U' P' d b ):= by
   apply Sound.Formal.Told.sum; intro i; refine Sound.Formal.Told.times (Sound.Formal.Told.times ?_ _) _
   exact Sound.Formal.Told.sum (fun j=> Sound.Formal.Told.times (H b.1.n i _ j) (_))
-- intrinsic Progress note.Reader. h inherited. post scope.
variable {T U: Rack F'} {D:Stock F'}
lemma recordWord (h:∀ i, Through p ( T 6 i ) ( U 6 i )) : Through p (Convention T).x (Convention U).x:=by
 have hp:= First.Portray.together_through (p:=T 6) (q:=U 6) h; have hr:= hp 0 ( Nat.zero_le p ); rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_zero_eq_constantCoeff_apply] at hr
 apply RG10.Through.mul ( RG10.Through.refl _); unfold Triangle.deviation; rw [hr]; exact hp.sub (RG10.Through.refl _)
lemma attends (h:∀ i v,Through p ( T i v ) ( U i v )) (w:ℕ) (z:Home.Datum ( Position.Deck F' w )) : Through p (Row T D w z) (Row U D w z):= Carryon.posting (fun _ _ _=>h _ _) z.1 (fun _=>h _ _) z.2
lemma congr (h:∀ i v,Through p ( T i v ) ( U i v )) (w:ℕ) (z: Home.Datum ( Position.Deck F' w )): Through p ( mintRack (Row T D) w z ) (mintRack ( Row U D ) w z):=by
 exact Warp.charges (p:= (Convention (Row T D)).refund ) (q:=( Convention (Row U D)).refund) (attends p h _ _) ( Warp.either ( recordWord p (attends p h 6) ) ) -- field unif warp.either orientation metav
end algebra
local notation "Κ"=> (( Study.Plan C ).stock)
include h
noncomputable def skin (x:X): Rack C.family.labels:= fun i=> takeReal∘ Perot.Raw (B) x ( vT x ) ( Study.Plan C ) i
noncomputable def Alive (x:X): Rack C.family.labels := mintRack ( Row ( ProgramT.skin Y Z C R t ht F p Λ a S i T x ) ( Study.Plan C ).stock )
local notation:max "S₁" k:max=> ( ProgramT.skin Y Z C R t ht F p Λ a S i T k )
local notation:max "S₂" k:max=> ( Study.Rack₁ Y Z C R t ht F Λ a k )
variable (b:ℕ)(v:Home.Datum (Deck C.family.labels b))
lemma skin_paid : Through p ( S₁ x b v ) ( S₂ x b v ):= by intro j hj; unfold ProgramT.skin Study.Rack₁; change coeff j ( takeReal _ )=coeff j ( takeReal _ ); unfold takeReal; simp only [PowerSeries.coeff_mk]; exact congr_arg Complex.re ( ProgramT.perotE p (U:= vT x) (U':= F!) (fun _ _ _ _=>coinRead Y Z C R t ht F p Λ a S i x h T _ _ _ _) v j hj ) -- supply
lemma chosen(x:X):Through p ( ProgramT.Alive Y Z C R t ht F p Λ a S i T x b v ) ( Study.Normal Y Z C R t ht F Λ a x b v ):= by apply ProgramT.congr p (T:=S₁ x) (U:=S₂ x); exact fun b v=> skin_paid Y Z C R t ht F p Λ a S i x h T b v
-- practical stronger τ plot normalization. fromPeriod.Colour
end YM.RegulatorIR.FVAAlt2.Moving.ProgramT
