import YM.SignedWilsonExpansion.Vault.Rocket
/-! # Uniform first correction through Hot. -/
set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 420000
noncomputable section
namespace YM.Integration.Election.VaultM.Till.Dossier
open Function Finset Filter MeasureTheory Extraction Climb Spec Table Next.UVStress Trace.Pilot PhysMS Maxwell Extra.FD
open RG.Supply PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot Asymptotics
open SignedWilsonExpansion SignedWilsonExpansion.Homes Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank RG PowerSeries SignedWilsonExpansion.Purchases UVClock Schedules
open XSpace Commission Dancer Dancer.Drawing Dancer.Shell Dancer.Fort Dancer.Stitch Dancer.Motif Camera SignedWilsonExpansion.Vault
open OPE.Therm Lattice Wilson RG05Readout RG05Readout.Address RG05Readout.Records Marker Cells HeartT HeartT.Spritz
open Precision XSpace.Normalize WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ WilsonCoeffUV.Cosmos.Polestar
open FVA2 FVA2.Dframe XSpace.Cirrus FVA2.Register
open Pert.Asymptotics Logwood HeatS StageG Exporter.Loans
open scoped Topology ContDiff Classical BigOperators ENNReal
open PRAY Fire Diary Dancer.Supper SignedWilsonExpansion.Purchases.HalfRoof PurchVoice
variable {G:Gauge}{R:PhysicalNext.Repeat.Legato.Run G}{h:G.Simple}{e:Axis}{T₀:Campaign R}{W₀:Campaign.Pillars R T₀}
variable {P:PRAY R h}{D:ℕ}{W:P.Wings D}
universe u₀
variable {σ:OrderS G}{ε:ℝ}(p:PaidP.{u₀} e h ε σ R T₀ W₀) {Z:WilsonPrescription G} {u:Scarf G D}
variable {a:Axis}{ι:Type}{L:Filter ι}{r t:ι→ℝ} {M:Diary W L r t}{S:Plans a}
variable {hv:Author.CameraT S}{money:ℕ}(X:Dossier W M S money hv)(b:Draft G D S)
local notation "C₀" => R.family
local notation "Fℓ" => reporter W M
local notation "κ" => filing W M X.K
local notation "S₀" => R.family.path.levels
local notation "LP" => alongT L P.f
open FVA2.Scale Level Dancer.SeatsW Future
local notation "θ" => ( ( liftV ( needle G∘r ) )^money )
variable (hr:Tendsto r L trail) (U:XSpace.Normalize.Store G)(x: ι→Fin (Draft.bill b)→ Cover)
variable (u0:pad0 ( S.m b.1 ) r ( reporter W M ) x L R.family.S)
namespace Stamp
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book WardBin
variable {p hr} {Ω':MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S':MS.Land.Prescription (Press.portDeck G)} {Q':Initialize G}{Y₀:∀d,Rays G d Q'.hol} {T:Rose.Pick U} {Q:Speed.Quoted Q' T Ω' S'}
-- preserve budget after *normalization*, flesh & pulp crop ANY power.
open MarqueQ.Crops
open FVA1Physical.Exchange.F6Regular
variable (p hr) (v:Visual ι→ Shelves b)(V: funded (P:=P) (L:=L) b v) (s: Finset (Fin ( Draft.bill b )))
abbrev harborQ (i:Visual ι):= doors C₀ (stampK b) (Fℓ i.1) (κ i.1) i.2.2 (x i.1)
abbrev ledgerQ (i:Visual ι):= X.portionW b ( note (M:=M) b U ( fired b v s ) i )
abbrev wills (i:Visual ι) := priceV C₀ X.overhead i.2.2 (κ i.1) ( ledgerQ X b U v s i )
abbrev horizonT (i:Visual ι) : Prop := Tilted C₀ ( plume X b U x v i s ) ( harborQ X b x i ) i.2.1 (wills X b U v s i)
include p hr V
lemma logged : (fun i=> wills X b U v s i)=O[ LP ] payD (liftV ( cck G∘r)) X.overhead:=by
    have he:=X.epochs p hr; let f:= fst_late L ( track P.f ).fuse; let v0:= note_salary (M:=M) b hr U _ ( clip b v s V ); exact ((( wagesH _ _ _ v0 ).mul ( money_curve (( radius_clock h hr ).comp f) ( he.2.2.comp_tendsto f ) X.overhead ).1 ).congr' (EventuallyEq.rfl) ( Eventually.of_forall fun i=> one_mul _ )) -- weight not inferred?
include u0 hr p V
local notation "Ζ0" => (alongT L P.f)
lemma thermo_t : ∀ᶠ i in LP,horizonT X b U x v s i:=by
    filter_upwards [( cumulative p X b hr U x u0 _ ( clip b v s V )|>.2 ).lit, gearsEquiv p X b hr U x u0 v s] with i hi hu; unfold horizonT; rw[hu.2]; exact hi -- huge
local notation "Ω0" => (liftV (cck G∘r))
lemma flame (k e:ℕ)(hm:(X.overhead:ℝ)+((e:ℝ)+1)*(-1)< k*(-1/2:ℝ)) : (fun i=> priced X b U x v s e i- mash X b U x v i s)=o[LP] ( (mark Ω0)^k ) :=by
    let he:= thermo_t p X b hr U x u0 v V s; have hP:= he.mono fun i hi=> hi.tax e; refine (IsBigO.of_norm_eventuallyLE hP).trans_isLittleO (?_); refine HeatS.endsP R.makes.wilson (( radius_clock h hr ).comp ( fst_late L (track P.f).fuse )) (( X.epochs p hr ).2.2.comp_tendsto ( fst_late L ( track P.f ).fuse )) ( legS (L:=L) (P:=P) ( filing W M X.K ) |>.mono fun i hi=> hi.le ) (harborQ X b x) (Eventually.of_forall fun i=> boundD C₀ (stampK b) ( x i.1 ) univ ( Fℓ i.1 ) ( κ i.1 ) (i.2.2) ) (by push_cast; exact hm ) ( logged p X b hr U v V s ) -- hp infer
lemma litA (e:ℕ)(h:X.overhead+money≤e): (fun i=> priced X b U x v s e i -terminalU X b U x v s i)=o[LP] θ:=by
    have he:( ( X.overhead:ℝ )+(money:ℝ) ) ≤ e:= by exact_mod_cast h
    have ŧ: ( ( X.overhead:ℝ ) + ( (e:ℝ)+1 )*(-1) < (money:ℝ)*(-1/2:ℝ) ):=by linarith [show (0:ℝ)≤ money from Nat.cast_nonneg _]
    let P₀:= prorates p X b hr U x u0 v V s; exact (( flame p X b hr U x u0 v V s money e ŧ ).add ( P₀.phase.add P₀.oldest ) ).congr_left fun i=> by change _-_+(_-_+(_ - _))=_; abel -- syntax
/-- All-slot realizations of one and the same financed W-block on this paid shelf.
 Ret no requirement shrink k ahead. Later `eligible` enforces.
-/
inductive EraY where
  | ultraviolet
  | crop
  | posed
  | oldest
  | newer
  | ret (k:ℕ)
namespace EraY
variable (a:EraY)
def eligible (a:EraY)(b:ℕ): Prop:= match a with | ret k=> b ≤ k∧ 0<k | _=> True
-- same temperature. any mesh. no renormalization trick.
noncomputable def billT (i:Visual ι) : ℂ:= match a with
        | ultraviolet => nude (M:=M) b U x v i s
        | crop => mash X b U x v i s
        | posed => terminalU X b U x v s i
        | oldest => coin X b U x v i X.oldT s
        | newer => coin X b U x v i ( X.V i.1 ) s
        | ret k=> priced X b U x v s k i
omit p hr u0 V
lemma billQ (xQ:ι→ Shake (n:=Draft.bill b))(vs:x=xQ)(i:Visual ι) : billT X b U x v s a i=billT X b U xQ v s a i:=by rw [vs]
lemma localB (xQ:ι→ Shake (n:=Draft.bill b))(i:Visual ι)(vs:x i.1=xQ i.1) : billT X b U x v s a i=billT X b U xQ v s a i:=by
    cases a with
    | ultraviolet => exact congr_arg ( fun t=> natureL R.family (stampK b) t ( Nt (M:=M) b U v i ) (Fℓ i.1) i.2.1 i.2.2 s ) vs
    | crop => exact congr_arg ( fun t=> shelterK R.family (stampK b) t ( Kt X b U v i ) (Fℓ i.1) i.2.1 i.2.2 (κ i.1) s ) vs
    | posed => exact congr_arg ( fun t=> calcT (↑(regulatorRun C₀ i.2.1 i.2.2 ( X.V i.1 ))) (X.total b) (Crystal C₀ R.metals.O ( stampK b ) (Kt X b U ( fired b v s ) i) X.χP i.2.1 i.2.2 (Fℓ i.1) (κ i.1) ( X.V i.1 ) t) ) vs -- orient calcT namespace
    | oldest => exact congr_arg (fun t=> born₀ C₀ (stampK b) t (Kt X b U v i) (Fℓ i.1) i.2.1 i.2.2 X.oldT (κ i.1) s ) vs
    | newer => exact congr_arg (fun t=> born₀ C₀ (stampK b) t (Kt X b U v i) (Fℓ i.1) i.2.1 i.2.2 ( X.V i.1 ) (κ i.1) s ) vs
    | ret k=> exact show priced X b U x v s k i=_ from congr_arg (fun t=> let J':= doors C₀ ( stampK b ) ( Fℓ i.1 ) (κ i.1) i.2.2 t; let y:= stemK C₀ (stampK b) t (Kt X b U v i) (Fℓ i.1) i.2.1 i.2.2 (κ i.1) s; Logwood.Slate ( originalExterior R.family.path i.2.1 i.2.2 (κ i.1) J' ) (remit J' (R.family.path.rep i.2.1 i.2.2 (κ i.1)) y k)) vs -- need `exact`
include p hr V u0
lemma price (y:eligible a ( X.overhead + money )) : (fun i=> billT X b U x v s a i-terminalU X b U x v s i)=o[ LP ] θ:=by
     let z:= prorates p X b hr U x u0 v V s; cases a with
     | ultraviolet => exact z.pays -- signature inspect
     | posed => exact (isLittleO_zero ..).congr_left (fun i=> ( sub_self _ ).symm)
     | crop => exact ( z.phase.add z.oldest ).congr_left fun i=> sub_add_sub_cancel ..
     | oldest => exact z.oldest
     | newer => exact z.newest
     | ret k=> exact litA p X b hr U x u0 v V s k (y.1)
end EraY
end Stamp
end YM.Integration.Election.VaultM.Till.Dossier
