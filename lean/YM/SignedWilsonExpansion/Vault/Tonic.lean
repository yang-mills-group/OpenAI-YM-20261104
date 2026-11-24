import YM.SignedWilsonExpansion.Vault.Rosehips
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
open WickFace ProbeB Carbon Sierra Worksheets XSpace.Structure1 Contrast Belle Belle.Path
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book WardBin
variable (u: Rose.Badge)(m:S.hired 2)(V0:Pad 3)(w0:4 ≤ D)(e':Bool)(N:WilsonPrescription G)
local notation "η" => ( fiver G m w0 e' )
local notation "Ξ0" => (testE G 3)
variable (hm:2 ≤ money)(x':ι→Shake (n:=3))(wit:pad0 ( S.Arena 2 m ) r ( reporter W M ) x' L R.family.S)
local notation "μ0" => ( liftV ( needle G ∘ r ) )
variable (ρ :Visual ι→ℝ)(y':IsEquivalent (alongT L P.f) ρ (liftV ( needle G∘r ))) (A₀: EraY) (Y: A₀.eligible ( X.overhead+money ))
variable {p hr} {Ω':MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S':MS.Land.Prescription (Press.portDeck G)}{Y₀:∀d,Rays G d N.scheme.hol} {Q:Speed.Quoted N.scheme N.criterion Ω' S'}
variable {q':Bool} (H:Main.Match N h Ω' S' q')
variable {N X} (p': ∀i,0<r i) (Z':Bucket.Edition (Y₀:=Y₀) Q ( X.install p hr ) p')
open EraY Belle.Buffet
local notation "z0" => (plot r ( reporter W M ) x' R.family.S)
local notation "τ₀" => ( fun _ : Visual ι=> Ξ0 )
-- includes shared price & genuine ruler coordinates at homolog poses.
open Kane.Tilted
local notation "Ψ" => (liftV ( sizeP r ( reporter W M ) R.family.S ))
local notation "zoneℓ" => ( S.Arena 2 m ) -- shadow risk
abbrev realized (i:ι)(y: Points 3) (j:Rose.Badge):= PlotW P.last ( P.W U ) none ( r i ) 4 3 y ( maskE G j )
local notation "η0" => ( fiver G m w0 false )
local notation "W'" => (P.W U)
local notation "Φ'" => ( dress (M:=M) U )
variable (x: Shake (n:=3))
include p X hr wit
lemma scopeY (j: Rose.Badge) : ∀ᶠ i in L,Tendsto (fun p:ℕ×ℕ=> ( charges (X:=X) U m w0 false EraY.ultraviolet x' (i,p) j )) (P.Y:Filter (ℕ×ℕ)) (𝓝 ( realized (P:=P) (r:=r) U i ( z0 i ) j ) ) :=by
    let pV:= physical (p:=p) (hr:=hr) (U:=U) (X:=X) η0 x' wit (fun _=>testE G 3) j; filter_upwards [M.lo,hr.eventually self_mem_nhdsWithin,pV] with i hi hp hu; have pX (x:Points 3)(v: Tags G 4 3): ΩW P.last W' Φ' (earL η0) (stampK η0) r i x v=PlotW P.last W' none (r i) 4 3 x v :=by
        let Z:=Φ' false; have he:Z.home i=r i:=hi; have h' := ( show 0<r i from hp ).ne'; change P.S.classMoment _ (fun _=>4) _ _= P.S.classMoment _ (fun _=>4) _ _; apply congrArg _; funext k; change walk W' (Z.home i) 4 ( Level.Dial 4 (jumpY W' Z r i) ( v k ) )=walk W' (r i) 4 (v k); rw [jumpY,he,div_self h',Real.log_one,Level.flat]; rfl
    rw[pX] at hu; exact hu
local notation "FY" => ( P.Y:Filter (ℕ×ℕ) )
abbrev flash (i:ι)(x:Shake (n:=3)) (q:ℕ×ℕ):ℂ:= shout (X:=X) U m w0 false EraY.ultraviolet x (i,q)
abbrev scopeV (i:ι)(x:Shake (n:=3)):ℂ:= cumul ( realized (P:=P) (r:=r) U i (plot r ( reporter W M ) (fun _=>x) R.family.S i) )
def burst (i:ι)(x:Shake (n:=3)): Prop:= Tendsto (flash (X:=X) U m w0 i x) FY (𝓝 (scopeV (M:=M) U i x))
lemma candle : ∀ᶠ i in L,burst (X:=X) U m w0 i (x' i):=by
    have hw: Continuous cumul:=by unfold cumul; fun_prop
    filter_upwards [eventually_all.mpr (scopeY (X:=X) (p:=p) (hr:=hr) U m w0 x' wit)] with i hi; apply Tendsto.congr' (f₁:=fun (p:ℕ×ℕ)=> cumul ( charges (X:=X) U m w0 false EraY.ultraviolet x' (i,p) )) ( Eventually.of_forall fun q=>( crescent (X:=X) U m w0 false EraY.ultraviolet x' (i,q) ).symm ); exact hw.continuousAt.tendsto.comp ( tendsto_pi_nhds.mpr hi )
omit wit
include Z' Y -- need Z with N maybe can't have U both; ok let independent from U. omit Y
omit Y
variable (Wφ:Pad 3)(φ:Test 3)(f:tsupport φ⊆ interior Wφ.F)(hp:together m Wφ)
lemma stars : ∀ᶠ i:ι in L,∀ x:Shake (n:=3),Extraction.tag ( sizeP r ( reporter W M ) R.family.S i ) x∈ zone zoneℓ → burst (X:=X) U m w0 i x:=by
    let B:= Z'.Wν.paid; have he:Tendsto (sizeP r ( reporter W M ) R.family.S) L (𝓝 0):=by rw [← Z'.keys.1]; exact B.locationH hr
    let Q(i:ι)(_ :ℕ×ℕ)(x:Shake (n:=3)):=burst (X:=X) U m w0 i x; have hu :∀ᶠ i:ι×(ℕ×ℕ) in L.curry FY,∀ x: Shake (n:=3),Extraction.tag ( sizeP r ( reporter W M ) R.family.S i.1 ) x∈zone zoneℓ → Q i.1 i.2 x:= allP _ _ _ he (hr.eventually self_mem_nhdsWithin) Q (fun z hz=> eventually_curry_iff.mpr ( ( candle (hr:=hr) (X:=X) (p:=p) U m w0 z hz ).mono fun i hi => Eventually.of_forall fun k=> hi )); exact ( eventually_curry_iff.mp hu ).mono (fun i hi=>hi.exists.choose_spec)
include hp
local notation "s0" => ( sizeP r ( reporter W M ) R.family.S )
lemma chargedMusic : ∀ᶠ i in L,Tendsto (fun p:ℕ×ℕ=> feesQ φ Wφ ( s0 i ) (fun x=>flash (X:=X) U m w0 i x p) ) FY (𝓝 ( feesQ φ Wφ ( s0 i ) ( scopeV (M:=M) U i ) ) ) :=by
    filter_upwards [stars U m w0 p' Z'] with i hi; have h:0<s0 i:= div_pos (R.family.S.a_pos _) (p' _); let T:= bought Wφ ( s0 i ); let C (c: Shake (n:=3)→Shake (n:=3))(u: Shake (n:=3)→ℂ):= Worksheets.posted Wφ φ ( s0 i ) (u ∘ c); let φ'(x)(q):= flash (X:=X) U m w0 i x q; let Uψ:= scopeV (M:=M) U i
    have he (k:Shake (n:=3)→Shake (n:=3))(hu:∀ x∈T,Extraction.tag ( s0 i ) (k x)∈ zone zoneℓ): Tendsto (fun p=> C k (fun x=> φ' x p)) FY (𝓝 ( C k Uψ )):= by
        exact tendsto_finsetSum T (fun x hx=> show Tendsto (fun q=> cents φ ( s0 i ) x*φ' (k x) q) FY (𝓝 (cents φ ( s0 i ) x*Uψ (k x))) from Tendsto.const_mul _ (hi _ (hu x hx)) )
    refine ( he id (fun x hx=> hp.1 ( appears Wφ h x|>.mp hx )) ).sub ( Tendsto.const_mul _ ( he bp ( fun x hx=>?_ ) ) ); rw [Worksheets.forecast]; exact hp.2 ( appears Wφ h x|>.mp hx )
end Stamp
end YM.Integration.Election.VaultM.Till.Dossier
