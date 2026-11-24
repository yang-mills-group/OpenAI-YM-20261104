import YM.SignedWilsonExpansion.Vault.Bucket
import YM.SignedWilsonExpansion.Vault.Sirup
import YM.SignedWilsonExpansion.Ink.Reams
/-! # Dossier: semantic receipt for these exact sources on Original. Includes the exact older endpoint on both physical programs. All footprints from same reporter/term. Purchased in PartII. One vector of clocks. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.Election.VaultM
open Function Set Filter MeasureTheory Extraction Climb Spec Table Next.UVStress Trace.Pilot PhysMS Maxwell Extra.FD
open RG.Supply PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot Asymptotics
open SignedWilsonExpansion SignedWilsonExpansion.Homes Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank RG PowerSeries SignedWilsonExpansion.Purchases UVClock Schedules
open XSpace Commission Dancer Dancer.Drawing Dancer.Shell Dancer.Fort Dancer.Stitch Dancer.Motif Camera SignedWilsonExpansion.Vault
open Precision XSpace.Normalize WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ WilsonCoeffUV.Cosmos.Polestar
open FVA2 FVA2.Dframe XSpace.Cirrus FVA2.Register
open scoped Topology ContDiff Classical BigOperators ENNReal
open PRAY Fire
open Dancer.Supper SignedWilsonExpansion.Purchases.HalfRoof PurchVoice
open Pert.Asymptotics StageG Exporter.Loans
variable {G:Gauge}{R:PhysicalNext.Repeat.Legato.Run G}{h:G.Simple}{e:Axis}{T₀:Campaign R}{W₀:Campaign.Pillars R T₀}
variable {P:PRAY R h}{D:ℕ}(W:P.Wings D)
universe u₀
variable {σ:OrderS G}{ε:ℝ}(p:PaidP.{u₀} e h ε σ R T₀ W₀) {Z:WilsonPrescription G} {b:Scarf G D}
variable {a:Axis}{ι:Type}{L:Filter ι}{r t:ι→ℝ}
local notation "M₀" => R.family
local notation "P₀" => R.family.path.levels
variable (M:Diary W L r t)
open Diary HeartT HeartT.Spritz Cells Liner.InkP
variable {S:Plans a}{u:Author.CameraT S}{w:ℕ}
namespace Till
abbrev stampK (b:Draft G D S): Fin ( Draft.bill b )→ℕ:= capD ∘ Draft.port b
abbrev listT (d:ℕ) (S:Plans a): Type:= Σ m: Fin ( S.arity+2 ), Fin (m.val+1)→ℕ
abbrev progC (b: Draft G D S) := (⟨ b.1,stampK b ⟩:listT D S)
abbrev rankZ (b: Draft G D S): Fin (Draft.bill b)→ℕ:= fun i=> stampK b i+1
local notation "ϕB" => cck G ∘ r
local notation "ψT" => alongT L P.f
local notation "fT" => reporter W M
-- compiler verifies literal docket forecast.Reports valid turns on fitted names only.
abbrev alongS (L:Filter ι):Filter (Visual ι):= L.curry Extraction.Order.full.fuse
lemma useS (k:ι→ℕ) (X:Visual ι→Prop) (T:∀ᶠ i in L,∀ᶠ p:ℕ in atTop,∀N>k i,X (i,N,p)) (F:Extraction.Order) : ∀ᶠ i in L.curry F.fuse,X i:=by
    refine eventually_curry_iff.mpr (?_); filter_upwards [T] with i hi
    change ∀ᶠ k in atTop, ∀ᶠ j in atTop,_; filter_upwards [F.per.cofinal.eventually hi] with y hy; exact (F.mesh.cofinal.eventually_gt_atTop (k i)).mono fun j hj=> hy _ hj
variable (A: legsP R.family Bool ι) (K:ℕ) (b: Draft G D S) (i:Visual ι)
local notation "ϕ" => Fin (Draft.bill b)
abbrev earL := earD∘ Draft.port b
abbrev emitsσ (z:ι)(ℓ: Bool)(d:ℕ)(x: Sec G d) (N p:ℕ): R.family.label d:= streak ((station W M ℓ) z ) x N p
abbrev votedσ (z:Visual ι) (b:ℕ) (ℓ:Bool)(d:ℕ)(x:Sec G d): R.family.label d:= states R.family d ((rootJ W M ℓ) z.1) ( loN ι z ) ( lop ι z ) ( filing W M b z.1 ) ( emitsσ W M z.1 ℓ d x z.2.1 z.2.2 ) ( A ℓ z d )
abbrev Emit (x: (v:ϕ)→ Sec G ( stampK b v )) := fun v:ϕ=> emitsσ W M i.1 (earL b v) ( stampK b v ) (x v) i.2.1 i.2.2
abbrev Elect (x: (v:ϕ)→ Sec G ( stampK b v )):= fun v:ϕ=> votedσ W M A i K ( earL b v ) ( stampK b v ) (x v)
abbrev finalist (b: Draft G D S) := fun v: Fin (Draft.bill b)=> clothD ( Draft.port b v )
abbrev ballot (q :Scarf G D)(x: Toon G (capD q)): Scarf G D:= ⟨q.1,q.2.1,some x⟩
abbrev pays (u:capBox G ( stampK b )): Draft G D S:= ⟨ b.1, fun v=> ballot ( Draft.port b v ) ( u v ) ⟩
abbrev Bequeath (K:ℕ)(V c:ι→ℕ)(z: Shake (n:=Draft.bill b)): precisionQ (Draft.bill b):= valued R ( stampK b ) (D:=rankZ b) (fun _=> Embroider.zeroC) ( loN ι i ) ( lop ι i ) ( V i.1 ) ( filing W M K i.1 ) ( c i.1 ) ( Elect W M A K b i (finalist b)) ( location R.family.S (reporter W M i.1) ( filing W M K i.1 ) ( lop ι i )∘ z ) -- chamber zero
variable {A}
structure Dossier (S:Plans a)(bX:ℕ)(v:Author.CameraT S) where
    K : ℕ
    V : ι→ℕ
    c : ι→ℕ
    τ₁ : ι→ℝ
    oldT : ℕ
    axes : legsP R.family Bool ι
    supports : bX<K
    aperture : ℕ
    enough : target₀ bX (S.arity+2) D (window W) K ≤ aperture
    stage : AgeRead (window W) K aperture L P₀ r (cck G∘ r) (reporter W M) ( filing W M K ) c V τ₁
    total : Draft G D S→ ℕ
    wise : ∀ b, demandΦ bX (S.arity+2) D (window W) K ≤ total b
    matched : ∀ (b b':Draft G D S), progC b=progC b'→ total b=total b'
    Pre : ℕ
    Out : ℕ
    earns : bX < Pre ∧ bX < Out
    overhead : ℕ
    phaseB : (b : Draft G D S)→ Finset ( Fin (Draft.bill b))→ℝ
    upperB : (b : Draft G D S)→ Finset ( Fin (Draft.bill b))→ℝ
    calls : ∀ᶠ i in L,∀ᶠ s:ℕ in atTop,∀N>filing W M K i,∀p:Slice D,∀t:Bool, ReceivesQ R.family p.val N s ((rootJ W M t) i) ((shapeS W M K t) i) ( axes t (i,N,s) p.val )
    years : ∀ᶠ i in L,V i≤c i∧ c i≤ filing W M K i∧ oldT≤ V i∧ reporter W M i≤ filing W M K i
    issued : ∀ᶠ i in L, ∀ᶠ p:ℕ in atTop,∀ N> filing W M K i,∀ (b:Draft G D S) (x: Shake (n:=Draft.bill b)), Extraction.tag ( sizeP r (reporter W M) R.family.S i ) x ∈ ( S.m b.1 ).F→
        let Y:= needH bX (S.arity+2) D (window W) K
        let s:= (i,N,p)
        Spirits R.family R.metals.O (stampK b) ( Emit W M b s (finalist b) ) ( Elect W M axes K b s (finalist b) ) x Pre overhead Out (phaseB b) (upperB b) Y ( reporter W M i ) (c i) (filing W M K i) (V i) oldT (total b) N p ( Bequeath W M axes b s K V c x ) -- beware Issued(V hides lens)
namespace Dossier
variable {W M} (X:Dossier W M S w u) (hr:Tendsto r L trail)
local notation "zB" => (liftV ( cck G∘r ))
local notation "δB" => (needH w (S.arity+2) D (window W) X.K)
local notation "ℓK" => filing W M X.K
local notation "KK" => liftV ( filing W M X.K )
include X hr
omit X hr in
abbrev shapeS' (b:Draft G D S)(x:Visual ι→ Shake (n:=Draft.bill b)): Prop:= ∀ᶠ v in alongT L P.f, Extraction.tag ( sizeP r (reporter W M) R.family.S v.1 ) ( x v ) ∈ ( S.m b.1 ).F
omit hr
variable {B:Draft G D S}
lemma pumped (b:Draft G D S)(x:Visual ι→ Shake (n:=Draft.bill b))(u:shapeS' (W:=W) (M:=M) b x):
     ∀ᶠ i in alongT L P.f, Spirits R.family R.metals.O (stampK b) (Emit W M b i (finalist b)) (Elect W M X.axes X.K b i (finalist b)) (x i) X.Pre X.overhead X.Out (X.phaseB b) (X.upperB b) (needH w (S.arity+2) D (window W) X.K) ( reporter W M i.1 ) ( X.c i.1 ) ( filing W M X.K i.1 ) ( X.V i.1 ) X.oldT ( X.total b ) i.2.1 i.2.2 ( Bequeath W M X.axes b i X.K X.V X.c ( x i ) ) :=by
     have hP:= (useS (L:=L) ( filing W M X.K ) (fun i=> ∀ z, Extraction.tag ( sizeP r ( reporter W M ) R.family.S i.1 ) z∈ ( S.m b.1 ).F→ Spirits R.family R.metals.O (stampK b) (Emit W M b i (finalist b)) (Elect W M X.axes X.K b i (finalist b)) z X.Pre X.overhead X.Out (X.phaseB b) (X.upperB b) δB (reporter W M i.1) ( X.c i.1 ) ( filing W M X.K i.1 ) ( X.V i.1 ) X.oldT (X.total b) i.2.1 i.2.2 (Bequeath W M X.axes b i X.K X.V X.c z)) ( X.issued.mono fun i hi=> hi.mono fun p hv N ht=> hv N ht b ) (track P.f))
     filter_upwards [hP,u] with i hi hu; exact hi _ hu
include hr p
variable {hD:0<D}
lemma epochs : Epoch L ϕB P₀ ( reporter W M ) ∧ Epoch L ϕB P₀ X.V∧ Epoch L ϕB P₀ ( filing W M X.K ):=by
    let a:= radius_clock h hr; let v:= hr.eventually self_mem_nhdsWithin; refine ⟨ epoch_wave a EventuallyEq.rfl ( X.stage.reporter h a v EventuallyEq.rfl ), epoch_wave a EventuallyEq.rfl ( X.stage.past h ( Liner.gentleLicense R h p.menu ) a v EventuallyEq.rfl ), epoch_wave a EventuallyEq.rfl ( X.stage.file h a v EventuallyEq.rfl ) ⟩ -- need p hierarchy.Frame.R.not P
omit p hr
noncomputable def install (p:PaidP.{u₀} e h ε σ R T₀ W₀) (hr:Tendsto r L trail) : Bucket W r t w S M u :=
    { K:= X.K
      c:= X.c
      o:= X.V
      ν:= X.aperture
      e:= max (demandΦ w (S.arity+2) D (window W) X.K) ( Finset.univ.sup X.total )
      τ:=X.τ₁
      rosterL:= X.stage
      suited:= Nat.zero_le _|>.trans_lt X.supports
      banked:= X.supports
      bought:= X.enough
      spent:= le_max_left ..
      axes:= X.axes
      calls:= fun g s=> useS (L:=L) ( filing W M X.K ) _ ( X.calls.mono (fun i hi=> hi.mono fun f ht N hy=> ht N hy g s ) ) ( track P.f ) -- likely implicit
      budget:= X.total
      escrow:= fun w=> ⟨ X.wise w,( Finset.le_sup (f:=X.total) ( Finset.mem_univ w ) ).trans ( le_max_right .. )⟩
      wears:=by
        intro b x hx d' f' l field Υ; let s:Visual ι→ Shake (n:=Draft.bill b):= liftV x; let μ:= finalist b; let T:= X.Pre; let ψ:= alongT L P.f; let Z:= cck G ∘ r; let X' (i:Visual ι):= Emit W M b i μ; let Y:= fun i=> Elect W M X.axes X.K b i μ
        have he:= ( fst_late L (track P.f).fuse ); have hV:= X.pumped b s ( he.eventually (p:=fun i=> plot r f' x R.family.S i∈( S.m b.1 ).F ) hx ); have hz:= X.epochs (p:=p) hr; have hP:= ( radius_clock h hr ).comp he; have hi:= publicized R.family R.metals.O d' Finset.univ zB ψ X' Y s hP w T X.earns.1 X.Out X.earns.2 ( hz.1.comp_tendsto he ) ( hz.2.1.comp_tendsto he ) R.makes h hV; refine IsLittleO.congr' hi ( hV.mono fun i hi=>?_ ) (?_); · exact congrArg₂ (fun x y:ℂ=>x-y) (fullT R.family d' ( s i ) ( f:=f' i.1 ) ( N:= i.2.1 ) ( p:=i.2.2 ) ( X' i ) R.makes).symm (congrArg (Crops.calcT (↑(regulatorRun R.family i.2.1 i.2.2 (X.V i.1))) ( X.total b )) hi.draught)
        exact EventuallyEq.rfl
    }
end Dossier
end Till
end YM.Integration.Election.VaultM
