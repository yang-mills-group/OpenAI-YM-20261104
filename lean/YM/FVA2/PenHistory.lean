import YM.FVA2.Interface
import YM.FVA2.MixedRates
/-! # Transfer identity for even the calibrated/mixed copies
 All assumptions on covariance, normalization, shift and chart are the same as
 in `IteratedWilsonPrescription`. Keep weights also for all open conditional scales. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Shipment
open RayScatter
open Function Filter Topology Metric Finset PowerSeries
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Blocking FormalOPE.RG10.Sync
open Lattice Gauge Precision Fabric Inherit PertExtension PertExtension.Chart GaussianScore RG InversionTop
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {c f n:Side}{G:Gauge}{S:StepData c f}
variable {P:Inside S.ratio}{t:S.Choices}{H:S.patch.Branches S.kernel G}
local notation "μ"=> tangent G (Blocking.Index S P)
open Source
variable (I:Type) {L: Fabric G n}(F:Cloth L)(J:ChartRatio G)(hJ:LocalRatio J)(w:L.Accounts→PowerSeries ℝ)(hp:∀ i,0< Series.Tested.term ( w i ) 0)(h0:w none=1)
section scenes
variable {B: MS.Local.Physical.Deck G} (D: Warehouse G)
variable {W: Type} [DecidableEq W] (d:W→ℕ) ( y:W→Site n) (A:(i:W)→D.Atom (d i)) (s:Finset W)
local notation "Sκ"=> Track.Seals D y d A
local notation "Yκ"=> Stamp.shafts Sκ s
local notation "dκ"=> Stamp.degrees Sκ s
local notation "µκ"=> Stamp.pre_all Sκ s

def UpM : Ticket (Flats G n):= ∏ i∈s, burn ((Sκ i).slots) ( Sκ i ).stencil -- slots actual.Cost lower.
omit [DecidableEq W] in
lemma sealBurnM (i:W) : X^( Sκ i ).slots * burn (( Sκ i ).slots) ( Sκ i ).stencil = imprintRoot ( Sκ i ).stencil := by unfold burn; apply MultiGauge.Stack.recover; let a:=A i; exact fun j hj=> set_min (D.poised (d i) a) (D.awake ..).low j hj
include F
omit [DecidableEq W] in
lemma ignitionM : X^dκ * UpM D d y A s= imprintRoot Yκ:= by unfold UpM Stamp.degrees Stamp.shafts; rw [ ← prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, rootOfProduct F s _ (fun i _=> (Sκ i).test) ]; simp_rw [ sealBurnM D d y A ]
include h0 hJ
-- pre-log transmission in primitive, same at every horizon.
omit [DecidableEq W] in
theorem manifestedM : purchase F w hp hJ (UpM D d y A s)= Channel.realRead Sκ s := by
    unfold Channel.realRead; rw [ ← diagram F w hp hJ h0 µκ, ← ignitionM F,purchaseX, Stack.drop_mul ] -- exact capsule
omit h0 hJ

-- direct same object characteristic in Fk.read.Origin ray along V.Month metrics permits.
omit hp w F
variable {L': Fabric G c} (T:Cloth L') (hf:Even f.val) (z:W→Site f)(v:Flats G c)
local notation "Ωκ"=> OrbitPlanet.frame P t v
local notation "ρ"=> Track.Seals D z d A
variable (P H t)
include H hf T hJ
omit [DecidableEq W] in
theorem first_stepM : Stack.read v (Broadcast P t J 1 (initialFull G f 1) (OrbitPlanet.billedStep P t H L' T hf) (boost (blankRight P) (UpM D d z A s))) = PowerSeries.mk ( RGComparison.Core16.Lumen.Fk.read Ωκ J (OrbitPlanet.tagAll P) (OrbitPlanet.book P (Stamp.shafts ρ s)) (Stamp.degrees ρ s) ):= by
    have h:OrbitPlanet.distinct (Stamp.shafts ρ s):= OrbitPlanet.distinctProduct _ s (fun i _=> OrbitPlanet.distinct_source (x:=z i) (hp:=D.poised _ (A i))) -- binder names
    rw [ OrbitPlanet.arrival P t H _ _ hJ _ T hf _ h, ← ignitionM (F:=Cloth.inLayer (t:=t) (b:=H) (h:=hf) P T) (D:=D) (y:=z), dragX,map_mul,map_pow,show ∀ v:Flats G c,Stack.read v X=X from fun v=> PowerSeries.map_X _, Stack.drop_mul ] -- type
end scenes
end YM.FVA2.Shipment
namespace YM.FVA2
open Function Filter Topology Metric Finset PowerSeries
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Blocking FormalOPE.RG10.Sync
open Lattice Gauge Precision Fabric Inherit PertExtension PertExtension.Chart GaussianScore RG InversionTop
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n c f:Side} {G:Gauge}

open Shipment
namespace IteratedWilsonPrescription
variable (C0:IteratedWilsonPrescription G n)
local notation "J"=> C0.ratio
local notation "L"=> C0.L
local notation "μ"=> C0.goods
local notation "z"=> C0.z
local notation "hp"=> C0.entitled
local notation "hJ"=> C0.calibrated
local notation "fp"=> C0.pure

variable {B: MS.Local.Physical.Deck G} (D: Warehouse G)
variable {W: Type} [LinearOrder W] (d:W→ℕ)(Λ:(i:W)→ MS.Menus.Acts B (d i)) (P:Lattice.Cover)(c:W→Lattice.Cover) (s:Finset W)
variable (t:MS.Book.Program.Team)(x:ℝ)
local notation "Σκ"=> Track.Crew D B d s
local notation "δ0"=> Channel.coord n P c
local notation "ζ"=> (s:Type) -- weird
-- use Styled sampler as formal.Coupling ℝ series substitution `Clock.rate`. Multiply `Sum`.

def billM : PowerSeries ℝ := ∑ a:Track.Crew D B d s, Track.debt D d Λ x s a * Clock.reprℝ t x (purchase μ z hp hJ (UpM D (fun i=>(a i).1.size) (δ0 ∘ Subtype.val) (fun i=>(a i).2) Finset.univ))

lemma folio_valueM : C0.billM D d Λ P c s t x=Track.ticketRead D n d t x Λ P c s:= by unfold billM Track.ticketRead Track.deckRead; simp_rw [ Shipment.manifestedM μ J hJ z hp fp]
theorem real_folioM (X: MS.Book.Convolve.T ℂ) : MS.Fleet.PhysicalSum G t x n true s c P (Track.request D d Λ t) X ↔ Score.netE ( C0.billM D d Λ P c s t x )=X:= by rw [folio_valueM,Track.finite_bridge D C0.ofEven]

-- post-bare engine coordinate. Sustain validity for all next steps.
end IteratedWilsonPrescription
end YM.FVA2
