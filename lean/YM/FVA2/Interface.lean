import YM.FVA2.Shipment
import YM.FVA2.Tiles

/-!
# `IteratedWilsonPrescription`: coefficients with all step identities and shared unmarked/marked choices

Spelling the current prescription in a record with no quantitative bridge assumptions,
so as to share it with a comparison consumer. Primary definition uses
`T.Cloth` OpenSlots.Pipeline with raising/lowering
insertion degrees before mixing, **including full unmarked conditional denominator**.
Bare thermal phase x=μ-θ; `shipment` costs are unscaled with point orientation;
coordinates in `Masks` may be reexpressed explicitly. `folio_value` reduces the
matter to the same Orbit and PS ticket of the actual MS call (b=true,
`flesh=menus.rent`). Subsequent choice of `A: Land.Prescription` thus selects a
common precomposition/mixing for MS comparison. Normalization of position-scheme
frames on the physical field subquotient remains additional work. This file
concerns one finite regulator at a time, including when repeatedly reached by
AnyProfile.

You may put z weights (bare-step clock) in any formal series as stipulated before
arriving; `1` is the canonical bare choice used for our exact `Fk.read` at the
open top step. `StepData.Choices` fixed *once per step*. Gauges from any trees
of the inversion graph as stipulated. Everywhere, both inserted and unmarked
terms call the same voyage. No relation to a NONquotient `Fk` on a different
StepData demanded or implied. See `FkMoment` for its algebraic connection.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2
open Function Filter Topology Metric Finset PowerSeries
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Blocking FormalOPE.RG10.Sync
open Lattice Gauge Precision Fabric Inherit PertExtension PertExtension.Chart GaussianScore RG InversionTop
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n c f:Side} {G:Gauge}

-- all-order rule.At a SINGLE linked regulator. Same projection across subsets.
-- printable external transformation μ appears below. Optional top weigh via replacing `pure` etc; here require 1.
structure IteratedWilsonPrescription (G:Gauge)(n:Side) where
     ofEven : Even n.val
     L : Fabric G n
     ratio : ChartRatio G
     calibrated : LocalRatio ratio
     goods : Cloth L
     z : L.Accounts → PowerSeries ℝ
     entitled i : 0< coeff 0 ( z i )
     pure : z none=1

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

variable {B: MS.Local.Physical.Deck G} (D: Source.NativeDictionary B)
variable {W: Type} [LinearOrder W] (d:W→ℕ)(Λ:(i:W)→ MS.Menus.Acts B (d i)) (P:Lattice.Cover)(c:W→Lattice.Cover) (s:Finset W)
variable (t:MS.Book.Program.Team)(x:ℝ)
local notation "Σκ"=> Channel.Crew B d s
local notation "δ0"=> Channel.coord n P c
local notation "ζ"=> (s:Type) -- weird
-- use Styled sampler as formal.Coupling ℝ series substitution `Clock.rate`. Multiply `Sum`.

def bill : PowerSeries ℝ := ∑ a:Channel.Crew B d s, Channel.debt d Λ x s a * Clock.reprℝ t x (purchase μ z hp hJ (Up D (d ∘ ( Subtype.val: ↥s→W)) (δ0 ∘ Subtype.val) a Finset.univ))

lemma folio_value : C0.bill D d Λ P c s t x=Channel.ticketRead D n d t x Λ P c s:= by unfold bill Channel.ticketRead Channel.deckRead; simp_rw [ Shipment.manifested μ J hJ z hp fp]
theorem real_folio (X: MS.Book.Convolve.T ℂ) : MS.Fleet.PhysicalSum G t x n true s c P (Channel.request D d Λ t) X ↔ Score.netE ( C0.bill D d Λ P c s t x )=X:= by rw [folio_value,Channel.finite_bridge D C0.ofEven]

-- post-bare engine coordinate. Sustain validity for all next steps.
end IteratedWilsonPrescription
namespace Open
variable {S : StepData c f}{P:Inside S.ratio}{t:S.Choices}{U:Unmasked G f}
variable (J:ChartRatio G)(J0:LocalRatio J)
-- Episode corresponds to SHELTER replot. `RayScatter.digital_ink` for alternative basis without replot.
local notation "Kp"=> Index S P
-- certify every step from any given Commission recursor

def floatD (v: PowerSeries ℝ)(H:(gated P U t v|>.core).RespectsPrice) : Prop:= ∀ (T: Ticket (Flats G f))(I B:Type)(_ : Fintype I) (_:Fintype B)(a:Layout I (Flats G f))(b:Layout B (Flats G c)),
   let e:= Engine J t P a b v U H
   digital b ( Broadcast P t J v U H (boost (blankRight P) T) ) = Route.Bulk.transfer e.joint (Route.replot e.spur (digital a T)) e.vertices ∧
   incline (Update P t J v U H|>.W) ∧ Route.Bulk.income e.joint e.vertices=digital b ((Update P t J v U H).W)
include J0
lemma transmits {v:PowerSeries ℝ}(H:(gated P U t v|>.core).RespectsPrice)(hv:incline U.W): floatD J v H:= by
    intro T I B _ _ a b e; refine ⟨ available J t P a b v U J0 hv H T,funded J0 v hv _,?_⟩
    unfold e Engine; change Route.Bulk.income _ (voltage _ _ _ _) = digital b (Quadratic.uptake _ _ H _) -- Q.Core shift
    rw [Sync.stationed]; exact Sync.revenue H.inner _ _ (OpenSlots.extend P) (threadTo P) _ (pursue P) (tangent G (Index S P)) ( preserve_boost _ (OpenSlots.along J0 v hv))

-- Nonempty of ext canonical normalization with enough covariance witnesses. Maintain Θ..
def certified {n:Side}{L:Fabric G n}(G0:Cloth L)(V:Unmasked G n)(t:L.Cost→PowerSeries ℝ) (h:Commission J G0 V t): Prop := incline V.W ∧ match G0 with
 | .floor _ _ _=> True
 | .inLayer (t:=p) P T=> floatD (P:=P) J (t none) (Exists.choose h) ∧ certified T _ _ (Exists.choose_spec h)

lemma guaranteed {n:Side}{L:Fabric G n}(G0:Cloth L)(V:Unmasked G n)(t:L.Cost→PowerSeries ℝ) (h:Commission J G0 V t) (H: incline V.W): certified J G0 V t h:= by
   cases G0 with| floor=> exact ⟨H,trivial⟩| inLayer P T=> rw [certified]; exact ⟨H,transmits _ J0 _ H, guaranteed T _ _ (Exists.choose_spec h) (funded J0 _ H _)⟩
termination_by structural G0
variable (F:IteratedWilsonPrescription G n)
omit J0 in
theorem protocol (F:IteratedWilsonPrescription G n) : Commission F.ratio F.goods (initialFull G n (F.z none)) (F.z ∘ some) := released F.calibrated ( paidRoot (J:=F.ratio) F.goods F.z F.entitled ) -- returns proof, naming theorem not def
omit J0 in
lemma possible : certified F.ratio F.goods (initialFull G n ( F.z none )) (F.z ∘ some) ( protocol F ) := guaranteed _ F.calibrated _ _ _ _ (OpenSlots.restores _ _)
end Open
-- nontrivial ladders realized on MUCH finer regulators.Allow inscribed tags chosen for all roots.
namespace IteratedWilsonPrescription
variable (P : Patch)(κ:KernelChoices) (H:P.Branches κ G)

def gradeSide (i:ℕ): Side:= ⟨8*P.L.val^i, mul_pos (by norm_num) (pow_pos P.L.property _)⟩
lemma stepSide (i:ℕ): (gradeSide P (i+1)).val= (gradeSide P i).val * P.L.val:= by change (8:ℕ)*P.L.val^(i+1) = 8*P.L.val^i*P.L.val; simp only [pow_succ]; ring
lemma evenSide (i:ℕ): Even (gradeSide P i).val:= ⟨4* ( P.L.val^i ),by change 8*_=4* _+4*_; omega⟩
def stepData (i:ℕ): StepData (gradeSide P i) (gradeSide P (i+1)):= ⟨ P,κ,stepSide ..⟩
def route : (i:ℕ)→ Fabric G (gradeSide P i) | 0=> Fabric.endcap _ (evenSide P 0) | i+1=> Fabric.layer (stepData P κ i) H (Classical.choice (inferInstance : Nonempty ((stepData P κ i).Choices))) (evenSide P _) (route i)

def ticket (i:ℕ) : IteratedWilsonPrescription G (gradeSide P i) where
    ofEven:= evenSide ..
    L:= route P κ H i
    ratio:= Orb.tray G
    calibrated:= Orb.traySpec G
    goods:= Fabric.localTruss _
    z:=1
    entitled _:= by change 0 < coeff (R:=ℝ) 0 1; norm_num
    pure:=rfl

lemma same (i:ℕ) : MS.Orbit.dimT ( Tiles.roof P.L ) i=gradeSide P (i+i*i):= Subtype.ext (Tiles.fullSide ..)
-- no bound on `history`: finite each invocation

def universal (G:Gauge)(i:ℕ)(k:ℝ) (hk:0<k) : IteratedWilsonPrescription G ( MS.Orbit.dimT ( Tiles.roof P.L ) i ) := (same P i).symm ▸ ticket P ( Next.Foundations.kernel G k hk ) ( Next.Foundations.branches G k hk P ) (i+i*i)
end IteratedWilsonPrescription
end YM.FVA2
