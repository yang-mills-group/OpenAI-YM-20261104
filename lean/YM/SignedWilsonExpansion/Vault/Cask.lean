import YM.SignedWilsonExpansion.Vault.Cordial
import YM.Integration.WilsonOriginalGeneralRosterHomeReturn
import YM.Integration.WilsonMovingForkTerminalFile
import YM.Integration.WilsonReflectedMixedIntrinsicAxis
/-! # Choose real dossier, purchase all on phase calendar f. Front sale includes exact msgs. -/
set_option autoImplicit false
set_option maxHeartbeats 310000
set_option maxRecDepth 4000
noncomputable section
namespace YM.Integration.Election.VaultM.Till
open Function Finset Set Filter MeasureTheory Lattice RG Wilson Source Labels Extra.Histories -- Motion
open Extraction Table Spec Trace.Pilot PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalGeneralRosterFare (rotation debit)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonMeasuredPublicEntranceTransferSubmitted (vector)
open WilsonMeasuredPublicEntranceTransferWord (field price)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker Cells HeartT HeartT.Spritz
open WilsonReflectedPublicOrientedFaces (displayed)
open PRAY
open SignedWilsonExpansion Homes Purchases UVClock Schedules StageG Camera SignedWilsonExpansion.Vault Asymptotics
open XSpace FVA2 FVA2.Register Dancer Dancer.Fort Dancer.Stitch
open WilsonOriginalGeneralRosterUnion (Row need request)
open WilsonOriginalGeneralRosterFile (Issued)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonOriginalGeneralRosterUnionReturn (Returned)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open WilsonReflectedPublicStationFare (station)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open Cordial Pane PRAY.Wings
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{R:PhysicalNext.Repeat.Legato.Run G}{h:G.Simple}{e:Axis}{T₀:Campaign R}{W₀:Campaign.Pillars R T₀}
variable {P:PRAY R h}{D:ℕ}(W:P.Wings D)
universe u₀
variable {σ:OrderS G}{ε:ℝ}(p:PaidP.{u₀} e h ε σ R T₀ W₀) (Z:WilsonPrescription G)
variable {a:Axis}{ι:Type}{L:Filter ι}{r t:ι→ℝ} {P':Plans a} (U: Author.CameraT P')
local notation "C₀" => R.family
abbrev adjoint (w:Draft G D P'): Fin (Draft.bill w):= ⟨0,by dsimp[ Draft.bill ]; omega⟩
variable (b:ℕ)
abbrev docket (w:Draft G D P') : Row ( Scarf G D ) := ⟨ w.1.val+1,Nat.zero_lt_succ _, Draft.port w,b,U.test w.1 ⟩ -- check cast Fin.nat
abbrev MaskW (s:Scarf G D) (w:Draft G D P') := ∃t,Draft.port w t=s
abbrev εAs := fun x:Scarf G D=> cleanT x
variable (M:Diary W L r t)
abbrev reserveW (X:Scarf G D→ℕ) := depth ((2*(univ.sup (need ( SlotX ) X ( docket U b ))+1)+ ∑ i,X i)+1) (width W.T 1) D
abbrev tuitionW (X: Scarf G D→ℝ):= max 1 (4*∑i,X i)
abbrev powerW (X:Scarf G D→ℕ):= (∑i,X i)+WilsonAddressedMixedRawTrial.power W.T 1 ( reserveW W U b X ) D
abbrev matrixW (_u:P.Wings D): Type:=∀ _N _p:ℕ,(i:Scarf G D)→ Bool→ (R.family.label (capD i)≃ₗ[ℂ] R.family.label (capD i))
abbrev lending (W:P.Wings D)(x:ι→ matrixW W): legsP R.family Bool ι :=fun s i d=> if h:d≤D∧ 0<d then x i.1 i.2.1 i.2.2 ( carryT d h.2 h.1 none s ) true else LinearEquiv.refl .. -- wing.
open Diary
structure Barrel (X:Scarf G D→ℝ)(E:Scarf G D→ℕ) (due base u v:ℕ) (A:matrixW W)(i:ι) :Prop where
    returned : ∀w:Draft G D P',∃j:ℕ,v≤j ∧ j+2≤reporter W M i∧Returned P.last W.book ( fieldW W Z ) (ρ:=houseP W M i) (d:=SlotX) ( Draft.port w ) (fun _=> true) (fun _=> true) A X E (tuitionW X) (powerW W U b E) 1 due
      (reporter W M i) (filing W M (reserveW W U b E) i) base j u v (request E ( docket U b w )) b (U.test w.1) (r i)
abbrev VaultW (X:Scarf G D→ℝ)(E:Scarf G D→ℕ)(due:ℕ):Prop:=∀ lo:ℕ,∃ (base u v j:ℕ),lo≤base∧base≤u∧ u<v∧ j≤u∧RG16.Literal.Stop C₀ 0 j u∧∃ A:ι→matrixW W, ∀ᶠ i in L,Barrel W Z U b M X E due base u v ( A i ) i -- locate Stop
include p
lemma barrel (d':0<D) (rP:Tendsto r L trail) : ∃ due≥D+3,∃ X:Scarf G D→ℝ,∃ E:Scarf G D→ℕ,VaultW W Z U b M X E due:=by
     classical
     letI : Nonempty (Scarf G D):= ⟨ Draft.headR d' false ⟩; obtain ⟨due,ht,hP⟩:= litMarket W p Z d'; have pr:= WilsonMeasuredPublicEntrancePanelSchool.received P.last hP; have grant:=WilsonOriginalGeneralRosterHomeUnion.original P.last W.book ( fieldW W Z ) p.paid p.gear.1 p.gear.2.1 P.bliss pr
     obtain ⟨X,E,one,hl⟩:= WilsonOriginalGeneralRosterHomeReturn.original P.last W.book ( fieldW W Z ) P.pillar P.bliss p.receiptsP.2 grant; refine ⟨ due,ht,X,E,fun lo=> ?_⟩; obtain ⟨base,j,u,y,v,LB,bj,ju,uv,yv,st,-,pred⟩:= hl (Draft G D P') ( docket U b ) 1 lo
     have hh:∀ᶠ i in L, ∃A,Barrel W Z U b M X E due base u v A i:=by
         filter_upwards [M.allHomes W d',rP.eventually pred,rP.eventually ( annex (I:= Scarf G D) W )] with i hi hj hp; let ρ:= houseP W M i; obtain ⟨A,-,ha⟩:= hj ρ ( hp _ hi ) hi.2; refine ⟨A,⟨fun w=>?_⟩⟩; obtain ⟨z,h,w',u⟩:= ha w; obtain ⟨t,ht⟩:= hi.2; have hx:= (hp _ hi t).2; rw [ ht ] at hx; exact ⟨z,h,w',u _ le_rfl hx _ _⟩
     let A (i:ι): matrixW W := if h:∃A,Barrel W Z U b M X E due base u v A i then h.choose else fun _ _ _ _=> LinearEquiv.refl ..; refine ⟨ base,u,v,j,LB,bj.trans ju,uv,ju,st,A,hh.mono fun i hi=> (?_) ⟩; unfold A; rw[dif_pos hi]; exact hi.choose_spec
omit p
lemma reserve_large (z:Scarf G D→ℕ)(d:0<D) : b<reserveW W U b z:=by
    haveI:Nonempty (Draft G D P'):=⟨ Draft.first d false ⟩; let w:Draft G D P':= Classical.arbitrary _; let a:=adjoint w; let g:= accuracy ( stampK w ) (request z (docket U b w)) a; have hp: g≤univ.sup ( need SlotX z ( docket U b ) ):= ( WilsonOriginalGeneralRosterUnion.meets SlotX z ( docket U b ) w a ).trans ( Finset.le_sup (f:= need SlotX z ( docket U b ) ) ( mem_univ _ ) ); have hb:b<g:=by unfold g accuracy WilsonMeasuredPublicEntranceFixedBill.depth WilsonMeasuredPublicEntranceFixedBill.order request; dsimp only [ docket ]; omega
    unfold reserveW depth; omega
end YM.Integration.Election.VaultM.Till
end
