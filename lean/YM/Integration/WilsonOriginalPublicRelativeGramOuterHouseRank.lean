import YM.Integration.WilsonOriginalPublicRelativeGramOuterPhysicalPins
import YM.Integration.WilsonOriginalPublicRelativeGramOuterCards
import YM.Integration.WilsonOriginalPublicRelativeGramOuterSelf
import YM.Integration.WilsonMacroscopicRichTwoDatePivot

/-! The genuine physical homogeneous self-Gram has an own-date coercive
direction on all public coordinates, including its unit and lower fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOuterHouseRank
open Filter Set Function Lattice Wilson RG Source Extraction RG17 Table Spec Climb
open FVA2 FVA2.Register
open Trace.Pilot PhysMS Frame XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical PhysicalNext.Repeat.Legato
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonOriginalPublicRelativeGramLeading (fields)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPositionProgramPublicContrast (assay)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonMacroscopicRichTwoDatePivot (active)
open WilsonOriginalBlissMixedGram (grades)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
    {Y:(Bel R.family.book).Hierarchy} (B:Deck G)(h:ℕ)(a:Axis)
local notation "I" => Glyph B h
local notation "D" => grades h h
local notation "B₀" => Bel R.family.book
local notation "E" => named R B h
local notation "dual" => (Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) h a
local notation "goal" i:max j:max => fields R a (fun _:I=>h) (fun k=>E k) i j

open WilsonOriginalPublicRelativeGramOuterPhysical (truePair)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open WilsonOriginalPublicRelativeGramReflectedLimit (entered ordered)
open WilsonOriginalPublicRelativeGramPins (readings matrix)
variable {g:ℝ→ℝ}(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4)(Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g)
local notation "ω" => (fun (r:ℝ) (_:Unit)=>ports R avoid (pointsAt a) (Γ.date r) r)
local notation "S₀" => (fun r:ℝ=>shape avoid (pointsAt a) (R.family.S.a (Γ.date r)/r))
local notation "real" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))

open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalPublicRelativeGramPins (cutoff)
variable {arch:Trace.Terrace.Arch R.family}

theorem original (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)
    (earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    {height T:ℕ}(cap:h≤height)(room:ℝ→Prop)(activeRoom:∀ᶠr in trail,room r)
    (books:∀r,room r→Book F (l:=ℓ) Y arch height T r)(arm:I→Bool):
    ∃k:ℝ,0<k ∧ ∀ᶠr in trail,∀hr:room r,∀ᶠb in (ℓ:Filter (ℕ×ℕ)),∀x:I→ℂ,
      k*‖x‖^2 ≤ ‖assay x x (cutoff R a (fun _:I=>h) (Γ.date r) (ω r) (fun _:Unit=>(1:ℂ))
        (fun _ w j=>(((books r hr).rows ⟨h,Nat.lt_succ_of_le cap⟩).arm (arm j)
          (homogeneous F J Z r h (E j))).source w) false b)‖ := by
  classical
  let claim (r:ℝ)(hr:room r)(j:I) :=
    ((books r hr).rows ⟨h,Nat.lt_succ_of_le cap⟩).arm (arm j) (homogeneous F J Z r h (E j))
  let source (r:ℝ)(w:ℕ×ℕ)(j:I) : R.family.label h:=if hr:room r then (claim r hr j).source w else 0
  let name (r:ℝ)(j:I) : R.family.label h:=if hr:room r then (claim r hr j).label else 0
  have income:∀ᶠr in trail,∀j,Tendsto (fun b=>source r b j) (ℓ:Filter (ℕ×ℕ)) (𝓝 (name r j)) := by
    filter_upwards [activeRoom] with r hr j
    simpa only [source,name,dif_pos hr] using (claim r hr j).approaches
  have same:∀ᶠr in trail,∀i,S.project h (name r i)=homogeneous F J Z r h (E i) := by
    filter_upwards [activeRoom] with r hr i
    simpa only [name,dif_pos hr] using (claim r hr i).represents
  obtain ⟨k,kp,ev⟩ := WilsonOriginalPublicRelativeGramOuterPhysicalPins.original R F J Z B h a ℓ avoid Γ
    simple temperature lead earned below source name income same
  refine ⟨k,kp,?_⟩
  filter_upwards [ev] with r prices
  intro hr
  simpa only [entered,source,dif_pos hr,claim] using prices

end YM.Integration.WilsonOriginalPublicRelativeGramOuterHouseRank
