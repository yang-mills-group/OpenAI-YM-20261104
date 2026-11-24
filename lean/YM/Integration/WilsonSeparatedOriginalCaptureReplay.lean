import YM.Integration.WilsonAllDateHarvestCenteredReplay
import YM.Integration.WilsonSeparatedOriginalCloseLedger

/-! One original trajectory from its prescribed opening to every earlier
physical three-point reading, before the choice of resident or gauge field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalCaptureReplay
open Function Filter Finset Lattice Wilson RG Source Extra.Histories Push Local Marker
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Records
open RG05Readout.Native RG05Readout.View GridApprox.Nil WilsonAllDateHarvestStability WilsonAllDateHarvestPropagation
open Bid Pressure Copper Ac Extra.Trajectories PhysicalNext.Repeat Next.Rank.Station
open WilsonAllDateHarvestObservedReplay WilsonSeparatedOriginalResidentReadout WilsonSeparatedOriginalMarkedCubic
open scoped Classical BigOperators Topology
variable {G:Gauge}{C:Family G}{n t N per:ℕ}

theorem original (made:C.Makes)(o:Fin 3→Site (C.side n per))(E:Fin 3→Motion)(s:Fin 3→ℕ)
    (q:ManyStem C o n→Body)(P:(i:Fin 3)→Sight C (s i) per)(S:(i:Fin 3)→Emblems C (s i))
    (x:(i:Fin 3)→Palette C (s i))(roster:Census (Fin 3))(nt:n≤t)(tN:t≤N)(d k:ℕ)(Q fee:ℝ)
    (paid:Captured o E s q made P S x roster nt tN d k Q fee):
    let A:=Mine.tree o E
    let J:=Mine.ward o E roster
    let Y:=C.path.rep N per
    let I:=headings o E q
    let rows:=fun i (iN:i≤N)=>imprint made A I (plants (m:=t) s P S x) i iN
    let f:=WilsonMixedTaggedFields.columns o E s q S x t N
    let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster nt (le_refl t)
    let opened:=WilsonAllDateHarvestEndpointOpening.opening inc (shadow A s I t)
    ∃L:∀i,Config G (C.side i per)→Poly (J i),Replay A s (le_refl n) t L N ∧
      L t=(fun W=>opened (density (Y t) (rows t tN) (fun _ _=>0) (fun _ _=>0) W)) ∧
      ∀ (i : ℕ), n ≤ i → ∀ (it : i < t) (z : Fin 3 → ManyStem C o i), Injective z →
        ∀ (present : Finset.univ.image z ∈ (J i).choices) (W : Config G (C.side i per)), flags (Y i).p.threshold W = ∅ →
        ‖cubic (moment C z (f i) (it.le.trans tN) W)-
          (connected (((Y i).eval W:ℂ)⁻¹ • L i W)).part (modes z present univ)‖≤fee:=by
  intro A J Y I rows f inc opened
  obtain ⟨L,run,top,admitted⟩:=WilsonAllDateHarvestCenteredReplay.original o E s q made P S x roster nt tN paid
  refine ⟨L,run,top,?_⟩
  intro i ni it z special present W clear
  obtain ⟨B,Z,reg,_,_⟩:=admitted i ni it.le
  apply WilsonSeparatedOriginalCloseLedger.measured C made (it.le.trans tN) (f i) (fun _=>RG05Readout.Records.clinic_cut ..) z special present B Z reg _ W clear
  rw [if_neg it.ne]
  exact (C.path.levels.budget i).exponent_pos.le

/-- At the base of this specific group the three resident names are forced
by their prescribed origins and all their original measured locations. -/
theorem placed (o:Fin 3→Site (C.side n per))(E:Fin 3→Motion)(roster:Census (Fin 3))(live:univ∈roster.choices):
    let v:Fin 3→ManyStem C o n:=(Mine.remap o E).symm
    univ.image v∈(Mine.ward o E roster n).choices:=by
  intro v
  apply Finset.mem_filter.mpr
  refine ⟨mem_univ _,?_,(Mine.remap o E).injective.injOn⟩
  have indices:(univ.image v).image ((Mine.tree o E).labelY n)=univ:=by
    rw [Finset.image_image]
    have direct:(Mine.tree o E).labelY n ∘ v=id:=funext (fun i=>(Mine.remap o E).apply_symm_apply i)
    rw [direct,Finset.image_id]
  rwa [indices]

end YM.Integration.WilsonSeparatedOriginalCaptureReplay
