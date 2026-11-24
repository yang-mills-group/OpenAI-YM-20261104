import YangMills.WilsonProof.NativeSupport.JointPhysicalOutput
import YangMills.WilsonProof.NativeSupport.JointPhysicalMount
import YangMills.WilsonProof.NativeSupport.JointProjectedHaar
import YangMills.WilsonProof.NativeSupport.JointDatedMask

/-! One complete original measured date, including the new primitive fees, both sheets, the fixed-board physical purchases, and the exact transition of the original density. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 120000
noncomputable section
namespace YM.Integration.InletSusceptibility.BoardAdmission
open RG Wilson Lattice Pressure Push.PriceCompiler Marker MergeProof PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Muse PhysicalNext.Repeat.Muse.Veil PhysicalNext.Repeat.Pass PhysicalNext.Repeat.Jams FullVolume.Ray FullVolume.Urns
open Extra.Iteration Progress.DirectedRecipe PhysicalNext.Repeat.Roof RG.Shoot AnalyticBridge VerifiedReset Collection
open PhysicalNext.Repeat.Luna PhysicalNext.Repeat.Luna.Frets
open Orchard MergeProof.Menu FullVolume.Amp Pass Tent
open ConnectedActivityE6.Empire
open Chord
open JointShadow Painted Packet JointLeaves Merge MergeProof.Accent Finset Function MeasureTheory
open scoped Classical BigOperators
variable {G:Gauge} {R:Run G} {N m n:ℕ} {t p a u₀ v e : ℝ} {M:ℕ}
variable {T : Team (stageP R.alloy.B.a (m+1) n)}
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq V] {B:Census V}
variable (H : Chord R.kit N m n t t) (Θ : Tableau p 300)
local notation "B₁" => R.alloy.B.a.budget (m+1)
local notation "B₀" => R.alloy.B.a.budget m
local notation "L₀" => R.rolls.L (R.alloy.B.a.clock.J (m+1))
local notation "C₀" => R.alloy.B.a.S.side m n
local notation "S₀" => R.alloy.B.a.clock.op m n
local notation "O₀" => Booker R.alloy N m n T

open Push Push.SectorMeasure Extra.Multi PhysicalNext.Repeat.Mallow Planned.GuardedAtom
open MeasureTheory Push.BetaTransport Extra.Trajectories RGGapR2 JointShadow
local notation "CC" => Stock.census (Ink V)
local notation "X₁" => R.alloy.B.a.S.side (m+1) n
local notation "X₀" => R.alloy.B.a.S.side m n
theorem measured_flight (f:Chord.Flight R.alloy N m n) (visit:Orchard.Visit H f)
    (q:I → Hat (Stock.census (Ink V)) f.val) (vw:Ink V → ℝ) (J:V → Finset (Pressure.Bond X₀))
    (test:V → Pressure.Bond X₀ → ℝ → ℝ)
    (meas:∀ i,∀ b∈J i,Measurable (test i b))
    (unit:∀ i,∀ b∈J i,∀ z∈Set.Icc 0 (linkCap S₀),‖test i b z‖ ≤ 1) (Z:Config G X₀) (s:Finset V) :
    (Painted.project (SelectedKernel.given (S:=S₀) (fun i=>(q i).M)
      (fun i=>JointLeaves.bonds (J ∘ Prod.fst) (q i).s.val) (fun i=>JointLeaves.probe (J ∘ Prod.fst) (test ∘ Prod.fst) (q i).s.val)
      (fun i=>sumFee (q i) vw) CC (fun i=>sing (q i) vw) Z)).part (tag s)=
    ∑ k:(S₀).Choices,∫ U,(Push.SectorMeasure.taggedKernel S₀ f.val.beta k U Z:ℂ)*
      (diagonal (fun i=>(JointPhysical.sample S₀ k (J i) (test i) U Z:ℂ))
        (Painted.project (Expense q vw S₀ U))).part (tag s) ∂prior G X₁ := by
  obtain ⟨_,_,_,Y,l,_,_,same⟩:=visit
  have eq:f=Cryst.flown Y l:=Subtype.ext same
  subst eq
  exact projected_haar q vw J test (PhysicalNext.Repeat.Mallow.houseS Y l) Z meas unit s

theorem measured_flight_live (f:Chord.Flight R.alloy N m n) (visit:Orchard.Visit H f)
    (q:I → Hat (Stock.census (Ink V)) f.val) (vw:Ink V → ℝ) (J:V → Finset (Pressure.Bond X₀))
    (test:V → Pressure.Bond X₀ → ℝ → ℝ)
    (meas:∀ i,∀ b∈J i,Measurable (test i b))
    (unit:∀ i,∀ b∈J i,∀ z∈Set.Icc 0 (linkCap S₀),‖test i b z‖ ≤ 1) (Z:Config G X₀) (s:Finset V) (k:(S₀).Choices) :
    Integrable (fun U=>(Push.SectorMeasure.taggedKernel S₀ f.val.beta k U Z:ℂ)*
      (diagonal (fun i=>(JointPhysical.sample S₀ k (J i) (test i) U Z:ℂ))
        (Painted.project (Expense q vw S₀ U))).part (tag s)) (prior G X₁) := by
  obtain ⟨_,_,_,Y,l,_,_,same⟩:=visit
  have eq:f=Cryst.flown Y l:=Subtype.ext same
  subst eq
  exact projected_live q vw J test (PhysicalNext.Repeat.Mallow.houseS Y l) Z meas unit s k

variable {J₀:Type} [Fintype J₀]
variable (site:V → Site (R.alloy.B.a.S.side (m+1) n)) (w:V → ℝ) (born:Finset V) (birth:J₀ → V) (st:J₀ → Support (R.alloy.B.a.S.side (m+1) n)) (val:J₀ → Config G (R.alloy.B.a.S.side (m+1) n) → ℂ)
variable (amp:J₀ → ℝ) (J:V → Finset (Pressure.Bond (R.alloy.B.a.S.side m n))) (test:V → Pressure.Bond (R.alloy.B.a.S.side m n) → ℝ → ℝ)
variable (x:Booker R.alloy N m n T)
local notation "F₁" => x.val.val.val
local notation "F₀" => H.moment x.val.val
local notation "Γ" => R.alloy.B.a.clock.forcedAllowance (m+1)
local notation "Bv" => Stock.census V
local notation "o₀" => ((S₀).ratio.parent ∘ site)
local notation "pc" => R.alloy.B.a.budget (m+1)
variable (E:Support (R.alloy.B.a.S.side (m+1) n) → Config G (R.alloy.B.a.S.side (m+1) n) → Marker.Poly (Stock.census V))
variable (K:Box (R.alloy.B.a.S.side (m+1) n) → Config G (R.alloy.B.a.S.side (m+1) n) → Marker.Poly (Stock.census V))
variable {A D U z:ℝ}
local notation "old" => A*((M:ℝ)*Extra.Multi.siteFactor (F₁).p.B*U)
local notation "freshFee" => (M:ℝ)*Extra.Multi.siteFactor (F₁).p.B*(D*z)
theorem native_step (simple:G.Simple) (visited:Orchard.Visit H x.val.val)
    {Y:Mist R.alloy.B.a m (fire G L₀ (R.alloy.B.a.clock.hatBeta m)) (thaw G L₀ (R.alloy.B.a.clock.hatBeta m))}
    (hx:SectorOn (A:=R.alloy) (fun _:sun=>x.val.val) Y) (fund:Ship.Fund H Θ a u₀ v e)
    (prev:Rough.Ledger site E K (F₁).p.threshold) (re:RootedSheet (F₁).p id E w U) (rk:RootedSheet (F₁).p Prod.fst K w U)
    (ageE:∀ i s,Vivid E i (tag s) → Disjoint s born) (ageK:∀ i s,Vivid K i (tag s) → Disjoint s born)
    (u0:0 ≤ U) (aa:1 ≤ A) (dd:1 ≤ D) (hw:∀ i,0 < w i)
    (births:∀ j,birth j∈born) (distinct:Injective birth) (home:∀ j,site (birth j)∈st j)
    (localF:∀ j,LocalOn (st j) (val j)) (sym:∀ j,GaugeInvariant (val j)) (borel:∀ j,Measurable (val j))
    (apos:∀ j,0 ≤ amp j) (bound:∀ j Z,‖val j Z‖ ≤ amp j)
    (size:0 < M) (occ:Extra.Multi.Occupancy site M) (occIn:Extra.Multi.Occupancy (site ∘ (Prod.fst : Ink V → V)) M)
    (occOut:Extra.Multi.Occupancy (o₀ ∘ (Prod.fst : Ink V → V)) M)
    (small:0 ≤ z) (stencil:∀ j,Real.exp ((F₁).p.supportExponent*coverNumber (F₁).p.B (st j))*(w (birth j)*amp j) ≤ z)
    (exp0:0 ≤ (F₁).p.supportExponent-4) (room:(((F₁).p.B+(F₁).p.B+1:ℕ):ℝ)^4*(Γ+old+freshFee) ≤ 3)
    (cash:fullFare (mountedFare Γ old freshFee) ≤ u₀/M)
    (before:∀ i,i∉born → J i=∅) (meas:∀ i,∀ b∈J i,Measurable (test i b))
    (unit:∀ i,∀ b∈J i,∀ c∈Set.Icc 0 (linkCap S₀),‖test i b c‖ ≤ 1)
    (anchored:∀ i b,b∈J i → site i=(S₀).ratio.embed b.1) :
    ∃ (E':Support X₀ → Config G X₀ → Marker.Poly (Stock.census V)) (K':Box X₀ → Config G X₀ → Marker.Poly (Stock.census V)),
      Rough.Ledger o₀ E' K' (B₀).threshold ∧ RootedSheet B₀ id E' w (tempo Θ L₀*(4*U)+1/min D (A^2)) ∧
      RootedSheet B₀ Prod.fst K' w (Real.sqrt (R.alloy.B.a.clock.forcedAllowance m)*(4*U)+2/min D (A^2)) ∧
      ∀ (Z:Config G X₀) (s:Finset V),
        let body (k:(S₀).Choices) (X:Config G X₁):ℂ:=(Push.SectorMeasure.taggedKernel S₀ (F₁).beta k X Z:ℂ)*(diagonal
          (fun i=>(JointPhysical.sample S₀ k (J i) (test i) X Z:ℂ))
          (play F₁ Bv (exclaim (F₁).activities Bv+K) (fun x'=>∑ i,E i x') X*
            ∏ j,(1+Poly.send ((Stock.census V).fire (birth j)) (val j X)))).part (tag s)
        (play F₀ Bv (exclaim (F₀).activities Bv+K') (fun X=>∑ i,E' i X) Z).part (tag s)=
          (∑ k:(S₀).Choices,∫ X,body k X ∂prior G X₁) ∧ ∀ k,Integrable (body k) (prior G X₁) := by
  obtain ⟨a₀,vac⟩:=original_forced_intake x
  have point:=x.val.val.property.1.point
  have slots:HasSlots (F₁).p (F₁).activities := x.val.property
  obtain ⟨q,invoice,blank,roots,charges,reg,dirt,shaped⟩:=physical_mount F₁ site w E K born birth st val amp slots vac
    prev re rk ageE ageK u0 aa dd hw births distinct home localF sym borel apos bound occ occIn small stencil exp0 room cash
  let complete {Z:Type} [Fintype Z] (pack:Z → Hat (Stock.census (Ink V)) (F₁)) : Fintype (Mound pack):=inferInstance
  letI : Fintype (Mound q):=complete q
  let vw:=Painted.weight w A D born
  have paid := point ▸ invoice
  have measured:=physical_output H Θ site w born (J ∘ Prod.fst) (test ∘ Prod.fst) simple x x.val.val rfl visited hx q
    (fun i y=>blank i y.val.val.val y.val.property) hw aa dd roots (fun i=>before i.1)
    fund size occOut paid (fun i=>meas i.1) (fun i=>unit i.1) (fun i=>anchored i.1) charges
  obtain ⟨E',K',proper,pr,pk,exactOutput⟩:=measured
  refine ⟨E',K',proper,pr,pk,fun Z s=>?_⟩
  have positive (j:Ink V): 0 < vw j:=by
    have h1:=hw j.1;have h2:=zero_lt_one.trans_le aa;have h3:=zero_lt_one.trans_le dd
    unfold vw Painted.weight
    split <;> split <;> positivity
  have density (X:Config G X₁):Painted.project (Expense (heap q) vw S₀ X)=
    play F₁ Bv (exclaim (F₁).activities Bv+K) (fun x'=>∑ i,E i x') X*∏ j,(1+Poly.send ((Stock.census V).fire (birth j)) (val j X)) := by
    rw [heap_density q x.val.val.property.1.valid vw positive S₀ reg dirt,shaped X]
    exact project_physical_product F₁ site E K birth val prev X
  dsimp only
  constructor
  · rw [←exactOutput Z,measured_flight H _ visited (heap q) vw J test meas unit Z s]
    simp_rw [density]
  · intro k
    have cap:=measured_flight_live H _ visited (heap q) vw J test meas unit Z s k
    simpa only [density] using cap

end YM.Integration.InletSusceptibility.BoardAdmission
