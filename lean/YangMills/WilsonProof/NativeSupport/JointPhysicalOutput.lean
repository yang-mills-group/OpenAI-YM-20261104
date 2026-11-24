import YangMills.WilsonProof.NativeSupport.JointHeldOutput

/-! On the original retained board, the measured kernel and both charged
physical one-switch probes are supplied together on its actual history. -/
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

private theorem prices_at_flight (simple:G.Simple) (x:O₀) (f:Chord.Flight R.alloy N m n) (atBoard:x.val.val=f) (q:I → Hat B f.val)
    (blank:∀ i (y:O₀),(q i).M.turn.blank y.val.val.val)
    {Y:Mist R.alloy.B.a m (fire G L₀ (R.alloy.B.a.clock.hatBeta m)) (thaw G L₀ (R.alloy.B.a.clock.hatBeta m))}
    (hx:SectorOn (A:=R.alloy) (fun _ : sun=>x.val.val) Y)
    (w:V → ℝ) (hw:∀ i,0 < w i) (site:V → Site (R.alloy.B.a.S.side (m+1) n))
    (pay:Offer site q w (R.alloy.B.a.budget (m+1)).B ((R.alloy.B.a.budget (m+1)).supportExponent-4) (u₀/M))
    (fund:Ship.Fund H Θ a u₀ v e) (hm:0 < M) (occ:Extra.Multi.Occupancy ((R.alloy.B.a.clock.op m n).ratio.parent ∘ site) M) (i:I) :
    let z:=NativeSwitch.singleProbe i
    let wq j:=sumFee (q j) w
    let c:=‖((wq i:ℝ):ℂ)‖*MergeProof.load (q i).M
    RollsUp B₀ id (fun _ : sun=>fun X Z=>(memoE H f (fun j=>(q j).M) z wq X Z).part ((Stock.census Unit).fire ()))
      (p/2) (R.alloy.B.a.budget m).supportExponent (tempo Θ L₀*c) ∧
    RollsUp B₀ Prod.fst (fun _ : sun=>fun X Z=>(memoK H f (fun j=>(q j).M) z wq X Z).part ((Stock.census Unit).fire ()))
      (p/2) (R.alloy.B.a.budget m).supportExponent (Real.sqrt (R.alloy.B.a.clock.forcedAllowance m)*c) := by
  subst f
  exact fixed_probe_prices H Θ simple x q blank hx w hw site pay fund hm occ i

variable (site:V → Site (R.alloy.B.a.S.side (m+1) n)) (w:V → ℝ) {opt increase baseBill:ℝ}
variable (born:Finset V) (J:Ink V → Finset (Pressure.Bond (R.alloy.B.a.S.side m n)))
  (test:Ink V → Pressure.Bond (R.alloy.B.a.S.side m n) → ℝ → ℝ)
local notation "C" => Stock.census (Ink V)
local notation "wv" => weight w opt increase born
local notation "outputSite" => (R.alloy.B.a.clock.op m n).ratio.parent ∘ site
open PhysicalNext.Repeat.Muse.Veil.Orchard
theorem physical_output (simple:G.Simple) (x:O₀) (f:Chord.Flight R.alloy N m n) (atBoard:x.val.val=f)
    (seen:Orchard.Visit H f)
    {Y:Mist R.alloy.B.a m (fire G L₀ (R.alloy.B.a.clock.hatBeta m)) (thaw G L₀ (R.alloy.B.a.clock.hatBeta m))}
    (hx:SectorOn (A:=R.alloy) (fun _ : sun=>x.val.val) Y)
    (q:I → Hat (Stock.census (Ink V)) f.val)
    (blank:∀ j (y:O₀),(heap q j).M.turn.blank y.val.val.val)
    (hw:∀ z,0 < w z) (oldR:1 ≤ opt) (newR:1 ≤ increase)
    (rooted:∀ i,∃ u∈(q i).s.val,u∈active born)
    (before:∀ u,u.1∉born → J u=∅)
    (fund:Ship.Fund H Θ a u₀ v e) (hm:0 < M)
    (occ:Extra.Multi.Occupancy (outputSite ∘ (Prod.fst : Ink V → V)) M)
    (pay:Offer (site ∘ Prod.fst) (heap q) wv (R.alloy.B.a.budget (m+1)).B ((R.alloy.B.a.budget (m+1)).supportExponent-4) (u₀/M))
    (borel:∀ u,∀ b∈J u,Measurable (test u b))
    (unit:∀ u,∀ b∈J u,∀ z∈Set.Icc 0 (Push.BetaTransport.linkCap (R.alloy.B.a.clock.op m n)),‖test u b z‖ ≤ 1)
    (anchors:∀ u b,b∈J u → site u.1=(R.alloy.B.a.clock.op m n).ratio.embed b.1)
    (old_bill:∀ y:V,(∑ i:I with y∈(q i).s.val.image Prod.fst ∧ ¬gains born (q i).s.val,
      sumFee (q i) (fun u:Ink V=>w u.1)*MergeProof.load (q i).M) ≤ baseBill) :
    ∃ (E:Support (R.alloy.B.a.S.side m n) → Config G (R.alloy.B.a.S.side m n) → Marker.Poly (Stock.census V))
      (K:Box (R.alloy.B.a.S.side m n) → Config G (R.alloy.B.a.S.side m n) → Marker.Poly (Stock.census V)),
      RGGapR2.Rough.Ledger outputSite E K (R.alloy.B.a.budget m).threshold ∧
      RootedSheet (R.alloy.B.a.budget m) id E w (tempo Θ L₀*baseBill+1/min increase (opt^2)) ∧
      RootedSheet (R.alloy.B.a.budget m) Prod.fst K w (Real.sqrt (R.alloy.B.a.clock.forcedAllowance m)*baseBill+2/min increase (opt^2)) ∧
      ∀ Z,Painted.project (SelectedKernel.given (S:=R.alloy.B.a.clock.op m n) (fun i=>(heap q i).M)
         (fun i=>JointLeaves.bonds J (heap q i).s.val) (fun i=>JointLeaves.probe J test (heap q i).s.val)
         (fun i=>sumFee (heap q i) wv) C (fun i=>sing (heap q i) wv) Z)=
        play (H.moment f) (Stock.census V) (exclaim (H.moment f).activities (Stock.census V)+K) (fun U=>∑ i,E i U) Z := by
  obtain ⟨b,b',curve,spring,t₀,good,order,atSpring⟩:=seen
  have eq:f=Cryst.flown spring t₀ := Subtype.ext atSpring
  subst eq
  have prices (i:I) := prices_at_flight H Θ simple x (Cryst.flown spring t₀) atBoard (heap q) blank hx wv
    (fun j=>by
      have z:=hw j.1
      have zo:=zero_lt_one.trans_le oldR
      have zi:=zero_lt_one.trans_le newR
      unfold Painted.weight
      split <;> split <;> positivity)
    (site ∘ Prod.fst) pay fund hm occ (Sum.inl i)
  have canon (d₀:DecidableEq (Mound q)) (j:Mound q) :
      @NativeSwitch.singleProbe (Mound q) d₀ j=@NativeSwitch.singleProbe (Mound q) (fun a b=>Classical.propDecidable (a=b)) j :=
    congrArg (fun d₁:DecidableEq (Mound q)=>@NativeSwitch.singleProbe (Mound q) d₁ j) (Subsingleton.elim _ _)
  rw [(Cryst.regarded H spring t₀ good order).1]
  exact Orchard.held_output (H:=H) (g:=simple) (Y:=spring) (x:=t₀) (tone:=good) (order:=order) (Q₁:=q)
    (load:=w) (positive:=hw) (site:=site) (aOld:=opt) (aNew:=increase) (aa:=oldR) (dd:=newR) (born:=born) (rooted:=rooted) (J:=J)
    (test:=test) (before:=before) (Θ:=Θ) (fund:=fund) (M0:=hm) (occ:=occ) (pay:=pay) (borel:=borel) (unit:=unit) (anchors:=anchors)
    (old_bill:=old_bill) (probeE:=fun i=>by
      convert (prices i).1 using 1
      exact congrArg (fun z=>fun _:sun=>fun X Z=>(memoE H (Cryst.flown spring t₀) (fun j=>(heap q j).M) z
        (fun j=>sumFee (heap q j) wv) X Z).part ((Stock.census Unit).fire ())) ((canon _ (Sum.inl i)).trans (canon _ _).symm)
      rfl)
    (probeK:=fun i=>by
      convert (prices i).2 using 1
      exact congrArg (fun z=>fun _:sun=>fun X Z=>(memoK H (Cryst.flown spring t₀) (fun j=>(heap q j).M) z
        (fun j=>sumFee (heap q j) wv) X Z).part ((Stock.census Unit).fire ())) ((canon _ (Sum.inl i)).trans (canon _ _).symm)
      rfl)

end YM.Integration.InletSusceptibility.BoardAdmission
