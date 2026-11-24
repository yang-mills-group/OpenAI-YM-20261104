import YangMills.WilsonProof.NativeSupport.JointPhysicalHeap
import YangMills.WilsonProof.NativeSupport.JointLinearTariff
import YangMills.WilsonProof.NativeSupport.JointPhysicalVisit
import YangMills.WilsonProof.NativeSupport.JointFundedVisit

/-! The base-price probe uses the original full colored heap for its
fixed orchard and the original physical spring, at every field and
support. Separate admission of single rows would lose their common law. -/
set_option autoImplicit false
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

theorem fixed_probe_prices (simple:G.Simple) (x:O₀) (q:I→Hat B x.val.val.val)
    (blank : ∀ i (y:O₀),(q i).M.turn.blank y.val.val.val)
    {Y:Mist R.alloy.B.a m (fire G L₀ (R.alloy.B.a.clock.hatBeta m)) (thaw G L₀ (R.alloy.B.a.clock.hatBeta m))}
    (hx:SectorOn (A:=R.alloy) (fun _ : sun=>x.val.val) Y)
    (w:V→ℝ) (hw:∀ i,0 < w i) (o:V→Site (R.alloy.B.a.S.side (m+1) n))
    (pay : Offer o q w (R.alloy.B.a.budget (m+1)).B ((R.alloy.B.a.budget (m+1)).supportExponent-4) (u₀/M))
    (fund:Ship.Fund H Θ a u₀ v e) (hm:0 < M) (occ:Extra.Multi.Occupancy ((R.alloy.B.a.clock.op m n).ratio.parent ∘ o) M) (i:I) :
    let z := NativeSwitch.singleProbe i
    let wq j := sumFee (q j) w
    let c := ‖((wq i:ℝ):ℂ)‖*MergeProof.load (q i).M
    RollsUp B₀ id (fun _ : sun=>fun X Z=>(memoE H x.val.val (fun j=>(q j).M) z wq X Z).part ((Stock.census Unit).fire ()))
      (p/2) (R.alloy.B.a.budget m).supportExponent (tempo Θ L₀*c) ∧
    RollsUp B₀ Prod.fst (fun _ : sun=>fun X Z=>(memoK H x.val.val (fun j=>(q j).M) z wq X Z).part ((Stock.census Unit).fire ()))
      (p/2) (R.alloy.B.a.budget m).supportExponent (Real.sqrt (R.alloy.B.a.clock.forcedAllowance m)*c) := by
  intro z wq c
  let U:=fixed x q blank
  let f := fun _ : sun=>x
  let Q₁:=vacation H U f hx (0:ℝ)
  have room : Rooms H Θ M (a/M) v e := {fund.rooms with bill:=palette_multiplicity fund.rooms.bill M hm}
  have leA : u₀ ≤ a := (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le fund.positive.le)).trans fund.foldE
  have pos : 0 ≤ a/M := div_nonneg (fund.positive.le.trans leA) (Nat.cast_nonneg _)
  have point := x.val.val.property.1.point
  have hpay : Offer o q w (R.alloy.B.a.budget (m+1)).B ((R.alloy.B.a.budget (m+1)).supportExponent-4) (a/M) := by
    rw [← point] at pay ⊢
    exact Offer.fatten pay (div_le_div_of_nonneg_right leA (Nat.cast_nonneg _))
  obtain ⟨u,admit⟩:=admitted x q blank w o (a/M) hpay
  have pr:=probe_regular H Θ U f hx hw admit room occ pos (0:ℝ) (by norm_num) i
  have pf:=probe_forced H Θ simple U f hx hw admit room occ pos (0:ℝ) (by norm_num) i
  have moved (j:I) : U.orbit x (0:ℝ) j=(q j).M := rfl
  have funds : U.vitality w=wq := rfl
  have leafLoad {f':Side} {Z:Rep G f'} (M₀:Lotus.Leaf Z) (b:ℝ) : MergeProof.load (leafG b M₀)=MergeProof.load M₀ := by
    unfold MergeProof.load
    change Z.p.mass (M₀.turn.support (Rain.initialBed Z b)) M₀.weight=Z.p.mass (M₀.turn.support Z) M₀.weight
    cases M₀.turn <;> rfl
  have load0 : MergeProof.load (Q₁ i).pole=MergeProof.load (q i).M := by
    change MergeProof.load (leafG _ (U.orbit x (0:ℝ) i))=_
    rw [leafLoad,moved]
  rw [funds,load0] at pr pf
  have head (s:sun) :
      memoE H (Jams.gate (fun _ : sun=>x.val.val) Y s.val) (ConnectedActivityE6.Empire.Imago.Crew.facesT Q₁ s) z wq =
      memoE H x.val.val (fun j=>(q j).M) z wq := by
    have atFlight (a₁:Chord.Flight R.alloy N m n) (eq:a₁=x.val.val) :
        memoE H a₁ (fun j=>eq.symm ▸ (q j).M) z wq=memoE H x.val.val (fun j=>(q j).M) z wq := by subst a₁; rfl
    exact atFlight _ (Jams.gatestone (F:=fun _ : sun=>x.val.val) (Y:=Y) s)
  have chain (s:sun) :
      memoK H (Jams.gate (fun _ : sun=>x.val.val) Y s.val) (ConnectedActivityE6.Empire.Imago.Crew.facesT Q₁ s) z wq =
      memoK H x.val.val (fun j=>(q j).M) z wq := by
    have atFlight (a₁:Chord.Flight R.alloy N m n) (eq:a₁=x.val.val) :
        memoK H a₁ (fun j=>eq.symm ▸ (q j).M) z wq=memoK H x.val.val (fun j=>(q j).M) z wq := by subst a₁; rfl
    exact atFlight _ (Jams.gatestone (F:=fun _ : sun=>x.val.val) (Y:=Y) s)
  let one := (Stock.census Unit).fire ()
  have he : (fun (s:sun) (X:Support C₀) (Z:Config G C₀)=>
      (memoE H (Jams.gate (fun _ : sun=>x.val.val) Y s.val) (ConnectedActivityE6.Empire.Imago.Crew.facesT Q₁ s) z wq X Z).part one) =
      (fun (_:sun) (X:Support C₀) (Z:Config G C₀)=>(memoE H x.val.val (fun j=>(q j).M) z wq X Z).part one) := by
    funext s X Z
    exact congrArg (fun φ=> (φ X Z).part one) (head s)
  have hk : (fun (s:sun) (X:Box C₀) (Z:Config G C₀)=>
      (memoK H (Jams.gate (fun _ : sun=>x.val.val) Y s.val) (ConnectedActivityE6.Empire.Imago.Crew.facesT Q₁ s) z wq X Z).part one) =
      (fun (_:sun) (X:Box C₀) (Z:Config G C₀)=>(memoK H x.val.val (fun j=>(q j).M) z wq X Z).part one) := by
    funext s X Z
    exact congrArg (fun φ=> (φ X Z).part one) (chain s)
  exact ⟨(congrArg (fun Φ=> RollsUp B₀ id Φ (p/2) (R.alloy.B.a.budget m).supportExponent (tempo Θ L₀*c)) he).mp pr,
    (congrArg (fun Φ=> RollsUp B₀ Prod.fst Φ (p/2) (R.alloy.B.a.budget m).supportExponent (Real.sqrt (R.alloy.B.a.clock.forcedAllowance m)*c)) hk).mp pf⟩

end YM.Integration.InletSusceptibility.BoardAdmission
