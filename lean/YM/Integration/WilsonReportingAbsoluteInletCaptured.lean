import YangMills.WilsonProof.NativeSupport.WilsonReportingAbsolutePlantedPort
import YM.Integration.WilsonReportingAbsoluteInletNativeInvoice
import YM.Integration.WilsonReportingAbsoluteInletGust
import YM.Integration.WilsonReportingAbsoluteInletPower

/-! At the measured inlet, apply the absolute planted estimate at every
intermediate inverse temperature. The output is the complete normalized
Wilson source at the actual upper regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletCaptured
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 RGComparison.Core16.Spool
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics Next.Foundations Labels
open WilsonConditionalTaylorLabels WilsonOffsetJointRoster WilsonUniformUnmarkedInletEnergySites
open WilsonUniformUnmarkedInletBondRemainder WilsonUniformUnmarkedInletConnectedShift
open InletSusceptibility.Packet WilsonReportingAbsoluteInletNativeDates
open WilsonReportingAbsoluteInletNativeCoordinates WilsonReportingAbsoluteInletNativeInvoice
open scoped Classical BigOperators Topology
variable {G:Gauge}

def engineering (a:Roster G) (s:Finset (Fin a.length)):ℕ :=
  ∑j:↥s,(((frames G).level (a.get j.val).1).grades (a.get j.val).2).2

def extent (b:Roster G) (s:Finset (Fin b.length)):ℕ:=
  Finset.univ.sup (fun j:↥s=>minSide G (grades b s j))
def span (P:ℕ):ℕ:=⌈width P+2⌉₊
def cells (b:Roster G) (s:Finset (Fin b.length)):ℕ:=(2*extent b s+1)^4
def degree (κ:ℝ) (P:ℕ) (b:Roster G) (s:Finset (Fin b.length)):ℕ:=
  radiusDegree (span P) (cells b s) (tariffDegree κ)
def loss (κ:ℝ) (P:ℕ) (b:Roster G) (s:Finset (Fin b.length)):ℕ:=
  susceptibilityLoss s.card (span P) (cells b s) (tariffDegree κ)
def cost (κ:ℝ) (P:ℕ) (b:Roster G) (s:Finset (Fin b.length)):ℝ:=
  2*5^s.card*bill (grades b s) G*4^(2*degree κ P b s*(s.card+1))

theorem threshold (κ:ℝ) (P:ℕ) (b:Roster G) (s:Finset (Fin b.length)) (hs:s.Nonempty):
    2*(2*degree κ P b s+1)≤loss κ P b s:=by
  let D:=degree κ P b s
  have hd:1≤D:=by dsimp [D,degree,radiusDegree];omega
  have hc:0<s.card:=Finset.card_pos.mpr hs
  change 2*(2*D+1)≤4*D*(s.card+1)
  calc
    2*(2*D+1)≤4*D*2:=by omega
    _≤4*D*(s.card+1):=Nat.mul_le_mul_left _ (by omega)

variable {R:Run G} {C:Campaign R} {Θ:Luna.Tableau C.width 300} {vsky:ℕ→ℕ→ℝ}
local notation "A₀" => R.alloy.B.a

def Paid (R:Run G) (κ:ℝ) (P q:ℕ) (c ε:ℝ) (b:Roster G) (s:Finset (Fin b.length)) (h:ℕ→ℕ→ℕ→ℝ):Prop :=
  ∀ᶠ k:ℕ in atTop,∀u,ultraviolet R.family c k≤u →
    let t:=inlet R P u
    let N:=u+1
    ∃tu:t≤u,∀per,∀ T:Slices R.family.path.levels per,∀ (o:Fin b.length→Site (R.family.side N per)) i,i∈s→
      ∀ (z e:Site (R.family.side N per)) (part:Bool),
        let d:=traversal T (tu.trans u.le_succ)
        let x:=shifts R per t N
        let v:=finite R N per t (h N per)
        let δ:=x-v
        let g:=regulatorRun R.family N per N
        let β:=Descent.offset v g
        let φ:=WilsonReportFrozenTraversal.planted R b s o i z e part
        let A:=WilsonReportingAbsoluteInletGust.physical R (tu.trans u.le_succ) φ 1-d.conditioned β φ 1
        (∀r∈Set.Icc (0:ℝ) 1,(∑j∈interior d,|picture d β δ 1 φ r j|)≤cost κ P b s/g^loss κ P b s) ∧
        (∃r∈Set.Ioo (0:ℝ) 1,A=∑j∈interior d,δ (WilsonUniformUnmarkedInletEnergySites.lag d j)*picture d β δ 1 φ r j) ∧
        |A|/g^engineering b s≤ε*g^q

theorem original (sky:Campaign.Sky R C Θ vsky) (simple:G.Simple) (slow:Pace R)
    (support:∀j,(((A₀).budget j).supportExponent+1)*(((A₀).S.block (j-1)).val:ℝ)^4≤Real.sqrt ((A₀).clock.hatBeta j))
    {c:ℝ} (hc:1<c) (P p q:ℕ) (b:Roster G) (s:Finset (Fin b.length)) (hs:s.Nonempty)
    (h:ℕ→ℕ→ℕ→ℝ) (fund:InversePrice R p h)
    (order:q+engineering b s+loss Θ.price P b s≤p) {ε:ℝ} (ep:0<ε):
    Paid R Θ.price P q c ε b s h:=by
  let K:=cost Θ.price P b s
  let ε₀:=min ε 1
  let η:=ε₀/(1+|K|)
  have pos:0<(1:ℝ)+|K|:=by positivity
  have ep₀:0<ε₀:=lt_min ep zero_lt_one
  have eta:0<η:=div_pos ep₀ pos
  have small:η≤1:=(div_le_one pos).2 ((min_le_right ε 1).trans (by linarith only [abs_nonneg K]))
  have atoms(j:↥s):minSide G (grades b s j)≤extent b s:=
    Finset.le_sup (f:=fun j:↥s=>minSide G (grades b s j)) (Finset.mem_univ j)
  have crop:=WilsonReportingAbsolutePlantedPort.original sky simple slow support b s hs (extent b s) (span P) atoms
  have bill:=WilsonReportingAbsoluteInletNativeInvoice.paid R simple slow hc P p h fund eta
  have gate:2*(2*degree Θ.price P b s+1)≤p:=(threshold Θ.price P b s hs).trans (by omega)
  filter_upwards [crop,bill] with k paid filed u front t N
  obtain ⟨tu,kt,low,high,windows⟩:=filed u front
  refine ⟨tu,?_⟩
  intro per T o i hi z e part d x v δ g β φ A
  have coordinates:=windows per T
  have packet:=paid u t kt (Nat.lt_succ_of_le tu) low high per T o i hi z e part p β δ η small gate
    coordinates.2.2.1 coordinates.2.2.2.1 coordinates.2.2.2.2
  obtain ⟨rows,r,inside,word,fee⟩:=packet
  have trueSource:=WilsonReportingAbsoluteInletGust.original R T (tu.trans u.le_succ) φ 1
  have fix:A=d.conditioned (RGComparison.Core16.line R.family.path per t N) φ 1-d.conditioned β φ 1:=
    congrArg (fun z:ℝ=>z-d.conditioned β φ 1) trueSource
  refine ⟨rows,⟨r,inside,fix.trans word⟩,?_⟩
  have signed:|A| ≤ (ε₀/(1+|K|))*g^p*(K/g^loss Θ.price P b s):=by rw [fix];exact fee
  have paidPrice:=WilsonReportingAbsoluteInletPower.paid coordinates.1 coordinates.2.1 ep₀ order signed
  exact paidPrice.trans (mul_le_mul_of_nonneg_right (min_le_left ε 1) (pow_nonneg coordinates.1.le _))

def rank (κ:ℝ) (P q:ℕ) (b:Roster G):ℕ :=
  q+1+Finset.univ.sup (fun s:Finset (Fin b.length)=>engineering b s+loss κ P b s)

theorem roster (sky:Campaign.Sky R C Θ vsky) (simple:G.Simple) (slow:Pace R)
    (support:∀j,(((A₀).budget j).supportExponent+1)*(((A₀).S.block (j-1)).val:ℝ)^4≤Real.sqrt ((A₀).clock.hatBeta j))
    {c:ℝ} (hc:1<c) (P q:ℕ) (b:Roster G) (h:ℕ→ℕ→ℕ→ℝ) (fund:InversePrice R (rank Θ.price P q b) h)
    {ε:ℝ} (ep:0<ε):
    ∀ᶠ k:ℕ in atTop,∀s:Finset (Fin b.length),s.Nonempty→∀u,ultraviolet R.family c k≤u →
      let t:=inlet R P u
      let N:=u+1
      ∃tu:t≤u,∀per,∀ T:Slices R.family.path.levels per,∀ (o:Fin b.length→Site (R.family.side N per)) i,i∈s→
        ∀ (z e:Site (R.family.side N per)) (part:Bool),
          let d:=traversal T (tu.trans u.le_succ)
          let x:=shifts R per t N
          let v:=finite R N per t (h N per)
          let δ:=x-v
          let g:=regulatorRun R.family N per N
          let β:=Descent.offset v g
          let φ:=WilsonReportFrozenTraversal.planted R b s o i z e part
          let A:=WilsonReportingAbsoluteInletGust.physical R (tu.trans u.le_succ) φ 1-d.conditioned β φ 1
          (∀r∈Set.Icc (0:ℝ) 1,(∑j∈interior d,|picture d β δ 1 φ r j|)≤cost Θ.price P b s/g^loss Θ.price P b s) ∧
          (∃r∈Set.Ioo (0:ℝ) 1,A=∑j∈interior d,δ (WilsonUniformUnmarkedInletEnergySites.lag d j)*picture d β δ 1 φ r j) ∧
          |A|/g^engineering b s≤ε*g^(q+1) := by
  apply eventually_all.2
  intro s
  by_cases hs:s.Nonempty
  · have prices:engineering b s+loss Θ.price P b s≤Finset.univ.sup (fun t:Finset (Fin b.length)=>engineering b t+loss Θ.price P b t):=
      Finset.le_sup (f:=fun t:Finset (Fin b.length)=>engineering b t+loss Θ.price P b t) (Finset.mem_univ s)
    have order:q+1+engineering b s+loss Θ.price P b s≤rank Θ.price P q b:=by unfold rank;omega
    have row:=original sky simple slow support hc P (rank Θ.price P q b) (q+1) b s hs h fund order ep
    exact row.mono (fun _ paid _=>paid)
  · exact Eventually.of_forall (fun _ h=>(hs h).elim)
end YM.Integration.WilsonReportingAbsoluteInletCaptured
