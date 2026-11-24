import YM.Integration.WilsonMeasuredPublicEntranceTransferSeparatedNodes
import YM.Integration.WilsonMeasuredPublicEntranceTransferForkNodes
import YM.Integration.WilsonMeasuredPublicEntranceTransferSiteBox
import YM.Integration.WilsonPhysicalLicensedFaces
import YM.Integration.WilsonMeasuredPublicEntranceTransferSubmitted
import YM.Integration.WilsonMeasuredPublicEntranceCutoffHearing

/-! At a reporting knot, compare the true older conditional of the already
appointed, unrestricted K word with the continuum value of the corresponding
physical N columns on the ordered UV and period tails. The exact signed
K-vacuum-to-flat term is retained for the unconditional reading. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferKnotBoard
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Labels Cells
open Extra.Histories PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonReflectedPublicOrientedFaces (displayed)
open OPE Next.Rank Overlay Bid Push.GridApprox MergeProof Ribbons Accent ManyCopies
open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (submitted physical)
open WilsonMeasuredPublicEntranceOrderedPins (Release publicValue)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open Table Climb Next.UVStress
open Extraction Spec PertExtension PertExtension.LatticePT Trace.Pilot Trace.Terrace
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
variable {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Arch R.family}
local notation "C₀" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
open WilsonMovingForkOpticalBook (reporter)
open RG16 RG16.Literal PhysicalNext.Repeat.Mallow Bandage
local notation "full" => Stock.final (Fin n)

def At {D T n:ℕ}(d:Fin n→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→ Book F (l:=l) H arch D T s.val)
    (ρ:Fin n→{s:ℝ // 0<s ∧ s<δ})(name:∀i,Bool→S.Field (d i).val)
    (q u f:ℕ)(o:Fin n→ Cover)(ε:ℝ)(N p:ℕ):Prop:=
    let grade:=fun i=>(d i).val
    ∀_deep:f<N,∀K:ℕ,∀fk:f≤K,∀live:K≤N,∀req power t:ℕ,∀B:ℝ,
      ∀A:Panel R grade N p f K fk live req power t B,∀file:Filed R grade K,
      A.slot=file.station → A.axis=file.A N p →
      A.loc=(fun i=>wrap ((C₀).side f p) (o i)) →
      ∀weak:Fin n→Bool,let v:=fun i=>name i (weak i)
     
      A.names=(fun i=>(((books (ρ i)).rows (d i)).arm (weak i) (v i)).source (N,p)) →
      ∀early:u≤f,Reading R grade A early → (∀i,1≤A.M i) → ∀E:Fin n→ℕ,
      (∀i b,b≤grade i→(C₀).ref b≤N) →
      (∀i,Next.Rank.Spindle.paid (C₀) (grade i) f N p (A.names i)≤A.M i*(β f)^(E i)) →
      ∀desired:ℕ,desired+∑i,E i≤req →
      let y:=fun i=>displayed R (grade i) (A.names i) (A.turn i)
      let ren:=publicValue (S:=S) grade f o y
      let spend:=(∏i:↥(Stock.final (Fin n)).val,Motion.orbitCost ((C₀).labels.level (grade i.val))*
        charge F ((books (ρ i.val)).rows (d i.val)) f (weak i.val) (v i.val))*((β f)^q)⁻¹+
        (∏i,WilsonAddressedHomeDose.ceiling (R:=R) (grade i) (A.M i))*((β f)^desired)⁻¹
      let Q:=WilsonMeasuredPublicEntranceTransferWord.field (N:=N) R grade
        (WilsonMeasuredPublicEntranceTransferSubmitted.vector R grade A)
        (fun i=>((C₀).S.toDepth fk p).embed (A.loc i)) (Stock.final (Fin n)).val
      let old:=actualTransport (C₀) (N:=N) Q (early.trans fk) 1
      let gibbs:=∫U,Q U ∂scene (C₀).path N p K
      ‖old-ren‖≤ spend+ε ∧ ‖gibbs-ren‖≤‖gibbs-old‖+(spend+ε)

private theorem at_node {D T n f u c q N p:ℕ}(d:Fin n→Fin (D+1)){δ ε:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→ Book F (l:=l) H arch D T s.val)
    (ρ:Fin n→{s:ℝ // 0<s ∧ s<δ})(name:∀i,Bool→S.Field (d i).val)(o:Fin n→ Cover)
    (native:WilsonPhysicalLicensedFaces.measured F d books ρ q u f c (Stock.final (Fin n)))
    (housed:∀i,8*‖(C₀).S.gridPoint f (o i)‖≤(C₀).S.a (c+1))
    (apart:Pairwise fun i k=>2*(C₀).S.a f*(((C₀).path.levels.budget f).B:ℝ)^2≤
      ‖(C₀).S.gridPoint f (o i)-(C₀).S.gridPoint f (o k)‖)
    (bound:Fin n→ℝ)(wage:∀b t i,‖WilsonMeasuredPublicEntranceTransferForkNodes.marked F
      (fun i=>books (ρ i)) d name b t (N,p) i‖≤bound i)
    (released:∀y:(C₀).book.Vector (fun i=>(d i).val),(∀i,‖y i‖≤bound i)→
      ‖WilsonMeasuredPublicEntranceOrderedPins.physical (C:=C₀) (fun i=>(d i).val) f o N p y-
        publicValue (C:=C₀) (S:=S) (fun i=>(d i).val) f o y‖≤ε):
    At F d books ρ name q u f o ε N p:=by
  classical
  let grade:=fun i=>(d i).val
  intro deep K fk live req power t B A file station axes places weak v booked atU sale one E refs cash desired expo y ren spend Q old gibbs
  have bounded:∀i,‖y i‖≤bound i:=by
    intro i
    simpa only [y,booked,WilsonMeasuredPublicEntranceTransferForkNodes.marked,
      WilsonMeasuredPublicEntranceOrderedRoster.raw,WilsonMeasuredPublicEntranceOrderedRoster.enrolled] using (wage weak A.turn i)
  let raw:=physical R grade (N:=N) A.names A.turn A.loc (Stock.final (Fin n))
  let prev:=actualTransport (C₀) (N:=N) raw (atU.trans deep.le) 1
  have photo:(C₀).omega N p raw=WilsonMeasuredPublicEntranceOrderedPins.physical (C:=R.family) grade f o N p y:=by
    dsimp only [raw]
    rw [places]
    exact WilsonMeasuredPublicEntrancePinnedPass.cutoff R grade o A.names A.turn
  have projection:=released y bounded
  rw [←photo] at projection
  have issued:=native N p deep o (fun i _=>housed i) (fun _ _ h=>apart (Subtype.val_injective.ne h)) weak v A.turn atU
  have first:‖(C₀).omega N p raw-prev‖≤
      (∏i:↥(Stock.final (Fin n)).val,Motion.orbitCost ((C₀).labels.level (grade i.val))*
        charge F ((books (ρ i.val)).rows (d i.val)) f (weak i.val) (v i.val))*((β f)^q)⁻¹:=by
    simpa only [raw,prev,booked,places] using issued
  have middle:=WilsonMeasuredPublicEntranceCellWords.paid R grade A file station axes atU sale one E refs cash (Stock.final (Fin n))
    desired (by simpa only [Stock.final] using expo)
  rw [WilsonMeasuredPublicEntranceCutoffHearing.original] at middle
  unfold WilsonMeasuredPublicEntranceCutoffHearing.difference at middle
  rw [WilsonMeasuredPublicEntranceTransferSubmitted.original R grade A file station axes] at middle
  change ‖prev-old‖≤(∏i,WilsonAddressedHomeDose.ceiling (R:=R) (grade i) (A.M i))*((β f)^desired)⁻¹ at middle
  change ‖(C₀).omega N p raw-ren‖≤ε at projection
  have signed:‖old-ren‖≤ spend+ε:=by
    calc
      _ ≤ ‖old-prev‖+‖prev-(C₀).omega N p raw‖+‖(C₀).omega N p raw-ren‖:=by
        linarith only [norm_sub_le_norm_sub_add_norm_sub old ((C₀).omega N p raw) ren,
          norm_sub_le_norm_sub_add_norm_sub old prev ((C₀).omega N p raw)]
      _ ≤ _:=by rw [norm_sub_rev old prev,norm_sub_rev prev ((C₀).omega N p raw)]
                dsimp only [spend]
                linarith only [middle,first,projection]
  exact ⟨signed,(norm_sub_le_norm_sub_add_norm_sub gibbs old ren).trans (add_le_add_right signed _)⟩


theorem original {wid lo teach}(L:Package R.family wid lo teach)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit){J u:ℕ}
    (stop:Stop (C₀) 0 J u){D T n:ℕ}[Nonempty (Fin n)](d:Fin n→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→ Book F (l:=l) H arch D T s.val)
    (window q:ℕ):
    ∃gate:ℕ,∀ρ:Fin n→{s:ℝ // 0<s ∧ s<δ},let f:=reporter F books ρ
      ∀c:ℕ,gate≤c → u+2≤c → c+2≤f → (C₀).S.a c/(C₀).S.a f≤(β f)^window →
      ∀name:∀i,Bool→S.Field (d i).val,∀radius ε:ℝ,0<ε →
      order.late fun N p=>∀o:Fin n→ Cover,
        (∀i,‖(C₀).S.gridPoint f (o i)‖≤radius) → Extraction.Order.grid (C₀) f o∈conf n →
        (∀i,8*‖(C₀).S.gridPoint f (o i)‖≤(C₀).S.a (c+1)) →
        (Pairwise fun i k=>2*(C₀).S.a f*(((C₀).path.levels.budget f).B:ℝ)^2≤
          ‖(C₀).S.gridPoint f (o i)-(C₀).S.gridPoint f (o k)‖) →
        At F d books ρ name q u f o ε N p:=by
  classical
  obtain ⟨gate,issue⟩:=WilsonPhysicalLicensedFaces.original F L simple slow stop d books window q
  refine ⟨gate,?_⟩
  intro ρ f c hit earlier later ratio name radius ε ep
  have native:=issue ρ c hit earlier later ratio (Stock.final (Fin n)) Finset.univ_nonempty
  obtain ⟨first,cap,wage,_⟩:=WilsonMeasuredPublicEntranceTransferForkNodes.original F (fun i=>books (ρ i)) d name
  let grade:=fun i=>(d i).val
  let sites:Finset (Fin n→ Cover):=WilsonMeasuredPublicEntranceTransferSiteBox.room R f radius
  let P:=fun (z:ℕ×ℕ) (o:Fin n→ Cover)=>Extraction.Order.grid (C₀) f o∈conf n → 
    ∀y:(C₀).book.Vector grade,(∀i,‖y i‖≤cap i) →
      ‖WilsonMeasuredPublicEntranceOrderedPins.physical (C:=C₀) grade f o z.1 z.2 y-publicValue (C:=C₀) (S:=S) grade f o y‖≤ε
  have estimates:∀ᶠz:ℕ×ℕ in order.fuse,∀o∈sites,P z o:=by
    apply (Finset.eventually_all _).mpr
    intro o _
    by_cases safe:Extraction.Order.grid (C₀) f o∈conf n
    · have each:=WilsonMeasuredPublicEntranceTransferSeparatedNodes.ordered R F grade f o simple safe cap ep
      let D:=fun z:ℕ×ℕ=>∀y:(C₀).book.Vector grade,(∀i,‖y i‖≤cap i) →
        ‖WilsonMeasuredPublicEntranceOrderedPins.physical (C:=C₀) grade f o z.1 z.2 y-publicValue (C:=C₀) (S:=S) grade f o y‖≤ε
      filter_upwards [(order.fused D).mpr each] with z read
      exact fun _=>read
    · exact Eventually.of_forall fun _ good=>False.elim (safe good)
  let S₀:=fun z:ℕ×ℕ=>∀o∈sites,P z o
  have cal:order.late fun N _=>first≤N:=Eventually.of_forall fun _=>order.mesh.cofinal.eventually (eventually_ge_atTop first)
  filter_upwards [(order.fused S₀).mp estimates,cal] with k receipts onDate
  filter_upwards [receipts,onDate] with j values opened
  intro o inBox safe room apart
  exact at_node F d books ρ name o native room apart cap (wage _ _ opened)
    (values o (WilsonMeasuredPublicEntranceTransferSiteBox.inside R o inBox) safe)

end YM.Integration.WilsonMeasuredPublicEntranceTransferKnotBoard
end
