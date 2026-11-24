import YM.Integration.WilsonMarkedIndependentConnectedHistory
import YM.Integration.WilsonFiniteMarkedHistory
import YM.Integration.PeriodicMarkedWinding

/-! Signed finite-minus-folded price on the two independent connected programs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentWinding
open Function Filter Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Mesa Next.Free Stationary Work.F03 Work.F05 Work.F08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonFiniteMarkedHistoryStep
open WilsonMarkedIndependentConnectedHistory (finite cover)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}

omit [DecidableEq I] in
private theorem applyRow {V U α:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
    [NormedAddCommGroup U][NormedSpace ℝ U] {n:Side}{r:ℕ}{x:I → Cover}{S:Finset I}
    {P:Ten V (Co n α) r}{F:Ten V (Cloth α) r}{σ B:ℝ}
    (old:MarkU x S P F σ B)(f:V→L[ℝ]U):
    MarkU x S (fun y=>f (P y)) (fun y=>f (F y)) σ (‖f‖*B):=by
  refine ⟨⟨mul_nonneg (norm_nonneg _) old.access.1,fun y=>?_⟩,
    ⟨mul_nonneg (norm_nonneg _) old.bill.1,fun y=>?_⟩,
    ⟨mul_nonneg (norm_nonneg _) old.gulf.coal,fun y h=>?_⟩⟩
  · exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (old.access.2 y) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)
  · exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (old.bill.2 y) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)
  · rw [←map_sub]
    exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (old.gulf.local_w y h) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)

variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

theorem rooted (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N b j e:ℕ}(live:j≤b)(top:b≤N)(K k:I→ℕ)(seed:Outerm G D)(well:Wellness k seed)(a:Loc G 1)
    {σ B:ℝ}(issued:paired e (Gears V R.metals.O K k N b j seed) σ B)
    (x:I → Cover)(A:Case D)(S:Finset I)(n:Side)(cap:ℕ)(cost:mass k S≤cap)(i r:ℕ)(cut:i≤e):
    MarkU x S (finite R u tags N b j K seed x A S n i r)
      (cover R u N b j cap K seed x A S i r) σ (‖touch A S‖*B^S.card):=by
  obtain ⟨here,there⟩:=WilsonMarkedIndependentConnectedHistory.original R u tags simple v funded live top
    K k seed well a x A S n cap cost
  rw [←here,←there]
  exact applyRow (issued n x S i cut r) (touch A S)

def Folded {N b j e:ℕ}(K k:I→ℕ)(seed:Outerm G D)(σ B:ℝ):Prop:=
  ∀ (n:Side)(z:I → Site n)(A:Case D)(S:Finset I)(o:I),o∈S→∀cap,mass k S≤cap→∀i,i≤e→∀r,
    let x:=PeriodicMarkedWinding.roots n z o
    let E:=‖touch A S‖*B^S.card
    let price:=(priceM (Hooks G) r σ + tiePay (Hooks G) r (σ/4)+1)*E+E
    Wig (tor n) z (σ/32/2) (price*catchW (σ/32/16) n) S
      (Carp.plume (cover R u N b j cap K seed x A S i r) n - finite R u tags N b j K seed x A S n i r)

theorem periodized (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N b j e:ℕ}(live:j≤b)(top:b≤N)(K k:I→ℕ)(seed:Outerm G D)(well:Wellness k seed)(a:Loc G 1)
    {σ B:ℝ}(hs:0<σ)(issued:paired e (Gears V R.metals.O K k N b j seed) σ B):
    Folded R u tags (N:=N) (b:=b) (j:=j) (e:=e) K k seed σ B:=by
  intro n z A S o ho cap fee i cut r
  exact PeriodicMarkedWinding.periodized z o ho hs
    (rooted R u tags simple v funded live top K k seed well a issued
      (PeriodicMarkedWinding.roots n z o) A S n cap fee i r cut)

end YM.Integration.WilsonMarkedIndependentWinding
end
