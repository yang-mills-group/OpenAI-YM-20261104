import YM.Integration.WilsonThermometerWeakIssuedSites
import YM.Integration.WilsonMixedTaggedStart
import YM.Integration.WilsonMixedTaggedWeightedReserve
import YM.Integration.WilsonMarkedUltravioletMixedWallet

/-! Enlarge only the actual deposited mixed arrays on the original representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMixedMenu
open Function Filter Finset Lattice Wilson RG Source Marker Push AbsoluteSums
open MergeProof MergeProof.Accent RG05Readout RG05Readout.Address Extra.Histories Ac
open GridApprox.Nil RG05Readout.Native Cells PhysicalNext.Repeat.Legato
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOffsetTrajectory
open scoped Topology BigOperators Classical
variable {G:Gauge}

def Paired {n:Side} {V:Type} [Fintype V] [DecidableEq V] {J:Census V} (P:Rep G n)
    (Φ:V→ Config G n→ℂ) (κ:V→Box n→ Config G n→ℂ) (X:Config G n→ Poly J) (o:V→Site n)
    (w:V→ℝ) (e:ℝ) (D:ℕ) : Prop :=
  let δ:=Real.exp (-(D:ℝ))
  Served P Φ κ X o w (e-1) δ ∧ ∃ Z:Config G n→ Poly (census J),
    Served P (liveRow Φ) (liveRow κ) Z (o ∘ Prod.fst) (w ∘ Prod.fst) (e-1) 1 ∧
    (∀U,specialize J (δ:ℂ) (Z U)=X U) ∧
    (∀U,specialize J 0 (Z U)=restore P Φ κ (0:Support n→ Config G n→ Poly J) 0 U)

theorem paid {n:Side} {V:Type} [Fintype V] [DecidableEq V] {J:Census V} {P:Rep G n}
    {Φ:V→ Config G n→ℂ} {κ:V→Box n→ Config G n→ℂ} {X:Config G n→ Poly J} {o:V→Site n}
    {w:V→ℝ} {e:ℝ} {D:ℕ} (source:Served P Φ κ X o w e 1) (wp:∀v,0<w v)
    (far:∀i j,i≠j→D*(4*P.p.B+2)+2*P.p.B < separation (o i) (o j)) :
    Paired P Φ κ X o w e D := by
  obtain ⟨H,K,cart,hr,hk,field⟩:=source
  have separated (s:J.Mode) (many : 2 ≤ s.val.card) :
      ∃a∈s.val,∃b∈s.val,D*(4*P.p.B+2)+2*P.p.B < separation (o a) (o b) := by
    obtain ⟨a,ha,b,hb,ne⟩:=Finset.one_lt_card.mp (show 1 < s.val.card from many)
    exact ⟨a,ha,b,hb,far a b ne⟩
  have regs:=WilsonMarkedUltravioletMixedWallet.reach (fun i=>(cart.exp i).1.toBorne)
    (fun i U s nz=>separated s ((cart.exp i).2 U s nz))
  have forces:=WilsonMarkedUltravioletMixedWallet.reach (fun i=>(cart.flag i).1.toBorne)
    (fun i U s nz=>separated s ((cart.flag i).2 U s nz))
  have smallH : Towed w id H P.p.B (e-1) (Real.exp (-(D:ℝ))) := by
    simpa only [mul_one] using WilsonMixedTaggedWeightedReserve.original hr wp regs
  have smallK : Towed w (fun i:Box n=>i.1) K P.p.B (e-1) (Real.exp (-(D:ℝ))) := by
    simpa only [mul_one] using WilsonMixedTaggedWeightedReserve.original hk wp forces
  let δ:=Real.exp (-(D:ℝ))
  let Z:=WilsonMixedTaggedStart.lifted (R:=P) Φ κ δ H K
  have pos:0<δ:=Real.exp_pos _
  refine ⟨⟨H,K,cart,smallH,smallK,field⟩,Z,WilsonMixedTaggedStart.represented Φ κ pos cart smallH smallK,?_,?_⟩
  · intro U
    exact (WilsonMixedTaggedStart.endpoints Φ κ pos cart U).1.trans (congrFun field U).symm
  · intro U
    exact (WilsonMixedTaggedStart.endpoints Φ κ pos cart U).2

variable (R:Run G) {w N p t j:ℕ} {o:Fin 3→Site (R.family.side N p)}
local notation "d" => WilsonThermometerFundedWeakCells.degree
local notation "slots" => (Stock.census (Fin 3))
variable {V:(i:Fin 3)→Sight R.family (d i) p} {Q:(i:Fin 3)→Emblems R.family (d i)} {h:w≤N}
variable (y:(i:Fin 3)→Palette R.family (d i))
local notation "Y₀" => (fun i=>WilsonThermometerMarchSource.reduce (y i))
local notation "row" => (fun j i=>state (k:=w) R (V i) (Q i) (Y₀ i) (o i) j)
local notation "P" => R.family.path.rep N p j

theorem original (income:WilsonThermometerIntrinsicRoster.filed R d o Y₀ V Q slots h t)
    (lower:w≤j) (before:j≤N) {D:ℕ}
    (far:∀i i':Fin 3,i≠i'→D*(4*(P).p.B+2)+2*(P).p.B <
      separation (WilsonThermometerOwnOffsetJoint.origins R o j i) (WilsonThermometerOwnOffsetJoint.origins R o j i')) :
    Paired (P) (fun i=>(row j i).2.1) (Accent.tapes R.family.path p N (fun l i=>(row l i).2.2) j)
      (WilsonThermometerIntrinsicRoster.density R d o Y₀ Q slots h before) (WilsonThermometerOwnOffsetJoint.origins R o j)
      (fun _=>radius R t w j) (topPitch R.family.path N j) D :=
  paid (income j lower before).2.2 (fun _=>radius_pos R t w j lower) far

end YM.Integration.WilsonThermometerWeakMixedMenu
end

