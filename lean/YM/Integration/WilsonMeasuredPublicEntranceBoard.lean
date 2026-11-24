import YM.Integration.WilsonMeasuredPublicEntranceSelected
import YM.Integration.WilsonMeasuredPublicClearance

/-! The exact finite slot enrollment on *every* board of the previously elected
PublicFullRoster. Its source, proper faces and scalar restoration use this bank. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceBoard
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    {D : ℕ} (l:Ultrafilter (ℕ×ℕ))
open WilsonMeasuredPublicClearance WilsonThermometerUnitFilingFourPoolClock WilsonThermometerUnitFilingFourPoolShell
open GapsContact GapsContact.Seams GapsContact.Stamps OPE Trace.Pilot PhysMS FVA2 FVA2.Register
variable {z:Trace.Terrace.Arch R.family}
local notation "C₀" => R.family

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    :
    ∃ t ≥ D+3, ∀ (T count:ℕ) (δ:ℝ), 0<δ → ∀ᶠ r:ℝ in trail,
    ∀ board:Book F l (z:=z) D T count δ r, let j:=board.bank.j
    ∀ p N (deep : j < N),
    ∃ (V : (a : Fin (D+1)) → Sight C₀ a.val p) (u : (a : Fin (D+1)) → Emblems C₀ a.val)
      (est : ∀ a : Fin (D+1), Opened C₀ a.val (j) p),
    (∀ a, Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) (j) N p a.val
      (digits R N p 0) (V a) (u a)) ∧
    ∀ (I : Type) [Fintype I] [DecidableEq I] (d : I → Fin (D+1)) (v : (i : I) → S.Field (d i).val)
      (c : I → Site ((C₀).side (j) p)) (names : Census I),
    let radius:=WilsonThermometerUnitFilingFourPoolShell.radius z (WilsonMeasuredPublicClearance.deep T) r
    let wallet:=dock radius^T
    let L:=fun i=>(board.bank.department (d i).val (Nat.le_of_lt_succ (d i).isLt)).print (v i)
    (∀ i j' : I, i≠j' → ((C₀).path.levels.budget (j)).B^2 <
      separation (point R (N:=N) 0 (1,false) (c i) (j)) (point R (N:=N) 0 (1,false) (c j') (j))) →
    let x:=fun i=>(L i).arm.source (N,p)
    let y := fun i => offer R (x i) (est (d i)) deep.le
    let b := fun i => anchorAt R (c i) N
    let data := fun i => reduce (y i)
    (∀ i, charge (y i) ≤ max 1 (2*(wallet*GapsContact.Ascent.cost F (d i).val (radius) (v i)))) ∧
    WilsonThermometerReflectedRoster.filed R (fun i => (d i).val) (fun _ => 0) (fun _ => (1,false)) c
      data (fun i => V (d i)) (fun i => u (d i)) names deep.le t ∧
    ∀ j (hj : j ≤ N) (s : names.Mode) T,
      (WilsonThermometerReflectedRoster.density R (fun i => (d i).val) (fun _ => 0) (fun _ => (1,false)) c
        data (fun i => u (d i)) names deep.le hj T).part s =
      ((C₀).path.rep N p j).eval T • actualTransport C₀ (N:=N)
        (fun W => ∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p (x i) (b i) W) hj T := by
  obtain ⟨t,tp,cash⟩:=WilsonMeasuredPublicEntranceSelected.original (D:=D) R F l simple shop
  obtain ⟨J,wake⟩:=eventually_atTop.mp cash
  refine ⟨t,tp,?_⟩
  intro T count δ _hδ
  have small:∀ᶠ r:ℝ in trail,δ*r<(C₀).S.a J:=by
    have lim:Tendsto (fun r:ℝ=>δ*r) trail (𝓝 0):=by
      have h:Tendsto (fun r:ℝ=>r) trail (𝓝 0):=nhdsWithin_le_nhds
      simpa using h.const_mul δ
    exact lim.eventually_lt_const ((C₀).S.a_pos J)
  filter_upwards [small] with r cost b
  let d₀:=b.bank.department 0 (Nat.zero_le _)
  let seed:=d₀.print 0
  obtain ⟨eqj,eqm⟩:=d₀.dated 0
  have mj:b.bank.m≤b.bank.j:= by simpa only [seed,eqj,eqm] using seed.fore
  have hi:J≤b.bank.j:=by
    apply le_of_not_gt
    intro no
    have decay:=(C₀).S.strictAnti.antitone ((b.before.trans mj).trans no.le)
    linarith [b.small]
  intro j p N deep
  obtain ⟨V,u,est,applied,issued⟩:=wake b.bank.j hi p N deep
  refine ⟨V,u,est,applied,?_⟩
  intro I fi di d v c names radius wallet L room
  exact issued I d radius wallet v c names L
    (fun i=>((b.bank.department (d i).val (Nat.le_of_lt_succ (d i).isLt)).dated _).1) room

end YM.Integration.WilsonMeasuredPublicEntranceBoard
end
