import YM.Integration.WilsonOriginalPhysicalCorridorLength
import YM.Integration.WilsonOriginalMountedFailedHalo
import YM.RG17.Rook

/-! The finite signed Wilson comparison at the original flat field and every genuine finite-grade ClockFace. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalCorridorAtBoard
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open Source Labels
open Pert.Asymptotics WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
include simple in
theorem clear (columns:∀ᶠ i:ℕ in atTop,(R.family.path.levels.params i).columns ≤ H i):
    ∀ᶠ i:ℕ in atTop,∀{N per:ℕ}(_live:i ≤ N)(W:Config G (R.family.side i per)),
      WilsonOriginalMountedFailedHalo.board R N per i W →
      flags (R.family.path.rep N per i).p.threshold W=∅:=by
  filter_upwards [Next.Rank.Spindle.paidThrough R.family 0 R.makes simple columns] with i bank
  intro N per live W which
  rcases which with rfl|⟨d,face,a,rfl⟩
  · exact UVNext.CouplingReset.flags_one _
  · exact (bank N per live).1 _ (face.tiles a).property

variable {V:Type}[DecidableEq V][Fintype V](marks:Marker.Census V)
include simple in
theorem original (n cost a p desired debt ext raw w:ℕ)(np:0<n)(load:∀s:marks.Mode,s.val.card ≤ n)(e:ℝ)(ep:0<e)
    (order:desired+ext ≤ p)(reserve:desired+1+debt*n+2 ≤ p)
    (columns:∀ᶠ i:ℕ in atTop,(R.family.path.levels.params i).columns ≤ H i):
    ∃start:ℕ,∀(b N per m k L:ℕ),start ≤ b → m ≤ b+1 → ∀(live:b+1+L ≤ N),
    R.family.S.a (b+1)/R.family.S.a (b+1+L) ≤ (H (b+1))^cost →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(physical:Config G (R.family.side N per)→Poly marks),
    Integrable physical (prior G _) →
    ∀(trial:∀j,Config G (R.family.side j per)→Poly marks),
    (∀i,b+1 ≤ i → i ≤ b+1+L → Integrable (trial i) (prior G _)) →
    ∀(P:∀j:Fin L,Slice R marks (Ψ (b+j.val+1))),
    (∀j:Fin L,(P j).A.density (P j).x=LocalComparison.actualPush R.family N per (b+j.val+1) (trial (b+j.val+1+1))) →
    ∀(s:marks.Mode)(S:Fin L → V → ℝ),(∀j v,0 < S j v) → (∀j:Fin L,(WilsonOriginalOccupiedSalary.debit (P j).regular (P j).hard)^s.val.card ≤
      (H (b+j.val+1))^a*(Poly.toll (S j) s*Poly.toll (P j).w s)) →
    ∀W:Config G (R.family.side (b+1) per),WilsonOriginalMountedFailedHalo.board R N per (b+1) W →
    ∀{d₀:ℕ}{frame:Frame G d₀}(section_:SectionData frame)(group:Hol G)
    (F:∀j:Fin L,WilsonOriginalMountedRegular.Filing R (Ψ (b+j.val+1)) (P j) (trial (b+j.val+1)) s),
    let enter:=read R N per W (show b+1 ≤ b+1+L by omega)
      (gust R.family.path N per N physical (b+1+L) live-trial (b+1+L)) s
    let g:=regulatorRun R.family N per (b+1)
    let q:=desired+1+debt*n
    (∀j,Poly.toll (S j) s ≤ (g^ext)⁻¹) → (∀j,(F j).M ≤ (g^debt)⁻¹) →
    (∀j:Fin L,(R.family.path.levels.budget (b+j.val+1)).supportExponent ≤ 100) →
    (∀j,1 ≤ (F j).α ∧ (F j).h=WilsonOriginalMountedRegularFare.crop (q+1+w+raw) g) →
    (∀j,(F j).W ≤ (g^w)⁻¹ ∧ (F j).gross ≤ (g^raw)⁻¹ ∧ (F j).rent ≤ g^(q+1+w) ∧ (F j).δ ≤ g^(q+1)) →
    ‖read R N per W (show b+1 ≤ N by omega) physical s-
      (((R.family.path.rep N per (b+1)).eval W:ℂ)⁻¹)*(trial (b+1) W).part s‖ ≤
      ‖enter‖+((4*(cost:ℝ)/Real.log 3)*WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+e*(shards marks s).card)*g^desired:=by
  let c:ℝ:=(cost:ℝ)/Real.log 3
  let q:=desired+1+debt*n
  let cap:ℝ:=(↑(q+1+w+raw):ℝ)
  have cap0:0 ≤ cap:=Nat.cast_nonneg _
  have cp:0 ≤ c:=div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  obtain ⟨r0,signed⟩:=WilsonOriginalPhysicalCorridorPrecision.original R simple marks n 1 a p desired debt ext np load c e
    (4*(cost:ℝ)/Real.log 3) cp ep order
  obtain ⟨r1,thermal⟩:=eventually_atTop.mp (WilsonOriginalPhysicalCorridorLength.original R simple cost)
  obtain ⟨r2,cleared⟩:=eventually_atTop.mp (clear R simple columns)
  let first:=WilsonOriginalMountedFailedHalo.first R simple n cap0 ep.le
  let opening:=(eventually_atTop.mp (WilsonOriginalMountedFailedHalo.received R simple)).choose
  refine ⟨r0+r1+r2+first+opening,?_⟩
  intro b N per m k L age mb live ratio way D Q π Γ Ψ course ticket physical hp trial ht rows source s S sp wages W node
    dim frame section_ group F
  dsimp only
  intro toll gross fixed crop tarifs
  let g:=regulatorRun R.family N per (b+1)
  obtain ⟨gp,cold,length⟩:=thermal (b+1) (by omega) live ratio
  have gs:g ≤ 1:=by linarith only [gp,cold]
  have size:debt*s.val.card ≤ debt*n:=Nat.mul_le_mul_left _ (load s)
  have sufficient:desired+1+debt*s.val.card ≤ q:=Nat.add_le_add_left size _
  have span (j:Fin L):(j.val:ℝ) ≤ c*(1+Real.log (H (b+j.val+1)))^1:=by
    simpa only [Nat.add_right_comm b 1 j.val] using WilsonOriginalPhysicalCorridorLength.span R simple cost (b+1) L j ratio
  have point:(Ψ (b+1)).p=(R.family.path.rep N per (b+1)).p:=
    (course.1.walk (b+1) mb (by omega)).truep.point.trans (R.makes.wilson.represents N per (b+1) (by omega)).vac.symm
  have clearW:flags (Ψ (b+1)).p.threshold W=∅:=by
    rw [point]
    exact cleared (b+1) (by omega) (by omega) W node
  apply signed b N per m k L (by omega) mb live span way D Q π Γ Ψ course ticket physical hp trial ht rows source s S sp wages W
    clearW section_ group F gp gs length (fun j=>zero_le_one.trans (R.family.path.levels.fits.delayed (b+j.val+1)).le) toll gross
  · intro j
    obtain ⟨wp,sz,old,peg⟩:=tarifs j
    exact (WilsonOriginalMountedRegularFare.small q w raw (F j).h gp cold (crop j).1 (crop j).2.ge wp sz
      (F j).rent_nn (F j).gross_nn old peg).trans (pow_le_pow_of_le_one gp.le gs sufficient)
  · intro j
    have cut:(F j).h ≤ Nat.ceil (cap*(1+Real.log g⁻¹)):=by
      rw [(crop j).2]
      exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) cap0)
    exact WilsonOriginalMountedFailedHalo.original R simple n cap0 ep.le course mb (by omega) (by omega) (F j) (fixed j)
      (load s) cut (desired+1) debt p (Nat.le_trans (Nat.add_le_add_right sufficient 2) reserve) W (by omega) (by omega) node

end YM.Integration.WilsonOriginalPhysicalCorridorAtBoard
end
