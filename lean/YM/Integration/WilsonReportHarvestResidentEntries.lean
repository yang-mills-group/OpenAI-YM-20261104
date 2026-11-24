import YM.Integration.WilsonMarkedUltravioletReportingEntries
import YM.Integration.WilsonReportHarvestResidentCalendar
import YM.Integration.WilsonReportHarvestResidentScale
import YM.Integration.WilsonReportHarvestResidentWallet

/-! Whole original mixed regular and hard tables on all genuinely later harvest dates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestResidentEntries
open Finset Function Filter Lattice Wilson RG Marker Push AbsoluteSums
open Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil
open RG05Readout.Many PhysicalNext.Repeat.Legato WilsonReportHarvestSourceReach
open private spend from YM.Integration.WilsonMarkedUltravioletReportingEntries
open scoped Topology BigOperators Classical
variable {G:Gauge}

/-- The unweighted bill covers the whole originally enrolled table, including all its retained heights. -/
theorem original (R:Run G)(simple:G.Simple)(p k h engineering:ℕ){ε:ℝ}(ep:0<ε):
    ∀ᶠ m:ℕ in atTop,∀j:ℕ,m ≤ j → ∀N:ℕ,j<N → ∀per d n:ℕ,∀nm:n ≤ m,
      ∀(o:Fin 3 → Site (R.family.side n per))(E:Fin 3 → Motion)(roster:Census (Fin 3)),
      let J:=Mine.masts o E nm (barren o E roster m) j
      let places:=(Mine.tree o E).supportX j
      let P:=R.family.path.rep N per j
      let α:=(R.family.path.levels.budget j).supportExponent
      let g:=(Real.sqrt P.beta)⁻¹
      ∀(Q:Fin 3 → ℝ)(rows:ManyStem R.family o j → RG05Readout.Address.Three G (R.family.side j per))
        (Z:Config G (R.family.side j per) → Poly J),
      (∀v,0<Q v) → (∀v,Q v ≤ (R.family.path.levels.clock.hatBeta m)^h) → 
      MenuBoard P rows Z places (fun v => RG05Readout.Many.envelope R.family m d k (Q v.val.1) j) α 1 → 
      ∃H K,Carton places H K P.p.threshold ∧
        Z=restore P (fun v => (rows v).2.1) (fun v => profile P.activities (rows v).2.2) H K ∧
        Towed (fun _ : ManyStem R.family o j => (1:ℝ)) id H P.p.B (α-1)
          (ε*g^p/(R.family.S.a m/R.family.S.a j)^engineering) ∧
        Towed (fun _ : ManyStem R.family o j => (1:ℝ)) (fun i:Box (R.family.side j per) => i.1)
          K P.p.B (α-1) (ε*g^p/(R.family.S.a m/R.family.S.a j)^engineering):=by
  let A:=R.family.path.levels
  let T:=(k+h)*3
  let c:ℝ:=(T:ℝ)+p+1
  let t:ℝ:=(engineering:ℝ)+3
  obtain ⟨start,paid⟩:=eventually_atTop.mp (WilsonReportHarvestResidentCalendar.forfeit R simple p T engineering ep)
  filter_upwards [WilsonReportHarvestResidentCalendar.housing R simple (show 0 ≤ c by dsimp [c];positivity)
      (show 0 ≤ t by dsimp [t];positivity),
    WilsonReportHarvestResidentWallet.weights R.family simple k h 3,eventually_ge_atTop start]
    with m rooms wallet late j mj N live per d n nm o E roster J places P α g Q rows Z positive ceiling board
  let e:=elapsed R.family.S m j
  let D:=reach A c t m j
  let M:=(A.clock.hatBeta j)^T*Real.exp (3*e)
  let w:=fun v:ManyStem R.family o j => RG05Readout.Many.envelope R.family m d k (Q v.val.1) j
  have mp:0 ≤ M:=mul_nonneg (pow_nonneg (zero_lt_one.trans (A.fits.delayed j)).le _) (Real.exp_pos _).le
  have wp (v:ManyStem R.family o j):0<w v:=by
    unfold w RG05Readout.Many.envelope RG05Readout.Many.west
    rw [rust_above mj,one_mul]
    exact grantw (totalpos (positive v.val.1) j)
  have sizes (s:J.Mode):1 ≤ M*Poly.toll w s:=by
    apply wallet j mj d (fun v:ManyStem R.family o j => Q v.val.1) (fun v => positive v.val.1)
      (fun v => ceiling v.val.1) s
    simpa only [Fintype.card_fin] using WilsonAllDateHarvestTuningModes.cardinal o E roster nm mj s
  have engp:0<(R.family.S.a m/R.family.S.a j)^engineering:=pow_pos
    (div_pos (R.family.S.a_pos m) (R.family.S.a_pos j)) _
  have fee:M*Real.exp (-(D:ℝ)) ≤ ε*g^p/(R.family.S.a m/R.family.S.a j)^engineering:=by
    apply (le_div_iff₀ engp).2
    have charged:=paid j (late.trans mj) m mj N live.le per
    simpa only [M,D,c,t,T,e,g,P,mul_assoc,mul_comm,mul_left_comm] using charged
  have same:P.p=A.budget j:=(R.T.choice.represents N per j live.le).vac
  have apart (s:J.Mode)(two:2 ≤ s.val.card):
      ∃a∈s.val,∃b∈s.val,D*(4*P.p.B+2)+2*P.p.B < separation (places a) (places b):=by
    obtain ⟨a,ha,b,hb,separated⟩:=WilsonReportHarvestResidentScale.pair o E roster nm mj s two
    refine ⟨a,ha,b,hb,?_⟩
    rw [same]
    exact (rooms j mj per).trans_lt separated
  obtain ⟨H,K,layout,regular,forced,allFields⟩:=board.grants
  refine ⟨H,K,layout,allFields,?_,?_⟩
  · exact spend regular wp mp fee sizes (fun i => (layout.exp i).1.toBorne)
      (fun i => (layout.exp i).2) apart
  · exact spend forced wp mp fee sizes (fun i => (layout.flag i).1.toBorne)
      (fun i => (layout.flag i).2) apart
end YM.Integration.WilsonReportHarvestResidentEntries
