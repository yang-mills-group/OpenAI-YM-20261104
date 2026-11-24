import YM.Integration.WilsonReportHarvestUpperConnected
import YM.Integration.WilsonReportHarvestReplayReach
import YM.Integration.WilsonReportHarvestReplayFee
import YM.Integration.WilsonMarkedUltravioletReportingEntries
import YM.Integration.WilsonReportHarvestResidentCalendar
import YM.Integration.WilsonReportHarvestResidentScale
import YM.Integration.WilsonReportHarvestResidentWallet

/-! Whole regular and forced coefficient arrays with the original microscopic palette price. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestReplayEntries
open Finset Function Filter Lattice Wilson RG Marker Push AbsoluteSums
open Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil
open RG05Readout.Many PhysicalNext.Repeat.Legato WilsonReportHarvestSourceReach
open private spend from YM.Integration.WilsonMarkedUltravioletReportingEntries
open scoped Topology BigOperators Classical
variable {G:Gauge}

open private rotate from YM.Integration.WilsonReportHarvestUpperConnected

/-- Both complete signed arrays pay every earlier radius on the original marked interval. -/

theorem original (R:Run G)(simple:G.Simple)(p k h engineering sourceHeat sourceScale reserve berth:ℕ){ε:ℝ}(ep:0<ε):
    ∀ᶠ m:ℕ in atTop,∀j:ℕ,m ≤ j → ∀N:ℕ,j<N → ∀per d n:ℕ,∀nm:n ≤ m,
      ((m-n:ℕ):ℝ) ≤ (berth:ℝ)*(1+Real.log (WilsonMeasuredAdmission.mast R.family.path.levels m)) →
      ∀(o:Fin 3 → Site (R.family.side n per))(E:Fin 3 → Motion)(roster:Census (Fin 3)),
      let J:=Mine.masts o E nm (barren o E roster m) j
      let places:=(Mine.tree o E).supportX j
      let P:=R.family.path.rep N per j
      let α:=(R.family.path.levels.budget j).supportExponent
      let g:=(Real.sqrt P.beta)⁻¹
      ∀(Q:Fin 3 → ℝ)(rows:ManyStem R.family o j → RG05Readout.Address.Three G (R.family.side j per))
        (Z:Config G (R.family.side j per) → Poly J),
      ∀factor:ℝ,1 ≤ factor →
      factor ≤ (R.family.S.a m/R.family.S.a j)^sourceScale*(R.family.path.levels.clock.hatBeta j)^sourceHeat →
      (∀v,0<Q v) → (∀v,Q v ≤ (R.family.path.levels.clock.hatBeta m)^h*factor) → 
      MenuBoard P rows Z places (fun v => RG05Readout.Many.envelope R.family m d k (Q v.val.1) j) α 1 → 
      ∃H K,Carton places H K P.p.threshold ∧
        Z=restore P (fun v => (rows v).2.1) (fun v => profile P.activities (rows v).2.2) H K ∧
        Towed (fun _ : ManyStem R.family o j => (1:ℝ)) id H P.p.B (α-1)
          (ε*g^p/(R.family.S.a m/R.family.S.a j)^engineering/(R.family.path.levels.clock.hatBeta j)^(reserve*(j-n+1))) ∧
        Towed (fun _ : ManyStem R.family o j => (1:ℝ)) (fun i:Box (R.family.side j per) => i.1)
          K P.p.B (α-1) (ε*g^p/(R.family.S.a m/R.family.S.a j)^engineering/(R.family.path.levels.clock.hatBeta j)^(reserve*(j-n+1))):=by
  let A:=R.family.path.levels
  let T₀:=(k+h)*3
  let T:=T₀+sourceHeat*3
  let H:=engineering+sourceScale*3
  let c:ℝ:=(T:ℝ)+p+1
  let t:ℝ:=(H:ℝ)+3
  have cp:0 ≤ c:=by dsimp [c];positivity
  have tp:0 ≤ t:=by dsimp [t];positivity
  obtain ⟨start,paid⟩:=eventually_atTop.mp (WilsonReportHarvestResidentCalendar.forfeit R simple p T H ep)
  filter_upwards [WilsonReportHarvestReplayReach.housing R simple cp tp reserve berth,
    WilsonReportHarvestUpperWallet.weights R.family simple k h 3,eventually_ge_atTop start]
    with m rooms wallet late j mj N live per d n nm prior o E roster J places P α g Q rows Z factor factor₁ upper positive ceiling board
  let e:=elapsed R.family.S m j
  let base:=reach A c t m j
  let D:=WilsonReportHarvestReplayReach.required A c t reserve n m j
  let x:=A.clock.hatBeta j
  let ratio:=R.family.S.a m/R.family.S.a j
  let M:=ratio^(sourceScale*3)*x^T*Real.exp (3*e)
  have rp:0<ratio:=div_pos (R.family.S.a_pos m) (R.family.S.a_pos j)
  have xp:0<x:=zero_lt_one.trans (A.fits.delayed j)
  let w:=fun v:ManyStem R.family o j => RG05Readout.Many.envelope R.family m d k (Q v.val.1) j
  have mp:0 ≤ M:=by dsimp [M];positivity
  have wp (v:ManyStem R.family o j):0<w v:=by
    unfold w RG05Readout.Many.envelope RG05Readout.Many.west
    rw [rust_above mj,one_mul]
    exact grantw (totalpos (positive v.val.1) j)
  have sizes (s:J.Mode):1 ≤ M*Poly.toll w s:=by
    have card:s.val.card ≤ 3:=by simpa only [Fintype.card_fin] using WilsonAllDateHarvestTuningModes.cardinal o E roster nm mj s
    have raw:=wallet j mj d (fun v:ManyStem R.family o j => Q v.val.1) factor factor₁
      (fun v=>positive v.val.1) (fun v=>ceiling v.val.1) s card
    have term:factor^3*(x^T₀*Real.exp (3*e)) ≤ M:=by
      calc
        _ ≤ (ratio^sourceScale*x^sourceHeat)^3*(x^T₀*Real.exp (3*e)):=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans factor₁) upper 3) (mul_nonneg (pow_nonneg xp.le _) (Real.exp_pos _).le)
        _ = _:=by dsimp only [M,T];rw [mul_pow,←pow_mul,←pow_mul,pow_add];ring
    exact raw.trans (mul_le_mul_of_nonneg_right term (Poly.worth wp s).le)
  have engp:0<ratio^engineering:=pow_pos rp _
  have baseFee:M*Real.exp (-(base:ℝ)) ≤ ε*g^p/ratio^engineering:=by
    apply (le_div_iff₀ engp).2
    have charged:=paid j (late.trans mj) m mj N live.le per
    change ratio^(engineering+sourceScale*3)*x^T*Real.exp (3*e)*Real.exp (-(base:ℝ)) ≤ ε*g^p at charged
    rw [pow_add] at charged
    exact (rotate _ _ _ _ _).symm.le.trans charged
  have fee:M*Real.exp (-(D:ℝ)) ≤ ε*g^p/ratio^engineering/x^(reserve*(j-n+1)):=
    WilsonReportHarvestReplayFee.purchased A j (reserve*(j-n+1)) base mp baseFee
  have same:P.p=A.budget j:=(R.T.choice.represents N per j live.le).vac
  have apart (s:J.Mode)(two:2 ≤ s.val.card):
      ∃a∈s.val,∃b∈s.val,D*(4*P.p.B+2)+2*P.p.B < separation (places a) (places b):=by
    obtain ⟨a,ha,b,hb,separated⟩:=WilsonReportHarvestResidentScale.pair o E roster nm mj s two
    refine ⟨a,ha,b,hb,?_⟩
    rw [same]
    exact (rooms n nm prior j mj per).trans_lt separated
  obtain ⟨H,K,layout,regular,forced,allFields⟩:=board.grants
  refine ⟨H,K,layout,allFields,?_,?_⟩
  · exact spend regular wp mp fee sizes (fun i => (layout.exp i).1.toBorne)
      (fun i => (layout.exp i).2) apart
  · exact spend forced wp mp fee sizes (fun i => (layout.flag i).1.toBorne)
      (fun i => (layout.flag i).2) apart
end YM.Integration.WilsonReportHarvestReplayEntries
