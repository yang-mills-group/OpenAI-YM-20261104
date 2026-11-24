import YM.Integration.WilsonReportHarvestResidentConnected
import YM.Integration.WilsonReportHarvestUpperWallet

/-! The actual upper course pays a scale-dependent ultraviolet source at admissible dated separations. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestUpperConnected
open Finset Function Filter Lattice Wilson RG Marker Push AbsoluteSums
open Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil
open RG05Readout.Many PhysicalNext.Repeat.Legato WilsonReportHarvestSourceReach
open private spend from YM.Integration.WilsonMarkedUltravioletReportingEntries
open scoped Topology BigOperators Classical
open WilsonMeasuredAdmission Extra.Trajectories
variable {G:Gauge}

private theorem rotate (a b c f v:ℝ) : a*b*c*f*v = b*c*f*v*a := by ring

open private allotted from YM.Integration.WilsonReportHarvestResidentConnected

theorem original (R:Run G)(simple:G.Simple)(p k h engineering sourceHeat sourceScale:ℕ){ε:ℝ}(ep:0<ε):
    ∀ᶠ m:ℕ in atTop,∀j:ℕ,m ≤ j → ∀N:ℕ,j<N → ∀per d n:ℕ,∀nm:n ≤ m,
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
      ∀(U:Config G (R.family.side j per)),flags P.p.threshold U=∅ → ∀s:J.Mode,2 ≤ s.val.card →
        ‖(connected ((P.eval U:ℂ)⁻¹ • Z U)).part s‖ ≤ ε*g^p/(R.family.S.a m/R.family.S.a j)^engineering:=by
  let A:=R.family.path.levels
  let T₀:=(k+h)*3
  let T:=T₀+sourceHeat*3
  let H:=engineering+sourceScale*3
  let c:ℝ:=(T:ℝ)+p+1
  let t:ℝ:=(H:ℝ)+3
  let a:=(A.params 0).supportExponent
  have ap:0<a:=(A.params 0).price_pos
  have cp:0 ≤ c:=by dsimp [c];positivity
  have tp:0 ≤ t:=by dsimp [t];positivity
  obtain ⟨start,paid⟩:=eventually_atTop.mp (WilsonReportHarvestResidentCalendar.forfeit R simple p T H ep)
  filter_upwards [WilsonReportHarvestResidentCalendar.housing R simple (show 0 ≤ (c+2)/a by positivity)
      (show 0 ≤ t/a by positivity),
    WilsonReportHarvestUpperWallet.weights R.family simple k h 3,eventually_ge_atTop start]
    with m rooms wallet late j mj N live per d n nm o E roster J places P α g Q rows Z factor factor₁ upper positive ceiling board U clear s two
  let e:=elapsed R.family.S m j
  let D:=reach A c t m j
  let D':=reach A ((c+2)/a) (t/a) m j
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
  have card:s.val.card ≤ 3:=by simpa only [Fintype.card_fin] using WilsonAllDateHarvestTuningModes.cardinal o E roster nm mj s
  have raw:=wallet j mj d (fun v:ManyStem R.family o j => Q v.val.1) factor factor₁
    (fun v=>positive v.val.1) (fun v=>ceiling v.val.1) s card
  have term:factor^3*(x^T₀*Real.exp (3*e)) ≤ M:=by
    calc
      _ ≤ (ratio^sourceScale*x^sourceHeat)^3*(x^T₀*Real.exp (3*e)):=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans factor₁) upper 3) (mul_nonneg (pow_nonneg xp.le _) (Real.exp_pos _).le)
      _ = _:=by dsimp only [M,T];rw [mul_pow,←pow_mul,←pow_mul,pow_add];ring
  have sizes:1 ≤ M*Poly.toll w s:=raw.trans (mul_le_mul_of_nonneg_right term (Poly.worth wp s).le)
  have engp:0<ratio^engineering:=pow_pos rp _
  have fee:M*Real.exp (-(D:ℝ)) ≤ ε*g^p/ratio^engineering:=by
    apply (le_div_iff₀ engp).2
    have charged:=paid j (late.trans mj) m mj N live.le per
    change ratio^(engineering+sourceScale*3)*x^T*Real.exp (3*e)*Real.exp (-(D:ℝ)) ≤ ε*g^p at charged
    rw [pow_add] at charged
    exact (rotate _ _ _ _ _).symm.le.trans charged
  obtain ⟨left,hl,right,hr,span⟩:=WilsonReportHarvestResidentScale.pair o E roster nm mj s two
  have same:P.p=A.budget j:=(R.T.choice.represents N per j live.le).vac
  have room:D'*(4*P.p.B+2)+2*P.p.B<separation (places left) (places right):=by
    rw [same];exact (rooms j mj per).trans_lt span
  have width:a ≤ α:=A.fits.deepExp (Nat.zero_le j)
  have weighted:=WilsonReportHarvestResidentLog.original board wp (ap.le.trans width) U clear s two left right hl hr D' room
  have charge:=allotted A cp tp ap mj width
  have discount:Real.exp (-α*(D':ℝ)) ≤ Real.exp (-(D:ℝ)):=Real.exp_le_exp.mpr (by
    change (D:ℝ) ≤ α*(D':ℝ) at charge;linarith only [charge])
  rw [mul_one] at weighted
  let X:=‖(connected ((P.eval U:ℂ)⁻¹ • Z U)).part s‖
  calc
    X ≤ (M*Poly.toll w s)*X:=le_mul_of_one_le_left (norm_nonneg _) sizes
    _ = M*(Poly.toll w s*X):=mul_assoc _ _ _
    _ ≤ M*Real.exp (-α*(D':ℝ)):=mul_le_mul_of_nonneg_left weighted mp
    _ ≤ M*Real.exp (-(D:ℝ)):=mul_le_mul_of_nonneg_left discount mp
    _ ≤ _:=fee

end YM.Integration.WilsonReportHarvestUpperConnected
