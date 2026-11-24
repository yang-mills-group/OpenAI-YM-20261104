import YM.Integration.WilsonReportHarvestResidentLog
import YM.Integration.WilsonReportHarvestResidentEntries

/-! Normalized actual connected prices at every later date of the same harvest. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestResidentConnected
open Finset Function Filter Lattice Wilson RG Marker Push AbsoluteSums
open Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil
open RG05Readout.Many PhysicalNext.Repeat.Legato WilsonReportHarvestSourceReach
open private spend from YM.Integration.WilsonMarkedUltravioletReportingEntries
open scoped Topology BigOperators Classical
open WilsonMeasuredAdmission Extra.Trajectories
variable {G:Gauge}

private theorem allotted (A:Levels G){c t a:ℝ}(cp:0 ≤ c)(tp:0 ≤ t)(ap:0<a)
    {m j:ℕ}(mj:m ≤ j){α:ℝ}(wide:a ≤ α):
    (reach A c t m j:ℝ) ≤ α*(reach A ((c+2)/a) (t/a) m j:ℝ):=by
  let x:=mast A j
  let e:=elapsed A.S m j
  have one:1 ≤ x:=(mast_gt_one A j).le
  have e0:0 ≤ e:=sub_nonneg.mpr ((OPE.scale_mono A.S).monotone mj)
  have p1:(⌈c*x⌉₊:ℝ)<c*x+1:=Nat.ceil_lt_add_one (mul_nonneg cp (zero_le_one.trans one))
  have p2:(⌈t*e⌉₊:ℝ)<t*e+1:=Nat.ceil_lt_add_one (mul_nonneg tp e0)
  have lo1:=Nat.le_ceil (((c+2)/a)*x)
  have lo2:=Nat.le_ceil ((t/a)*e)
  simp only [WilsonReportHarvestSourceReach.reach,WilsonReportHarvestSourceReach.depth,pow_one,pow_zero,mul_one,Nat.cast_add]
  change (⌈c*x⌉₊:ℝ)+⌈t*e⌉₊ ≤ α*((⌈((c+2)/a)*x⌉₊:ℝ)+⌈t/a*e⌉₊)
  calc
    _ ≤ (c+2)*x+t*e:=by linarith only [p1,p2,one]
    _ = a*(((c+2)/a)*x+(t/a)*e):=by field_simp [ap.ne']
    _ ≤ a*((⌈((c+2)/a)*x⌉₊:ℝ)+⌈t/a*e⌉₊):=mul_le_mul_of_nonneg_left (add_le_add lo1 lo2) ap.le
    _ ≤ _:=mul_le_mul_of_nonneg_right wide (by positivity)

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
      ∀(U:Config G (R.family.side j per)),flags P.p.threshold U=∅ → ∀s:J.Mode,2 ≤ s.val.card →
        ‖(connected ((P.eval U:ℂ)⁻¹ • Z U)).part s‖ ≤ ε*g^p/(R.family.S.a m/R.family.S.a j)^engineering:=by
  let A:=R.family.path.levels
  let T:=(k+h)*3
  let c:ℝ:=(T:ℝ)+p+1
  let t:ℝ:=(engineering:ℝ)+3
  let a:=(A.params 0).supportExponent
  have ap:0<a:=(A.params 0).price_pos
  have cp:0 ≤ c:=by dsimp [c];positivity
  have tp:0 ≤ t:=by dsimp [t];positivity
  obtain ⟨start,paid⟩:=eventually_atTop.mp (WilsonReportHarvestResidentCalendar.forfeit R simple p T engineering ep)
  filter_upwards [WilsonReportHarvestResidentCalendar.housing R simple (show 0 ≤ (c+2)/a by positivity)
      (show 0 ≤ t/a by positivity),
    WilsonReportHarvestResidentWallet.weights R.family simple k h 3,eventually_ge_atTop start]
    with m rooms wallet late j mj N live per d n nm o E roster J places P α g Q rows Z positive ceiling board U clear s two
  let e:=elapsed R.family.S m j
  let D:=reach A c t m j
  let D':=reach A ((c+2)/a) (t/a) m j
  let M:=(A.clock.hatBeta j)^T*Real.exp (3*e)
  let w:=fun v:ManyStem R.family o j => RG05Readout.Many.envelope R.family m d k (Q v.val.1) j
  have mp:0 ≤ M:=mul_nonneg (pow_nonneg (zero_lt_one.trans (A.fits.delayed j)).le _) (Real.exp_pos _).le
  have wp (v:ManyStem R.family o j):0<w v:=by
    unfold w RG05Readout.Many.envelope RG05Readout.Many.west
    rw [rust_above mj,one_mul]
    exact grantw (totalpos (positive v.val.1) j)
  have sizes:1 ≤ M*Poly.toll w s:=by
    apply wallet j mj d (fun v:ManyStem R.family o j => Q v.val.1) (fun v => positive v.val.1)
      (fun v => ceiling v.val.1) s
    simpa only [Fintype.card_fin] using WilsonAllDateHarvestTuningModes.cardinal o E roster nm mj s
  have engp:0<(R.family.S.a m/R.family.S.a j)^engineering:=pow_pos
    (div_pos (R.family.S.a_pos m) (R.family.S.a_pos j)) _
  have fee:M*Real.exp (-(D:ℝ)) ≤ ε*g^p/(R.family.S.a m/R.family.S.a j)^engineering:=by
    apply (le_div_iff₀ engp).2
    have charged:=paid j (late.trans mj) m mj N live.le per
    simpa only [M,D,c,t,T,e,g,P,mul_assoc,mul_comm,mul_left_comm] using charged
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

end YM.Integration.WilsonReportHarvestResidentConnected
