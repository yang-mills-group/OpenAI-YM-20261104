import YM.Integration.WilsonReportCashierWindow
import YM.Integration.WilsonReportCashierPrice
import YM.Integration.WilsonReportPartialShell
import YM.Integration.WilsonReportCitizenRun

/-! The real finite Wilson vacuum correlation at the first reporting scale.
All early charged terms are included in the error. The original signed
fine-site minus parent-site offset is displayed on the Wilson measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCashier
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Table OPE.Orbits RG12 RG17 WilsonReportFineSmear Push.GridApprox
open scoped Topology BigOperators Classical
universe u
variable {G : Gauge} {C : Family G}

private theorem rates (hG : G.Simple) (hC : C.Makes) (q : ℕ) {A ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ N p,k≤N → let b := C.path.levels.clock.hatBeta k
    Real.exp (-((C.path.levels.budget k).B:ℝ)) ≤ (b^(q+1))⁻¹ ∧
    (2*A)*(b^(q+1))⁻¹ ≤ ε*Pert.Asymptotics.regulatorRun C N p k^q := by
  have grow := Station.hat_rate C.path.levels hG
  filter_upwards [(Real.tendsto_log_atTop.comp grow).eventually_ge_atTop ((q+1:ℕ):ℝ),
    grow.eventually_ge_atTop ((2*A)*2^q/ε)] with k tall large N p hk
  let b := C.path.levels.clock.hatBeta k
  have one : 1≤b := (C.path.levels.fits.delayed k).le
  have bp : 0<b := zero_lt_one.trans_le one
  have good := Real.log_nonneg one
  change ((q+1:ℕ):ℝ)≤Real.log b at tall
  have bound : b^(q+1)≤Real.exp ((C.path.levels.budget k).B:ℝ) := by
    apply (Real.log_le_iff_le_exp (pow_pos bp _)).mp
    rw [Real.log_pow]
    exact (mul_le_mul_of_nonneg_right tall good).trans ((sq _).ge.trans (Nat.le_ceil _))
  let a := C.path.β N p k
  have rep := (hC.wilson.represents N p k hk).band
  have low : b/2≤a := rep.1
  have upper : a≤2*b := rep.2
  have ap := (half_pos bp).trans_le low
  have b2 : 0<2*b := mul_pos (by norm_num) bp
  have root : Real.sqrt a≤2*b := (Real.sqrt_le_left b2.le).mpr
    (upper.trans (by nlinarith only [mul_nonneg b2.le (show 0≤2*b-1 by linarith only [one])]))
  have gp : (2*b)⁻¹ ≤ Pert.Asymptotics.regulatorRun C N p k := inv_anti₀ (Real.sqrt_pos.mpr ap) root
  have m := (div_le_iff₀ hε).mp large
  refine ⟨by rw [Real.exp_neg]; exact inv_anti₀ (pow_pos bp _) bound,?_⟩
  change (2*A)*(b^(q+1))⁻¹ ≤ ε*Pert.Asymptotics.regulatorRun C N p k^q
  calc
    _ = ((2*A)*2^q/b)*((2*b)⁻¹)^q := by rw [inv_pow,mul_pow,pow_succ]; field_simp
    _ ≤ ε*((2*b)⁻¹)^q := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ bp).mpr (m.trans_eq (mul_comm ..))) (pow_nonneg (inv_nonneg.mpr b2.le) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr b2.le) gp q) hε.le

/-- Full genuine regulated zero-exterior reading. Both the earlier-connected
portion and the discrepancy after replacing every anchor by the true complete
regular field are paid with the fixed order-zero test seminorm. -/
theorem on_run {R : Run G} (hG : G.Simple) {U : Campaign R} (W : Campaign.Pillars R U)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {S : Table R.family.book} {f : Extraction.Order} {F : Spec.Final R.family f S}
    (loc : Layout F) (T : Test 1) {n : ℕ} (d : Fin (n+1)→ℕ) (t q : ℕ) {ε : ℝ} (hε : 0<ε)
    {K : Set (Points (n+1))} (hK : IsCompact K) (hc : K⊆conf _) (B : ℕ) (big : 17≤B) :
    ∀ᶠ r in RG17.home,let C := R.family
    let k := WilsonMeasuredWindow.stop C.path.levels hG B r
    ∀ᶠ p : ℕ in atTop,∀ N : ℕ,∀ hk : k<N,∀ v : (j:Fin (n+1))→C.label (d j),
    let V := fun j => RG17.atRef loc (d j) r (N,p) (v j)
    (∀ j,Spindle.paid C (d j) k N p (V j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ ψ : Test (n+1),tsupport ψ⊆K → ∀ b : ℝ,Demand 0 ψ b →
    let X := RG17.cashier F T
    let op := RG17.shape X r ψ
    let E := RG17.refTags X
    let error := ε*b*Pert.Asymptotics.regulatorRun C N p k^q
    ‖∑ y : Sites C N p (n+1) X.n,weight C op y*early hk.le d V E y‖ ≤ error ∧
    ‖RG17.packMark loc X d v r ψ (N,p)-
       ∑ y : Sites C N p (n+1) X.n,weight C op y*(sampled hk.le d V E y+offset hk.le d V E y)‖ ≤ error := by
  let C := R.family
  let stop := WilsonMeasuredWindow.stop C.path.levels hG B
  obtain ⟨citizen,book⟩ := WilsonReportCitizenRun.on_run hG W original subsidy
  obtain ⟨br,hbr,annulus⟩ := WilsonReportCashierWindow.admitted hG pace F T hK hc B big
  obtain ⟨c,hc0,mesh⟩ := WilsonReportCashierPrice.purchased F T hK hc
  obtain ⟨grow,paidWindow⟩ := WilsonFundedMeasuredWindow.all_radii R pace hG (B:=B) (by omega)
  have shell := WilsonReportPartialShell.moments hG R.makes citizen d hbr t (q+1)
  have back := WilsonReportDisjointBack.entire hG R.makes citizen d
  have flagship := WilsonReportFlagSectors.original hG R.makes citizen d
  have packed := WilsonReportRegulatedSmear.purchased hG book.money citizen loc d t hK hc B big
  filter_upwards [annulus,mesh,grow.eventually shell,grow.eventually back,grow.eventually flagship,
    grow.eventually packed,grow.eventually (rates hG R.makes q (A:=c) hε),RG17.positiveLength,
    (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds,
    (eventually_le_nhds (C.S.a_pos 0)).filter_mono nhdsWithin_le_nhds] with r positions priced localPrice separate flags whole fee pos small start
  let k := stop r
  let h := C.path.levels.clock.hatBeta k
  obtain ⟨dis,near,hi,sites⟩ := positions
  have band := (paidWindow r pos start).1
  have gear : Real.log h≤RG16.Lambda C.path.levels k := by change Real.log h≤2+Real.log h; linarith
  have first : Real.log h^B ≤ r/C.S.a k := (pow_le_pow_left₀
    (Real.log_nonneg (C.path.levels.fits.delayed k).le) gear B).trans band
  have lit : 1≤RG16.Lambda C.path.levels k := by
    change 1≤2+Real.log h; linarith only [Real.log_nonneg (C.path.levels.fits.delayed k).le]
  have ak : C.S.a k≤r := by
    have once := (le_div_iff₀ (C.S.a_pos k)).mp ((one_le_pow₀ lit (n:=B)).trans band)
    simpa only [one_mul] using once
  filter_upwards [whole r pos small first] with p actual N hk v
  dsimp only
  intro pub ψ supported b cost
  let X := RG17.cashier F T
  let op := RG17.shape X r ψ
  let V := fun j => RG17.atRef loc (d j) r (N,p) (v j)
  let E := RG17.refTags X
  let Y := Sites C N p (n+1) X.n
  let α (y : Y) := early hk.le d V E y
  let w (y : Y) := weight C op y
  let real (y : Y) := sampled hk.le d V E y+offset hk.le d V E y
  let e := (h^(q+1))⁻¹
  have nneg : 0 ≤ e := inv_nonneg.mpr (pow_nonneg ((zero_le_one.trans (C.path.levels.fits.delayed k).le)) _)
  have mn : 0≤∑ y,‖w y‖ := sum_nonneg fun _ _ => norm_nonneg _
  have mass := priced ψ supported b cost k N p hk.le ((C.S.strictAnti.antitone hk.le).trans ak)
  change (∑ y,‖w y‖) ≤ c*b at mass
  have vac (y : Y) : exterior E y = (fun _ => (1:ℂ)) := by
    funext Z
    change (∏ j : Fin 0,_)=_
    simp
  have points (y : Y) (alive : op (Order.cells C N p y)≠0) : ‖α y‖ ≤ e := by
    let x := parents hk.le y
    have agree : Sites26 (C:=C) br dis x := sites N p hk.le y
      (RG17.gathered C F T K hK supported (subset_tsupport op alive))
    have away (j l) (ne : j≠l) := near.trans (agree.apart j l ne)
    have measured := flags N p hk.le x away V univ (fun _ => (1:ℂ)) (integrable_const _)
    change Wilson.moment (C.beta N p) (fun Z => (1:ℂ)*fineJob (BarePack d x hk.le V) univ Z) -
      Wilson.moment (C.beta N p) (fun Z => (1:ℂ)*backTo C.path N p hk.le (fineJob (ScenePack (N:=N) d x V) univ) Z) =
      WilsonReportFlagSectors.signed hk.le d x V univ (fun _ => (1:ℂ)) at measured
    have product : backTo C.path N p hk.le (fineJob (ScenePack (N:=N) d x V) univ)=
        fineJob (fun j => backTo C.path N p hk.le (ScenePack (N:=N) d x V j)) univ :=
      separate N p hk.le x away V univ
    change ‖WilsonReportFlagSectors.signed hk.le d x V univ (exterior E y)‖ ≤ e
    rw [vac,←measured,product]
    have bought : ‖Wilson.moment (C.beta N p) (fineJob (BarePack d x hk.le V) univ)-
        Wilson.moment (C.beta N p) (fineJob (WilsonReportPartialShell.hybrid univ hk.le d x V) univ)‖≤ e :=
      localPrice dis near hi N p hk x agree V pub univ univ
    have film : WilsonReportPartialShell.hybrid univ hk.le d x V =
        fun j => backTo C.path N p hk.le (ScenePack (N:=N) d x V j) := by
      funext j
      exact if_pos (Finset.mem_univ j)
    rw [film] at bought
    simpa only [one_mul] using bought
  have sumEarly : ‖∑ y,w y*α y‖ ≤ (∑ y,‖w y‖)*e := by
    rw [sum_mul]
    refine (norm_sum_le ..).trans (sum_le_sum (fun y _ => ?_))
    by_cases accepted : op (Order.cells C N p y)=0
    · simp [w,WilsonReportFineSmear.weight,accepted]
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (points y accepted) (norm_nonneg _)
  obtain ⟨radius,account⟩ := fee N p hk.le
  change Real.exp (-((C.path.levels.budget k).B:ℝ))≤e at radius
  change (2*c)*e ≤ ε*Pert.Asymptotics.regulatorRun C N p k^q at account
  have paid : (2*(c*b))*e≤ ε*b*Pert.Asymptotics.regulatorRun C N p k^q :=
    (show (2*(c*b))*e=((2*c)*e)*b by ring).le.trans <|
      (mul_le_mul_of_nonneg_right account cost.nonneg).trans_eq (by ring)
  have half := mul_le_mul_of_nonneg_right mass nneg
  have rest := actual N hk v pub X ψ supported
  have flat (y : Y) : (∫ Z,‖exterior E y Z‖ ∂law G (C.side N p) (C.beta N p))=1 := by
    rw [vac]; simp
  change ‖RG17.packMark loc X d v r ψ (N,p)-∑ y,w y*(real y+α y)‖ ≤ ∑ y : Y,‖w y‖*
    ((∫ Z,‖exterior E y Z‖ ∂law G (C.side N p) (C.beta N p))*Real.exp (-((C.path.levels.budget k).B:ℝ))) at rest
  have payRest : ‖RG17.packMark loc X d v r ψ (N,p)-∑ y,w y*(real y+α y)‖≤(∑ y,‖w y‖)*e := by
    apply rest.trans
    simp only [flat,one_mul]
    rw [←sum_mul]
    exact mul_le_mul_of_nonneg_left radius mn
  refine ⟨(sumEarly.trans half).trans ((by nlinarith only [mul_nonneg (mul_nonneg hc0 cost.nonneg) nneg] :
    (c*b)*e≤(2*(c*b))*e).trans paid),?_⟩
  have join : (RG17.packMark loc X d v r ψ (N,p)-∑ y,w y*real y)=
      (RG17.packMark loc X d v r ψ (N,p)-∑ y,w y*(real y+α y))+(∑ y,w y*α y) := by
    simp only [mul_add,sum_add_distrib]; ring
  change ‖RG17.packMark loc X d v r ψ (N,p)-∑ y,w y*real y‖≤_
  rw [join]
  exact (norm_add_le ..).trans ((add_le_add (payRest.trans half) (sumEarly.trans half)).trans
    ((by ring : (c*b)*e+(c*b)*e=(2*(c*b))*e).le.trans paid))

end YM.Integration.WilsonReportCashier
end

