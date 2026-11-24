import YM.RG01.Vacuum.Hard

/-! # General high/rare set on the actual unforced log

A Bool selector on H.fragrances (cluster IDs, never on fields), retain same
listing and hard occurrence. Template consumes scalar beacon payment per
selected cluster, not any asymptotic statement about that component's value.
Objective: reduce both perturbative-arity truncation and *any number of
actual shares* (`Cash.numP`) in an unforced cluster to the very small side.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Vacuum
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe
open Real
section ledger
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    {m n N : ℕ}
variable {u: RG.Rep G (A.B.a.S.side (m+1) n)}
   (H : Guide A.B R.shape N m n u) (O : Return.Wood A.B m n)
   (hH : Opera.Price A.B R.shape N m n u H) (hm:m<N) (hl : Lives A.B.bake N (m+1) n u) (hb : u.beta ∈ band A.B.a (m+1))

abbrev chooseMark (take : H.fragrances → Prop) (b : Bool) (z : H.fragrances): ℝ:= if take z then (if b then 1 else 0) else if b then 0 else 1

def shelf (take : H.fragrances → Prop) (b : Bool) : Collection.Source G (A.B.a.S.side m n) :=
    let ι : Match.Alliance H H 1 0:= Match.staple rfl rfl rfl
    weigh H ι Chi.canonical (chooseMark R H take b) (!b) (Alpha (A:=A) N m)

lemma shelfUnion (take : H.fragrances→Prop) :
    (plusone H (Match.staple rfl rfl rfl : Match.Alliance H H 1 0) Chi.canonical (Alpha (A:=A) N m)).logRead=
      (shelf R H take false).logRead+(shelf R H take true).logRead := by
  funext i
  unfold shelf
  simp only [Pi.add_apply, weightedReading, ← add_smul]
  let h : Match.Alliance H H 1 0 := Match.staple rfl rfl rfl
  rw [show weightAt H h (chooseMark R H take false) (!false) i + weightAt H h (chooseMark R H take true) (!true) i=1 by
       unfold weightAt
       cases (pennant H i).2 with
       | inl z=> dsimp only [Sum.elim,chooseMark]; split <;> norm_num
       | inr => dsimp only [Sum.elim]; norm_num, one_smul]

def Decision (take : H.fragrances → Prop) (e t w : ℝ) : Prop:=
    let p:=A.B.a.budget m
    let S:=A.B.a.clock.op m n
    let W:= A.B.kin.path N m
    let L:= posting p H
    let keep := shelf R H take false
    let err := shelf R H take true
    Collection.Local L p keep e w ∧ Collection.Local L p err t w ∧
      S.push u.beta u.eval = earlyValue L W ((A.B.a.params m).clip) p keep u.beta
        (weighty H Chi.canonical O) (Alpha (A:=A) N m) * exponentialShare L p err

def voucher (m) := grow G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)

include hH hm hl hb
/-- Actual native supports at true step, any exceptional filter satisfying
this beacon lower bound has a physical residual with the indicated cost. -/
theorem choiceLocal (take : H.fragrances → Prop) (t : ℝ) (hε:0 ≤ t)
    (hT: ∀ z, take z → 1 ≤ t*beacon H z) :
    Decision R H O take (Opera.earlyFee (p:=R.expense) A.B N m u.beta)
      (t*voucher (A:=A) m^3) (A.B.a.clock.forcedAllowance m) := by
  let z := A.B
  let p := A.B.a.budget m
  let j := A.B.a.clock.J (m+1)
  let i := A.B.a.clock.J m
  let x := A.B.a.clock.hatBeta m
  let L := D.L j
  let U := Pressure.Testing.ships A.B N m n
  let Ta := R.target j i
  let T := R.expense j i
  let g := grow G L x
  have hM:= R.pledging.jewels j x (A.B.valid.pays m) i (step_paid A.B.a m)
  obtain ⟨C,d',r,g',b,t',z',Y',q,l,i',⟨N',hv⟩,hK,hp'⟩:= hM.2 _ _ _ U H.laws.data.funds (Opera.protocol A.B hm R.pledging.conducts.full) u H
  obtain ⟨hH',hh,hY,hK'⟩:=R.pledging.peak.large j i (step_paid A.B.a m) x (A.B.valid.pays m)
  obtain ⟨hv',ht',he'⟩:= hK' Y' l i' hK N'.balance hp'
  let σ:=A.B.a.params m
  have hσ : σ=X.p.profile i:= params_eq A.B.valid m
  have hE:p.order=(X.p.profile i).order:= congr_arg RG.Stage.order hσ
  have hV:p.power=(X.p.profile i).power:= congr_arg RG.Stage.power hσ
  have hC:p.supportExponent=(X.p.profile i).supportExponent:= congr_arg RG.Stage.supportExponent hσ
  have h₀: preExponent p ≤ T.earn:= by unfold preExponent; rw [hC]; apply R.pledging.agenda j i (step_paid A.B.a m)|>.1
  have hΞ : preExponent p / (p.B:ℝ) ≤ σ.width/2 := by change (σ.supportExponent+3)/radiusB x ≤ _; rw [hσ]; exact R.pledging.range j x (A.B.valid.pays _) i (step_paid A.B.a m)
  have hd:= (R.machine.passes (Q:=fun _ : ℝ=> u) hm (l:=Set.univ) (fun _ _=> ⟨hl,hb⟩)).1.decent
  have hg : U.down.Bounds U.low σ.width σ.paths (A.B.a.clock.loopCap m):=A.B.support.cap _ _ hm.le
  let α:=Alpha (A:=A) N m
  let Ae : Match.Alliance H H 1 0 := Match.staple rfl rfl rfl
  let A':= posting p H; let S:= plusone H Ae Chi.canonical α
  let S₁:= shelf R H take false; let S₂:= shelf R H take true
  have hw:0<g:= zero_lt_one.trans_le hH'
  have hO := Opera.backing A.B R.shape R.pledging.conducts.income hb
  have hL := (hO.trans (hard_le R _ hm u.beta hb))
  have hs {a b c d} {s} (h:Collection.Local A' p s a b) (ha:a≤c) (hb:b≤d) : Collection.Local A' p s c d := by
    obtain ⟨hF,hK,hM,⟨u,hu,hU⟩,k,hk,hX⟩:=h
    exact ⟨hF,hK,hM,⟨u,hu,fun x=> Cost.enlarge (hU x) ha⟩,k,hk,fun x=> Cost.enlarge (hX x) hb⟩
  -- keep
  have h₁' := Song.loaded (ℓ:=(X.p.profile i).power) p H Ae Chi.canonical α N' rfl hE.le rfl hg hH h₀ hK hV.le hd hΞ
  have h₁ := attenuate p H Ae α (chooseMark R H take false) _ _ h₁' (by intro z; unfold chooseMark; split <;> norm_num) true
  have h₁ : Collection.Local A' p S₁ (Opera.earlyFee (p:=R.expense) A.B N m u.beta) (A.B.a.clock.forcedAllowance m) :=
    hs h₁ (mul_le_mul_of_nonneg_left (add_le_add_left hp' _) (turnFee_pos _|>.le)) hL
  have h₂' := beaconLocal p H Ae α N' rfl hE.le rfl (X.p.profile i).power hV.le (chooseMark R H take true) h₀ hH' hv hv' hY ht' hH t hε (by
    intro z; unfold chooseMark; split
    next h=> norm_num; exact hT z h
    norm_num; apply mul_nonneg hε ((pow_nonneg hw.le _).trans (beacon_ge hH' z)))
  let m₀:=R.shape.μ j i
  let f₀:= collars G (asset T) x (X.p.profile i).order (X.p.profile i).power*(g*salary Ta L m₀ Y' x (X.p.profile i).order i'*(1-1/2)⁻¹)
  have h₂:Collection.Local A' p S₂ (t*g^3) (A.B.a.clock.forcedAllowance m) := hs h₂' (by
    let c:=turnFee p
    have hc:0<c:=turnFee_pos _
    have hf : (g^3)⁻¹*f₀≤heap G (X.p.profile i) (1/16)*δE x := by unfold f₀; rw [←mul_assoc]; exact he'
    rw [inv_mul_le_iff₀ (pow_pos hw _)] at hf
    change c * (t*f₀) ≤ t*g^3
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf hε) hc.le).trans
    have hR:δE x ≤ 1 := by
      unfold δE Clock.gap; apply Real.rpow_le_one
      · positivity
      · exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (A.B.a.fits.delayed m).le)
      norm_num
    let h:=heap G (X.p.profile i) (1/16)
    have hp:0 ≤ h:= (heap_pos G _ (by norm_num : (0:ℝ)<1/16)).le
    have hU : c*h ≤ 1 := by
      unfold h heap; rw [show away (X.p.profile i) = c by unfold c away turnFee; rw [hE,hV], mul_div_cancel₀ _ hc.ne']
      have H := (Time.authorized G (X.p.profile i)).1; norm_num1 at H ⊢; linarith only [H]
    apply le_trans (b:=t*g^3*(c*h*δE x)) (le_of_eq (by unfold h; ring))
    exact mul_le_of_le_one_right (mul_nonneg hε (by positivity)) ((mul_le_mul_of_nonneg_left hR (mul_nonneg hc.le hp)).trans (by simpa using hU))) hL
  refine ⟨h₁,h₂,?_⟩
  exact Eq.trans (funext fun V=> (Song.forward p H Ae Chi.canonical α N' O rfl hE.le hg hH V).symm)
    (earlySplit (X:=A') (s:=S) (s₁:=S₁) (s₂:=S₂) (shelfUnion R H _) rfl _ _ _ _ _ h₁.unweighted h₂.unweighted)
end ledger
end YM.RG01.Vacuum
