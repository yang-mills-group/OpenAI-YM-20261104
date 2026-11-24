import YM.Integration.WilsonFundedMeasuredWindow
import YM.Integration.WilsonReportRegulatedSmear
import YM.RG17.Corners

/-! Before testing any coefficient, put every true fine vacuum stencil into
the measured early-connection annulus at the actual first reporting stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCashierWindow
open Filter Set Finset Function MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open OPE OPE.Strobe.Vista26 PhysicalNext.Repeat.Legato
open OPE.Orbits RG17 Table Next.Rank
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G}

private theorem fee (A : Levels G) (hG : G.Simple) (B : ℕ) (large : 17≤B) {c : ℝ} (hc : 0<c) :
    ∀ᶠ k : ℕ in atTop,let L := RG16.Lambda A k
    (1:ℝ)≤c*L^B ∧ (((A.budget k).B^8:ℕ):ℝ)≤c*L^B ∧
    (c+1)*L^(B+1)≤A.clock.hatBeta k := by
  let f := (c+1)*3^(B+1)
  have fp : 0<f := by dsimp only [f]; positivity
  have grows := Real.tendsto_log_atTop.comp (Station.hat_rate A hG)
  have cheap := ((Real.isLittleO_pow_exp_atTop (n:=B+1)).comp_tendsto grows).bound (inv_pos.mpr fp)
  filter_upwards [grows.eventually_ge_atTop (max 1 (2^8/c)),cheap] with k high hp
  let b := A.clock.hatBeta k
  let l := Real.log b
  change max 1 ((2:ℝ)^8/c) ≤ l at high
  have l1 : 1≤l := (le_max_left ..).trans high
  have bl : 2^8≤c*l := by
    have z := (div_le_iff₀ hc).mp ((le_max_right ..).trans high)
    simpa only [mul_comm] using z
  have cap : (⌈l^2⌉₊:ℝ)≤2*l^2 := by
    linarith only [(Nat.ceil_lt_add_one (sq_nonneg l)).le,one_le_pow₀ l1 (n:=2)]
  have positive := zero_le_one.trans l1
  have base : l≤2+l := by linarith
  have hs : (⌈l^2⌉₊:ℝ)^8≤c*(2+l)^B := calc
    _ ≤ (2*l^2)^8 := pow_le_pow_left₀ (Nat.cast_nonneg _) cap _
    _ = (2:ℝ)^8*l^16 := by ring
    _ ≤ (c*l)*l^16 := mul_le_mul_of_nonneg_right bl (pow_nonneg positive _)
    _ = c*l^17 := by ring
    _ ≤ c*l^B := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ l1 large) hc.le
    _ ≤ c*(2+l)^B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ positive base B) hc.le
  have one : 1≤(⌈l^2⌉₊:ℝ) := (one_le_pow₀ l1).trans (Nat.le_ceil _)
  change 1≤c*(2+l)^B ∧ ((⌈l^2⌉₊^8:ℕ):ℝ)≤c*(2+l)^B ∧ (c+1)*(2+l)^(B+1) ≤ b
  rw [Nat.cast_pow]
  refine ⟨(one_le_pow₀ one).trans hs,hs,?_⟩
  have hb : 0<b := zero_lt_one.trans (A.fits.delayed k)
  change ‖l^(B+1)‖ ≤ f⁻¹*‖Real.exp l‖ at hp
  rw [Real.norm_of_nonneg (pow_nonneg positive _),Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_log hb] at hp
  have sold := mul_le_mul_of_nonneg_left hp fp.le
  have credit : f*l^(B+1)≤b := by simpa only [←mul_assoc,mul_inv_cancel₀ fp.ne',one_mul] using sold
  calc
    _ ≤ (c+1)*(3*l)^(B+1) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith only [l1]) _) (by linarith only [hc])
    _ = f*l^(B+1) := by rw [mul_pow]; exact (mul_assoc ..).symm
    _ ≤ b := credit

private theorem parent_upper {k N p : ℕ} (h : k≤N) (u v : Site (C.side N p)) :
    C.S.a k*separation ((C.S.toDepth h p).parent u) ((C.S.toDepth h p).parent v) ≤
      C.S.a N*separation u v+C.S.a k := by
  let F := C.S.toDepth h p
  let t := F.count.val
  let d := separation (F.parent u) (F.parent v)
  have geom : t*d < separation u v+t := (OPE.Log.Trunk.Canvas.expands (C:=C) u v h).1
  have sale : (t:ℝ)*(d:ℝ) ≤ (separation u v:ℝ)+(t:ℝ) := by exact_mod_cast geom.le
  have mesh : C.S.a N*(t:ℝ)=C.S.a k := C.S.embeds_scale F
  calc
    _ = C.S.a N*((t:ℝ)*d) := by rw [←mesh]; ring
    _ ≤ C.S.a N*((separation u v:ℝ)+(t:ℝ)) := mul_le_mul_of_nonneg_left sale (C.S.a_pos N).le
    _ = _ := by rw [mul_add,mesh]

private theorem parent_lower {k N p : ℕ} (h : k≤N) (u v : Site (C.side N p)) {d : ℕ}
    (low : C.S.a k*(d:ℝ)≤C.S.a N*separation u v) :
    d ≤ separation ((C.S.toDepth h p).parent u) ((C.S.toDepth h p).parent v) := by
  let F := C.S.toDepth h p
  have mesh : C.S.a N*(F.count.val:ℝ)=C.S.a k := C.S.embeds_scale F
  have hreal : (F.count.val:ℝ)*(d:ℝ)≤(separation u v:ℝ) := by
    apply le_of_mul_le_mul_left _ (C.S.a_pos N)
    rw [←mul_assoc,mesh]
    exact low
  have hnat : F.count.val*d ≤ separation u v := by exact_mod_cast hreal
  have dist := (OPE.Log.Trunk.Canvas.expands (C:=C) u v h).2
  change separation u v < F.count.val*separation (F.parent u) (F.parent v)+F.count.val at dist
  by_contra! bad
  have cost := Nat.mul_le_mul_left F.count.val (Nat.succ_le_of_lt bad)
  rw [Nat.mul_succ] at cost
  exact (not_le_of_gt dist) (cost.trans hnat)

/-- Each true finest tuple on which the submitted cutoff vacuum test is
nonzero satisfies all the genuine Vista comparison gates, at the prescribed
first Wilson stop, with one aspect ratio before every arity-specific test. -/
theorem admitted {R : Run G} (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit)
    {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S)
    (T : Test 1) {n : ℕ} {K : Set (Points (n+1))} (hK : IsCompact K) (hc : K⊆conf _)
    (B : ℕ) (large : 17≤B) :
    ∃ br : ℕ,0<br ∧ ∀ᶠ s in RG17.home,let C := R.family
    let k := WilsonMeasuredWindow.stop C.path.levels hG B s
    ∃ dis : ℕ,(C.path.levels.budget k).B^8≤dis ∧ (dis:ℝ)≤C.path.levels.clock.hatBeta k ∧
    ∀ N p,∀ hk : k≤N,∀ y : Fin (n+1)→Site (C.side N p),
    Order.cells C N p y∈RG17.gathersIn C F T K s →
    Sites26 (C:=C) br dis (fun j => (C.S.toDepth hk p).parent (y j)) := by
  let C := R.family
  let A := C.path.levels
  let k := WilsonMeasuredWindow.stop A hG B
  obtain ⟨_μ,v,η,_hμ,hv,hη,mark⟩ := RG17.stencilSpace C F T K hK hc
  let c := η/4
  have cc : 0<c := by dsimp only [c]; positivity
  let br := ⌈v/c⌉₊+1
  have brtop : v/c+1≤(br:ℝ) := by
    change v/c+1 ≤ ((⌈v/c⌉₊+1:ℕ):ℝ)
    rw [Nat.cast_add,Nat.cast_one]
    exact add_le_add (Nat.le_ceil (v/c)) le_rfl
  obtain ⟨growing,actual⟩ := WilsonFundedMeasuredWindow.all_radii R pace hG (B:=B) (by omega)
  refine ⟨br,Nat.succ_pos _,?_⟩
  filter_upwards [growing.eventually (fee A hG B large cc),mark,RG17.positiveLength,
    (eventually_le_nhds (C.S.a_pos 0)).filter_mono nhdsWithin_le_nhds] with s prices census pos small
  let i := k s
  let a := C.S.a i
  let X := s/a
  let L := RG16.Lambda A i
  let d := ⌈c*X⌉₊
  have ha : 0<a := C.S.a_pos _
  have hx : 0<X := div_pos pos ha
  obtain ⟨lo,hi⟩ := actual s pos small
  have lpos : 1≤L := by change 1≤2+Real.log (A.clock.hatBeta i); linarith only [Real.log_nonneg (A.fits.delayed i).le]
  have x1 : 1≤c*X := prices.1.trans (mul_le_mul_of_nonneg_left lo cc.le)
  have ceil := Nat.le_ceil (c*X)
  have cap : (d:ℝ) ≤ 2*c*X := by linarith only [(Nat.ceil_lt_add_one (mul_nonneg cc.le hx.le)).le,x1]
  have d1 : 1≤(d:ℝ) := x1.trans ceil
  have dw : ((A.budget i).B^8:ℕ) ≤ d := by
    have n : (((A.budget i).B^8:ℕ):ℝ)≤(d:ℝ) := prices.2.1.trans ((mul_le_mul_of_nonneg_left lo cc.le).trans ceil)
    exact_mod_cast n
  have dh : (d:ℝ)≤A.clock.hatBeta i := calc
    _ ≤ c*X+1 := (Nat.ceil_lt_add_one (mul_nonneg cc.le hx.le)).le
    _ ≤ c*L^(B+1)+L^(B+1) := add_le_add (mul_le_mul_of_nonneg_left hi cc.le) (one_le_pow₀ lpos)
    _ ≤ _ := by rw [←add_one_mul]; exact prices.2.2
  refine ⟨d,dw,dh,?_⟩
  intro N p hk y hy
  obtain ⟨_,close,apart⟩ := census N p y hy
  constructor
  · intro j l
    let e := separation ((C.S.toDepth hk p).parent (y j)) ((C.S.toDepth hk p).parent (y l))
    have first : a*(e:ℝ) ≤ v*s+a := (parent_upper hk ..).trans (add_le_add (close j l) le_rfl)
    have second : (e:ℝ)≤v*X+1 := by
      apply le_of_mul_le_mul_left _ ha
      exact first.trans_eq (by dsimp only [X]; field_simp)
    have cash : v*X ≤ (v/c)*(d:ℝ) :=
      (show v*X=(v/c)*(c*X) by field_simp).le.trans (mul_le_mul_of_nonneg_left ceil (div_nonneg hv.le cc.le))
    have bound : (e:ℝ)≤(br:ℝ)*(d:ℝ) := calc
      _ ≤ (v/c)*(d:ℝ)+(d:ℝ) := second.trans (add_le_add cash d1)
      _ = (v/c+1)*(d:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right brtop (Nat.cast_nonneg _)
    exact_mod_cast bound
  · intro j l ne
    apply parent_lower hk
    have each := mul_le_mul_of_nonneg_left cap ha.le
    have hc4 : c*4=η := by dsimp only [c]; ring
    have exacts : a*(2*c*X)=η*s/2 := by dsimp only [X]; field_simp; linarith only [hc4]
    exact each.trans (exacts.le.trans (by linarith only [apart j l ne]))

end YM.Integration.WilsonReportCashierWindow
end

