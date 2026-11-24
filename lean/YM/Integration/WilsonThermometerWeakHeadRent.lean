import YM.Integration.WilsonThermometerWeakGroupFiling

/-! A before-test coefficient price on the actual displaced polynomial passed to the
weak Wick examiner, in its measured gauge rather than its protected angular coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakHeadRent
open Function Filter Set Lattice Wilson RG Source Labels RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Source.Drops WilsonThermometerWeakTaylor WilsonThermometerWeakPrimary
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge} {n:Side} {b D:ℕ} (R:Run G)
local notation "C" => R.family
local notation "Lev" => R.family.path.levels

private theorem shrink {V:Type*} (P:poly V) (z:ℂ) (small:‖z‖≤1):coin (factors z P)≤coin P:=by
  classical
  have inside:(factors z P).support⊆P.support:=by
    intro i h;rw [mem_support_iff] at h ⊢;rw [factors,jets_coeff] at h;exact right_ne_zero_of_mul h
  rw [metal,metal]
  apply (Finset.sum_le_sum (g:=fun i=>‖coeff i P‖) (fun i _=>?_)).trans (Finset.sum_le_sum_of_subset_of_nonneg inside (fun _ _ _=>norm_nonneg _))
  rw [factors,jets_coeff,norm_mul,norm_pow];apply mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) small)

private theorem raw {ι:Type*} {S:Rules G} {P:BudgetPoint}
    {Z:ι→Support n} {A:ι→ Config G n→ℂ} {f:ι→ℂ} {q:poly (links G (0:Site n) b)} {rent H cash:ℝ}
    (stock:Summary S P b D Z A f rent cash q) (hr:0≤rent) (hm:rent≤H):0≤cash ∧ coin q≤cash*H:=by
  obtain ⟨e,ce,T⟩:=stock
  have h0:0≤cash:=(tsum_nonneg ce.1).trans ce.2.2
  exact ⟨h0,T.charge.trans ((mul_le_mul_of_nonneg_right ce.2.2 hr).trans (mul_le_mul_of_nonneg_left hm h0))⟩

theorem original (simple:G.Simple) (S:Rules G) (D:ℕ):
    ∀ᶠ k:ℕ in atTop,∀ N (_:k≤N) p,
    let P:=(C).path.rep N p k;let b:=sizeQ C k;let s:=clim (Lev) k;let m:=scouts C k;let g:=GaugeScale C k N p
    ∀ {d:ℕ} (X:Coefficient ((C).labels.level d) ((C).side k p)) (K:Provision C d k N p m b) (_:4*b≤wood (Lev) k)
      {q u v:poly (Up C k p b)} {a e cap cash:ℝ},0≤a→a≤tin s D→0≤e→e≤tin s D→
    Summary S P.p b D (verseX C d k p) (verseA C d k p) (weights C P.p.threshold X.x) a cap q →
    Summary S P.p b D (fun j:Near (P:=P) X m=>X.support j) (fun j=>X.regular j) (fun _=>1) e cash u →
    Summary S P.p b D (fun j:Far (P:=P) X m=>X.support j) (fun j=>X.regular j) (fun _=>1) e (expCut P.p m*cash) v →
    coin (sender K.length P.p.threshold g (q+(u+v)))≤(cap+2*cash)*bill (1/2) s:=by
  let h:=shade D
  have grow:∀ᶠ k:ℕ in atTop,(1+4*(sizeQ C k:ℝ))^D≤bill h (clim (Lev) k):=by
    filter_upwards [setter C h (shade_pos D) (4^D) simple R.makes D] with k hg
    apply le_trans _ hg;rw [←mul_pow];apply pow_le_pow_left₀ (by positivity);linarith only
  filter_upwards [grow,supports D C simple R.makes] with k reach ready N hk p P b s m g d X K wide q u v a e cap cash a0 ah e0 eh lhs mid tail
  have H:=raw lhs a0 ah
  have I:=raw mid e0 eh
  have J:=raw tail e0 eh
  have cutoff:0≤tin s D:=(Real.exp_pos _).le
  have endPrice:=J.2.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left I.1 (exp_le P.p m)) cutoff)
  let z:=q+(u+v)
  have head:coin z≤(cap+2*cash)*tin s D:=by
    have hu:=((taller 0 zero_le_one u v).trans (add_le_add I.2 endPrice))
    apply ((taller 0 zero_le_one q _).trans (add_le_add H.2 hu)).trans_eq;ring
  have deg:z.totalDegree≤D:=totalDegree_add .. |>.trans (max_le (lhs.choose_spec.2.produced.choose_spec.1.degree)
    ((totalDegree_add ..).trans (max_le mid.choose_spec.2.produced.choose_spec.1.degree tail.choose_spec.2.produced.choose_spec.1.degree)))
  have cal:=coin_rename (dustAt K.length z) _ (call_inj wide)
  have geometry:=WilsonThermometerWeakWickRoom.curvature K.length wide z deg
  have g0:0<g:=(ready N hk p).1
  have present:P.p.threshold=(Lev).clock.threshold k:=((R.makes.wilson.represents N p k hk).vac) ▸ rfl
  have clip:g≤P.p.threshold:=present ▸ (ready N hk p).2.1
  have gt:0<P.p.threshold:=P.p.threshold_pos
  have ratio:‖((g/P.p.threshold:ℝ):ℂ)‖≤1:=by rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg g0.le gt.le),div_le_iff₀ gt,one_mul];exact clip
  apply ((shrink (dustAt K.length z) _ ratio).trans (cal.trans geometry)).trans
  refine (mul_le_mul head reach (by positivity) ((Real.exp_pos _).le |> mul_nonneg (by linarith only [H.1,I.1]))).trans ?_
  rw [mul_assoc];apply mul_le_mul_of_nonneg_left _ (by linarith only [H.1,I.1]);rw [tin,overlap]
  exact Glimmer.billed _ (by unfold h;linarith only [shaded D])

end YM.Integration.WilsonThermometerWeakHeadRent
end
