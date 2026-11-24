import YM.Integration.WilsonPointChildNormalizedWidth

/-! The terminal strong-width bill is on the common native bare section
    before either the itinerary or the ultraviolet end is selected. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildTerminalWidth
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Dove.Lab Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildNormalizedWidth WilsonNeutralPointCourse WilsonPointChildFiledPress
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {d D:ℕ}

theorem original (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (o:Loc G 1)(simple:G.Simple){orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)
    (E:ℕ):∃c:ℝ,∃w:ℕ,0≤c ∧ ∀ᶠ N:ℕ in atTop,∀digit:∀j,Site (R.family.S.block j),
      Wallet o (R.family.labels.level d) (filed R wood a depth digit N N) (width R N) E
        (c*(max 1 (ageZ (R.family.path.levels.clock.hatBeta N)))^w):=by
  let V:=R.family.path.levels
  let J:=d+D+E+5
  obtain ⟨k,onward⟩:=eventually_atTop.mp (V.fits.deep.eventually_ge_atTop J)
  let acc:=WilsonWindowFormalAnnouncement.on_run R granted
  let X:=Letter (R.family.labels.level d)×Fin (d+E+1)
  have each (x:X):=Primer.landedFields R.family simple a wood o acc (show 5≤J by dsimp[J];omega)
    (onward (k+1) (Nat.le_succ _)) (show E≤J by dsimp[J];omega) depth (show d+3≤J by dsimp[J];omega)
    (show D≤J by dsimp[J];omega) x.1 x.2.val
  choose c w cn buy using each
  let B:=∑x,c x
  let v:=∑x,w x
  have cm (x:X):c x≤B:=Finset.single_le_sum (fun y _=>cn y) (Finset.mem_univ x)
  have wm (x:X):w x≤v:=Finset.single_le_sum (fun y _=>Nat.zero_le (w y)) (Finset.mem_univ x)
  have bn:0≤B:=Finset.sum_nonneg (fun y _=>cn y)
  refine ⟨B,v,bn,?_⟩
  filter_upwards [eventually_ge_atTop k] with N late digit
  have ht:=acc.power.beta N
  have lg:1≤Real.log (V.clock.hatBeta N):=by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht
  have age:1≤ageZ (V.clock.hatBeta N):=by dsimp [ageZ];linarith [Real.log_nonneg lg]
  let day:=max 1 (ageZ (V.clock.hatBeta N))
  have day1:1≤day:=le_max_left ..
  refine ⟨mul_nonneg bn (pow_nonneg (zero_le_one.trans day1) _),?_⟩
  intro s p j je r hr
  let x:X:=⟨s,⟨r,by omega⟩⟩
  have paid:=((buy x N late p j je).2.2 N le_rfl).1
  rw [top,← show Primer.fieldCoeffs R.family a wood depth N N=sectionY (R.family.localSection d) depth from Elm.terrace_zero ..]
  apply paid.mono
  apply mul_le_mul _ (Annex.comp_le p) (norm_nonneg _) (mul_nonneg bn (pow_nonneg (zero_le_one.trans day1) _))
  apply mul_le_mul (cm x) _ (pow_nonneg (zero_le_one.trans age) _) bn
  exact (pow_le_pow_left₀ (zero_le_one.trans age) (le_max_right ..) _).trans (pow_le_pow_right₀ day1 (wm x))

end YM.Integration.WilsonPointChildTerminalWidth
