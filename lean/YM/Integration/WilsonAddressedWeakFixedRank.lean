import YM.Integration.WilsonAddressedWeakFixedObservation

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakFixedRank
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Ship Next.Rank.Station Next.Rank.Spindle
open Function Filter Set Metric Source RG12 Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Tapes.West Configuration Normal Rise
open Paint Thirst Relation Perch Glimmer LiftMark Beamer Station Atlas Tariffs Ribbon
open Edition Peak Value Marker Corona Alarm Next.Rank.Glyph
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonAddressedWeakCalibration WilsonAddressedWeakReflectedHearing WilsonThermometerReflectedTrajectory
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone PhysMS
open Trace Trace.Pilot WilsonAddressedWeakCorrectedCylinder WilsonAddressedWeakPointCells WilsonAddressedWeakMaxwellPositions
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {d H:ℕ}
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R

variable {C:Local.Physical.Deck G} {O₀:Booked C} (M:MS_Data G O₀)

private theorem entry (a e:Glyph C d) (μ:ℝ) (x:Points 2) (hx:x∈conf 2):
    ContinuousAt (fun z=>MSDeckProbeGram.raw M ![a,e] z μ 0) x:=by
  have chart:Continuous (Fountain.metric (m:=2)):=by
    apply continuous_pi;intro i
    exact Theater.out.toLinearMap.continuous_of_finiteDimensional.comp
      ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 2=>E4)).continuous)
  have legal:Injective (Fountain.metric x):=Theater.out.injective.comp hx
  exact (Dial.contin M (labelAt C ∘ ![a,e]) (Fountain.metric x) legal Finset.univ 0 μ).1.comp chart.continuousAt

private theorem stable {ι:Type} [Fintype ι] [DecidableEq ι] (K:Matrix ι ι ℂ) (unit:IsUnit K) (ε:ℝ) (pos:0<ε):
    ∃ δ:ℝ,0<δ ∧ ∀ A:Matrix ι ι ℂ, (∀a b,‖A a b-K a b‖<δ) →
      IsUnit A ∧ ∀a b,‖A⁻¹ a b-K⁻¹ a b‖<ε:=by
  let assemble (s:(ι×ι)→ℂ):Matrix ι ι ℂ:=fun a b=>s (a,b)
  let z₀:(ι×ι)→ℂ:=fun t=>K t.1 t.2
  have regular:Continuous assemble:=continuous_matrix fun a b=>continuous_apply (a,b)
  have det:K.det≠0:=isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp unit)
  have openDet:=regular.matrix_det.continuousAt (x:=z₀)
  have invs:ContinuousAt (fun s=>(assemble s)⁻¹) z₀:=
    (continuousAt_matrix_inv K (by rw [Ring.inverse_eq_inv'];exact continuousAt_inv₀ det)).comp regular.continuousAt
  have entries:∀ᶠ s in 𝓝 z₀,∀a b,‖(assemble s)⁻¹ a b-K⁻¹ a b‖<ε:=by
    apply eventually_all.mpr;intro a;apply eventually_all.mpr;intro b
    have h:=(continuous_apply b).continuousAt.comp ((continuous_apply a).continuousAt.comp invs)
    have small:∀ᶠ s in 𝓝 z₀, (assemble s)⁻¹ a b∈Metric.ball (K⁻¹ a b) ε:=h.tendsto (Metric.ball_mem_nhds _ pos)
    filter_upwards [small] with s hs;simpa only [Metric.mem_ball,dist_eq_norm] using hs
  obtain ⟨δ,hδ,sure⟩:=Metric.mem_nhds_iff.mp ((openDet.tendsto.eventually_ne det).and entries)
  refine ⟨δ/2,half_pos hδ,?_⟩; intro A paid
  let w:(ι×ι)→ℂ:=fun j=>A j.1 j.2
  have ball:w∈Metric.ball z₀ δ:=by
    rw [Metric.mem_ball,dist_eq_norm]
    exact lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (half_pos hδ).le).mpr
      (fun j=>(paid j.1 j.2).le)) (half_lt_self hδ)
  obtain ⟨ok,price⟩:=sure ball
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ok),price⟩

/-- Each input field and its corrected inverse are fixed on its own original residue
throughout the point detector. The inverse converges with all finite Wilson face prices. -/
theorem coordinates (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (V:Warehouse G)
    (exam:Panel H) (grade:d≤H) (φ:Test 2) (separated:tsupport φ⊆generic 2) (o w:E4) (away:o≠w)
    (near:tsupport φ∈𝓝 (Extra.FD.couple o w)) (μ ε:ℝ) (pos:0<ε) (B:Binding Rf) (J:ChartRatio G) (O:HaarBudget G)
    (n:ℕ) (arity:2≤n):
    let x₀:=Extra.FD.couple o w;let K:=MSDeckProbeGram.matrix M d o w μ 0
    IsUnit K ∧ ∀ᶠ k:ℕ in atTop, ∀ᶠ N:ℕ in atTop, ∀ (p:ℕ) (hk:k<N),
    let s:=clim (Lev) k;let ξ:=exam.bag ((Lev).clock.J k)
    let ρ:=gap (Lev) ξ.band k;let g:=(Rf).S.toDepth hk.le p
    ∀ (b l q:ℝ) (menu:LegacyCost B J (-3) b ξ k n H O l q) (Q:Rep G ((Rf).side k p)),
      (∀ j≤d,Accent.generator G j≤b) → Actum B R.makes O J exam menu Q hk →
    ∀ (z₀:Fin 2→Site ((Rf).side N p)) (V₀:Fin 2→Sight Rf d p) (r:Fin 2→Emblems Rf d),
      (∀ i,Enrolled R.makes R.doors cash k N p d (digits R N p (z₀ i)) (V₀ i) (r i)) →
      ∃ u:Fin 2→Glyph C d→(Rf).label d,
      let y:=fun (i:Fin 2)(j:Glyph C d)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j); (∀ i j,size (y i j)≤Perch.bill (ξ.credit-1) s) ∧
      let z:=fun i=>WilsonAddressedWeakFixedChild.slide R hk.le (z₀ i)
          (g.parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x₀ i))
      let A:Matrix (Glyph C d) (Glyph C d) ℂ:=fun a e=>reading R (fun _=>d) z (fun i=>y i (![a,e] i)) r hk.le full
      IsUnit A ∧ ∀a e,‖A⁻¹ a e-K⁻¹ a e‖<ε:=by
  intro x₀ K
  have good:IsUnit K:=MSDeckProbeGram.invertible V M μ away d
  refine ⟨good,?_⟩
  obtain ⟨δ,hδ,check⟩:=stable K good ε pos
  have xconf:x₀∈conf 2:=by exact Extra.FD.couple_ok away
  have con:∀ᶠ v in 𝓝 x₀,∀a e:Glyph C d,‖MSDeckProbeGram.raw M ![a,e] v μ 0-K a e‖<δ/2:=by
    apply eventually_all.mpr;intro a;apply eventually_all.mpr;intro e
    have close:∀ᶠ v in 𝓝 x₀, MSDeckProbeGram.raw M ![a,e] v μ 0∈Metric.ball (K a e) (δ/2):=
      (entry M a e μ x₀ xconf).tendsto (Metric.ball_mem_nhds _ (half_pos hδ))
    filter_upwards [close] with v hv;simpa only [Metric.mem_ball,dist_eq_norm] using hv
  obtain ⟨c,hc,continuousSample⟩:=Metric.mem_nhds_iff.mp con
  obtain ⟨D,hD,prices⟩:=WilsonAddressedWeakFixedObservation.coordinates R M simple shop S exam grade φ separated x₀ near μ B J O
  have posArc:0<exam.arc:=by linarith only [exam.huge,Nat.cast_nonneg (α:=ℝ) H]
  have mesh:Tendsto (fun k=>(40:ℝ)*(mag (Lev) exam.arc k)⁻¹) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp (mag_rate (Lev) simple posArc)).const_mul 40
  have small:Tendsto (fun k=>(1+2*D)*Ship.budget (Lev) n k) atTop (𝓝 0):= by
    simpa only [mul_zero] using (Ship.diminishes (Lev) n simple (show 0<n by omega)).const_mul (1+2*D)
  filter_upwards [prices,mesh.eventually (gt_mem_nhds hc),small.eventually (gt_mem_nhds (half_pos hδ))] with k hear landed cost
  filter_upwards [hear] with N post
  intro p hk s ξ ρ g b l q menu Q funds current z₀ V₀ r enrolled
  obtain ⟨u,rent,x,placed,move,paid⟩:=post p n hk arity b l q menu Q funds current z₀ V₀ r enrolled
  let y:=fun (i:Fin 2)(j:Glyph C d)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j)
  refine ⟨u,rent,check _ ?_⟩
  let v:=projected R (p:=p) hk.le ρ (gap_pos ..) x
  have band:ξ.band=exam.arc:=exam.factor _
  have clos:dist v x₀<c:=move.trans_lt (by rwa [band])
  intro a e
  have one:=paid a e
  rw [placed] at one
  have two:=continuousSample (Metric.mem_ball.mpr clos) a e
  exact (norm_sub_le_norm_sub_add_norm_sub _ (MSDeckProbeGram.raw M ![a,e] v μ 0) _).trans_lt
    ((add_lt_add (one.trans_lt cost) two).trans_eq (add_halves δ))

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (V:Warehouse G)
    (exam:Panel H) (grade:d≤H) (φ:Test 2) (separated:tsupport φ⊆generic 2) (o w:E4) (away:o≠w)
    (near:tsupport φ∈𝓝 (Extra.FD.couple o w)) (μ ε:ℝ) (pos:0<ε) (B:Binding Rf) (J:ChartRatio G) (O:HaarBudget G)
    (n:ℕ) (arity:2≤n):
    let x₀:=Extra.FD.couple o w;let K:=MSDeckProbeGram.matrix M d o w μ 0
    IsUnit K ∧ ∀ᶠ k:ℕ in atTop, ∀ᶠ N:ℕ in atTop, ∀ (p:ℕ) (hk:k<N),
    let s:=clim (Lev) k;let ξ:=exam.bag ((Lev).clock.J k)
    let ρ:=gap (Lev) ξ.band k;let g:=(Rf).S.toDepth hk.le p
    ∀ (b l q:ℝ) (menu:LegacyCost B J (-3) b ξ k n H O l q) (Q:Rep G ((Rf).side k p)),
      (∀ j≤d,Accent.generator G j≤b) → Actum B R.makes O J exam menu Q hk →
    ∀ (z₀:Fin 2→Site ((Rf).side N p)) (V₀:Fin 2→Sight Rf d p) (r:Fin 2→Emblems Rf d),
      (∀ i,Enrolled R.makes R.doors cash k N p d (digits R N p (z₀ i)) (V₀ i) (r i)) →
      ∃ y:Fin 2→Glyph C d→Palette Rf d, (∀ i j,size (y i j)≤Perch.bill (ξ.credit-1) s) ∧
      let z:=fun i=>WilsonAddressedWeakFixedChild.slide R hk.le (z₀ i)
          (g.parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x₀ i))
      let A:Matrix (Glyph C d) (Glyph C d) ℂ:=fun a e=>reading R (fun _=>d) z (fun i=>y i (![a,e] i)) r hk.le full
      IsUnit A ∧ ∀a e,‖A⁻¹ a e-K⁻¹ a e‖<ε:=by
  intro x₀ K
  obtain ⟨unit,rows⟩:=coordinates R M simple shop S V exam grade φ separated o w away near μ ε pos B J O n arity
  refine ⟨unit,?_⟩
  filter_upwards [rows] with k rows;filter_upwards [rows] with N rows
  intro p hk s ξ ρ g b l q menu Q funds current z₀ V₀ r enrolled
  obtain ⟨u,done⟩:=rows p hk b l q menu Q funds current z₀ V₀ r enrolled
  exact ⟨fun (i:Fin 2)(j:Glyph C d)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j),done⟩

end YM.Integration.WilsonAddressedWeakFixedRank
end
