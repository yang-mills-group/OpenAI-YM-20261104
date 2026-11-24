import YM.Integration.WilsonNeutralNormalizedForestStep
import YM.Integration.WilsonWindowFormalAnnouncement
import YM.FormalBulk08.Primer.Fields

/-! The normalized graph, upper quiet action and adjacent matrix are the
independently prescribed Primer objects on the *same* booked Wilson course.
Using the full field horizon at the input gives precisely the rooted column
published by the curvature roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralAppointedForestStep
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open scoped Topology BigOperators Matrix Classical

variable {G:Gauge} {d D:ℕ} (R:Run G) (wood:Primer.Families R.family) (a:hue G)
variable (depth:d<D) {U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)

include grant in
theorem column (N i:ℕ) : graph R wood a depth N i=Primer.fieldCoeffs R.family a wood depth N i := by
  let line (ρ:ChartRatio G):=Elm.terrace ρ R.family.path.levels wood (Hay.Wday _) a
    (R.family.labels.level d) (R.family.localSection d) depth N i
  exact congrArg line grant.1

include grant in
theorem vacuum (N i:ℕ) :
    Dove.model R.family.path.levels wood (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a N i =
      Primer.densityCoeff R.family wood a N i := by
  let line (ρ:ChartRatio G):=Dove.model R.family.path.levels wood (Hay.Wday _) ρ a N i
  exact congrArg line grant.1

include grant in
theorem step (N i:ℕ) : matrix R wood a depth N i=Primer.fieldStep R.family a wood depth N i := by
  let line (ρ:ChartRatio G):=Elm.bornM (ρ:=ρ) (T:=R.family.localSection d) (W:=Primer.ChamberU R.family wood 0)
    a depth PUnit.unit N i
  exact congrArg line grant.1

def integral (run:Run G) (routes:Primer.Families run.family) (col:hue G) (Dfit:d<D) (top i:ℕ) (n:Side)
    (F:Forest (primary (destination run.family.path.levels top i).patch run.family.path.levels.clock.kernel n).ratio)
    (t:(primary (destination run.family.path.levels top i).patch run.family.path.levels.clock.kernel n).Choices)
    (b:Letter (run.family.labels.level d)) (f:Studio D) : Pap (wire G n) := by
  let A:=destination run.family.path.levels top i
  let α:=Reef.flush F t run.metals.O (Mesa.stone (Primer.densityCoeff run.family routes col top (i+1)) (n*A.L))
  let H:=chamber A (run.family.path.levels.blocks i 0).branches n F t
  let y:=Primer.fieldCoeffs run.family col routes Dfit top (i+1)
  exact PowerSeries.C (MvPolynomial.C (Kemp.aven A.L d)) *
    ∑ x : Site A.L, Orb.flag H α (Reef.seat F (Kemp.resite (wrap _ (lift x)) (Kemp.banner d
        (y b (Dawn.throughW x D (Elm.growL run.family.path.levels i) f)) (n*A.L))))

include grant in
theorem input (N i:ℕ) (hs:G.Simple) (o:Loc G 1) (live:i<N) (hd:d≤R.family.path.levels.clock.J (i+1))
    (n:Side) (F:Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).ratio)
    (t:(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).Choices)
    (b:Letter (R.family.labels.level d)) (f:Studio D) :
    WilsonNeutralNormalizedForestStep.integral R wood a depth N i n F t b f =
      integral R wood a depth N i n F t b f := by
  have native:=normalized R wood a depth hs o N (i+1) live
    (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have rise:=Kemp.banner_rise (native.officers b).fare (slotsFits _ b)
  rw [column R wood a depth grant] at rise
  unfold WilsonNeutralNormalizedForestStep.integral integral
  dsimp only
  rw [column R wood a depth grant]
  change _ * ∑ x, Orb.flag _ (Reef.flush F t R.metals.O (Mesa.stone
    (Dove.model R.family.path.levels wood (fun k=>(R.family.path.levels.blocks k 0).branches)
      R.metals.O a N (i+1)) _)) _ = _
  rw [vacuum R wood a grant]
  simp_rw [rise]
  rfl

include grant in
theorem measured (N i:ℕ) (hs:G.Simple) (o:Loc G 1) (live:i<N) (hd:d≤R.family.path.levels.clock.J (i+1))
    (per:ℕ) (F:∀n:Side,Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).ratio)
    (t:∀n:Side,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).Choices)
    (b:Letter (R.family.labels.level d)) (f:Studio D) (e r:ℕ) (v:chain (wire G (R.family.S.side i per)) r) :
    let n:=R.family.S.side i per
    let A:=destination R.family.path.levels N i
    let w:=Primer.densityCoeff R.family wood a N (i+1)
    let coin:=Roof.epoch a A (wood i) R.family.path.levels.clock.kernel w R.metals.O (R.family.path.levels.blocks i 0).branches
    Tendsto (fun m:Side=>∑k∈Finset.range (e+1),Wine.bill (bookH coin) (bookU coin) e k r*
      Shore.cores (Shore.tray m n) (rancho (integral R wood a depth N i (m*n) (F _) (t _) b f) k r) v)
      atTop (𝓝 (rancho (Kemp.banner d ((Roof.larch (Primer.fieldCoeffs R.family a wood depth N i)
        (Primer.fieldStep R.family a wood depth N i)) b f) n) e r v)) := by
  intro n A w coin
  have own:=WilsonNeutralNormalizedForestStep.original R wood a depth N i hs o live hd per F t b f e r v
  dsimp only at own
  simp_rw [input R wood a depth grant N i hs o live hd] at own
  rw [column R wood a depth grant,step R wood a depth grant] at own
  convert own using 1
  dsimp only [coin,w,A,n]
  rw [←vacuum R wood a grant]

end YM.Integration.WilsonNeutralAppointedForestStep
end
