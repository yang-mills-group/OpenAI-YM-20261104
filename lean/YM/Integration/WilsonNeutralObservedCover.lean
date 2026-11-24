import YM.Integration.WilsonNeutralReceivedCoverLimit

/-! Combine the original finite angular tensors into the actual signed
held-potential reading. The field order of each finite coefficient is
bounded on every native cover before the copy limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralObservedCover
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Matrix Classical

private theorem read {I:Type} [Fintype I] (K:ℕ) (A:I→ℝ) (P:TypeR I)
    (trunc:∀r,K<r→marble r P=0) :
    MvPolynomial.eval A P=∑r∈Finset.range (K+1),∑v:chain I r,marble r P v*∏j:Fin r,A (v j) := by
  have h:=congrArg (MvPolynomial.eval A) (crema P K trunc)
  simpa only [map_sum,Lava.facade_eq,map_mul,MvPolynomial.eval_C,cards,map_prod,MvPolynomial.eval_X] using h.symm

variable {G:Gauge} {d D:ℕ} (R:Run G) (wood:Primer.Families R.family) (a:hue G)
variable (depth:d<D) {U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)

include grant in
theorem degree (N i:ℕ) (hs:G.Simple) (o:Loc G 1) (live:i<N)
    (hd:d≤R.family.path.levels.clock.J (i+1)) (n:Side)
    (F:Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).ratio)
    (t:(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).Choices)
    (tags:∀s:Side,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).Choices)
    (b:Letter (R.family.labels.level d)) (f:Studio D) :
    Young (rancho (WilsonNeutralAppointedForestStep.integral R wood a depth N i n F t b f)) d := by
  let A:=destination R.family.path.levels N i
  let y:=WilsonRunFormalMarkedStep.graph R wood a depth N (i+1)
  let w:=Dove.model R.family.path.levels wood (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a N (i+1)
  have path:Wade o (y b) (slots (R.family.labels.level d) b):=
    ((WilsonRunFormalMarkedStep.normalized R wood a depth hs o N (i+1) live
      (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))).officers b).fare
  have story:Story w (pink R.family.path.levels.clock.kernel.penalty A.wing):=
    (Dove.genu R.family.path.levels wood (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a
      R.alloy.B.ratio hs (i:=i+1) (N:=N) live).toStory
  have fit:=slotsFits (R.family.labels.level d) b
  have h:=Kemp.quickP_breeze o A (wood i) w (y b) R.metals.O (R.family.path.levels.blocks i 0).branches
    (d:=d) (Elm.growL R.family.path.levels i) path story R.alloy.B.ratio fit (R.family.path.levels.clock.adm i)
    f n (tags n)
  rw [Kemp.preQ o A (wood i) w R.metals.O (R.family.path.levels.blocks i 0).branches path
    (Elm.growL R.family.path.levels i) fit tags f d] at h
  rw [←WilsonNeutralAppointedForestStep.input R wood a depth grant N i hs o live hd]
  rw [WilsonNeutralNormalizedForestStep.received R wood a depth N i hs o live hd n F t (tags n) b f]
  exact fun e r hr=>(h e r hr).trans (Nat.add_le_add_right fit e)

include grant in
theorem original (N i:ℕ) (hs:G.Simple) (o:Loc G 1) (live:i<N)
    (hd:d≤R.family.path.levels.clock.J (i+1)) (n:Side)
    (F:∀s:Side,Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).ratio)
    (t:∀s:Side,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).Choices)
    (b:Letter (R.family.labels.level d)) (f:Studio D) (e:ℕ) (B:wire G n→ℝ) :
    let A:=destination R.family.path.levels N i
    let w:=Primer.densityCoeff R.family wood a N (i+1)
    let y:=Primer.fieldCoeffs R.family a wood depth N (i+1)
    let pre:=Kemp.quick A (wood i) w (y b) R.metals.O (R.family.path.levels.blocks i 0).branches
      (Elm.growL R.family.path.levels i) d d
    Tendsto (fun c:Covers R.family.path.levels.S i n=>
      let m:=WilsonNeutralReceivedCoverLimit.multiplicity R.family.path.levels.S i n c
      MvPolynomial.eval B (MvPolynomial.rename (Shore.tray m n)
        (coeff e (WilsonNeutralAppointedForestStep.integral R wood a depth N i (m*n) (F _) (t _) b f))))
      (coverFilter R.family.path.levels.S i n) (𝓝 (MvPolynomial.eval B (coeff e (Kemp.banner d (pre f) n)))) := by
  intro A w y pre
  let m:=WilsonNeutralReceivedCoverLimit.multiplicity R.family.path.levels.S i n
  let J (c:Covers R.family.path.levels.S i n):=WilsonNeutralAppointedForestStep.integral R wood a depth N i
    (m c*n) (F _) (t _) b f
  have young (c:Covers R.family.path.levels.S i n): Young (rancho (J c)) d:=
    degree R wood a depth grant N i hs o live hd _ (F _) (t _) t b f
  have small (c:Covers R.family.path.levels.S i n)(r:ℕ)(large:d+e<r):
      marble r (MvPolynomial.rename (Shore.tray (m c) n) (coeff e (J c)))=0:=by
    rw [Shore.pebble]
    have vanish:marble r (coeff e (J c))=0:=by
      by_contra hn
      exact large.not_ge (young c e r hn)
    rw [vanish];funext v;simp [Shore.cores]
  have hi (r:ℕ)(large:d+e<r):marble r (coeff e (Kemp.banner d (pre f) n))=0:=by
    rw [marble_eq_zero_iff,Kemp.banner,coeff_mk,map_sum]
    apply Finset.sum_eq_zero
    intro k hk
    rw [MvPolynomial.homogeneousComponent_of_mem (facade_grade ..),if_neg (by have:=Finset.mem_range.mp hk; omega)]
  change Tendsto (fun c=>MvPolynomial.eval B (MvPolynomial.rename (Shore.tray (m c) n) (coeff e (J c)))) _ _
  simp_rw [read (d+e) B _ (small _),Shore.pebble]
  rw [read (d+e) B _ hi]
  apply tendsto_finsetSum
  intro r _
  apply tendsto_finsetSum
  intro v _
  exact (WilsonNeutralReceivedCoverLimit.original R wood a depth grant N i hs o live hd n F t b f e r v).mul tendsto_const_nhds

end YM.Integration.WilsonNeutralObservedCover
end
