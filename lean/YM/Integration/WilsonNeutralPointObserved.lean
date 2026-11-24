import YM.Integration.WilsonNeutralPointAngle
import YM.Integration.WilsonNeutralPointPageAverage

/-! The original held potential for a single moved child and its genuine
periodic copies, before integrating over the other child positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointObserved
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
variable (depth:d<D) (digit:∀i,Site (R.family.S.block i)) {U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)


include grant in
theorem degree (N i:ℕ) (hs:G.Simple) (o:Loc G 1) (live:i<N)
    (hd:d≤R.family.path.levels.clock.J (i+1)) (n:Side)
    (F:Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).ratio)
    (t:(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).Choices)
    (b:Letter (R.family.labels.level d)) (f:Studio D)(x:Site (destination R.family.path.levels N i).L):
    Young (rancho (WilsonNeutralPointAngle.reading R wood a depth digit N i n F t b f (wrap _ (lift x)))) d:=by
  let A:=destination R.family.path.levels N i
  let w:=Primer.densityCoeff R.family wood a N (i+1)
  let Y:=WilsonNeutralPointCourse.filed R wood a depth digit N (i+1) b f
  have c:=WilsonNeutralPointCourse.original R wood a depth digit N (i+1) hs o live
    (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have ritual:Sierra.Ritual Y d:=by
    dsimp only [Y]
    exact Sierra.ritual_cell o f (clef_through (c.officers b) (slotsFits _ b))
  have moved:=Sierra.from_R Y d ritual (lift x)
  have story:Story w (pink R.family.path.levels.clock.kernel.penalty A.wing):=by
    dsimp only [w]
    rw [←WilsonNeutralAppointedForestStep.vacuum R wood a grant]
    exact (Dove.genu R.family.path.levels wood (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a
      R.alloy.B.ratio hs (i:=i+1) (N:=N) live).toStory
  have paid:=Kemp.tossed_gen A (wood i) w (Kemp.work (lift x) Y) R.metals.O
    (R.family.path.levels.blocks i 0).branches story R.alloy.B.ratio (R.family.path.levels.clock.adm i)
    moved.young d moved.committees le_rfl n t
  rw [Kemp.seated (lift x) Y d _ ritual.young ritual.committees] at paid
  rw [WilsonNeutralPointAngle.original R wood a depth digit grant N i hs o live hd n F t t b f _]
  exact paid

include grant in
theorem observed (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (n:Side)(F:∀s:Side,Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).ratio)
    (t:∀s:Side,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio D)(x:Site (destination R.family.path.levels N i).L)
    (e:ℕ)(B:wire G n→ℝ) :
    let A:=destination R.family.path.levels N i
    let w:=Primer.densityCoeff R.family wood a N (i+1)
    let Y:=WilsonNeutralPointCourse.filed R wood a depth digit N (i+1) b f
    let out:=Kemp.braise A (wood i) w (Kemp.work (lift x) Y) R.metals.O (R.family.path.levels.blocks i 0).branches d
    Tendsto (fun c:Covers R.family.path.levels.S i n=>
      let m:=WilsonNeutralReceivedCoverLimit.multiplicity R.family.path.levels.S i n c
      MvPolynomial.eval B (MvPolynomial.rename (Shore.tray m n)
        (coeff e (WilsonNeutralPointAngle.reading R wood a depth digit N i (m*n) (F _) (t _) b f (wrap _ (lift x))))))
      (coverFilter R.family.path.levels.S i n) (𝓝 (MvPolynomial.eval B (coeff e (Kemp.banner d out n)))):=by
  intro A w Y out
  let m:=WilsonNeutralReceivedCoverLimit.multiplicity R.family.path.levels.S i n
  let J (c:Covers R.family.path.levels.S i n):=WilsonNeutralPointAngle.reading R wood a depth digit N i
    (m c*n) (F _) (t _) b f (wrap _ (lift x))
  have young (c:Covers R.family.path.levels.S i n):Young (rancho (J c)) d:=
    degree R wood a depth digit grant N i hs o live hd _ (F _) (t _) b f x
  have small (c:Covers R.family.path.levels.S i n)(r:ℕ)(large:d+e<r):
      marble r (MvPolynomial.rename (Shore.tray (m c) n) (coeff e (J c)))=0:=by
    rw [Shore.pebble]
    have vanish:marble r (coeff e (J c))=0:=by
      by_contra hn
      exact large.not_ge (young c e r hn)
    rw [vanish];funext v;simp [Shore.cores]
  have hi (r:ℕ)(large:d+e<r):marble r (coeff e (Kemp.banner d out n))=0:=by
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
  have c:=WilsonNeutralPointCourse.original R wood a depth digit N (i+1) hs o live
    (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have ritual:Sierra.Ritual Y d:=by
    dsimp only [Y]
    exact Sierra.ritual_cell o f (clef_through (c.officers b) (slotsFits _ b))
  have moved:=Sierra.from_R Y d ritual (lift x)
  have story:Story w (pink R.family.path.levels.clock.kernel.penalty A.wing):=by
    dsimp only [w]
    rw [←WilsonNeutralAppointedForestStep.vacuum R wood a grant]
    exact (Dove.genu R.family.path.levels wood (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a
      R.alloy.B.ratio hs (i:=i+1) (N:=N) live).toStory
  have accepted:Sierra.Ritual out d:=Sierra.paragon ((0,o):edgeL G) A (wood i) w R.metals.O
    (R.family.path.levels.blocks i 0).branches story R.alloy.B.ratio (R.family.path.levels.clock.adm i) moved t
  change Tendsto (fun c=>Shore.cores (Shore.tray (m c) n) (rancho (J c) e r) v * ∏j,B (v j)) _
    (𝓝 (rancho (Kemp.banner d out n) e r v*∏j,B (v j)))
  rw [Kemp.badge out accepted.young accepted.committees le_rfl]
  exact (WilsonNeutralPointAngle.covered R wood a depth digit grant N i hs o live hd n F t b f x e r v).mul tendsto_const_nhds

def atPages (run:Run G) (routes:Primer.Families run.family) (col:hue G) (Dfit:d<D) (digit:∀i,Site (run.family.S.block i))
    (N i:ℕ)(n m:Side)
    (F:Forest (primary (destination run.family.path.levels N i).patch run.family.path.levels.clock.kernel (m*n)).ratio)
    (t:(primary (destination run.family.path.levels N i).patch run.family.path.levels.clock.kernel (m*n)).Choices)
    (b:Letter (run.family.labels.level d))(f:Studio D)
    (z:Site (n*(destination run.family.path.levels N i).L))(e:ℕ)(B:wire G n→ℝ) :ℝ:=
  let A:=destination run.family.path.levels N i
  let r:Ratio n (n*A.L):=Ratio.mk A.L rfl
  let R':Ratio (m*n) (m*n*A.L):=Ratio.mk A.L rfl
  let h:n.val∣(m*n).val:=dvd_mul_left n.val m.val
  let fine_dvd: (n*A.L).val∣(m*n*A.L).val:=subdiv_dvd r R' rfl h
  (Pages (n*A.L) (m*n*A.L):ℝ)⁻¹ * ∑ p:Fin (Pages (n*A.L) (m*n*A.L)),
    MvPolynomial.eval (B ∘ Prod.map (splitter h) id) (coeff e
      (WilsonNeutralPointAngle.reading run routes col Dfit digit N i (m*n) F t b f (page fine_dvd z p).val))

include grant in
theorem original (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (n:Side)(F:∀s:Side,Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).ratio)
    (t:∀s:Side,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio D)
    (z:Site (n*(destination R.family.path.levels N i).L))(e:ℕ)(B:wire G n→ℝ) :
    let A:=destination R.family.path.levels N i
    let r:Ratio n (n*A.L):=Ratio.mk A.L rfl
    let w:=Primer.densityCoeff R.family wood a N (i+1)
    let Y:=WilsonNeutralPointCourse.filed R wood a depth digit N (i+1) b f
    let out:=Kemp.braise A (wood i) w (Kemp.work (lift (r.residue z)) Y) R.metals.O (R.family.path.levels.blocks i 0).branches d
    Tendsto (fun c:Covers R.family.path.levels.S i n=>atPages R wood a depth digit N i n
      (WilsonNeutralReceivedCoverLimit.multiplicity R.family.path.levels.S i n c) (F _) (t _) b f z e B)
      (coverFilter R.family.path.levels.S i n)
      (𝓝 (MvPolynomial.eval (B ∘ Lotus.tint (r.parent z)) (coeff e (Kemp.banner d out n)))):=by
  intro A r w Y out
  refine (observed R wood a depth digit grant N i hs o live hd n F t b f (r.residue z) e
    (B ∘ Lotus.tint (r.parent z))).congr' (.of_forall fun c=>?_)
  let m:=WilsonNeutralReceivedCoverLimit.multiplicity R.family.path.levels.S i n c
  let h:n.val∣(m*n).val:=dvd_mul_left n.val m.val
  have tray: Shore.tray m n = (Prod.map (splitter h) id : wire G (m*n)→wire G n):=by
    funext v
    apply Prod.ext _ rfl
    exact WilsonNeutralReceivedCoverLimit.residues m n v.1
  let M:=m*n
  let R':Ratio M (M*A.L):=Ratio.mk A.L rfl
  let h':(n*A.L).val∣(M*A.L).val:=subdiv_dvd r R' rfl h
  let Z:=Kemp.banner d Y (M*A.L)
  let Q:=Reef.tossed A R.metals.O (R.family.path.levels.blocks i 0).branches (wood i) M (t M) (Mesa.stone w (M*A.L))
  let k:=wrap (M*A.L) (lift (r.residue z))
  have own (p:Site (M*A.L)):WilsonNeutralPointAngle.reading R wood a depth digit N i M (F M) (t M) b f p=
      Q (Kemp.resite p Z):=WilsonNeutralPointAngle.original R wood a depth digit grant N i hs o live hd M (F M) (t M) (t M) b f p
  change MvPolynomial.eval (B ∘ Lotus.tint (r.parent z)) (MvPolynomial.rename (Shore.tray m n)
    (coeff e (WilsonNeutralPointAngle.reading R wood a depth digit N i M (F M) (t M) b f k)))=_
  rw [own k,MvPolynomial.eval_rename,tray]
  symm
  calc
    atPages R wood a depth digit N i n m (F M) (t M) b f z e B=
        (Pages (n*A.L) (M*A.L):ℝ)⁻¹*∑p:Fin (Pages (n*A.L) (M*A.L)),
        MvPolynomial.eval (B ∘ Prod.map (splitter h) id) (coeff e (Q (Kemp.resite (page h' z p).val Z))):=by
      apply congrArg ((Pages (n*A.L) (M*A.L):ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro p _
      rw [own _]
    _ = _ := WilsonNeutralPointPageAverage.original R wood a depth digit grant N i hs o live hd n M h b f z (t M) B e

end YM.Integration.WilsonNeutralPointObserved
end
