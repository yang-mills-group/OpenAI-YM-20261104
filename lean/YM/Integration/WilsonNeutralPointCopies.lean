import YM.Integration.WilsonNeutralPointObserved

/-! The genuine physical cover filter for one displaced fine word. The
upper pupil is held fixed, each indexed cover uses its own actual phase,
forest, and joint tag, and its coarse link field is the one from Mk/Fk. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointCopies
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Matrix Classical

open AllOrder.Ker

theorem conveyed {G:Gauge}{n M:Side}(h:n.val ∣ M.val)(x:Stationary.Link G n):
    FreeResolvent.flatten (Stationary.arm G M 1 (convey (coverWin h) x)) =
      FreeResolvent.flatten (Stationary.arm G n 1 x) ∘ Prod.map (splitter h) id:=rfl

variable {G:Gauge} {d D:ℕ} (R:Run G) (wood:Primer.Families R.family) (a:hue G)
variable (depth:d<D) (digit:∀i,Site (R.family.S.block i)) {U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)

def phase (run:Run G) (routes:Primer.Families run.family) (col:hue G) (Dfit:d<D) (digit:∀i,Site (run.family.S.block i))
    (N i:ℕ)(n M:Side)(h:n.val∣M.val)
    (F:Forest (primary (destination run.family.path.levels N i).patch run.family.path.levels.clock.kernel M).ratio)
    (t:(primary (destination run.family.path.levels N i).patch run.family.path.levels.clock.kernel M).Choices)
    (b:Letter (run.family.labels.level d))(f:Studio D)
    (z:Site (n*(destination run.family.path.levels N i).L))(e:ℕ)(B:Stationary.Link G n) :ℝ:=
  let A:=destination run.family.path.levels N i
  let r:Ratio n (n*A.L):=Ratio.mk A.L rfl
  let s:Ratio M (M*A.L):=Ratio.mk A.L rfl
  let fine_dvd: (n*A.L).val∣(M*A.L).val:=subdiv_dvd r s rfl h
  (Pages (n*A.L) (M*A.L):ℝ)⁻¹ * ∑ p:Fin (Pages (n*A.L) (M*A.L)),
    MvPolynomial.eval (FreeResolvent.flatten (Stationary.arm G M 1 (convey (coverWin h) B))) (coeff e
      (WilsonNeutralPointAngle.reading run routes col Dfit digit N i M F t b f (page fine_dvd z p).val))

include grant in
theorem same_at (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (n m M:Side)(same:m*n=M)(h:n.val∣M.val)
    (F:Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel (m*n)).ratio)
    (F':Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel M).ratio)
    (t:(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel (m*n)).Choices)
    (t':(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel M).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio D)
    (z:Site (n*(destination R.family.path.levels N i).L))(e:ℕ)(B:Stationary.Link G n):
    WilsonNeutralPointObserved.atPages R wood a depth digit N i n m F t b f z e (FreeResolvent.flatten (Stationary.arm G n 1 B))
      =phase R wood a depth digit N i n M h F' t' b f z e B:=by
  subst M
  dsimp only [WilsonNeutralPointObserved.atPages,phase]
  rw [conveyed h B]
  apply congrArg (fun u:ℝ=>(Pages (n*(destination R.family.path.levels N i).L) (m*n*(destination R.family.path.levels N i).L):ℝ)⁻¹*u)
  apply Finset.sum_congr rfl
  intro u _
  rw [WilsonNeutralPointAngle.original R wood a depth digit grant N i hs o live hd _ F t t b f _,
    WilsonNeutralPointAngle.original R wood a depth digit grant N i hs o live hd _ F' t' t b f _]

include grant in
theorem original (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (n:Side)
    (F:∀c:Covers R.family.path.levels.S i n,Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel (R.family.side i c.val)).ratio)
    (t:∀c:Covers R.family.path.levels.S i n,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel (R.family.side i c.val)).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio D)
    (z:Site (n*(destination R.family.path.levels N i).L))(e:ℕ)(B:Stationary.Link G n) :
    let A:=destination R.family.path.levels N i
    let r:Ratio n (n*A.L):=Ratio.mk A.L rfl
    let w:=Primer.densityCoeff R.family wood a N (i+1)
    let Y:=WilsonNeutralPointCourse.filed R wood a depth digit N (i+1) b f
    let out:=Kemp.braise A (wood i) w (Kemp.work (lift (r.residue z)) Y) R.metals.O (R.family.path.levels.blocks i 0).branches d
    Tendsto (fun c:Covers R.family.path.levels.S i n=>phase R wood a depth digit N i n (R.family.side i c.val) c.prop
      (F c) (t c) b f z e B) (coverFilter R.family.path.levels.S i n)
      (𝓝 (MvPolynomial.eval (FreeResolvent.flatten (Stationary.arm G n 1 B) ∘ Lotus.tint (r.parent z)) (coeff e (Kemp.banner d out n)))):=by
  intro A r w Y out
  let K:=R.family.path.levels.clock.kernel
  let F₀:=fun u:Side=>Reef.floor K A (wood i) u
  let t₀ (u:Side):(primary A.patch K u).Choices:=Classical.arbitrary _
  refine (WilsonNeutralPointObserved.original R wood a depth digit grant N i hs o live hd n F₀ t₀ b f z e
    (FreeResolvent.flatten (Stationary.arm G n 1 B))).congr' (.of_forall fun c=>?_ )
  exact same_at R wood a depth digit grant N i hs o live hd n _ _ (WilsonNeutralReceivedCoverLimit.actual_size _ i n c)
    c.prop (F₀ _) (F c) (t₀ _) (t c) b f z e B

end YM.Integration.WilsonNeutralPointCopies
end
