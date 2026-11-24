import YM.Integration.WilsonOlderFreshGraphFold
import YM.Integration.WilsonOlderFreshGraphPainter

/-! Exact publication on every period of the full original normalized column.
The test mark is independent of the angular field at its own root. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphPublication
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Mentor Push.PriceCompiler Primer AllOrder
open AllOrder.Ink Primitives.TwoWave Push.AbsoluteSums WilsonOlderFreshGraphInk
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)

theorem table (o:Loc G 1) (T:Pot G) (e h:ℕ)
    (wallet:∀r:Fin (h+e+1),∃b C:ℝ,0≤b ∧ Knoxville (fame _) b (0,o) (T e r) C)
    (n:Side) (A:Board (Loc G 1) n ℝ) (s:Board Unit n ℝ):
    (WilsonOlderFreshGraphInk.all (fun r:Fin (h+e+1)=>T e r)).table n (mingle A s) =
      ∑y:Site n,s (y,())*MvPolynomial.eval (fun x:wire G n=>A (y+x.1,x.2))
        (coeff e (Kemp.banner h T n)) := by
  choose b C pos earn using wallet
  let F(r:Fin (h+e+1)):=tensor (T e r)
  have hf(r:Fin (h+e+1)):(F r).Good 0 (C r) (h+e+1):=by
    apply (WilsonOlderFreshGraphInk.paid o (T e r) (earn r) le_rfl (by simpa using pos r)).debt le_rfl le_rfl
    omega
  have hc:=budget_finite (fun r=>(earn r).1) le_rfl
  change (Ink.Field.sum F).table n _=_
  rw [Ink.Field.contribution F hf hc le_rfl n,Finset.sum_apply]
  simp_rw [show ∀r:Fin (h+e+1),(F r).table n (mingle A s)=_ from fun r=>
    WilsonOlderFreshGraphFold.whole (T e r) ((penn_total (earn r) (pos r)).of_norm) n A s]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _=>?_
  rw [Kemp.banner,coeff_mk,map_sum,Finset.mul_sum]
  exact Fin.sum_univ_eq_sum_range (fun r:ℕ=>s (y,())*MvPolynomial.eval (fun x:wire G n=>A (y+x.1,x.2)) (facade r (sieve n (T e r)))) (h+e+1)

include simple in
theorem original {U:ℕ→ℕ} (purchase:WilsonWindowFormalPurchase.Canonical U R.kit)
    (o:Loc G 1) (w:Letter (R.family.labels.level d)):
    ∀ᶠ i:ℕ in atTop,∀(N:ℕ),i≤N→∀(f:Studio D)(e:ℕ)(n:Side)
      (A:Board (Loc G 1) n ℝ)(s:Board Unit n ℝ),
      (WilsonOlderFreshGraphRoster.row R L a depth N i w f e).table n (mingle A s) =
       ∑y:Site n,s (y,())*MvPolynomial.eval (fun x:wire G n=>A (y+x.1,x.2))
         (coeff e (Kemp.banner d (Primer.fieldCoeffs R.family a L depth N i w f) n)) := by
  let C:=R.family
  let J:=d+D+5
  have j5:5≤J:=by dsimp [J];omega
  have jD:D≤J:=by dsimp [J];omega
  have jd:d+3≤J:=by dsimp [J];omega
  obtain ⟨K,eventual⟩:=eventually_atTop.mp (C.path.levels.fits.deep.eventually_ge_atTop J)
  have gate:J≤C.path.levels.clock.J (K+1):=eventual _ (Nat.le_succ K)
  let ann:=WilsonWindowFormalAnnouncement.on_run R purchase
  filter_upwards [eventually_ge_atTop K] with i past
  intro N room f e n A s
  have wage:=(Primer.primal C simple a L o ann j5 gate depth jd jD past N room).1.officers w
  apply table o _ e d _ n A s
  intro r
  obtain ⟨b,B,hb,_,price⟩:=wage.fare.2.2 e r
  exact ⟨b,_,hb.le,price f⟩

end YM.Integration.WilsonOlderFreshGraphPublication
end
