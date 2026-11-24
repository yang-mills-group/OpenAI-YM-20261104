import YM.Integration.WilsonOriginalPublicTrialRegulators
import YM.Integration.WilsonReceivedCanonicalVerseWeighted

/-! The two winding salaries of the chronological finite Wick histories are
booked at the trial stop. Their signed difference disappears on the original
physical order, uniformly over all tested finite placements and angular
directions inside the stated hull, including positive-grade scalars. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialMarkedHearing
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Tree Exterior Stationary
open PowerSeries Next.Free FormalBulk08 Flat Reef Jets Series Shore Gorge Lotus Mesa City Cork
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonPointChildPlacedFamily
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations Pose Dawn Kemp Rift
open WilsonMarkedIndependentPhysicalIntake WilsonPointChildFiledPress
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Realm
open WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators


open WilsonReceivedDatedVerseReprint (Issued printed)
open WilsonMarkedIndependentEnrolledPeriod (registered)

open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonReceivedMicroscopicVerseWallet (gross)

open WilsonReceivedReplantedVerseTrail (Paid)

open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonReceivedCanonicalVerseRegister (start)

open WilsonReceivedCanonicalVerseWeighted (Measured wick filed)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open WilsonReceivedCanonicalVerseHearing (fee)
open WilsonOriginalPublicTrialInput (salary fitted)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)(d j mask:Fin 3→ℕ){h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (tags:∀i n,(Flat.primary ((R.family.path.levels).clock.op i 0).patch (R.family.path.levels).clock.kernel n).Choices)
    (prices:ℕ→Gear G→ℝ)(bank:FundedMarkedCoverRows.prices prices R.kit)(e target:ℕ)(η:ℝ)
    (M:Fin 3→ℝ)(Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))(opened:Indexed R d j target η M Y)
    (f:Extraction.Order):
    ∀ᶠm:ℕ in atTop,∀b,m≤b → ∀before:∀a,j a≤b,∀ (rank:ℕ)(ε:ℝ),0<ε →
    ∀ᶠz:ℕ×ℕ in f.fuse,b<z.1 ∧ ∀(S:Finset (Fin 3))(r:Fin (rank+1))(u:G.ColorIndex)
      (home:Fin 3 → Cover)(read:Pen h S→L[ℝ]ℝ)(a:ℕ),a≤e → ∀(x:Fin r.val→YForest G)(c:Cover)(D:ℕ),
      (∀i∈S,terrain.gap c (home i)≤D)→(∀i,terrain.gap c (x i).1≤D)→8*D<(R.family.side m z.2).val →
      let v:=fitted R d j b target η M Y before opened z.1 z.2
      let w:=weight R d z.1 z.2 b v S
      let n:=R.family.side m z.2
      ‖(∑q:Selection R d S,w q*wick R d mask κ pt u tags z.1 b m home S read n a r x q)-
        (∑q:Selection R d S,w q*filed R d mask κ pt e z.1 b m home S read n a r x q)‖ ≤ ε*‖read‖:=by
  filter_upwards [WilsonReceivedCanonicalVerseWeighted.original R d mask κ pt simple quiet tags prices bank e] with m issued
  intro b past before rank ε pos
  obtain ⟨s,t,A,B,hs,ht,_,_,sale⟩:=issued b past
  let salaries:=salary R d j b η M
  have hearing (S:Finset (Fin 3))(r:Fin (rank+1)):
      ∀ᶠp:ℕ in atTop,wallet R d salaries S*fee (h:=h) e r.val S (R.family.side m p) s t A B < ε:=by
    have one:=WilsonMarkedIndependentMixedOrderedWinding.disappears R s hs (b:=m)
    have two:=WilsonMarkedIndependentMixedOrderedWinding.disappears R t ht (b:=m)
    have limit:Tendsto (fun p:ℕ=>wallet R d salaries S*fee (h:=h) e r.val S (R.family.side m p) s t A B) atTop (𝓝 0):=by
      unfold fee
      simpa using (((one.const_mul (WilsonMarkedOrdinaryCaptureGap.tariff h e r.val S*A^S.card)).add
        (two.const_mul (WilsonMarkedOrdinaryCaptureGap.tariff h e r.val S*B^S.card))).const_mul (wallet R d salaries S))
    exact limit (Iio_mem_nhds pos)
  have whole:=eventually_all.mpr (fun S=>eventually_all.mpr (hearing S))
  apply (Extraction.Order.fused f _).2
  rw [Extraction.Order.late]
  filter_upwards [f.per.cofinal.eventually whole] with per small
  filter_upwards [f.mesh.cofinal.eventually_ge_atTop (b+1)] with N top
  have live:b<f.mesh N:=by omega
  refine ⟨live,?_⟩
  intro S r u home read a grade x c D sites angles room v w n
  have actual:=WilsonOriginalPublicTrialInput.original R d j b target η M Y before opened (f.mesh N) (f.per per) live
  have swift:=sale (f.mesh N) live.le (f.per per) v salaries (fun i=>(actual.1 i).2)
  apply (swift u home S read a grade r x c D sites angles room).trans
  calc
    _=wallet R d salaries S*fee (h:=h) e r.val S n s t A B*‖read‖:=by ring
    _≤_:=mul_le_mul_of_nonneg_right (small S r).le (ContinuousLinearMap.opNorm_nonneg read)

end YM.Integration.WilsonOriginalPublicTrialMarkedHearing
end
