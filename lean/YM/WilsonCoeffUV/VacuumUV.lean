import YM.WilsonCoeffUV.VacuumLaw
import YM.WilsonCoeffUV.Reclosure.Paths.Common

/-!
# Thermal unmasked vacuum Wilson UV release.

Call this over A=C.path.levels with prescribed kernel, smoothing and block
index. Proof never uses momentum constraints on coarse harmonic modes,
loop costs of actual density, actual expectation or evaluation identities
from EveryPhase. Summary API: Kinetic normalization and RG recursion with derivative
(or symbol test) costs in log-link/Ten conventions. ‖ . ‖ is per chosen
external slot and anchor (smooth ten invariant, so any slot by re-ordering)
against TRUE distance/length exponent. SumBudget uses Laurent (sum of all
translated costs grafted into one row). Compatibility of quantities in
adaptive widths and publication of alternate curvature reps with correlated
reference in `Reclosure/Paths/Common (plated)`, consumption of Path certificates/E exact
low-order representative moves in `against_Kin`. Do not read larger
order i > e with estimates for e.

Examples of admission:
* `schedule_flat`, `feasible_awards`: pre widths then Gear & budget
  instances for the prescribed Branches (fix kernel/κ in advance). Observe
  pre vs post quantifier order.
* constructed A through `issuedTogether` & *same lease*, retains thermal
  alignment. Also reusable modified costs witnesses. Bias selections belong
  to those proofs, not averaged over phases.

In neither: IR/zero modes at report, derivative of θ-phases, convergence of
partition, gauge-distribution estimates, wire regulator inversion. `Branch`
independent of θ: no such parameter used in Wilson powers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Fk
open RG Function Filter Lattice Source Power Laurent Wilson Blue FreeResolvent Work.F08
open Precision Next.Foundations Input Supply WilsonCoeffLease Bank Bank.Mosaic
open Physical Realm Ticket
open PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {j m k e r i:ℕ} {U V:Credit}

/-- Universal prices in y. Here per archive position native true length of
potentials; for curvature use `plated`. Rank zero of the unmarked action
excluded except for freshet, which emits it DILUTED per coarse site (still
fine variable units before reset).
-/
structure VacuumUV (e i k r:ℕ) (D:Credit) (T:Credit) (G:Gauge) : Prop where
    money : ∀ R: Realm G e T, ∀ m (p:R.anchor ≤ m),
       let P:=R.draws
       let L:=R.paid
       let u:=(R.mint m p).σ
       let z:= R.y m
       let C := D.buy z
       i ≤ e ∧∀ N N',m ≤ N → N ≤ N' →
         let a:ℝ:= (P.S.a N / P.S.a m)^((4:ℝ)⁻¹)
         PairA u C a (actionW P L N m i k) (actionW P L N' m i k) ∧
         PairA u C a (actionW P L N m i k) (timeless P L m i k) ∧
         (∀ x:YForest G, Trunk (u/2) C a x (actionW P L N' m i (k+1)) (timeless P L m i (k+1)) r) ∧
         (m<N → PairA u C a (freshet P L N m i k) (freshet P L N' m i k) ∧ PairA u C a (freshet P L N m i k) (eternal P L m i k) ∧
           twain C a (coeff i (pitch P L N m)) (coeff i (pitch P L N' m)) ∧ twain C a (coeff i (pitch P L N m)) (coeff i (viridian P L m)))
    negativeLog : ∀ R:Realm G e T,∀ m (_:R.anchor≤ m),
       let U:=R.draws
       let L:=R.paid
       let Z:= viridian U L m
       let Q:= timeless U L m
       (Q i= Blue.mix (back Z) (lop (eternal U L m)) i) ∧ Doric Q (holdZ U m) e ∧ Z *(pace Z)^2=1 ∧ (i%2≠ 0 → coeff i Z=0)

lemma costV {A z A' s:ℝ}{P F: Ten ℝ (YForest G) (k+1)}{u:YForest G}(p:Trunk s A z u P F i)(h:A≤A')(hp:0≤ z): Trunk s A' z u P F i:=by
    obtain ⟨a,b,g⟩:=p
    exact ⟨⟨a.1,a.2.1,a.2.2.trans h⟩,⟨b.1,b.2.1,b.2.2.trans h⟩,⟨g.1,g.2.1,g.2.2.trans (mul_le_mul_of_nonneg_right h hp)⟩⟩

lemma export_domain (G:Gauge)(T: Credit)(e i k r:ℕ)(h:i≤e): ∃D:Credit, VacuumUV e i k r D T G:=by
    obtain ⟨V,H⟩:= full_vacuum G e T
    obtain ⟨J,hJ⟩:= releases (H i h (k+1)) r
    obtain ⟨B,u⟩:= advent G e T i k h
    obtain ⟨Y,f⟩:= pitch_step G e T i h
    let D:= (J.plus B).plus (Y.plus V)
    refine ⟨D,⟨fun R m p=>?_,fun R m b=>?_⟩⟩
    · let P:= R.draws; let L:= R.paid; let z:=R.y m
      have hv : 1 ≤ z:= R.depth _ p
      have hz: V.buy z≤ D.buy z:= (Credit.thickened _ hv).trans (Credit.thickened _ hv)
      have he: J.buy z≤ D.buy z:= (Credit.thickens _ hv).trans (Credit.thickens _ hv)
      have hf: B.buy z≤ D.buy z:= (Credit.thickened _ hv).trans (Credit.thickens _ hv)
      have hY: Y.buy z≤ D.buy z:= (Credit.thickens _ hv).trans (Credit.thickened _ hv)
      refine ⟨h,fun N N' hx hab=>?_⟩
      dsimp only
      have hA:= (H i h k R m p N N N' hx le_rfl hab)
      have hR:=PathCost.trail_ratio R.draws.S m N
      let a:=R.tempC m N; have ha:0≤a := (PathCost.trail_pos ..).le
      rw [←hR]; refine ⟨hA.up hz ha,(inherited (H i h _) R p hx (b:=N) le_rfl).up hz ha,fun x=>?_, fun I=>?_⟩
      · have hh:= hJ R m p N N' hx hab x
        rw [← hR] at hh; exact costV hh he ha
      have ht:= f R m p N N N' I le_rfl hab
      let F n:= coeff i (pitch P L n m)
      let g:= coeff i (viridian P L m)
      have hg:Tendsto F atTop (𝓝 g):= evergreen R p h
      refine ⟨(u R m p _ _ _ I le_rfl hab).up hf ha, (inherited_phase u h R p I le_rfl).up hf ha, ht.lift hY ha, (show twain (R.cash Y m) a (F N) g from ?_).lift hY ha⟩
      exact ⟨ht.main, le_of_tendsto hg.norm ((eventually_ge_atTop N).mono (fun M v=> (f R m p N M M I v v).main)), le_of_tendsto (tendsto_const_nhds.sub hg).norm ((eventually_ge_atTop N).mono fun n hn=> (f R m p N N n I le_rfl hn).gap)⟩
    exact ⟨sustainable R b h,modern R b,pace_tax (one_sun R b),key_turn R b h⟩

/-- One useful installation against supplied scheduler. Prices as in `zz`. -/
theorem pin_vacuum {X:ℕ→ℕ}{Ñ:ChartRatio G}{p:Sheet G}{W:Rolls p}{Θ:Protection W}{D:Delays Θ}{T:Bar D}{b0:Wait T}{A:Levels G}
    (g:G.Simple)(t:LocalRatio Ñ)(h:Paid b0 A)(pL:floors G p.kernel X≤ p.floorL)(hx: Tendsto X atTop atTop)(u:voucher W X Ñ ≤ D.betaEntry)(r:ℕ): ∀ᶠ ℓ:ℕ in atTop,
      ∃ R:Realm G r Credit.leanC,R.draws=A∧R.paid=Ñ∧R.anchor=ℓ∧R.y= zz A ∧ ∀ i≤ r,∀ k p,∃ T,VacuumUV r i k p T Credit.leanC G:=by
    filter_upwards [feasible_awards g t pL h u hx r] with ℓ h
    obtain ⟨R,z,f,v,q⟩:=h
    exact ⟨R,z,f,q,v,fun i hi k p=>export_domain G _ r i k p hi⟩
end YM.WilsonCoeffUV.Fk
