import YM.Integration.WilsonOlderFreshPointGauge
import YM.Integration.WilsonOlderFreshGraphDatedSalary
/-! Submit the complete normalized single-child tensor, at its authentic
rooted exponential width, to the same universal physical printer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointPainter
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)



open WilsonOlderFreshGraphCompiler
def terms (i:ℕ)(b:Letter (R.family.labels.level d))(p:WilsonOlderFreshPointGauge.Ballot R i D):
    ArrayBank G d:=fun e r=>WilsonOlderFreshPointGauge.field R L a depth i b p e r

def Price (i:ℕ)(o:Loc G 1)(b:Letter (R.family.labels.level d))(p:WilsonOlderFreshPointGauge.Ballot R i D)
    (Q:ℕ)(c:ℝ):Prop:=∀e≤Q,∀r:Fin (d+e+1),Knoxville (fame _) (WilsonPointChildFiledPress.width R i)
      (0,o) (terms R L a depth i b p e r) c

include simple in
theorem original (i:ℕ)(front:d≤R.family.path.levels.clock.J (i+1))(o:Loc G 1)
    (b:Letter (R.family.labels.level d))(p:WilsonOlderFreshPointGauge.Ballot R i D)(Q:ℕ)
    {c:ℝ}(c0:0≤c)(wage:Price R L a depth i o b p Q c):
    ∃t:Submission G d Q (WilsonOlderFreshGraphRoster.narrow R d Q i),
      t.bank=terms R L a depth i b p ∧ t.wage=(d+Q+1:ℕ)*c:=by
  let X:=terms R L a depth i b p
  let α:=WilsonOlderFreshGraphRoster.narrow R d Q i
  have raw (e:ℕ)(he:e≤Q):
      (diagram X e).Good α (∑_r:Fin (d+e+1),c) (d+e+1) ∧
      ∀z,QuadraticLocal.Sunrise.Focus.Depicted ({()}:Finset Unit) ((diagram X e).slip z):=by
    let ν:=WilsonPointChildFiledPress.width R i
    have ν₀:0<ν:=(windowBasis G R.family.path.levels.clock.kernel).pos _
    apply WilsonOlderFreshGraphInk.purchased (b:=ν) o (X e) _ (wage e he) (div_nonneg ν₀.le (by positivity))
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show d+e≤d+Q+1 by omega)) ν₀.le
  have T0:0≤(d+Q+1:ℕ)*c:=mul_nonneg (Nat.cast_nonneg _) c0
  have good (e:ℕ)(he:e≤Q):(diagram X e).Good α ((d+Q+1:ℕ)*c) (e+d+2):=by
    apply (raw e he).1.debt le_rfl _ (by omega)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show d+e+1≤d+Q+1 by omega)) c0
  have ward (n:Side)(s:Board Unit n ℝ)(e:ℕ)(_h:e≤Q):
      Haiku.Vernal G n (fun j A=>(diagram X j).table n (mingle A s)) e:=by
    have eq:(fun j A=>(diagram X j).table n (mingle A s))=
        WilsonOlderFreshPointGauge.panel R L a depth i b p n s:=funext fun j=>funext fun A=>
          (WilsonOlderFreshPointGauge.original R L a depth simple i o front b p n s j).2 A
    rw [eq]
    exact (WilsonOlderFreshPointGauge.original R L a depth simple i o front b p n s e).1
  exact ⟨⟨X,_,T0,good,fun e he=>(raw e he).2,ward⟩,rfl,rfl⟩

end YM.Integration.WilsonOlderFreshPointPainter
end
