import YM.Integration.WilsonOlderFreshGraphCompiler

/-! File every full normalized native Laurent array in the before-block
commission. Only its original polynomial age and physical test norm enter the
input wage. The signs, all dates and every held test slot survive. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphSubmit
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
def charge {d Q:ℕ} (B:Fin (d+Q+1)→ℝ) (e:Fin (Q+1)) (v:Fin (d+Q+1)→ℕ) (β:ℝ):ℝ:=
  ∑r:Fin (d+e.val+1), B (r.castLE (by omega))*ageZ β^(v (r.castLE (by omega)))

def roof {d Q:ℕ} (B:Fin (d+Q+1)→ℝ) (v:Fin (d+Q+1)→ℕ) (β:ℝ):ℝ:=
  ∑e:Fin (Q+1),|charge (d:=d) (Q:=Q) B e v β|

variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)

open WilsonOlderFreshGraphAward
include simple



open WilsonOlderFreshGraphCompiler
def terms (N i:ℕ) (w:Letter (R.family.labels.level d)) (f:Studio D):ArrayBank G d:=
  fun e r=>Primer.fieldCoeffs R.family a L depth N i w f e r.val

theorem original {U:ℕ→ℕ} (purchase:WilsonWindowFormalPurchase.Canonical U R.kit)
    (o:Loc G 1)(w:Letter (R.family.labels.level d)) (Q:ℕ):
    ∃(B:Fin (d+Q+1)→ℝ)(v:Fin (d+Q+1)→ℕ),(∀r,0≤B r) ∧
      ∀ᶠ i:ℕ in atTop,∀p:Ballot i D,
        ∃t:Submission G d Q (WilsonOlderFreshGraphRoster.narrow R d Q i),
          t.bank=terms R L a depth p.1.1 i w p.2 ∧
          t.wage=roof (d:=d) (Q:=Q) B v (R.family.path.levels.clock.hatBeta i)*‖Annex.compress D p.2‖:=by
  obtain ⟨B,v,nonneg,priced⟩:=WilsonOlderFreshGraphRoster.salary R L a depth simple purchase o w Q
  refine ⟨B,v,nonneg,?_⟩
  filter_upwards [priced,WilsonElectedPrimaryCurvature.heard R L a depth simple purchase o w,
    WilsonOlderFreshGraphPublication.original R L a depth simple purchase o w] with i salary heard net
  intro p
  let X:=terms R L a depth p.1.1 i w p.2
  let h:=roof (d:=d) (Q:=Q) B v (R.family.path.levels.clock.hatBeta i)
  let rent:=h*‖Annex.compress D p.2‖
  have h0:0≤h:=by unfold h roof; exact Finset.sum_nonneg fun _ _=>abs_nonneg _
  have earned (e:ℕ) (he:e≤Q): (diagram X e).Good (WilsonOlderFreshGraphRoster.narrow R d Q i)
      rent (e+d+2):=by
    have good:=(salary p.1.1 p.1.2 p.2 e he).1
    apply good.debt le_rfl _ (by omega)
    let j:Fin (Q+1):=⟨e,Nat.lt_succ_of_le he⟩
    rw [←Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    change charge B j v _ ≤ h
    exact (le_abs_self _).trans (Finset.single_le_sum (f:=fun z:Fin (Q+1)=>|charge B z v _|)
      (fun _ _=>abs_nonneg _) (Finset.mem_univ j))
  have ward (n:Side)(s:Board Unit n ℝ)(j:ℕ)(_hj:j≤Q):
      Haiku.Vernal G n (fun e A=>(diagram X e).table n (mingle A s)) j:=by
    have eq:(fun e A=>(diagram X e).table n (mingle A s))=WilsonOlderFreshGraphAward.probe R L a depth i w p n s:=
      funext fun e=>funext fun A=>net p.1.1 p.1.2 p.2 e n A s
    rw [eq];exact heard n s j p
  exact ⟨⟨X,rent,mul_nonneg h0 (norm_nonneg _),earned,
    fun j hj=>(salary p.1.1 p.1.2 p.2 j hj).2,ward⟩,rfl,rfl⟩
end YM.Integration.WilsonOlderFreshGraphSubmit
end
