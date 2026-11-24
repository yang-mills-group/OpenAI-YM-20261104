import YM.Integration.WilsonAddressedRestartedColumn
import YM.Integration.WilsonOriginalNullPlacedBlend

/-! The complete signed Wilson coefficient after matching the restart.
The active source is translated on the physical reporting grid. Both the
returned primary and the compulsory part travel with its signed density. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedRestartedFiled
open Function Filter Lattice RG Wilson Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Work.G08
open WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonAddressedRestartedColumn WilsonOriginalMicroscopicGuardedReporters
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (d N p f : ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "P₀" => (C₀).path.rep N p f

structure Filed (o : Site ((C₀).side f p)) (h : Config G ((C₀).side f p) → ℂ)
    (B : ℝ) (z : store C₀ d p f) : Prop where
  form : z.Format o (C₀).params P₀
  paid : z.remBound o P₀ (safety C₀ f) ((1+4*stock C₀ f)*B)
  primary : (F₀).coeffSize z.x ≤ (invoice (C:=C₀) d f p+4)*B
  measured : (F₀).coeffSize (projection F₀ (C₀).params (P₀).p.threshold o z) ≤ 2*B
  field : z.density o ((C₀).localSection d) P₀ = h ∘ Lattice.translate o

theorem moved (home : Opened C₀ d f p) (live : f ≤ N)
    (o : Site ((C₀).side f p)) (B : ℝ) (q : store C₀ d p f) (y : (C₀).label d)
    (paid : reads (C:=C₀) d N p f q B) (null : page (C:=C₀) d p f q=0)
    (scalar : mCost C₀ d N p f y ≤ 2*B) :
    ∃ z : store C₀ d p f, Filed R d N p f o
      (value (C:=C₀) d N p f q+calValues (C:=C₀) d N p f y) B z := by
  let r := ((C₀).factory d N p).entries f y
  let t := beside q r
  let E := mCost C₀ d N p f y
  let S := stock C₀ f
  let shift := Tour.placard C₀ R.makes N p live o
  have Spos : 0 ≤ S := zero_le_one.trans ((C₀).path.levels.params f).columns_ge
  have course := R.makes.wilson.represents N p f live
  have vac : (P₀).p=(C₀).path.levels.budget f := course.vac
  have root : (F₀).coeffSize q.x ≤ invoice (C:=C₀) d f p*B := by
    have c := measured_diff (C:=C₀) d N p f R.makes home.post live paid
    simpa only [null,zero_sub,Frame.coeffSize,Pi.neg_apply,norm_neg] using c
  have funded : reads (C:=C₀) d N p f r (2*S*E) := graph_cost d N p f R.makes home live y
  have rcap : (F₀).coeffSize r.x ≤ 2*E := (size_gap d N p f R.makes home live y).2
  obtain ⟨tf,tr⟩ := presentation paid.1 paid.2 funded.1 funded.2
  have paid' : t.remBound 0 P₀ (safety C₀ f) ((1+4*S)*B) := by
    apply rem_mono tr
    dsimp only [E,S] at *
    nlinarith only [mul_le_mul_of_nonneg_left scalar Spos]
  have cap : (F₀).coeffSize t.x ≤ (invoice (C:=C₀) d f p+4)*B := by
    rw [show t.x=q.x+r.x from reckon q r]
    have h := size_triangle F₀ (q.x+r.x) q.x
    rw [add_sub_cancel_left] at h
    dsimp only [E] at rcap
    linarith only [root,rcap,scalar,h]
  have sale := dimensions d N p f R.makes home.post live
  have eq := GermGraph.add_projection d q r paid.1 funded.1 sale.1 sale.2
    ⟨_,_,paid.2⟩ ⟨_,_,funded.2⟩
  have germ : page (C:=C₀) d p f t = page (C:=C₀) d p f r := by
    rw [vac] at eq
    exact eq.trans ((congrArg (·+page (C:=C₀) d p f r) null).trans (zero_add _))
  refine ⟨Drift.stamp o shift t,?_,?_,cap,?_,?_⟩
  · simpa only [zero_add] using Drift.stamp_format o shift t tf
  · simpa only [zero_add] using Drift.stamp_rem o shift t paid'
  · have same := WilsonOriginalNullRelocation.page F₀ (C₀).params (P₀).p.threshold 0 o shift t
    rw [zero_add,vac] at same
    rw [vac,same]
    change (F₀).coeffSize (page (C:=C₀) d p f t) ≤ 2*B
    rw [germ]
    exact scalar
  · have eqt := WilsonOriginalNullRelocation.registered C₀ R.makes d N p f live 0 o t
    rw [zero_add] at eqt
    exact eqt.trans (congrArg (· ∘ Lattice.translate o)
      (plus course.good paid.2 funded.2 ((C₀).localSection d)))

theorem original (simple : G.Simple) : ∀ᶠ j : ℕ in atTop,
    ∀ N p K (before : j ≤ K) (high : K ≤ N) (target : ℕ) (η : ℝ)
      (A : (C₀).label d ≃ₗ[ℂ] (C₀).label d) (x : (C₀).label d),
    let e := page (C:=C₀) d p j (((C₀).factory d N p).entries j x)
    let w := A.symm e
    let F := numerator R d N p K 0 w
    let B := (1+4*stock C₀ K)*(F₀).coeffSize w
    Arrived R d j K N p target before high η A e →
    ∀ f, j ≤ f → f ≤ K → ∀ o : Site ((C₀).side f p),
    ∃ z : store C₀ d p f, Filed R d N p f o
      (track R d N p K F f-calValues (C:=C₀) d N p f x) (hike C₀ K f rate*B) z := by
  obtain ⟨j₀,opened⟩ := eventually_atTop.mp (open_late C₀ simple d)
  filter_upwards [WilsonAddressedRestartedColumn.original R d simple,eventually_ge_atTop j₀]
    with j income large
  intro N p K before high target η A x e w F B arrival f jf fK o
  obtain ⟨q,y,bought,zero,scalar,field⟩ := income N p K before high target η A x arrival f jf fK
  rw [field]
  exact moved R d N p f (opened f (large.trans jf) p) (fK.trans high) o _ q y bought zero
    (by simpa only [mul_assoc] using scalar)

end YM.Integration.WilsonAddressedRestartedFiled
end
