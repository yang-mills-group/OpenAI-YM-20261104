import YM.Integration.WilsonMovingMayerWindow
import YM.Integration.WilsonRootedMayerOriginal
import YM.RGLocalTaylor.Laminate.Winding

/-! The signed original occupied column on its true joint finite-dimensional marginal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedMayerColumn

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Lotus Daisy RGLocalTaylor RGLocalTaylor.Mayer
open RGLocalTaylor.Insert RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {r q Y W d C' A b s μ C v B : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {K θ e uJ vJ discount : ℝ}

/-- The joint marginal of the true original Gaussian is obtained before the Haar integral. -/
theorem paid (H : Cash W s μ L Q o C T R) (prior : Team R) (p : Molecule S)
    {M : ℕ} (u : Decors (p\prior.signs S) M) (grade : decorOrder u≤M)
    (N : Captain H j C' d v Y A b r B q n χ) (hG : Awning H N.conduit A b discount e uJ vJ k l)
    (hg : Q.goal L s ≤ K) (hT : Approved K θ j M) (start : Start (p\prior.signs S))
    (X : Coat T F) (inside : Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hx : X.x=s) (hw : X.width=o.K) (hχ : X.χ=χ) (hm : X.manifest) :
    let E:=WilsonRootedMayerHull.coordinates H p X
    (∫ z, Mayer.planned H p u (Laminate.partner prior H) X z ∂moment X) =
      ∫ y : F.Slice G, ∫ z : Body (↥E),Mayer.planned H p u (Laminate.partner prior H) X
        (y,Pond.spill E z) ∂Pond.arch E X.relating ∂F.order G := by
  intro E
  have hf (i : Head S) (hi : i∈p\(p\prior.signs S)) :
      Fits H (Laminate.partner prior H i) (H.supportP i) j := by
    have hs : i∈prior.signs S := by
      by_contra h
      exact (mem_sdiff.mp hi).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hi).1,h⟩)
    exact (Laminate.partnerFit (H:=H) (j:=j) hs).1
  have integrable:=Mayer.integrable_planned u sdiff_subset grade N hG hg hT (Laminate.partner prior H)
    hf start inside hx hw hχ hm
  refine (integral_prod _ integrable).trans (integral_congr_ae (ae_of_all _ fun y=>?_))
  have same:=Mayer.physical_plan u sdiff_subset grade N hG hg hT (Laminate.partner prior H)
    start inside hx hw hχ hm
  exact (congr_arg (fun reader : momentSpace X→ℝ =>∫z : Air f G,reader (y,z) ∂X.dice) same).symm.trans
    ((WilsonMovingMayerWindow.decorated H prior p u X hx hw hm y).trans
      (congr_arg (fun reader : momentSpace X→ℝ =>∫ z : Body (↥E),reader (y,Pond.spill E z) ∂Pond.arch E X.relating) same))

/-- Original occupied component after retaining its true grade, summing every original
forest and tag, and only then projecting the one original Haar-Gaussian integral. -/
theorem original (H : Cash W s μ L Q o C T R) (prior : Team R) (loc : H.ThinP)
    (N : Captain H j C' d v Y A b r B q n χ) (hG : Awning H N.conduit A b discount e uJ vJ k l)
    (hg : Q.goal L s ≤ K) (M : ℕ) (grade : Orders M) (hT : Approved K θ j M)
    (allowed : authorized H loc.val) (live : grade.val≤M) (cohort : Start loc.val)
    (before : prior.signs S⊆loc.val) (V : Config G c) (inside : Healthy (Pressure.temp s) (H.smallAt loc) V) :
    let rest:=loc.val\prior.signs S
    Laminate.column prior loc.val H (χ:=χ) M grade V =
      ∑ u∈univ.filter (fun u : Decors rest M=>decorOrder u=grade.val),
        likely fun a : Greenbelt.Reserve S=>likely fun tag : S.Choices=>
          let X:=((planted (prism T s χ o.K V (Greenbelt.allot a)) loc.val).taggedL tag)
          let E:=WilsonRootedMayerHull.coordinates H loc.val X
          ∫ y : (Greenbelt.allot a).Slice G, ∫ z : Body (↥E),Mayer.planned H loc.val u
            (Laminate.partner prior H) X (y,Pond.spill E z) ∂Pond.arch E X.relating
              ∂(Greenbelt.allot a).order G := by
  intro rest
  have received:=Laminate.prescriptive (Y':=prior) χ H loc N hG hg M grade.val grade hT
    allowed live rfl cohort before V inside
  refine received.trans (Finset.sum_congr rfl fun u hu=>congr_arg (@likely (Greenbelt.Reserve S) _) (funext fun a=>
    congr_arg (@likely S.Choices _) (funext fun tag=>?_)))
  let X:=((planted (prism T s χ o.K V (Greenbelt.allot a)) loc.val).taggedL tag)
  exact paid H prior loc.val u ((mem_filter.mp hu).2.le.trans live) N hG hg hT
    (fun i hi=>cohort i (sdiff_subset hi)) X inside rfl rfl rfl (planted_valid _ _)

end YM.Integration.WilsonRootedMayerColumn
