import YM.LocalLTE.Fan.Germ
/-! From stamina (true Stained) to explicit ancestral leaf approximation. Keep same area invariantly. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Field
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel Bakers PhysicalNext.Repeat Greenbelt Blaze.Stained
variable {v z r W w s t y η γ B a μ b C C' q X : ℝ} {j n k m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}{χ:Chi}
variable (D: Finset (Veil c f)) (H: Cash W t μ L Q o a T R)
variable (K: Captain H j C v z r W -- edit
   C' w B q m χ)
include D
lemma rosterD : roster (Fan.arm (S:=S) D)= (⟨∅,∅,∅⟩:Stores S):=by
    unfold roster; rw [show (Fan.arm (S:=S) D).toLeft=∅ from ?_, biUnion_empty]; rfl
    have h : ∀ i, i∉ (arm (S:=S) D).toLeft := by intro i hi; obtain ⟨j,_,he⟩:=mem_image.mp (show Sum.inl i∈ Fan.arm (S:=S) D from mem_toLeft.mp hi); cases he
    exact Finset.eq_empty_of_forall_notMem h
-- Representative Y variable prism (k choices); analytic plan uses Y at identity.
-- ball cluster pieces. representable.
section
variable (χ)
def pin:=(podium S G (H.unionP (Fan.arm D)) (radiusB t))
def perLeaf (p: LevelsΛ D N)(x:Disk G c):= likely fun r:Reserve S=> likely fun k: S.Choices=>
     Bakers.curlP ((Greenbelt.prism T t χ o.K 1 (Greenbelt.allot r)).taggedL k) R D Q.table (postponement L t o) (Field.pin D H) x p
end
-- true Leaflet with X origin proof. captain phantom D. 
variable {Y A d : ℝ} (C₁ : Captain H j C v z r Y A w B q m χ)
variable (u:H.ThinP) (hu:u.val=arm D) (hA:Ac.Spark H.supportP u.val) (hP:troupe T R Q.halo (radiusB t) u.val)
include C₁ hu hA hP
lemma thrones (p:Disk G c)(U:Config G c)(he: U=increment 1 p.2)(hf:flags (Pressure.temp t) U=∅):
   leaflet H χ U u=likely fun i:Greenbelt.Reserve S=> likely fun k : S.Choices=> bars (Field.pin D H) (timeΛ ((prism T t χ o.K (1:Config G c) (Greenbelt.allot i)).taggedL k) p) (Fan.arm D) R Q.table W o.a Q.halo:=by
  apply congr_arg likely; funext r; let Y := Greenbelt.prism T t χ o.K U (Greenbelt.allot r)
  have hΘ:= C₁.oboe
  have hη: Healthy (Pressure.temp t) (H.unionP u.val) Y.V:= by change Disjoint _ _; change Disjoint _ (flags _ U); rw [hf]; simp
  have hx:= (rainbow u.val hΘ (show Y.x=t from rfl) (show Y.width=_ from rfl) (show Y.χ=χ from rfl) (show (roster u.val).flags = ∅ from by rw [hu, rosterD]) hη (x:=(0:ℝ)) (show Mode (fun _:ℝ=> Y.V) _ j z from ⟨C₁.position.le, fun i=> a_oneB G _ C₁.position.le⟩) rfl).self_of_nhds
  change fringe Y _ _ _ _ _ _= _; rw [show fringe Y W o.a _ _ _ _= _ from hx]; unfold Shield.shelter
  rw [if_pos ⟨hA,hP⟩]
  apply congr_arg likely; funext k
  unfold Field.pin; rw [hu,rosterD]; unfold Y; rw [he]; rfl
end YM.LocalLTE.Fan.Field
