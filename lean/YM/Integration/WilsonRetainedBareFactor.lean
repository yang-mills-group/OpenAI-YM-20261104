import YM.LocalLTE.Marked.Interior
import YM.LocalLTE.Marked.Roots
import YM.LocalLTE.Marked.Flint
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.CutGerm

/-! On a surviving low Wilson cluster the locally accepted signed team can
be read under the bare-store noise on the full compact exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRetainedBareFactor
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat
open PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Greenbelt Merge Merge.Palette
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals
open Control Window Coat Footprint Raw Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen
open Gate Tablet Strokes Quill Bid Matter Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open scoped Topology Classical BigOperators
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
    {R : Rep G f} {W t μ a : ℝ} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}
    (H : Cash W t μ L Q o a T R) (χ : Chi) {ι : Type} (M : ι → Leaf R)

def sampled (p : H.ThinP) (k : Tickets (sign M S)) (U : Config G c) : ℝ :=
  likely fun r : Greenbelt.Reserve S => likely fun b : S.Choices =>
    (team M k).qlocal4a_cinema ((prism T t χ o.K U (allot r)).taggedL b) p.val
      W o.a Q.table Q.halo (podium S G (H.unionP p.val) (radiusB t))

private lemma empty {p : H.ThinP} (h : p.val.toLeft=∅) : roster p.val=bareStores S := by
  simp [roster,h,Packets.store,bareStores]
  exact ⟨rfl,rfl,rfl⟩

/-- Locality of the original molecular activity removes rough exterior flags
before the Gaussian calculation. The coarse field itself is held fixed. -/
theorem factor (p : H.ThinP) (k : Tickets (sign M S)) (U : Config G c)
    (h : p.val.toLeft=∅)
    (allowed : Ac.Spark H.supportP p.val ∧ troupe T R Q.halo (radiusB t) p.val) :
    Palette.act M H χ U p.val k =
      RG.masked (Pressure.temp t) (H.unionP p.val) (sampled H χ M p k) U := by
  let Z r:=prism T t χ o.K U (Greenbelt.allot r)
  let A:=team M k
  have row (r : Greenbelt.Reserve S) :=
    Team.qlocal4a_pictured A (Z r) p.val H rfl rfl p.2.2
  by_cases health : Healthy (Pressure.temp t) (H.unionP p.val) U
  · rw [RG.masked_eq _ _ _ _ health]
    change likely (fun r=>A.bloom (Z r) W o.a Q.table Q.halo p.val)=_
    apply congrArg likely
    funext r
    rw [row r,RG.masked_eq _ _ _ _ (show Healthy (Pressure.temp t) (H.unionP p.val) (Z r).V from health)]
    unfold Team.qlocal4a_grove
    change (if Ac.Spark H.supportP p.val ∧ troupe T R Q.halo (radiusB t) p.val then _ else _) = _
    rw [if_pos allowed,empty H h]
    rfl
  rw [RG.masked_ne _ _ _ _ health]
  change likely (fun r=>A.bloom (Z r) W o.a Q.table Q.halo p.val)=0
  have zero (r : Greenbelt.Reserve S) : A.bloom (Z r) W o.a Q.table Q.halo p.val=0 :=
    (row r).trans (RG.masked_ne _ _ _ _ health)
  simp [likely,zero]

/-- A true nonvanishing low linked coefficient supplies the empty store and
the permission for every molecular factor. Its mask is still evaluated at
the arbitrary configuration at which that factor is heard. -/
theorem original (ℓ : ℕ) (z : H.fragrances) (D : Captain.Oscars M z)
    (low : ¬Height.tiredN H ℓ z) (U₀ : Config G c)
    (survives : Captain.wingTerm (H:=H) (χ:=χ) z M D U₀≠0)
    (i : Option (Fin z.1)) (U : Config G c) :
    Palette.act M H χ U (z.2 i).val (D i) =
      RG.masked (Pressure.temp t) (H.unionP (z.2 i).val) (sampled H χ M (z.2 i) (D i)) U ∧
    ∀F : Forest S.ratio, Assembly.Clear S t (roster (z.2 i).val) F := by
  have live (b : Option (Fin z.1)) : Captain.waltz H χ M (z.2 b) (D b) U₀≠0 :=
    fun dead=>survives (by unfold Captain.wingTerm
                           rw [Finset.prod_eq_zero (Finset.mem_univ b) dead,mul_zero,zero_div])
  have placed b:=Captain.silenced M (z.2 b) (D b) U₀ (live b)
  have ok b : Ac.Spark H.supportP (z.2 b).val ∧ troupe T R Q.halo (radiusB t) (z.2 b).val :=
    ⟨(placed b).1,(placed b).2.1⟩
  have opened:=((Height.aged (H:=H) ok low).1 i).unforced
  refine ⟨factor H χ M _ _ U opened (ok i),?_⟩
  rw [empty H opened]
  exact fun F=>Assembly.bare_is_Clear S t F

end YM.Integration.WilsonRetainedBareFactor
