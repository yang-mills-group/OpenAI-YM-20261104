import YM.FormalBulk08.Hay.Motor
import YM.MSbar.Wave.Merry
import YM.Integration.WilsonMovingBareVacuum
import YM.Integration.WilsonMovingVacuumRows

/-! The full classical quadratic at any physical height, on every finite torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorKineticHead
open Function PowerSeries Lattice Exterior RG Wilson Precision Tree Stationary Push.Uniform Bloch
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent Next.Free
open FormalBulk08 Jets Flat Reef Mesa Dove Lotus Shore Gorge City Cork Rift Lava Kemp Pose Glide
open Bank Dawn Wine Rial Roof Planned.PrimaryIntegral295
open scoped Classical BigOperators ContDiff
variable {G : Gauge}

theorem native (p : Clip) (Y : PathData G) {σ A Λ : ℝ} (budget : Y.Bounds p σ A Λ) (n : Side) :
    MvPolynomial.rename (WilsonMovingGaussianCoordinates.link G n).symm (coeff 0 (Hay.novel p Y n))=
      -MSbar.Wave.ink n p Y := by
  let P := Stationary.intended p Y (m:=n)
  let s := (WilsonMovingGaussianCoordinates.link G n).symm
  have whole : MSbar.Rolling.main n p Y ∘ (tint G (Body 1 n)) =
      fun z : Jets.Rays (Primary n G)=>P (z ∘ s) := rfl
  have loopZero : (turnSeries Y.loop (m:=n)) 0=0 :=
    (rays_at_zero (f:=turnSeries Y.loop (m:=n)) (turns_analytic Y.loop budget.width budget.two)).mp
      ((turns_low Y.loop budget.width budget.two).weaker (by decide))
  have mapped := WilsonMovingTaylorConvention.placed s P (strain (m:=n) p Y budget).analytic.contDiffAt
  rw [Hay.novel,map_sub,map_neg,after_one,paste_first,loopZero,map_zero,sub_zero,map_neg,
    MSbar.Wave.ink,WilsonMovingVacuumRows.homogeneous,WilsonMovingTaylorConvention.coefficient,whole,
    ← mapped,PowerSeries.coeff_map]
  rfl

variable (R : Run G) (simple : G.Simple)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (u : hue G) (N j : ℕ) (height : j≤N)

include simple height in
theorem measured (n : Side) :
    Series.Through 2 (stone (Dove.model R.family.path.levels wood (Hay.Wday _) R.metals.O u N j) n)
      (Hay.novel (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) n) := by
  let K := RunFormalChain.fromRun R
  let t := R.family.path.levels.params j
  obtain ⟨δ,C,D,hδ,hC,hD,book⟩:=Hay.manuscript G simple t.width t.paths t.clip.direct
    t.width_pos t.paths_pos.le t.clip.quadratic_pos.le 2
  obtain ⟨Y,hY,_⟩:=book _ le_rfl (K.kin.path N j) _ (K.planned.cap N j height)
  exact (hY.buys n) ▸ Hay.diary (Hay.mature wood K.receipt simple K.planned N u j height Y hY) n

include simple height wood u in
theorem physical (n : Side) :
    MSbar.Wave.ink n (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) =
      -MvPolynomial.rename (WilsonMovingGaussianCoordinates.link G n).symm
        (crunch (kernelP G R.family.path.levels.clock.kernel.penalty (location R.family.path.levels N j) n)) := by
  let K := RunFormalChain.fromRun R
  let V := R.family.path.levels
  let roofs : ∀ i,Lodge (V.clock.op i 0).patch := wood
  let axis : hue G := u
  let W := Dove.model V roofs (Hay.Wday V) R.metals.O axis N j
  have trueCap := native (V.params j).clip (K.kin.path N j) (K.planned.cap N j height) n
  have matchCap : coeff 0 (stone W n)=coeff 0 (Hay.novel (V.params j).clip (K.kin.path N j) n) :=
    measured R simple roofs axis N j height n 0 (by decide)
  have story := Dove.genu V roofs (Hay.Wday V) R.metals.O axis K.receipt simple height
  obtain ⟨v,x,hv,hx,rows,_⟩:=colors G V.clock.kernel.penalty V.clock.kernel.penalty_pos (V.clock.adm j)
  have independent : coeff 0 (stone W n)=crunch (kernelP G V.clock.kernel.penalty (location V N j) n) :=
    stoned_main hv.le hx.le (rows _).1 story.toVivid story.ink n
  rw [← independent,matchCap,trueCap,neg_neg]
  rfl

end YM.Integration.WilsonConditionalTaylorKineticHead

