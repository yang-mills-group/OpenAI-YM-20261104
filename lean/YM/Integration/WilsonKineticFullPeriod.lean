import YM.Integration.WilsonKineticResponseLimit
import YM.Integration.WilsonConditionalTaylorKineticHead

/-! The physical kinetic normalizer tends to minus two on all finite
torus sides; this supplies even the periods inserted in a formal
one-step recurrence before the physical period subsequence is taken. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonKineticFullPeriod
open Function Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open Mesa Gorge City Cork Rift Pose Glide Bank Dawn Rial Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Heath
open WilsonMovingPolynomialPull
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) (a : G.ColorIndex)

def bill (N j : ℕ) (n : Side) :=
  caliper n (Lis.sun G a) (Wave.ink n (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j))

theorem limit (simple : G.Simple) (roofs : ∀i,Lodge ((R.family.path.levels.clock.op i 0).patch))
    (N j : ℕ) (hi : j≤N) : Tendsto (bill R a N j) atTop (𝓝 (-2)) := by
  let V := R.family.path.levels
  let K := RunFormalChain.fromRun R
  let W := Dove.model V roofs (Hay.Wday V) R.metals.O a N j
  have story := Dove.genu V roofs (Hay.Wday V) R.metals.O a K.receipt simple hi
  obtain ⟨η,C,pos,fee⟩ := story.fare 0 2
  have response : Kith η (W 0 2) (fun n=>rancho (stone W n) 0 2) := by
    have slots : (fun n : Side=>rancho (stone W n) 0 2) =
      fun n=>cum (0:Fin 2) n (W 0 2) := funext fun n=>story.toVivid.flower 0 2 (0:Fin 2) n
    rw [slots]
    exact Bank.stable pos.le (story.civil 0 2) fee (0:Fin 2)
  have result := WilsonKineticResponseLimit.raw a (stone W) 0 (W 0 2)
    (Eventually.of_forall story.civic) pos response
  have fixed : Cork.value a (W 0 2)=1 := by
    rw [show W 0 2=_ from story.ink]
    exact Cork.pink_weigh V.clock.kernel.penalty V.clock.kernel.penalty_pos (V.clock.adm j) (location V N j) a
  rw [fixed,mul_one] at result
  apply result.neg.congr
  intro n
  change -caliper n (Lis.sun G a) (MvPolynomial.rename (WilsonMovingGaussianCoordinates.link G n).symm
    (coeff 0 (stone W n))) = _
  have income : coeff 0 (stone W n)=coeff 0 (Hay.novel (V.params j).clip (R.alloy.B.kin.path N j) n) :=
    WilsonConditionalTaylorKineticHead.measured R simple roofs a N j hi n 0 (by decide)
  have received := WilsonConditionalTaylorKineticHead.native (V.params j).clip (R.alloy.B.kin.path N j)
    (K.planned.cap N j hi) n
  have seam := (congrArg (MvPolynomial.rename (WilsonMovingGaussianCoordinates.link G n).symm) income).trans received
  rw [seam,map_neg,neg_neg]
  rfl

end YM.Integration.WilsonKineticFullPeriod
end
