import YM.LocalTaylorR2.Sails.Bract
import YM.LocalTaylorR2.Strange.Bayes
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (X:Coat T F) (H:Cash W s μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G} (χ:Chi) (p:H.ThinP)
local notation "Θ"=>p.val
local notation "Ω"=> (M.signs S)
open Exponent
open Reel (Strand)
def contourX (H:Cash W s μ L Q o C T R)(ψ: Reel.Scroll G f)(Ξ:Strange.Engine G)(l:ℕ)(t:ℝ): Exponent.Bevy T := replay (Reel.sprout H ψ) (Ξ.plug H ψ l) t
variable {ψ: Reel.Scroll G f}{X':Cash W s μ L Q o C T (Reel.bend R ψ)}{j k n l:ℕ}{θ e v₀ D K Ct A d:ℝ}
variable (Z:Utopia H j v₀ d r Ct χ) {I:Utopia X' j v₀ d r Ct χ}(Ξ:Strange.Engine G) (hR: Wealth Ξ.toObservatory X' D n A k m I l θ) (hh:∀ i,I.goalsL i ≤ Z.goalsL i)
open Reel.Strand (dial)
local notation:max "Yz" i:max => contourX H ψ Ξ l (dial i*θ^l)
include hR
lemma flightX (i:LogIndex c f) : Reel.Filled (Pop' H (H.supportP (identityLog i))) 1 dial (fun j=> (Yz j) i):=by
   unfold contourX; rw [Ξ.fits H ψ X' l]; have hz (T:Port.Test T) (hp:Port.Burst X' (X'.supportP (identityLog i)) T): Port.Burst H (H.supportP (identityLog i)) T:= ⟨hp.links, hp.borel,hp.rotate,hp.clutch⟩
   exact population (hz _ (Port.Burst.fat (logTest X' i))) (hz _ (hR.stuff _)) _ _
include hh
lemma ladleX (i:Strand): Lodestar H m D Z (Yz i):=by
 refine ⟨fun s=>(flightX H χ Ξ hR s).land i,?_⟩
 intro t Y hy E _ _ _ F X V u z x w h hX hY hK ht hu; unfold contourX; rw [Ξ.fits H ψ X' l]; exact ((hR.invests i).income t Y hy E F X V u z x w h hX hY hK ht hu).climb (mul_le_mul_of_nonneg_right (hh _) (pow_nonneg (zero_le_one.trans (frozenWide X Y w hR.positively)) _)) le_rfl
omit hR hh
lemma t'zero (t: Reel.Scroll G f)(l:ℕ)(a:ℝ): contourX H t Ξ l (0*a^l)= Reel.sprout H t:= by rw [zero_mul]; unfold contourX replay; rw [zero_smul,add_zero]
lemma t'one (t: Reel.Scroll G f)(l:ℕ)(a:ℝ)(h:0<a): contourX H t Ξ l ((a^l)⁻¹*a^l)= Ξ.plug H t l:= by rw [inv_mul_cancel₀ (pow_ne_zero _ h.ne')]; unfold contourX replay; rw [one_smul]; abel
end YM.LocalTaylorR2.Orbit
