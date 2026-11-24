import YM.Integration.WilsonGaussianDeterminantWindow

/-! The signed derivative of the principal-window inverse error at a retained root is paid at every order by the actual conditional field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantMarked

open LocalTaylorR2 LocalTaylorR2.Pavilion Analysis
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Mesh Port Work.G05 Animals Itinerary Reserves Census

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {F : Forest S.ratio} {P : Teller G}

open PhysicalAffineScalarLogarithm
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
  {F : Forest S.ratio} {R : Rep G f} {W s μ C : ℝ} {P : Teller G}
  {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}

open WilsonGaussianDeterminantFull WilsonGaussianDeterminantVertex
open RGLocalTaylor LocalLTE.Fan
open WilsonGaussianDeterminantRoster (model)

theorem available (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)
    (L : Side) (D : Patch) (hD : D.Branches P.bind G) (χ : Chi) (j : ℕ)
    (v d : ℝ → ℝ) (hv : Rate G L (-(1/2)) v) (t : ℝ) :
    ∃ fee : ℝ → ℝ, Rate G L t fee ∧ ∀ᶠ s : ℝ in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f) (μ C : ℝ)
        (H : Cash W s μ L Q o C T R) (i : Bond f), S.patch = D →
        Sees H j (v s) (d s) χ (fun _ X _ => correction X i) |fee s| 1 := by
  obtain ⟨C,hC,stencils⟩ := bounded_stencils P D hD
  let γ := min (P.top.width/2) (retain o.eta o.gap o.ample)
  have hγ : 0 < γ := lt_min (half_pos P.top.width_pos) o.f.prices
  have narrow : γ < P.top.width :=
    (min_le_left ..).trans_lt (half_lt_self P.top.width_pos)
  let A := carat D P L γ C
  let b := A*A+1
  let m := tubularPrice G L
  let k (s : ℝ) := kernelGrowth (radiusB s) G (v s)
  let z (s : ℝ) := k s + k s
  let e (s : ℝ) := derivativePrice j (z s)
  let w (s : ℝ) := windowPrice G j (radiusB s) m o.eta o.gap o.ample γ b
  have hz : Rate G L 0 z := ((jet_growth G L hv).add (jet_growth G L hv)).weaken (by norm_num)
  have he : Rate G L 0 e := hz.add ((hz.mul_left (j : ℝ)).add (hz.add (hz.mul_left (j : ℝ))))
  have hw : Rate G L t w := WilsonGaussianDeterminantWindow.rate G L j m _ _ _ γ b t hγ
  refine ⟨fun s => w s * (1+e s)^j, ?_, Filter.Eventually.of_forall ?_⟩
  · simpa only [zero_mul,add_zero] using hw.mul (((Rate.const 1).add he).pow j)
  intro s c f S T R μ C₀ H i hS E _ _ _ F X U u z₂ x q hx hk hm hχ hU hq
  subst s
  have port := H.laws.data.localP F X rfl hk hm
  have room := port.sails.room
  have bound := stencils c f S T hS room.accepted
  have p := plates X D hS H.laws.data.funds.length_eq room hU C hC bound hγ.le narrow
  have fixed : Mode (fun _ : E => (1 : Config G c)) x j (v X.x) :=
    ⟨hU.pos,fun i => a_oneB G (1:G.El) hU.pos⟩
  have blank := plates X.blank D hS H.laws.data.funds.length_eq port.empty.room fixed C hC bound hγ.le narrow
  have h₀ := window_jets X.shutter (fun _ : E => X.blank.plate) port.sails.full
    port.empty.scale blank (min_le_right ..) i
  have hscale : Allow (vary X (U x)).plate (along S) m o.eta o.gap o.ample := by
    rw [hq.atV]; exact port.sails.scale
  have h₁ := window_jets X.shutter (fun y => (vary X (U y)).plate) port.sails.full
    hscale p (min_le_right ..) i
  have difference := (h₀.separating h₁).smul (1/2:ℝ)
  have h₂ : ‖(1/2:ℝ)‖*(w X.x+w X.x) ≤ w X.x := by rw [Real.norm_of_nonneg (by norm_num)]; linarith
  apply (((difference.climb h₂ le_rfl).trim).climb (le_abs_self _) le_rfl).shimmy
  filter_upwards with y
  change (windowDifference X.shutter X.blank.plate i - windowDifference X.shutter (vary X (U y)).plate i)/2 =
    (1/2:ℝ) * (windowDifference X.shutter X.blank.plate i - windowDifference X.shutter (vary X (U y)).plate i)
  exact (show ∀ a : ℝ, a/2=(1/2:ℝ)*a from fun _ => by ring) _

end YM.Integration.WilsonGaussianDeterminantMarked
end
