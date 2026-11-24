import YM.RG02.Flat.Syntax

/-!
# Actual localized interacting Laplace projection

Occasionally called the uncut moment algorithm. Here identify it with
the Wick coefficient algorithm by working *directly* in the actual
Haar integral, no interpolation of cut covariance rows. Unmasked kernels
specified on actual fine raw links; do not extrapolate value bounds.
Constant scalar costs all given before division. Valid neighborhoods
of flat at fixed stencil / period only. There is no uniform-in-step-setup
relative estimate here, nor agreement of a conditional denominator sampled
outside the analytically modeled/no-hole branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk
open Filter Function MeasureTheory Set Metric Lattice Wilson RG Precision Tree Supply Bid Marker Extra.Trajectories
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade PowerSeries
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{I : Type}[DecidableEq I][Fintype I]{B : Census I}{c f : Side}{S : StepData c f}

namespace Draw
variable (T : Forest S.ratio) {p : Clip}{R : PathData G}{A : Space G f→ℝ}{m : ℕ}{W : Space G f→ Poly B}
    {η : ChartRatio G} {w : ℝ}{ρ : Dir G c → AxisChart G T}(i : S.Choices)(hp : 0<w)(hr:PriceGap T p R w)(h : Critical T p R ρ)

/-- Single tag before its probability. Also not included: per-bond noise
scalar, history R.v, any quotient by the fine background. -/
def raw (i : S.Choices)(p : Clip)(R : PathData G)(x : Dir G c)(A : Space G f→ℝ)(m : ℕ)(W : Space G f→ Poly B)(t : ℝ) (U : Set (Config G f)) : Poly B :=
   Poly.inject fun s : B.Mode=> ∫ v in U, (ion i p R x A m W t v).part s ∂prior G f

def cut (i : S.Choices)(p : Clip)(R : PathData G)(x : Dir G c)(A : Space G f→ℝ)(m : ℕ)(W : Space G f→ Poly B)(t : ℝ) (U : Set (Config G f)) :=
    (((t:ℂ)^(dim T G))⁻¹) • raw i p R x A m W t U

variable {σ v Λ : ℝ}(hW : R.Bounds p σ v Λ)(ht : Ink m W)(hh : Ambient A)(hs : S.patch.Branches S.kernel G)(hη : LocalRatio η)(x : Dir G c)

include hW ht hh hs hη
lemma cents_general (i : S.Choices)(y : Dir G c){e t : ℝ}(hu : 0<e)(he : e<Chart.small G η)(hT : 0<t){U : Set (T.Slice G)}(HE : MeasurableSet U)(H : U⊆Volume.block T e (motion T y t))(s : B.Mode) :
     let μ:= Chart.tangent G T.Free
     let L := Volume.inside T e (motion T y t) U t
     let D := lit (flex T i η p R x y A) m (Pins.ink T y W) s t
     IntegrableOn D L μ →
      IntegrableOn (fun u => (ion i p R x A m W t u).part s) (Profiles.wick T ⁻¹' U) (prior G f) ∧
      (cut T i p R x A m W t (Profiles.wick T ⁻¹' U)).part s=↑(weight T η)*∫ u in L, D u ∂μ := by
    intro μ L D hp
    let g:= fun u => (ion i p R x A m W t u).part s
    let M:= motion T y t
    have hg : Measurable g := ion_meas i hW hs x hh ht t s
    have hf := ion_volume i hW hs x hh ht t s
    have hj := Volume.inside_meas T e t M HE
    let f (u : T.Slice G) := g (T.drape u)
    have hy : Measurable f := hg.comp T.continuous_drape.measurable
    have hz : (fun u : AxisChart G T=> Volume.penalty T η M f (t • u))=ᵐ[μ.restrict L] fun u=> Complex.ofReal (weight T η)*D u:= by
       filter_upwards [ae_restrict_mem hj] with u (hx:u∈L)
       exact ion_flex T i p R x y A m W s hη t hT he.le u hx.2
    constructor
    · exact (Volume.on_right T hf hg U HE).2 ((Volume.counts T hη M hu he hT HE H hy).2 (Integrable.congr (hp.const_mul _) hz.symm))
    rw [cut,Poly.part_smul]
    change (((t:ℂ)^_)⁻¹)*(∫ u in _ , g u ∂_)=_
    have hZ:= integral_congr_ae hz
    rw [integral_const_mul] at hZ
    rw [Volume.to_slice_on T hf hg U HE, ← hZ]
    have hU := Volume.procures T hη M hu he hT HE H hy
    rw [hU]; simp [dim, f,g, Complex.real_smul]

lemma cents (i : S.Choices){e t : ℝ}(hu : 0<e)(he : e<Chart.small G η)(hT : 0<t){U : Set (T.Slice G)}(HE : MeasurableSet U)(H : U⊆Volume.block T e (motion T x t))(s : B.Mode) :
     let μ:= Chart.tangent G T.Free
     let L := Volume.inside T e (motion T x t) U t
     let D := lit (track T i η p R x A) m (Pins.ink T x W) s t
     IntegrableOn D L μ →
      IntegrableOn (fun u => (ion i p R x A m W t u).part s) (Profiles.wick T ⁻¹' U) (prior G f) ∧
      (cut T i p R x A m W t (Profiles.wick T ⁻¹' U)).part s=↑(weight T η)*∫ u in L, D u ∂μ := by
    exact cents_general T hW ht hh hs hη x i x hu he hT HE H s

section
variable {ψ : PertExtension.GaussianScore.Law (AxisChart G T)}{a:ℝ}{d:AxisChart G T}(y : Dir G c)(hQ : Steer ψ (flex T i η p R x y A) a d)

def flexion (ψ : PertExtension.GaussianScore.Law (AxisChart G T))(η : ChartRatio G)(p : Clip)(R : PathData G)(x y : Dir G c)(A : Space G f→ℝ)(m : ℕ)(W : Space G f→Poly B)(d : AxisChart G T) :=
    Wick.made ψ fun k => Grade.exponential (Therm.board (flex T i η p R x y A) m (Pins.ink T y W) d k)

include hW ht hh hs hη hQ
private lemma earned (s : B.Mode) : ∃ e>0, ∀ r>0,r<Chart.small G η → r≤e→ ∀ U:ℝ→Set (T.Slice G), Volume.Suitable T r (motion T y) U →
       (∀ᶠ t in Tested.germ, IntegrableOn (fun u => (ion i p R x A m W t u).part s) (Profiles.wick T ⁻¹' U t) (prior G f)) ∧
       Near (fun t => (cut T i p R x A m W t (Profiles.wick T ⁻¹' U t)).part s) (C (Complex.ofReal (weight T η * leading ψ (Chart.tangent G T.Free) a))*onMode (flexion T i ψ η p R x y A m W d) s) := by
    let W' := Pins.ink T y W
    have hg : ∀ s : B.Mode, Measurable fun z=> (W' z).part s:= fun s => (ht.borel s).comp (Pins.visit_motion ..).measurable
    obtain ⟨e,he,H⟩ := Therm.casts (Chart.tangent G T.Free) hQ (flex_meas T i x y hs hW hh.borel hη) (Pins.jobs T y ht) hg s
    refine ⟨e,he,fun r hr' H₁ HB U hP => ?_⟩
    obtain ⟨hX,HX⟩ := H _ (hP.2.raise HB)
    let C t := Profiles.wick (G:=G) T ⁻¹' U t
    let g (t:ℝ):= (cut T i p R x A m W t (C t)).part s
    let L := fun t => Volume.inside T r (motion T y t) (U t) t
    let D := lit (flex T i η p R x y A) m W' s
    let wP : ℂ:= ↑(weight T η)
    have H : ∀ᶠ t in Tested.germ, IntegrableOn (fun u => (ion i p R x A m W t u).part s) (C t) (prior G f) ∧
        g t=wP * ∫ u in L t, D t u ∂Chart.tangent G T.Free := by
       filter_upwards [hX,hP.1,Tested.eventually_pos] with t ht' ⟨ha,hb⟩ hE
       exact cents_general T hW ht hh hs hη x i y hr' H₁ hE ha hb s ht'
    refine ⟨H.mono (fun _ he=>he.1),?_⟩
    have he := Near.scaled HX wP
    rw [← mul_assoc, ← map_mul, show wP*_=Complex.ofReal (weight T η * leading ψ (Chart.tangent G T.Free) a) from ?_] at he
    · exact Near.same he (H.mono fun i hi=> hi.2.symm)
    unfold wP; push_cast; rfl

/-- Suitable aperture theorem. No-order-limit as r→∞ implied.
Tag i still held (only strip likelihood on the minimizing branch). -/
theorem uncut_target : ∃ r>0,r<Chart.small G η ∧ ∀ e>0,e≤r→ ∀ U:ℝ→Set (T.Slice G), Volume.Suitable T e (motion T y) U →
      (∀ᶠ t in Tested.germ,∀ s : B.Mode, IntegrableOn (fun u => (ion i p R x A m W t u).part s) (Profiles.wick T ⁻¹' U t) (prior G f)) ∧
       Aims (fun t => cut T i p R x A m W t (Profiles.wick T ⁻¹' U t)) (Complex.ofReal (weight T η * leading ψ (Chart.tangent G T.Free) a) • flexion T i ψ η p R x y A m W d) := by
   choose e he hv using earned T i hW ht hh hs hη x y hQ
   letI : Nonempty B.Mode:= ⟨B.quiet⟩
   obtain ⟨z,hz,HL⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
   have Hz w := HL w (Finset.mem_univ w)
   let u:=min (e z) (Chart.small G η/2)
   have hU : 0<u:= lt_min (he ..) (half_pos (Chart.Ratio.small_pos hη))
   have hD : u<Chart.small G η := lt_of_le_of_lt (min_le_right ..) (half_lt_self (Chart.Ratio.small_pos hη))
   refine ⟨u,hU,hD,fun r hr he U hP=> ⟨?_,?_⟩⟩
   · apply eventually_all.mpr; intro s
     exact (hv s r hr (he.trans_lt hD) (le_trans (he.trans (min_le_left ..)) (Hz s)) U hP).1
   intro s
   convert (hv s r hr (he.trans_lt hD) (le_trans (he.trans (min_le_left ..)) (Hz s)) U hP).2 using 1
   ext1 n; rw [mode_coeff, coeff_smul, Poly.part_smul,PowerSeries.coeff_C_mul, mode_coeff]

end

-- go down in price radius even for varying apertures. Multiplying normalized conditional uses this AFTER restoring charts and scalar.
variable {Y : Bed}(hY : Comptroller T Y p R)
include hp hr h hη ht hh hs hW hY
/-- Suitable aperture theorem. No-order-limit as r→∞ implied.
Tag i still held (only strip likelihood on the minimizing branch). -/
theorem extracted : ∃ r>0,r<Chart.small G η ∧ ∀ e>0,e≤r→ ∀ U:ℝ→Set (T.Slice G), Volume.Suitable T e (motion T x) U →
      (∀ᶠ t in Tested.germ,∀ s : B.Mode, IntegrableOn (fun u => (ion i p R x A m W t u).part s) (Profiles.wick T ⁻¹' U t) (prior G f)) ∧
       Aims (fun t => cut T i p R x A m W t (Profiles.wick T ⁻¹' U t)) (Complex.ofReal (multiplier T i hp hr h η x) • formal T i hp hr h η x A m W) :=
   uncut_target T i hW ht hh hs hη x x (flight T i hp hr h hY x hW hη hh)

/-- A genuine constant collar in physical fields, still unmasked. -/
theorem target : ∃ V∈𝓝 (1:T.Slice G),MeasurableSet V ∧ ∀ U∈𝓝 (1:T.Slice G),MeasurableSet U→ U ⊆ V→
      (∀ᶠ t in Tested.germ,∀ s : B.Mode, IntegrableOn (fun u => (ion i p R x A m W t u).part s) (Profiles.wick T ⁻¹' U) (prior G f)) ∧
       Aims (fun t => cut T i p R x A m W t (Profiles.wick T ⁻¹' U)) (Complex.ofReal (multiplier T i hp hr h η x) • formal T i hp hr h η x A m W) := by
   obtain ⟨r,hu,hs',HH⟩:= extracted T i hp hr h hW ht hh hs hη x hY
   obtain ⟨V,hV,Hv,H⟩ := Volume.coverage T η (motion_tends T x) hη hu hs'.le
   exact ⟨V,hV,Hv,fun U hU hx he=> HH r hu le_rfl (fun _=>U) (H U hU hx he)⟩

end Draw
end YM.RG02.Fk
