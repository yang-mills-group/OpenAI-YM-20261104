import YM.LocalTaylorR2.Exponent.Poster
import YM.LocalTaylorR2.Mesh.Ripple

/-!
 # Upfront post-normalization-moment adapter (true Bank), permits price on ALL q≤p phases.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
variable {a b t :ℝ} {χ:Chi}
variable {U : Molecule S}{Z:Support c}
def Rates (_H:Cash W s μ L Q o C T R)(Y:Support c)(j p m:ℕ)(b v d:ℝ)(χ:Chi)(K:Port.Test T)(e t:ℝ) :=
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F:Forest S.ratio) (X:Coat T F)
      (V:E→ Config G c) (u:E→ Directions G f) (z:E→ Air f G) (x:E) (w:Air f G), X.x=s → X.width=o.K → X.manifest → X.χ=χ → Mode V x j v →
      Clutch X w o.a R.beta d x j V u z → Brush j (e* glacial X Y w R.beta (o.ξ/2) b p ^ m) t (fun y=>K F (vary X (V y)) (z y)) x
namespace Rates
variable (H : Cash W s μ L Q o C T R)(M:Bank H j k n x l p b)(N:StoresR2 H j v d A D k x n χ)
variable {K : Port.Test T}
lemma era (Y:Support c) (b:ℝ)(p:ℕ)(h:Sees H j v d χ K a t): Rates H Y j p 0 b v d χ K a t:= fun E _ _ _ F X V u z x w hv hM hx hh hA ht=>by rw [pow_zero,mul_one]; exact h E F X V u z x w hv hM hx hh hA ht
lemma earns (h:Rates H Z j p k b v d χ K a t)(ht:1≤b)(hy:k ≤ m) : Rates H Z j p m b v d χ K a t:= by
   intro E _ _ _ F X V u z x w hv hM hx hh hA he
   have hk:= h E F X V u z x w hv hM hx hh hA he; have hz:1≤glacial X Z w R.beta (o.ξ/2) b p:= frozenWide _ _ _ ht
   have hN :0≤a:= nonneg_of_mul_nonneg_left hk.nonneg (by positivity)
   exact hk.climb (by gcongr) le_rfl
lemma times {K':Port.Test T}{a' t':ℝ}(h:Rates H Z j p k b v d χ K a t)(h':Rates H Z j p m b v d χ K' a' t'): Rates H Z j p (k+m) b v d χ (fun F X w=>K F X w*K' F X w) (a*a') (t+t'):= fun E _ _ _ F X V u z x w hv hM hx hh hA he => ((h E F X V u z x w hv hM hx hh hA he).paints (h' E F X V u z x w hv hM hx hh hA he)).climb (le_of_eq (by ring)) le_rfl
include M N
lemma elans (h:Rates H (H.unionP U) j p l b v d χ K a (t*(1+H.shapeW U)))(hb:1≤b)(hh:0≤a)(hy:0≤t):
    IntegrandCost H (H.unionP U) K j A v (a*(x*(1+D+t)^j)*(1+H.shapeW U)^(n+j)) χ:=by
 refine ⟨?_⟩; intro F X hx hk hX hY H' E _ _ _ V y hV hv m I
 let V':=1+H.shapeW U; have hF:= N.fuel; have hz:1≤V':= le_add_of_nonneg_right (H.positive_volume _)
 let P:=a*(1+D+t)^j*V'^j; have hP:0≤P:=by unfold P; positivity
 let f₀ z:= glacial X (H.unionP U) z R.beta (o.ξ/2) b p; let u(z: Air f G):= f₀ z^l * facescale I z^(k*j) -- name clash f
 obtain ⟨hu,hf⟩:= M.grant F X hx hk hX U
 let w(z: F.Slice G × Air _ G):= P*u z.2; have hw : Integrable w m:= (hu.const_mul P).comp_snd _
 refine ⟨w,hw,?_,?_⟩
 · rw [integral_prod _ hw]; unfold w; simp_rw [integral_const_mul]; rw [integral_const]; simp only [probReal_univ,one_smul]
   exact (mul_le_mul_of_nonneg_left hf hP).trans_eq (by unfold P V'; ring)
 intro ⟨i,z⟩; obtain ⟨hw,hq⟩:= N.flight F (X.wrapY i) hx hY hk hX z E V y hv hV; have hp:= h E F (X.wrapY i) V _ _ y z hx hk hX hY hV hw
 apply ((hq U|>.paints hp).trim).climb _ le_rfl; rw [one_mul]; let K':=facescale I z
 have he:1≤K':= (Flux.expenses I z).1; have h : 1≤ f₀ z:= frozenWide _ _ _ hb
 have H0 : 0 ≤ D*K'^k:=by positivity
 have hy':(1+(D*K'^k+t*V'))≤(1+D+t)*V'*K'^k:=by
    have hv:= one_le_mul_of_one_le_of_one_le hz (one_le_pow₀ (n:=k) he)
    have hB:K'^k≤ V'*K'^k:= le_mul_of_one_le_left (by positivity) hz
    have hL:V' ≤ V'*K'^k:= le_mul_of_one_le_right (zero_le_one.trans hz) (one_le_pow₀ he)
    nlinarith only [hv,mul_le_mul_of_nonneg_left hB hF,mul_le_mul_of_nonneg_left hL hy]
 change a*f₀ z^l*(1+(D*K'^k+t*V'))^j≤P*u z
 exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤1+(D*K'^k+t*V') by positivity) hy' j) (by positivity : 0≤a*f₀ z^l)).trans_eq (by unfold u K' P; rw [pow_mul,mul_pow, mul_pow]; ring)
end Rates
end YM.LocalTaylorR2.Exponent
