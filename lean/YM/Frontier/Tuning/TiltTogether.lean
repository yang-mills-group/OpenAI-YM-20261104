import YM.Frontier.Tuning.DensityTilt
import YM.Frontier.Tuning.HeldBurst
/-! Aggregating old held-word angular estimates with a *single* tilted marginal grant.
Branches checked separately (pressure catalogue / packets / priced directions). Never
extends an inequality on manifest to a new sector by dropping a mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.TiltTogether
open Footage HeldBurst DensityTilt
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift TwoMotion AngularReceipt Flux Shield Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R A : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {H0 a C α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
variable {χ:Chi}
local notation "b₁" => betaF G s L
local notation "M₀" => radiusB s
set_option maxRecDepth 8192
set_option pp.proofs false
set_option quotPrecheck false
set_option maxHeartbeats 1200000

variable {H: Cash W s μ L Q o H0 T R}
variable (P' : Pocket H A j v q C α d γ χ)


-- Actual reference *R.beta*, Rotor mask chooses I whole footprint. Don't call with forced rows not yet assembled without tickets.
def skewIntegral (X : Coat T F) (A W : ℝ) (R:Rep G f) (V:E→ Config G c) (u:E→ Directions G f) (g:E→ Air f G) (y:E)
    (z:Air f G) (I : Finset (Bond f)) (Q:ConnectedActivityE6.Target G P) (a:ℝ) (p:Molecule S) (τ:ℂ) (e f':Payload G f) :=
  scTilt X τ R I A (V y) z * ∏ i∈p, oldword V u g y (X.input (Vine.worldZ X R.beta z)) X R Q.table a W (own p) Q.halo τ e f' i

lemma collects {χC : ℝ} (τ:ℂ)(p:Molecule S) (H':Cash W s μ L Q o H0 T R) (X:Coat T F) (hx:X.x=s) (ht:0<τ.re)(hθ : Voice.strainG G L s * Real.log (‖τ‖/τ.re) ≤ χC):
    let I:=edgesM S (H'.unionP p) M₀
    airMark G I τ * phases X τ p ≤ Real.exp (χC*H'.shapeW p) := by
   intro I
   rw [airMark,phases, GaussContour.markup,← Real.exp_add,Fintype.card_coe,← add_mul]
   let D:= (lensS I G).card/2 + ∑ i∈p.toLeft, ComplexVertex.massPower X i
   let b:= Voice.strainG G L s; have hB:= show X.B=M₀ from congr_arg _ hx
   have hh:D ≤ H'.shapeW p*b:= by unfold D b I; rw [chargedU,← hB,add_comm]; rw [← congr_arg (fun L=>Voice.strainG G L s) H'.laws.data.funds.length_eq]; exact Voice.gain_sum H' X p hx (show 0<X.B from hB ▸ (H'.laws.data.room.sight.1.trans' (show 1≤100 by norm_num))) -- sight >=100
   apply Real.exp_monotone
   exact ((mul_le_mul_of_nonneg_right hh (Real.log_nonneg ((one_le_div ht).mpr ((le_abs_self _).trans (Complex.abs_re_le_norm _))))).trans (le_of_eq (by ring:_=(b * Real.log (‖τ‖/τ.re)) * H'.shapeW p))) |>.trans (mul_le_mul_of_nonneg_right hθ (H'.positive_volume _))
def coefficient (_P':Pocket H A j v q C α d γ χ)(B D:ℝ)(τ:ℂ) := (lumpSum s α d γ j L τ + |D|+(1+j.factorial*γ)*(1+4* |B|))
def envelope (P':Pocket H A j v q C α d γ χ) (B D:ℝ)(κ k:ℕ)(τ:ℂ)(p:Molecule S)(X:Coat T F)(I:Finset (Bond f))(z:Air f G):=
    (X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun _=> Real.exp (Q.ε*H.shapeW p) * ∏ i∈p,tag P' 1 i) z * (1+coefficient P' B D τ)^j * (1+H.shapeW p)^j * facescale I z^((κ+k)*j)
lemma simultaneous (τ:ℂ) (e f':Payload G f)(h: fans R A (PhysicalNext.Repeat.Height.grow G L s) e f') (hr:R.beta=τ.re)(hn:‖τ/R.beta‖ ≤ 3)(hθ : Voice.strainG G L s * Real.log (‖τ‖/τ.re) ≤ Q.ε) (X:Coat T F)(p:Molecule S)(hp:troupe T R Q.halo M₀ p)(hX:X.x=s)(hk:X.width=o.K)(hχ:X.χ=χ)(hM:X.manifest)(hQ:Healthy (Pressure.temp s) (H.unionP p) X.V) (α':ℝ)
  (V:E→ Config G c)(U:E→ Directions G f)(n:Air f G)(y:E→ Air f G) (t:E) (hf:Mode V t j v)(hs:Clutch X n o.a R.beta q t j V U y)(B D:ℝ)(κ i:ℕ)(hγ: ∀ b, Brush j (γ * ‖Complex.exp b‖) 1 Complex.exp b):
  let I:= edgesM S (H.unionP p) M₀
  Brush j 1 (|D| *facescale I n^κ) (fun t=> scalp I X (V t) R.beta α' n) t →
  Brush j (|B| * facescale I n^i) 1 (fun v:E=> draftI X I R.beta α' (V v) n) t →
  Brush j (envelope P' B D i κ τ p X I n) 1 (fun b=>skewIntegral X α' W R V U y b n I Q o.a p τ e f') t :=by
   intro I hI hJ
   have hβ : 0<τ.re := hr ▸ H.laws.intake.positive
   let K':=X.catastrophe (o.ξ/2) R.beta (blaze p)
   let a0:=lumpSum s α d γ j L τ; let a1:= |D|; let a2:= (1+j.factorial*γ)*(1+4* |B|)
   let z:=facescale I n; let d':=H.shapeW p; let D':=1+d'; have hd:=H.positive_volume p
   let m:=(a0+a1+a2)*D'*z^(i+κ); have hD:1≤D':=le_add_of_nonneg_right hd
   have ha:a0≥0:=by have hh:=P'.strong; have hx:=P'.wide; unfold a0 lumpSum; positivity -- positivity syntax
   have ha':a2≥0:=mul_nonneg (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans P'.strong))) (add_nonneg zero_le_one (mul_nonneg (by norm_num) (abs_nonneg _)))
   have hz:1≤z:=(expenses I n).1
   let c0:=fun i=>tag P' 1 i
   have hK:= complete (k:=own p) P' _ _ h hr hn p hp hχ hX hM hk hQ V U _ y t hf hs
   have hc:= (air_phase τ R X V n t I α' (zero_le_one.trans P'.strong) hγ hr hβ hn hJ).paints (ComplexBrush.cast hI)
   let rect : ℝ := K'.indicator (fun _=> Real.exp (Q.ε*d')*(∏ i∈p,c0 i)) n
   have hc' : Brush j rect m (fun b=> skewIntegral X α' W R V U y b n I Q o.a p τ e f') t:=by
       apply (hc.paints hK).climb ?A ?B
       · rw [mul_one]; change airMark G I τ*K'.indicator (fun _=> _ * ∏ i∈p,c0 i) n ≤ _
         by_cases hg:n∈K'; swap; · unfold rect; rw [Set.indicator_of_notMem hg,Set.indicator_of_notMem hg,mul_zero]
         unfold rect; rw [Set.indicator_of_mem hg,Set.indicator_of_mem hg];rw [← mul_assoc (airMark G I τ)]; exact mul_le_mul_of_nonneg_right (collects τ p H X hX hβ hθ) (prod_nonneg fun i _=> Footage.positive P' zero_le_one _)
       · change (1+(j.factorial:ℝ)*γ)*(1+4*(|B| * z^i))+|D| *z^κ+a0*d' ≤ m
         let Q1:=D'*z^(i+κ); have hm:1≤Q1:=one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hz)
         have hd : d'≤Q1:=(le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_right (zero_le_one.trans hD) (one_le_pow₀ hz))
         have hZ (k:ℕ)(hK:k ≤ i+κ) : z^k ≤ Q1:= le_trans (pow_le_pow_right₀ hz hK) (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hz) _) hD)
         have hh : (1+(j.factorial:ℝ)*γ)≥0:=add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans P'.strong))
         change _+_+a0*d' ≤ _
         refine (add_le_add (add_le_add (b:=(1+(j.factorial:ℝ)*γ)*(Q1+4*(|B| *Q1))) ?_ (mul_le_mul_of_nonneg_left (hZ κ (by omega)) (abs_nonneg D))) (mul_le_mul_of_nonneg_left hd ha)).trans (le_of_eq ?_)
         · exact mul_le_mul_of_nonneg_left (add_le_add hm (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hZ i (by omega)) (abs_nonneg B)) (show (0:ℝ)≤4 by norm_num))) hh
         unfold Q1 m a1 a2; ring
   refine hc'.trim.climb ?_ le_rfl
   have hh : 1+(a0+a1+a2)*D'*z^(i+κ) ≤ (1+(a0+a1+a2))*D'*z^(i+κ):= by nlinarith only [one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ (n:=i+κ) hz)]
   have hv:=hc'.pos
   change _ * _ ≤ rect * (1+(a0+a1+a2))^j * D'^j * z^_
   apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hv] : 0≤1+m) hh j) hc'.nonneg).trans_eq
   rw [pow_mul,mul_pow,mul_pow]; ring
end YM.Frontier.Tuning.TiltTogether
