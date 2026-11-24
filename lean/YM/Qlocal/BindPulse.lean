import YM.Qlocal.Davenport
import YM.Qlocal.Sequence
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Binding
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Work.F03 Work.F05
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped BigOperators Topology ENNReal Classical InnerProductSpace MatrixOrder ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side} {S:StepData c f} {k t j:ℕ}
    {V:Type} [DecidableEq V] {B:Census V}
variable (F:Forest S.ratio) (T:S.Choices) {b:Clip} {R:PathData G} {O:ChartRatio G} (W : Layout G)(U:Finset Age)
local notation "E"=> Apex c G
local notation "Z"=> Precision.Key F G
local notation "Y"=> Poll.Body Z
local notation "X"=> E × Y
local notation "I"=> ℝ × X
local notation "D"=> fieldDir G c 1
variable (K : Kernel S b R O)(w:Colors B G f) (h : Legal U W) (hv: w.vac=drawn W U f)
  {a L Λ:ℝ} (A:Before G a L S.patch.J S.kernel (j+3))(σ : fieldDir G c 1→AxisChart G F)
   (hR:R.Bounds b a L Λ) (hp:Bid.Larger (G:=G) S) (he:A.Service F b R σ)
local notation "τ"=> Uniform.tint G _
local notation "Γ'"=> weld Z
set_option quotPrecheck false
local notation "Γ"=> (Γ').trans (Uniform.tint G F.Free)
set_option quotPrecheck false
local notation "B₀"=> Laplace.startup F O T R b A hp hR he K.ratio
local notation "Bℓ"=> augment F W U B₀ h
local notation "θ"=> fderiv ℝ (orbit (G:=G) F σ) 0
include he
include he h A hR hp
local notation "G₀"=> K.covariance F T
local notation "Π"=> castle (Bℓ).hard (Bℓ).quiet (Bℓ).pay.steer
open Matrix PertExtension.GaussianScore
omit h A hR hp he in
lemma gauss_read : MeasurePreserving (Γ') volume (volume:Measure (Precision.Key F G → ℝ)):= PiLp.volume_preserving_ofLp _
omit h hR hp in
lemma bar : Lapis.gram F R b σ T 0 = (G₀)⁻¹:= by
 unfold Comparison.RG02.Bulk.Kernel.covariance; rw [Matrix.nonsing_inv_nonsing_inv _ (IsUnit.mk0 _ (K.hessian_pos F T).det_pos.ne'), Lapis.gram, _root_.map_zero, show σ 0=0 from ((same_path F K A σ he).eq_of_nhds.trans (K.critical F).1)]
lemma cloud_k (y:Y) : (Π).kern y= Real.exp (-(Gaussian.force (G₀) ((Γ') y))/2):= by
 rw [castle_pays (Bℓ).pay]; change Real.exp (-(Laplace.curvature (table F T R b) _ _))= _; rw [curvature_spine F T R b A hp hR he, bar F T K A σ he]; congr 1; unfold Gaussian.force; change -(1/2*_) = _; rw [show Γ' y=y.ofLp from rfl]; ring -- rewrite `table` ambiguity.Cost
omit A he h hR hp in
lemma from_cloud {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](f:(Precision.Key F G→ ℝ)→V) : (∫ z,f z ∂Gaussian.cloud (G₀)) = ∫ y:Y,(Gaussian.ratio (G₀) ((Γ') y)) • f ((Γ') y):= by
 let c:= G₀; let g:= fun z: Z→ℝ=> Gaussian.ratio c z; let q:=fun z: Z→ℝ=> g z • f z
 have h:= Gaussian.measurable_ratio c|>.ennreal_ofReal; let r x:= ENNReal.ofReal (g x); have ht : ∀ᵐ x ∂volume,r x<⊤:=Filter.Eventually.of_forall fun _=>ENNReal.ofReal_lt_top
 rw [Gaussian.cloud_formula (K.positive F T),integral_withDensity_eq_integral_toReal_smul h ht (f:=(fun x=> ENNReal.ofReal (Gaussian.ratio (G₀) x)))]; simp_rw [ENNReal.toReal_ofReal (Gaussian.ratio_pos (K.positive F T) _).le]; exact ((gauss_read (G:=G) F).integral_comp (Γ').toHomeomorph.toMeasurableEquiv.measurableEmbedding q).symm
lemma sensed {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](f:(Precision.Key F G→ ℝ)→V) : (∫ z,f z ∂Gaussian.cloud (G₀)) = (Gaussian.coat (G₀))⁻¹ • ∫ y:Y,((Π).kern y) • f ((Γ') y):= by rw [← integral_smul, from_cloud F T K]; simp_rw [cloud_k F T W U K h A σ hR hp he, smul_smul]; rfl
lemma capital_quote : capital Π volume = Gaussian.coat (G₀):= by
 let A' := capital Π volume; let w':= Gaussian.coat (G₀); have hw:= Gaussian.coat_pos (K.positive F T); have hv:= sensed F T W U K h A σ hR hp he (fun _ => (1:ℝ)); simp only [smul_eq_mul,mul_one,integral_const,probReal_univ] at hv; change 1=w'⁻¹*A' at hv; have hy : w' ≠ 0:= hw.ne'; field_simp at hv; first | exact hv | exact hv.symm
lemma revenue (u : (Precision.Key F G→ℝ)→ℝ) : (Π).average volume (u ∘ (Γ'))=∫ z,u z ∂Gaussian.cloud (G₀):= by
 rw [sensed F T W U K h A σ hR hp he]; unfold Law.average; rw [show (∫ y:Y,(Π).kern y)=_ from capital_quote F T W U K h A σ hR hp he]; rw [div_eq_mul_inv,mul_comm]; apply congr_arg; conv_lhs=> arg 2; ext x; rw [Pi.mul_apply,mul_comm]
 rfl
include hv
variable [Fintype V] (x:Apex c G)
include x
local notation "Ω₀"=> Floe.books F W U B₀
local notation "Q"=> climate Π volume (Ω₀)
local notation "X₁"=> Fk K F T w ((τ) x)
lemma off_axis (k:ℕ): denominator (X₁ k)=series B k (realCurve B (fun n=> Q n x)):= by
 let H : ℕ→E→ℝ := Q; let u:= Comparison.RG02.Bulk.geometric K F T w; let σ₀: Z→ℝ:= 0; let d:=translated K F ((τ) x); let A' := Comparison.RG02.Assembly.expansions w.power (markFn S F w) u
 apply Join.both_parts; intro i a; rw [denominator,bottom_value,polarization, realCoeff, beads]; split
 next hi=> 
    rw [Comparison.RG02.Bulk.table]; let k':= a.val.card; let f z:=EXP (Radial.layers u) k' (d z); have ht y : EXP (Ω₀) k' (x,y)= f ((Γ') y):= by
        have h' : Function.swap (Ω₀) (x,y)=Function.swap (Radial.layers u) (d ((Γ') y)):= by funext k; exact (pulse F T W U K w h hv A σ hR hp he x y k).symm.trans (vacuum_eq u _ k)
        change Laplace.SigmaP.expS (swap (Ω₀) (x,y)) k'= Laplace.SigmaP.expS (swap (Radial.layers u) (d _)) k'; rw [h']; -- expS ns wrong
    have hg : (Q) k' x= ∫ z,f z ∂Gaussian.cloud (G₀):= by change Law.average _ _ (fun y=> EXP (Ω₀) k' (x,y))= _; simp_rw [ht]; exact revenue F T W U K h A σ hR hp he f
    simp_rw [born]; apply congr_arg; change (∫ z, Complex.ofReal (f z) ∂Gaussian.cloud (G₀))= Complex.ofReal ((Q) k' x); rw [hg]; exact integral_ofReal
 next hi=> rw [mul_zero]
omit A he h hv hR hp x in
lemma polish {l : Grade B k} (hd:l.part (Board B k).quiet=0) : Extra.Trajectories.connected l.pass=l:= by
 have hv := Poly.pass_part _ hd; exact Extra.Trajectories.pass_inj (Extra.Trajectories.connected_quiet hv) hd (Extra.Trajectories.pass_connected hv)
lemma soul (k:ℕ) : logVac (X₁ k)= series B k (realCurve B (fun n=> distilled Bℓ n x)):= by
 unfold logVac; rw [off_axis F T W U K w h hv A σ hR hp he]; let w:=LOG (Q); change _=series B k (realCurve B (fun n=> w n x)); have he : (Ω₀) 0=0:=win0 _; have hh : w 0=0:= Fire.fades (toward volume he); have hK: EXP w=Q:= Fire.exponent_inv (toward volume he); rw [show (fun i=> (Q) i x)= (fun i=> Radial.expsum w i i x) from funext (fun i=> (by rw [← ray_exp w hh, hK])), real_pass w hh x]; exact polish (show (scalarLog B k fun i=>w i x).part (Board B k).quiet=0 from (by rw [← Join.pair_quiet,scalarLog,polarization,realCoeff,beads,if_pos rfl]; change _* Complex.ofReal (w 0 x)=0; rw [hh]; simp))
lemma action (k:ℕ) (l:ℕ)(hk:l ≤ k): Comparison.RG02.Symmetry.Orbit.ground K F T w k l ((τ) x)= ((distilled (Bℓ) l x - if l=0 then liftQ (Bℓ).hard (θ) x else 0:ℝ) : ℂ):= by
 unfold Comparison.RG02.Symmetry.Orbit.ground Comparison.RG02.Laplace.detail; rw [soul F T W U K w h hv A σ hR hp he,observation _ _ _ hk, realCoeff,beads,if_pos rfl]; by_cases hl:l=0
 · rw [if_pos hl, if_pos hl,Complex.ofReal_sub,sub_eq_add_neg, Comparison.RG02.Symmetry.price, ←accounting F T K A σ he]; rfl
 rw [if_neg hl,if_neg hl,sub_zero,add_zero]
end YM.Qlocal.Binding
