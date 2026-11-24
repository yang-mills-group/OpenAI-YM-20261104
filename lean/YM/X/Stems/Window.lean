import YM.X.Stems.Bob
import YM.X.Stems.Zest
import YM.X.Feyn.First
/-!
# Finite Wick symbols at lattice positions. Finite torus index for periodic seams and near terms, no wrap assumptions.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Stems
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Log Next.Rank Normal MvPolynomial
open Feyn Gauge LatticePT PertExtension.Orb Chart Series.Tested Finset
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Pointwise Classical
variable {G:Gauge} {n:Side} {j:ℕ}{d:ℕ}
variable (U : Potential G n)
local notation "E" => Potential G n
local notation "PM"=>Module.Dual ℝ E
abbrev Jam (n:Side)(G:Gauge):= (Edge (Site n)) × G.ColorIndex
def west (o:Site n) (e:Pin): Edge (Site n):= (wrap n e.1+o,e.2)
def place (o : Site n)(x:Hair G):Jam n G:= (west o x.1,x.2)
def hairAt (o:Site n): Curly G→ₐ[ℂ] poly (Jam n G):= rename (place o)
def pier (i:Jam n G):PM:= (EuclideanSpace.proj (𝕜:=ℝ) i.2).toLinearMap ∘ₗ Pert.Orb.takeLink i.1
abbrev glaze (v:E): poly (Jam n G) →ₐ[ℂ] ℂ:= aeval (fun i:Jam n G=> (pier i v:ℂ))
def peat (o:Site n)(v:E):Brush G:= expandAt o v.val
lemma shades (o:Site n)(p:Curly G): glaze U (hairAt o p) = snap (peat o U) p:= by unfold glaze snap hairAt;rw [aeval_rename];rfl
lemma positive (o:Site n): expandAt o (positiveLinks U)=posit (peat o U):= rfl
def blow (w:Word G)(o:Site n)(j:w.F.Index)(ε:ℝ):= fun r:E=> w.cost j ε * SlotEvaluation.fieldAt w.S j o (positiveLinks r)
abbrev number' (w:Word G) (j:w.F.Index):=(w.F.grades j).2
abbrev hut (j:ℕ) (w:Word G)(i:w.F.Index):= mark (evalS w.S i) (opt i w.sound w.chosen) (number' w i + j)

def bookMark (w:Word G)(j:ℕ):= ∑ i:w.F.Index,( (topBasis w.S w.H w.sound w.chosen w.axis i:ℂ)) • hut j w i
def baseMark (w:Word G) := Vertex.combination w.S w.H w.sound w.chosen w.axis
lemma base_book (w:Word G): bookMark w 0= loom (baseMark w):= by unfold baseMark bookMark Vertex.combination; rw [_root_.map_sum]; simp_rw [map_smul]; exact Finset.sum_congr rfl fun i _=> congr_arg _ (basis_moon i w.sound w.chosen).symm
lemma blow_ok (w:Word G)(o:Site n)(j:w.F.Index)(ε:ℝ): ContDiffAt ℝ ω (blow w o j ε) 0:= by
   refine contDiffAt_const.mul (curves_pos ?_ ?_ : ContDiffAt ℝ ω (evalS w.S j ∘ posit ∘ peat o) 0)
   · exact opt j w.sound w.chosen
   intro i; exact (Pert.Orb.takeLink (G:=G) (west o i)).toContinuousLinearMap.contDiff.contDiffAt
abbrev juice (k:ℕ)(w:Word G)(o:Site n)(j:w.F.Index)(ε:ℝ):= (w.cost j ε) * Jet.someJ (along (evalS w.S j) (peat o U)) (number' w j + k)
def bump (k:ℕ)(w:Word G)(o:Site n)(j:w.F.Index)(ε:ℝ):poly (Jam n G):= ((w.cost j ε:ℝ):ℂ) • hairAt o (hut k w j)
lemma blow_glows (w:Word G)(o:Site n)(j:w.F.Index)(ε:ℝ): Jet.Glow (number' w j) (fun t:ℝ=> blow w o j ε (t • U)) (juice U 0 w o j ε) (juice U 1 w o j ε):=
 Jet.Glow.nScale (f:=along (evalS w.S j) (peat o U)) ⟨along_zero (opt j w.sound w.chosen) _,fun i=> no_under (peat o U) j w.sound w.chosen,rfl,rfl⟩ _ -- opt ..
lemma glaze_seal (w:Word G)(o:Site n)(j:w.F.Index)(ε:ℝ)(r:ℕ): glaze U (bump r w o j ε)=(juice U r w o j ε:ℂ):= by unfold bump; rw [map_smul,shades,hut,mark_test]; exact Eq.symm (Complex.ofReal_mul ..)

variable {I : Type*} [Fintype I]
section
variable (o : I→Site n) (w:I→Word G)(t:Mixed.Task w)(ε:ℝ)
abbrev X := Mixed.product w Finset.univ t o ε
include U
private lemma infl (U':E): X o w t ε (positiveLinks U')=∏ i:I,blow (w i) (o i) (t i) ε U':= rfl
omit U
lemma smoothX : ContDiffAt ℝ ω (X o w t ε ∘ positiveLinks) 0:= by
   rw [show X o w t ε ∘ positiveLinks= (fun U:E=> ∏ i:I, blow (w i) (o i) (t i) ε U) from rfl]; exact contDiffAt_prod (f:=fun i v=> blow (w i) _ _ ε v) (fun _ _=> blow_ok ..)
lemma gaugeX: GaugeInvariant (X o w t ε):= by
   intro x v; unfold X Mixed.product; refine Finset.prod_congr rfl fun i _=> ?_; rw [SlotEvaluation.fieldAt,(w i).S.placed_invariant (w i).sound];rfl
lemma smoothRX (he:Even n.val) : ContDiffAt ℝ ω (X o w t ε ∘ representative) 0:= by
   let f:=(Feyn.fits (G:=G) he).toContinuousLinearMap; have ht: ContDiffAt ℝ ω (X o w t ε ∘ positiveLinks) (f 0):=by rw [map_zero]; exact smoothX .. -- edit
   rw [show X o w t ε ∘ representative= (X o w t ε ∘ positiveLinks) ∘ f from funext (fun x=> congr_arg (X o w t ε) (fits_at (G:=G) he x).symm)]; exact ht.comp _ f.contDiff.contDiffAt

def exactus (w:I→Word G)(t:Mixed.Task w)(o:I→Site n)(ε:ℝ)(j:ℕ): I→poly (Jam n G):= fun i=> bump j (w i) (o i) (t i) ε
def exact₁ [DecidableEq I]:= Jet.dot (exactus w t o ε 0) (exactus w t o ε 1) Finset.univ

def costs (j:ℕ): I→ℝ:= fun i=>juice U j (w i) (o i) (t i) ε
include U
lemma dynamic' [DecidableEq I] : Jet.Glow (Mixed.number w t) (fun v:ℝ=> X o w t ε (positiveLinks (v • U))) (∏ i:I,costs U o w t ε 0 i) (Jet.dot (costs U o w t ε 0) (costs U o w t ε 1) Finset.univ):= by
    have he:= Jet.Glow.product _ _ _ _ Finset.univ (fun i:I=> blow_glows U (w i) (o i) (t i) ε)
    apply Eq.mp ?_ he; congr 1; ext y; simp [infl U o w t ε, Finset.prod_apply]
lemma exact_glaze : glaze U (∏ i:I,exactus w t o ε 0 i) = ((jet (X o w t ε ∘ positiveLinks) (Mixed.number w t) U:ℝ):ℂ):= by rw [_root_.map_prod]; simp_rw [exactus,glaze_seal]; rw [← Complex.ofReal_prod,homogeneous_derivative _ U _ ((smoothX ..).of_le le_top)]; exact congr_arg Complex.ofReal (dynamic' U o w t ε).live.symm
lemma next_glaze [DecidableEq I] : glaze U (exact₁ o w t ε)=((jet (X o w t ε ∘ positiveLinks) (Mixed.number w t+1) U:ℝ):ℂ):= by
   rw [show jet _ _ U= Jet.dot (costs U o w t ε 0) (costs U o w t ε 1) Finset.univ from (homogeneous_derivative _ U _ ((smoothX ..).of_le le_top)).trans (dynamic' U o w t ε).then1,exact₁,Jet.dot,map_sum]; unfold Jet.dot; simp_rw [map_mul,map_prod,exactus,glaze_seal];simp_rw [costs,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]; simp_rw [juice,Complex.ofReal_mul]
end

def vertex (p:PlaqAxes):Curly G:= mark (Log.flame (G:=G) (0,p)) (Log.brief _) 3
def boil :poly (Jam n G):= ∑ p:Face (Per n), ((2:ℂ)⁻¹) • hairAt p.1 (vertex p.2)
lemma fire_at (p:Face (Per n)): G.price (faceValue (positiveLinks U) p)= Log.flame (0,p.2) (posit (peat p.1 U)):= by unfold Log.flame;rw [← positive,faceValue,faceValue,travel_at,map_zero,zero_add]
lemma along_fire (p:Face (Per n))(r:ℝ): G.price (faceValue (positiveLinks (r • U)) p) = along (Log.flame (0,p.2)) (peat p.1 U) r:= fire_at (r • U) p
lemma overTop : glaze U boil= ((jet wilson 3 U:ℝ):ℂ):= by
   let f (p:Face (Per n)):= along (Log.flame (0,p.2)) (peat p.1 U); have he (t:ℝ): wilson (t • U)=(∑ p:Face (Per n), f p t)* (2:ℝ)⁻¹:= by rw [overS, rwS]; unfold energy; simp_rw [along_fire]; exact div_eq_mul_inv ..
   have h p:ContDiffAt ℝ (↑(3:ℕ)) (f p) 0:= (along_zero (Log.brief _) _).of_le le_top
   rw [boil,map_sum]; rw [homogeneous_derivative _ U _ ?hf]; simp_rw [map_smul, shades,vertex,mark_test,Jet.someJ, he, iteratedDeriv_mul_const_field, iteratedDeriv_fun_sum (fun i _=> h i),Finset.sum_mul,Finset.mul_sum,Complex.ofReal_sum,Complex.ofReal_mul]
   apply Finset.sum_congr rfl; intro i hi; dsimp only [f]; rw [smul_eq_mul,smul_eq_mul,Complex.ofReal_mul];push_cast;ring -- edit
   case hf =>
      change ContDiffAt ℝ _ wilson (0:E); unfold wilson; refine (ContDiffAt.sum (fun x _ => ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => ?_)))).div_const _
      split_ifs; exact (Work.F03.price_smooth (Pert.Orb.pos_sqDiff ..).contDiffAt).of_le le_top; -- edit
      exact contDiffAt_const
end YM.PositionX.Stems
