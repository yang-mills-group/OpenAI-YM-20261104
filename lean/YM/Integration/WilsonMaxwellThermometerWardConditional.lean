import YM.UVExtension.Fallow.Micro
import YM.Wilson.Law
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Homeomorph.Lemmas

/-! Exact local Haar reading of the original Maxwell equations after fixing
all exterior bonds at their literal values. The beta is arbitrary at a fixed
finite torus, as it is in the native Mark.MicroAt theorem. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMaxwellThermometerWardConditional
open Function Filter Set MeasureTheory Lattice Wilson Push.Mark
open scoped Classical Topology ComplexConjugate
variable {G:Gauge} {n:Side}

def far (r:ℕ) (o:Site n) (e:Edge (Site n)) : Prop :=
  e.1∈Outer r o ∧ e.1+step e.2∈Outer r o
abbrev Held (G:Gauge) (r:ℕ) (o:Site n):=(e:{e//far r o e})→G.El
abbrev Free (G:Gauge) (r:ℕ) (o:Site n):=(e:{e//¬far r o e})→G.El

def chamber (r:ℕ) (o:Site n) : Config G n≃ₜHeld G r o×Free G r o :=
  Homeomorph.piEquivPiSubtypeProd (far r o) (fun _=>G.El)

abbrev law (G:Gauge) {I:Type*} [Fintype I] : Measure (I→G.El):=Measure.pi fun _=>G.probHaar

def numerator (r:ℕ) (o:Site n) (β:ℝ) (f:Pre G) (y:Held G r o) : ℂ:=
  ∫ z:Free G r o,(bare β ((chamber r o).symm (y,z)):ℂ)*f (expandAt o ((chamber r o).symm (y,z))) ∂law G

theorem smooth (r:ℕ) (o:Site n) (β:ℝ) {f:Pre G} (hf:Continuous f) :
    Continuous (numerator r o β f) := by
  have joint:Continuous (fun p:Held G r o×Free G r o=>
      (bare β ((chamber r o).symm p):ℂ)*f (expandAt o ((chamber r o).symm p))):=
    ((Complex.continuous_ofReal.comp (bare_cont β)).mul (onStencil o hf)).comp (chamber r o).symm.continuous
  have h:=continuous_parametric_integral_of_continuous (μ:=law G) (f:=fun y:Held G r o=>fun z:Free G r o=>
    (bare β ((chamber r o).symm (y,z)):ℂ)*f (expandAt o ((chamber r o).symm (y,z)))) joint
      (isCompact_univ (X:=Free G r o))
  unfold numerator
  simpa only [Measure.restrict_univ] using h

private theorem split (r:ℕ) (o:Site n) {φ:Config G n→ℂ} (hc:Continuous φ) :
    (∫U,φ U ∂prior G n)=∫y:Held G r o, ∫z:Free G r o,φ ((chamber r o).symm (y,z)) ∂law G ∂law G := by
  let M:=MeasurableEquiv.piEquivPiSubtypeProd (fun _:Edge (Site n)=>G.El) (far r o)
  have h:MeasurePreserving M (prior G n) ((law G).prod (law G)):=by
    exact measurePreserving_piEquivPiSubtypeProd (fun _:Edge (Site n)=>G.probHaar) (far r o)
  have cont:=hc.comp (chamber r o).symm.continuous
  have ent:Integrable (φ ∘ (chamber r o).symm) ((law G).prod (law G)):=
    cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [←h.symm.integral_comp' φ]
  exact integral_prod _ ent

theorem original {f:Pre G} (hf:Continuous f) {r M:ℕ} (paid:MicroAt f r M)
    (o:Site n) (cut:M≤n.val) {β:ℝ} (b:β≠0) :
    ∀ y:Held G r o,numerator r o β f y=0 := by
  let U:=chamber (G:=G) r o
  let k:=numerator r o β f
  have hk:Continuous k:=smooth r o β hf
  let tester (V:Config G n):=conj (k (U V).1)
  have test:Continuous tester:=Complex.continuous_conj.comp (hk.comp (continuous_fst.comp U.continuous))
  have localTest:LocalOn (Outer r o) tester := by
    intro X Y agree
    exact congrArg (fun y:Held G r o=>conj (k y)) (funext fun e=>agree e.val e.property.1 e.property.2)
  have admissible:RG.Envelope tester:=by
    obtain ⟨a,A⟩:=isCompact_univ.bddAbove_image test.norm.continuousOn
    exact ⟨test.measurable,a,fun v=>A ⟨v,mem_univ v,rfl⟩⟩
  have cancel:=paid n cut o β b tester localTest admissible
  have continuous:=onStencil o hf
  have ci:Integrable (fun V:Config G n=>f (expandAt o V)*tester V) (Wilson.law G n β):=continuous_integrable β (continuous.mul test)
  rw [moment_formula β _ ci] at cancel
  have pos:((partition G n β:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (partition_pos (G:=G) (n:=n) β).ne'
  have bare_zero:=(mul_eq_zero.mp cancel).resolve_left (inv_ne_zero pos)
  let load (V:Config G n):=(bare β V:ℂ)*(f (expandAt o V)*tester V)
  have cont:Continuous load:=(Complex.continuous_ofReal.comp (bare_cont β)).mul (continuous.mul test)
  change (∫V,load V ∂prior G n)=0 at bare_zero
  rw [split r o cont] at bare_zero
  have fiber (y:Held G r o) :
      (∫z:Free G r o,load (U.symm (y,z)) ∂law G) = k y * conj (k y) := by
    have value:k y=∫z:Free G r o, (bare β (U.symm (y,z)):ℂ)*f (expandAt o (U.symm (y,z))) ∂law G:=rfl
    nth_rw 1 [value]
    rw [←integral_mul_const]
    apply integral_congr_ae
    filter_upwards with z
    simp only [load,tester,U.apply_symm_apply,mul_assoc]
  have square : (∫y, k y*conj (k y) ∂law G)=0 :=by
    change (∫y:Held G r o, ∫z:Free G r o,load (U.symm (y,z)) ∂law G ∂law G)=0 at bare_zero
    simpa only [fiber] using bare_zero
  have realSquare : (∫y, ‖k y‖^2 ∂law G)=0:= by
    apply Complex.ofReal_injective
    change Complex.ofReal (∫y,‖k y‖^2 ∂law G)=0
    have coe : (∫y,((‖k y‖^2:ℝ):ℂ) ∂law G) = Complex.ofReal (∫y,‖k y‖^2 ∂law G) := integral_ofReal
    rw [←coe]
    simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq] using square
  have ae : (fun y=>‖k y‖^2)=ᵐ[law G] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _=>sq_nonneg _)
      ((hk.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp realSquare
  have eq : k=0 := Measure.eq_of_ae_eq (μ:=law G) (by
    filter_upwards [ae] with y hy
    simpa only [Pi.zero_apply,pow_eq_zero_iff (by decide : (2:ℕ)≠0),norm_eq_zero] using hy)
    hk continuous_zero
  exact fun y=>congrFun eq y

end YM.Integration.WilsonMaxwellThermometerWardConditional
