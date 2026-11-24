import YM.XSpace.ColorW
import YM.XSpace.TopProjection
/-!
# Top section specialization on arbitrary linear realizations
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson Source Source.Drops MeasureTheory
open Next.Rank Normal Spindle Beamer Next.Foundations Formal MvPolynomial
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff
variable {G : Gauge}

def input (A : CoverC G) (t : ℝ): CoverConfig G := fun x=> G.lieExp (t • A x)
lemma input_n (A : CoverC G) : input A 0 = 1 := by funext e; simp [input]
lemma point_path (A : CoverC G) (x : Cover) (w : Walk):
    HasDerivAt (fun t=> G.mat (travel (input A t) x w)) (G.colorMat (Exterior.linkSum A x w)) 0 ∧
    ContDiffAt ℝ ⊤ (fun t=> G.mat (travel (input A t) x w)) 0 := by
  have hx (k): HasDerivAt (fun t : ℝ=> G.mat (input A t k)) (G.colorMat (A k)) 0 ∧ ContDiffAt ℝ ⊤ (fun t=>G.mat (input A t k)) 0 := by
    constructor
    · unfold input; simp only [G.mat_lieExp,map_smul]; simpa using! (hasDerivAt_exp_smul_const (G.colorMat (A k)) (0:ℝ))
    exact G.exp_jet.contDiffAt.comp (f:=fun r:ℝ=>r • A k) (g:=fun x=>G.mat (G.lieExp x)) 0 (by fun_prop)
  induction w generalizing x with
  | nil=> simp only [travel,Exterior.linkSum,map_zero]; exact ⟨hasDerivAt_const _ _,contDiffAt_const⟩
  | cons a w ih=>
    have he : HasDerivAt (fun t=> G.mat (a.read (input A t) x)) (G.colorMat (if a.neg then - A (a.used x) else A (a.used x))) 0 ∧ ContDiffAt ℝ ⊤ (fun t=> G.mat (a.read (input A t) x)) 0 := by
      rcases a with ⟨a,h|h⟩
      · exact hx _
      simp only [Step.read,ite_true,G.mat_inv,map_neg]
      rw [← G.colorMat_skew]
      exact ⟨(hx _).1.star, (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hx _).2⟩
    simp only [travel,G.mat_mul, Exterior.linkSum,map_add]
    have hg : a.read (input A 0) x=1 := by rw [input_n]; simp only [Step.read]; split <;> simp
    refine ⟨(he.1.mul (ih _).1).congr_deriv ?_, he.2.mul (ih _).2⟩
    rw [input_n] at hg
    simp only [hg,G.mat_one,input_n,Pressure.one,one_mul,mul_one]

lemma point_c (A : CoverC G) (v : RG.Slot): HasDerivAt (fun t=> v.eval (input A t)) (Exterior.linkSum A v.offset (square v.plaq.val.1 v.plaq.val.2)) 0 ∧ ContDiffAt ℝ ⊤ (fun t=> v.eval (input A t)) 0 := by
  simp_rw [slot_eval]
  let w:= point_path A 0 v.walk
  let p:= point_path A v.offset (square v.plaq.val.1 v.plaq.val.2)
  constructor
  · refine Work.F03.curvature_of_hasDerivAt (V:=fun t=>_) ?_; simp_rw [G.mat_mul,G.mat_inv]
    refine ((w.1.mul p.1).mul w.1.star).congr_deriv ?_
    simp only [input_n,Pressure.one,G.mat_one,star_one,Pi.mul_apply,mul_one,one_mul,G.colorMat_skew]; abel
  refine curl_smooth _ (V:=fun t=>_) ?_; simp_rw [G.mat_mul,G.mat_inv, faceValue]
  exact ((w.2.mul p.2).mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ w.2))

variable {d : ℕ}

def alphabet (v : (Frame G d).Coeff) (A : CoverC G) (t : ℝ) := (authors G d).evaluate v (input A t)
def symbols (v : Index G d) := alphabet (d:=d) (Pi.single v 1)
def glyphCount (i : Index G d) := ((Frame G d).grades i).2

namespace Words
variable {i : Index G d} (s : Words i)
def stance (j:s.sites) (A:CoverC G) (t : ℝ):ℂ := (s.slots j.1).eval (input A t) j.2
lemma stance_at (j:s.sites) (A:CoverC G) : s.stance j A 0=0 := by unfold stance; rw [slot_eval,input_n]; simp [faceValue,Pressure.one,G.curvature_unit]
lemma stance_live (j:s.sites) (A:CoverC G) : ContDiffAt ℝ ⊤ (s.stance j A) 0 := Complex.ofRealCLM.contDiff.contDiffAt.comp 0 ((EuclideanSpace.proj (𝕜:=ℝ) j.2).contDiff.contDiffAt.comp 0 (point_c A _).2)
lemma stance_born (j:s.sites) (A:CoverC G) : deriv (s.stance j A) 0=(↑(curlC G A (locus (s.slots j.1) j.2)):ℂ) := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ((EuclideanSpace.proj (𝕜:=ℝ) j.2).hasFDerivAt.comp_hasDerivAt _ (point_c A _).1)).deriv

lemma rays (A : CoverC G): symbols i A=combine (fun j=> s.stance j A) s.pose:= _root_.funext fun t=> by unfold symbols alphabet; rw [s.past]; rfl
include s
lemma activated (A : CoverC G): ContDiffAt ℝ ⊤ (symbols i A) 0:= by
  rw [rays s A]; apply lush; intro j; exact stance_live s j A
lemma symbols_output (A:CoverC G):
    (↑((glyphCount i).factorial):ℂ)⁻¹ *iteratedDeriv (glyphCount i) (symbols i A) 0=text (curlC G A) (ground s) := by
  classical
  let σ:= Module.finBasis ℝ ℝ
  let k:=glyphCount i
  have he := jet_ray σ _ k ((activated s A).of_le le_top) 1
  simp only [smul_eq_mul,mul_one] at he
  rw [← he,rays s,jet_combine σ (fun j=>_) (fun j=> s.stance_live j _), pull_read' MvPolynomial.C _ (fun j=>?_)]
  · let φ (j:s.sites):= PowerSeries.coeff 1 (JetC σ (s.stance j A))
    let ψ (x:AKey G):= (↑(curlC G A x):ℂ)
    let m (j:s.sites) := locus (s.slots j.1) j.2
    have he : (Formal.test σ 1).comp (MvPolynomial.aeval φ) = (MvPolynomial.aeval ψ).comp (rename m) := by
      ext1 j; simp only [AlgHom.comp_apply, aeval_X,rename_X,φ,jet_ray σ _ _ ((stance_live s j A).of_le le_top),smul_eq_mul,mul_one,iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,inv_one,one_mul]; exact s.stance_born j A
    exact DFunLike.congr_fun he (homogeneousPart' s.pose k)
  · exact fun j => s.starts j
  rw [Formal.jet_zero,stance_at,map_zero]
end Words

-- orientation and star statements for linear section modulo realizations

def letters (G : Gauge) (d : ℕ): (Frame G d).Coeff →ₗ[ℂ] poly (AKey G) := LinearMap.lsum ℂ (fun _=>ℂ) ℂ (fun i:Index G d=> LinearMap.toSpanSingleton _ _ (ground (chosen i))) -- lsum? Pi vs finsupp

lemma canonical_expr (i : Index G d) : letters G d (Pi.single i 1) = ground (chosen i) := by simp [letters,LinearMap.lsum_apply,Pi.single_apply,ite_smul]
lemma coord_sum (v : (Frame G d).Coeff): v=∑ j,v j • Pi.single j (1:ℂ):= by funext j; simp [Finset.sum_apply, Pi.single_apply,mul_ite]

lemma letters_unfold (s : (Frame G d).Coeff): letters G d s = ∑ j:Index G d,s j • ground (chosen j) := by
  conv_lhs=> arg 2; rw [coord_sum s]
  rw [map_sum]; simp_rw [map_smul, canonical_expr]

lemma iterated_star (f : ℝ→ℂ) (i:ℕ) (x:ℝ) : iteratedDeriv i (star f) x=star (iteratedDeriv i f x):= by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  let s:= (starL ℝ : ℂ ≃L[ℝ] ℂ)
  change iteratedFDeriv ℝ i (s ∘ f) x _=_
  rw [s.iteratedFDeriv_comp_left]; rfl

lemma input_star (A : CoverC G) (i : Index G d) : star (symbols i A)=symbols i A := by
  funext t; have he : star (Pi.single i 1 : (Frame G d).Coeff)=Pi.single i 1:= by funext j; simp [Pi.single_apply, apply_ite star]
  change star ((authors G d).evaluate (Pi.single i 1) (input A t))=_
  rw [← (Next.Foundations.sound G d).ordinary_real,he]; rfl

theorem star_letters (v : (Frame G d).Coeff) (A : CoverC G) : text (curlC G A) (letters G d (star v))=star (text (curlC G A) (letters G d v)):= by
  unfold text; rw [letters_unfold,letters_unfold,map_sum,map_sum,star_sum]; apply Finset.sum_congr rfl; intro j hj
  rw [_root_.map_smul, _root_.map_smul, star_smul]
  change _ • text _ _= _ • star (text _ _)
  rw [← Words.symbols_output]; simp only [← iterated_star, input_star,star_mul', star_inv₀, star_natCast]; rfl

lemma input_colors (u:G.El) (A:CoverC G) (t : ℝ): input (colorPull G u A) t = gauge (fun _=>u) (input A t) := by
  funext x; unfold input colorPull Lattice.gauge; apply G.mat_injective
  rw [← map_smul,G.mat_mul,G.mat_mul,G.mat_lieExp,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate,G.mat_inv]; rfl

lemma input_spins (u:Signed) (A:CoverC G) (t : ℝ) : input (pulling A u 0) t=pull u 0 (input A t) := by
  funext i; simp only [input,pulling,pull,Step.read]; split <;> simp [Work.F03.exp_neg_color]

theorem color_letters (v : (Frame G d).Coeff) (A : CoverC G) (u:G.El): text (curlC G (colorPull G u A)) (letters G d v)= text (curlC G A) (letters G d v):= by
  rw [letters_unfold]; unfold text; rw [map_sum,map_sum]; apply Finset.sum_congr rfl; intro j hj
  have he : symbols j (colorPull G u A)= symbols j A := _root_.funext fun t=> by unfold symbols alphabet; rw [input_colors,(Next.Foundations.sound G d).gaugeInvariant]
  rw [map_smul,map_smul]; change _ • text _ _= _ • text _ _; rw [← Words.symbols_output,← Words.symbols_output, he]

lemma alphabet_symbols (v : (Frame G d).Coeff) (A : CoverC G) : alphabet v A=∑ i,v i • symbols i A := by
  funext t; rw [Finset.sum_apply]; unfold alphabet symbols Source.SectionData.evaluate
  conv_lhs=> rw [coord_sum v]; skip
  simp_rw [_root_.map_sum, _root_.map_smul,Pi.smul_apply]; rfl

lemma spun_label (s: Ortho) (i j:Index G d) (hh : glyphCount i≠glyphCount j):
    (Frame G d).act s (Pi.single i 1) j=0 := by
  let F:=Frame G d; let B:= F.basis i
  rw [← (Frame G d).coords_basis i,Labels.Frame.act_coords]; apply F.power_coefficient j (m:=F.grades i) (fun hx=> hh (congr_arg Prod.snd hx))
  have hv:= Labels.gradePart_mem (F.grades i) (Labels.tensor s B); rw [Labels.gradePart_turn, Labels.gradePart_self B _ (F.pure i)] at hv; exact hv

theorem spun_symbols (A : CoverC G) (s:Signed) (i:Index G d):
    text (curlC G (pulling A s 0)) (ground (chosen i))=text (curlC G A) (letters G d ((Frame G d).act s.ortho (Pi.single i 1))) := by
  let k:=glyphCount i; let v:= (Frame G d).act s.ortho (Pi.single i 1)
  have he : symbols i (pulling A s 0)= alphabet v A := _root_.funext fun t=> by unfold symbols alphabet; rw [input_spins,(Next.Foundations.sound G d).Hpart]
  rw [← Words.symbols_output, he, alphabet_symbols, iteratedDeriv_sum] -- inspect
  · unfold text; rw [letters_unfold,map_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj
    rw [iteratedDeriv_const_smul ((Words.activated (chosen j) _).of_le le_top),_root_.map_smul]; by_cases h:k=glyphCount j
    · change (↑k.factorial:ℂ)⁻¹ * (_ • _) = _ • text (curlC G A) (ground (chosen j)); rw [← Words.symbols_output]
      change (↑k.factorial:ℂ)⁻¹ * (v j*(iteratedDeriv k (symbols j A) 0)) = v j * _; rw [h]; ring
    change _ * (v j • _) = v j • _; rw [show v j=0 from spun_label _ _ _ h]; simp
  intro j _; exact ((Words.activated (chosen j) A).const_smul (v j)).of_le le_top

theorem signed_letters (v : (Frame G d).Coeff) (A : CoverC G) (s:Signed): text (curlC G (pulling A s 0)) (letters G d v)= text (curlC G A) (letters G d ((Frame G d).act s.ortho v)):= by
  unfold text; rw [coord_sum v,map_sum,map_sum,map_sum,map_sum,map_sum]; apply Finset.sum_congr rfl; intro j hj
  rw [map_smul,map_smul,map_smul,map_smul,map_smul,canonical_expr]; exact congr_arg (v j • ·) (spun_symbols A s j)
end YM.XSpace
