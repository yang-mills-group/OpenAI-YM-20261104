import YM.Contacts.Procession.Atlas
/-! # Pivots, aperture matrix before Wick normalization. Include one Mark, no source align bound. -/
noncomputable section
namespace YM.Contacts.Procession.Cartons
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Labels Source Drops Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Shuttle Tide
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
open Morning Mediator Next.Foundations
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 90000
set_option autoImplicit false
variable {G:Gauge}{X Y: Type}{m:Side}{F:Cohort G}{d k h u n:ℕ}(B: Labels.Frame G d)
-- read on entire Mark.App.No power prices assumed.
open Planned.PrimaryIntegral295 WardBin Push.Local Catch Welcome Lumen Larch Sun
local notation "u*" => (d*(d+1))
-- extend coordinates ℂ algebra through entire Pol; topology only needed on finite bins
variable {b:ℝ}
abbrev flood (F:Snap G d→ℝ) (j:ℕ)(l:ℕ) := tile (Tensor.coeff (cotton F) l 0) j
def taproot (B:Labels.Frame G d) : Pol G→ₗ[ℂ] B.Coeff := let X:=(localFields G d).subtype; B.coords.toLinearMap.comp (X.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))).choose
lemma cut_root (L:Label G d): taproot B L.val=B.coords L:= congr_arg B.coords (DFunLike.congr_fun ((localFields G d).subtype.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))).choose_spec L)
abbrev bins (G:Gauge)(d k:ℕ):= (i:Fin (k+1))→ Tensor.T (Ship G (d*(d+1))) ℝ i.val
def dollar (A:bins G d k) : Snap G d→ℝ:=fun x=>∑ i : Fin (k+1), Tensor.diagonal (A i) (costume (G:=G) d (d*(d+1)) x)
def tower (F:Cohort G)(d k:ℕ): bins G d k := fun i=> sheet i.val (F i.val) (Tide.lens G (d*(d+1)))
lemma gold (A:bins G d k):ContDiffAt ℝ ω (cotton (dollar A)) 0 := by refine ContDiffAt.comp _ Complex.ofRealCLM.contDiff.contDiffAt (ContDiffAt.sum fun i _ => (Tensor.diag_smooth ..|>.contDiffAt.comp _ (costume_diff G d _)))
def peek (B:Labels.Frame G d)(j k:ℕ) : bins G d k →L[ℝ] B.Coeff := by
    let f:= fun z:bins G d k => taproot B (flood (dollar z) j k);
    refine LinearMap.toContinuousLinearMap (show bins G d k →ₗ[ℝ] B.Coeff from ⟨ ⟨f,?_⟩,?_⟩) -- use mk
    · intro p q; have h: cotton (dollar (p+q))=cotton (dollar p)+cotton (dollar q):= funext fun x=>by change Complex.ofRealCLM (dollar (p+q) x)= _; simp only [dollar,Tensor.diagonal,Pi.add_apply,_root_.add_apply,Finset.sum_add_distrib,cotton,Function.comp_apply,map_add]
      unfold f flood; rw [h, Tensor.coeff, iteratedFDeriv_add_apply ((gold p).of_le le_top) ((gold q).of_le le_top),smul_add]; simp only [Tensor.coeff,tile,_root_.add_apply,map_add,add_mul,Finset.sum_add_distrib]
    intro a p; change f (a • p)=a • f p; have H:cotton (dollar (a • p))= a • cotton (dollar p):=by funext i; simp [cotton,dollar,Tensor.diagonal,Finset.smul_sum]
    unfold f flood; unfold Tensor.coeff; rw [H,iteratedFDeriv_const_smul_apply ((gold p).of_le le_top),smul_comm]; rw [show ∀(M: T (Snap G d) ℂ k), tile (a • M) j=(a:ℂ) • tile M j from ?_,map_smul]; · funext i; simp [Complex.real_smul]
    intro M; unfold tile; simp_rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [_root_.smul_apply,Complex.real_smul,  MvPolynomial.smul_eq_C_mul,map_mul,mul_assoc] -- orientation
variable {B}
lemma rubric {F:Cohort G}(h:Felt F) (hp:k ≤ d): Tensor.coeff (cotton (dollar (tower F d k))) k 0= Tensor.coeff (cotton (panel F d u* d)) k 0:= by
    let A:= costume (G:=G) d u*; have hA:A 0=0:= costume_zero G; let V(r:ℕ):= rows F u* r
    have he : dollar (tower F d k)=V k ∘ A:= by funext x; unfold dollar; change (∑ i:Fin (k+1), Tensor.diagonal (sheet i.val (F i.val) (lens G u*)) (A x))=_; exact (Fin.sum_univ_eq_sum_range (fun i=>Tensor.diagonal (sheet i (F i) (lens G u*)) (A x)) _ ) -- find lemma
    have hθ i (hi:i≤k) : iteratedFDeriv ℝ i (V k) (A 0)= iteratedFDeriv ℝ i (V d) (A 0) := by rw [hA]; apply smul_right_injective _ (show (i.factorial:ℝ)⁻¹≠0 by positivity); exact (h.plans u* hi).trans ((h.plans u* (hi.trans hp)).symm)
    rw [he,show panel F d u* d=V d ∘ A from rfl]; have hB i : ContDiffAt ℝ ω (V i ∘ A) 0:= ContDiffAt.comp _ (rows_diff F u* _|>.contDiffAt) (costume_diff ..)
    unfold cotton Tensor.coeff; rw [Complex.ofRealCLM.iteratedFDeriv_comp_left (hB k) (i:=k) le_top, Complex.ofRealCLM.iteratedFDeriv_comp_left (hB d) (i:=k) le_top]; apply congr_arg; apply congr_arg; exact Work.G05.jets_comp ((costume_diff G d u*).of_le (show (k:WithTop ℕ∞)≤ω from le_top)) ((costume_diff G d u*).of_le (show (k:WithTop ℕ∞)≤ω from le_top)) ((rows_diff F u* k).contDiffAt.of_le le_top) ((rows_diff F u* d).contDiffAt.of_le le_top) rfl (fun _ _=>rfl) hθ _ le_rfl
-- projection depends only on finite stencil choices, not kinetics. Boas cost lower orders only for higher n
lemma cane (h:Tags F)(v:B.Index) : peek B (B.grades v).1 (B.grades v).2 (tower F d (B.grades v).2) v = ((velum B F v):ℂ):= by
    let k:=(B.grades v).2; let A:=exhibit B (panel F d u* d); let p:= B.coords.symm A; let K:=gradePart (B.grades v) p; have he : (flood (dollar (tower F d k)) (B.grades v).1 k)=K.val:= by unfold flood; rw [rubric h.toFelt (Film.second_fits B v)]; exact ((gauges B h le_rfl le_rfl).detects v ((smooth_panel ..).of_le le_top)).symm
    change taproot B _ v= _; rw [he,cut_root]; exact ((Film.costs_only B v p).symm.trans ((congr_fun (B.coords.apply_symm_apply A) v).trans (charter h v).symm))
-- line observation for consumer. Supports tower with Tensor norms in Snap. weights h and slot forecasts after planner.Large
private lemma choices {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y](P:X →L[ℝ] Y):∃ a≥(0:ℝ),∀ x, ‖P x‖ ≤ a*‖x‖:= ⟨_,norm_nonneg P,ContinuousLinearMap.le_opNorm P⟩
lemma prices (v:B.Index):∃ C≥(0:ℝ),∀ F:Cohort G, Tags F → ‖velum B F v‖ ≤ C * ‖tower F d (B.grades v).2‖:= by
    obtain ⟨a,ha,h⟩:= choices (X:=bins G d (B.grades v).2) (Y:=B.Coeff) (peek B (B.grades v).1 (B.grades v).2); refine ⟨a,ha, fun F hf=>?_⟩; rw [← Complex.norm_real,← cane hf v]; let P:= peek B (B.grades v).1 (B.grades v).2; exact (norm_le_pi_norm (P (tower F _ _)) v).trans (h _)
lemma sheet_tilt (P:Cohort G)(H:Felt P)(U:Cohort G)(h:Felt U)(a:ℝ)(j:ℕ): sheet j ((a • P+U) j) (lens G u) = a • sheet j (P j) (lens G u)+ sheet j (U j) (lens G u):= by -- no requiring result Felt yet
    let A:=blanket j (P j) (lens G u); let Q:= blanket j (U j) (lens G u); have ht : blanket j ((a • P+U) j) (lens G u)=(fun q=> a • A q + Q q):= funext fun i=> ContinuousMultilinearMap.ext (fun v=> by simp only [A,Q,blanket_response, Pi.add_apply, Pi.smul_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,add_mul,mul_assoc]); unfold sheet; rw [ht, Summable.tsum_add ((H.board j u).const_smul a) (h.board j u), tsum_const_smul'']; -- simp
lemma peek_linear {P U :Cohort G} (h:Tags P)(hh:Tags U)(a:ℝ)(hw:Tags (a • P+U))(v:B.Index): velum B (a • P+U) v=a * velum B P v+velum B U v := by
    let k:=(B.grades v).2; let R (F:Cohort G):= tower F d k; apply Complex.ofReal_injective; rw [Complex.ofReal_add, Complex.ofReal_mul, ← cane hw v,← cane h v,←cane hh v]; rw [show tower (a • P+U) d (B.grades v).2=_ from (show R (a • P+U)=a • R P+R U from funext fun i=> sheet_tilt P h.toFelt U hh.toFelt a i.val), map_add, map_smul]; simp only [Pi.add_apply,Pi.smul_apply,Complex.real_smul]; rfl
end YM.Contacts.Procession.Cartons
