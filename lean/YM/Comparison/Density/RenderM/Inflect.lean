import YM.Comparison.Density.Render.Weld
import YM.Comparison.Density.Convert.Annotated

/-!
Transfer marked analytic WilsonX GEM data into real-side budgets. Complex
coefficient tested at ALL test variables, use meaningful Reads support;
small-marker radius separately paid (and any load protocol). Geometry
receipt includes winding lengths and extra stencil footprints; cancellations
in covering-space chart prices not assumed. Keep origin probes at EVERY
root. Path amplitudes are on actual nonlinear transports, real group.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.RenderM
open Fusing Markers Testing Registers Marker Multi RG Lattice Function Finset MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums Assembly Ovens Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo UVNext.CouplingReset Next.Scheduling Precision Next.Foundations
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
open Transport AnalyticBridge.SectorAffine.Offset FreeResolvent.Affine FreeResolvent.TestD
variable {G : Gauge} {n : Side} {B : BudgetPoint} {V : Type} [DecidableEq V] {R : Census V} {X : V → Type} [∀ v,NormedAddCommGroup (X v)] [∀ v,NormedSpace ℂ (X v)] {t k : ℕ}
variable (G X n t)

abbrev Chroma := Fin t → G.ColorIndex
structure Token where
  root : Site n -- placement frame
  path : Fin t→ RG.Slot
  gem : Chroma (G:=G) t → Cross X → ℂ
  fall : ℕ -- visit length total (charged in earlier analytic data)
  plot : Support n
  coin : ℝ

variable {G X n t}
namespace Token
variable (T : Token G n X t)

def re (x : Cross X) : Atom G t := ⟨T.path, fun i=> (T.gem i x).re⟩
def im (x : Cross X) : Atom G t := ⟨T.path,fun i=> (T.gem i x).im⟩

def touch (x : Cross X) (w : Fin t→ G.Color) : ℂ:= ∑ i,(↑(∏ j, w j (i j)):ℂ)*T.gem i x

def read (x : Cross X) (U : Config G n) := T.touch x (fun i=> (T.path i).atSite U T.root)
omit [DecidableEq V] [∀ v,NormedAddCommGroup (X v)] [∀ v,NormedSpace ℂ (X v)] in
lemma real_and_imag (x w): (T.touch x w).re=(T.re x).poly w ∧ (T.touch x w).im=(T.im x).poly w:= by
  unfold touch; simp only [Complex.re_sum,Complex.im_sum,Complex.re_ofReal_mul,Complex.im_ofReal_mul]; unfold Atom.poly; refine ⟨sum_congr rfl ?_,sum_congr rfl ?_⟩ <;> intro _ _ <;> exact mul_comm ..
omit [DecidableEq V] [∀ v,NormedAddCommGroup (X v)] [∀ v,NormedSpace ℂ (X v)] in
lemma reading (x) : T.read x=(fun u : Config G n => (↑((T.re x).unmasked u T.root):ℂ))+ Complex.I • fun u=> (↑((T.im x).unmasked u T.root):ℂ):= by
  ext1 U; simp only [Pi.add_apply,Pi.smul_apply]; change T.read _ _ = ↑(_)+Complex.I*_; rw [mul_comm];
  convert (Complex.re_add_im (T.read x U)).symm using 2
  · exact congrArg (fun q:ℝ=> (↑q:ℂ)) ((T.real_and_imag ..).1.symm)
  exact congrArg (fun q:ℝ=> (↑q:ℂ)*Complex.I) ((T.real_and_imag ..).2.symm)

structure Alive (O : Readers V X n) (i : Hot R) (T : Token G n X t) : Prop where
  path_len (x) : (T.re x).length ≤ T.fall
  path_size (x) : (T.re x).footprint T.root ⊆ T.plot
  symmetry x U (g) : T.touch x (fun i=> G.adjoint g (U i)) = T.touch x U
  readoffs j : Reads O.locus T.plot i.sites (T.gem j)
  arity j : Slotted i.sites (T.gem j)
  includes (v : V) : v∈i.sites → O.source.uses v ⊆ T.plot
  funds x : UnitPage x → ∑ j,‖T.gem j x‖≤T.coin -- reserve as complex payload

variable {T} {i : Hot R} {O : Readers V X n} (he : T.Alive O i)
include he
lemma shades (U) : Reads O.locus T.plot i.sites (fun x=> T.read x U) ∧ Slotted i.sites (fun x=> T.read x U):= by
  refine ⟨fun x y h=> sum_congr rfl fun j _=> congrArg _ (he.readoffs j x y h),?_⟩
  exact Slotted.sums _ _ fun j _=> (he.arity j).scale _
lemma traces (x): (T.re x).Invariant ∧ (T.im x).Invariant:= by
  refine ⟨fun g U=> ?_,fun g U=>?_⟩
  · rw [← (T.real_and_imag ..).1,he.symmetry, (T.real_and_imag ..).1]
  rw [← (T.real_and_imag ..).2,he.symmetry, (T.real_and_imag ..).2]
lemma smooth_price (x) : B.Regular T.plot (T.read x):= by
  rw [reading]
  refine regular_larger (regular_add (regular_mapped Complex.ofRealCLM ?_) (regular_smul _ (regular_mapped Complex.ofRealCLM ?_))) (he.path_size x)
  · exact Derivs.canonical_regular _ _ _ (traces he x).1
  exact Derivs.canonical_regular _ _ _ (traces he x).2
lemma cost_pair x (hx : UnitPage x): (T.re x).magnitude ≤ T.coin ∧ (T.im x).magnitude ≤ T.coin:=
  ⟨le_trans (Finset.sum_le_sum (fun i _=> Complex.abs_re_le_norm (T.gem i x))) (he.funds x hx), le_trans (Finset.sum_le_sum (fun i _=> Complex.abs_im_le_norm (T.gem i x))) (he.funds x hx)⟩
lemma salary_nn : 0≤ T.coin:= (Finset.sum_nonneg (fun j _=>norm_nonneg _)).trans (he.funds (fun i=>0) (fun _=>by simp))
open Wages

variable (G) (B)
def subtotal (G : Gauge) (B : BudgetPoint) (t : ℕ) := 2*startup G t B.power B.order
omit he in
lemma start_safe (G : Gauge) : 0≤ startup G t B.power B.order:= by unfold startup; have hh:=lt_of_lt_of_le zero_lt_one (slot_ge G B.power B.order 0); positivity
omit he in
lemma pays_can (U : Atom G t) {m x} (hU : U.length ≤ m) (hc : U.magnitude ≤ x): price B U ≤ startup G t B.power B.order*B.threshold^t*x*((m:ℝ)+1)^grade t B.power B.order:= by
  rw [scan]; have Ht:=B.threshold_pos; have hp:=start_safe (t:=t) B G; have hb : 0 ≤ U.magnitude:=Finset.sum_nonneg fun i _=> abs_nonneg _
  have hh := hb.trans hc; gcongr

variable {G}

def units (T : Token G n X t) := subtotal G B t * B.threshold^t*T.coin*((T.fall:ℝ)+1)^ grade t B.power B.order
lemma rooted x (hx: UnitPage x) : B.supBounds T.root T.plot (T.read x) (units B T):= by
  rw [reading]; obtain ⟨hr,hi⟩:=traces he x; let P:=T.re x; let Q:=T.im x
  have ht := Derivs.canonical_regular P T.root B hr; have hf := Derivs.canonical_regular Q T.root B hi
  apply bound_larger (Push.Local.bound_weaken (bound_add (regular_mapped Complex.ofRealCLM ht) (regular_smul _ (regular_mapped Complex.ofRealCLM hf)) ((sup_real ht).2 (total B P T.root)) (bound_smul _ ((sup_real hf).2 (total B Q T.root)))) ?_) (he.path_size x)
  rw [Complex.norm_I,one_mul]; refine (add_le_add (pays_can G B P (he.path_len x) (cost_pair he x hx).1) (pays_can G B Q (he.path_len x) (cost_pair he x hx).2)).trans_eq ?_; unfold units subtotal; ring

def span (B : BudgetPoint) (T : Token G n X t) := (coverNumber B.B T.plot)*(4*B.B+2)+2*B.B

def touched (T : Token G n X t) := ((1+(span B T:ℝ))^(B.power*B.order))*units B T

lemma ranges (B : BudgetPoint) (x) (hx: UnitPage x) (v) (hv:v∈i.sites) : B.supBounds (O.source.root v) T.plot (T.read x) (touched B T):= by
  have hK:=rooted B he x hx
  have heo : T.root∈T.plot:= he.path_size x (mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩)
  have hu := Corona.extent T.plot B.B heo (he.includes v hv (O.source.listed v))
  refine Push.Local.bound_weaken (Push.Local.bound_shift hK (smooth_price he x) _) (mul_le_mul_of_nonneg_right ?_ hK.1)
  rw [pow_mul]; gcongr; exact hu

-- Uniform unweighted and ordinary valuation at all Windings.
omit he in
private lemma norm_cast (a : ℂ) : ‖a • Complex.ofRealCLM‖ ≤ ‖a‖:= by
  rw [norm_smul]; have hx : ‖Complex.ofRealCLM‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u=> by simp
  exact mul_le_of_le_one_right (norm_nonneg _) hx

omit he in
private lemma through_color (F H:Directions G n→ℝ) {u : Directions G n} {x:ℝ} (h : Through k F u x) (ht:Through k H u x):
    Through k ((Complex.ofRealCLM ∘ F)+(fun w=> Complex.I* ↑(H w))) u (2*x) := by
  let L := Complex.I • Complex.ofRealCLM
  let f:=Complex.ofRealCLM ∘ F; let g:=L ∘ H; have hx:=h.nonneg
  have ha : Through k f u x:= (Render.abroad h _).mono (mul_le_of_le_one_left hx (by simpa only [one_smul,norm_one] using norm_cast 1))
  have hb : Through k g u x:= (Render.abroad ht L).mono (mul_le_of_le_one_left hx (by simpa only [L,Complex.norm_I] using norm_cast Complex.I))
  refine ⟨ha.smooth.add hb.smooth, fun j hj=>?_⟩; change ‖iteratedFDeriv ℝ j (f+g) u‖ ≤ _
  rw [iteratedFDeriv_add_apply (through_le ha hj).smooth (through_le hb hj).smooth]
  rw [two_mul]; exact (norm_add_le ..).trans (add_le_add (ha.pay _ hj) (hb.pay _ hj))

def stamp (k : ℕ) (T : Token G n X t) := 2*(T.coin*Render.entry G t k*(1+(T.fall:ℝ))^(k*t))
lemma ordinary (A: Directions G n) x (hx : UnitPage x) (hA : ‖A‖≤1) : Through k (T.read x ∘ increment 1) A (stamp k T):= by
  have hE : 0≤ Render.entry G t k:= pow_nonneg (mul_nonneg (Render.code_nn _) (Render.pass_nn ..)) _
  have hr (U : Atom G t) (ho : U.length≤ T.fall) (hp : U.magnitude ≤ T.coin) : Through k (fun W:Directions G n=> U.unmasked (increment 1 W) T.root) A (T.coin*Render.entry G t k*(1+(T.fall:ℝ))^(k*t)):= by
    have h : 0≤ U.magnitude:= Finset.sum_nonneg fun _ _=>abs_nonneg _; refine (Render.reserved U T.root hA).mono ?_; unfold Render.fareAt; have hh:= salary_nn he; gcongr
  rw [reading]; exact through_color _ _ (hr _ (he.path_len x) (cost_pair he x hx).1) (hr _ (show (T.im x).length ≤ _ from he.path_len x) (cost_pair he x hx).2)

omit he [DecidableEq V] [∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℂ (X i)] in
lemma order_z (T : Token G n X t) (x) (hj : k<t): iteratedFDeriv ℝ k (T.read x ∘ increment 1) 0=0:= by
  have hi (j : Atom G t) : ContDiffAt ℝ k (fun y : Directions G n=> j.unmasked (increment 1 y) T.root) 0:= (Render.reserved (k:=k) j _ (by simp)).smooth
  have hz (L:ℝ→L[ℝ]ℂ) (j : Atom G t) : iteratedFDeriv ℝ k (L ∘ (fun y:Directions G n=> j.unmasked (increment 1 y) T.root)) 0=0:= by
    rw [L.iteratedFDeriv_comp_left (hi j) le_rfl, Render.valuation _ _ hj]; ext; simp
  rw [reading]; let L:= Complex.I • Complex.ofRealCLM
  let H:= fun (j : Atom G t) (y : Directions G n)=> j.unmasked (increment 1 y) T.root
  change iteratedFDeriv ℝ k ((Complex.ofRealCLM ∘ H _)+(L ∘ H _)) 0=0
  rw [iteratedFDeriv_add_apply (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hi (T.re x))) (L.contDiff.contDiffAt.comp _ (hi (T.im x))),hz,hz,zero_add]
end Token
end YM.Comparison.Density.RenderM
