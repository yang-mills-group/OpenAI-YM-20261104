import YM.XSpace.Abridged
import YM.XSpace.Specimen

/-!
# The first order bare report in terms of the proved local V3 and sampled sections
-/
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open Set Filter Function Wilson Source Source.Drops Labels RG Lattice Work.G05 CubicMatch
open Next.Rank.Normal Bare
open PowerSeries
open scoped BigOperators Topology ContDiff
variable {G : Gauge} {R : Period} (T : R.Tree) {H : Hol G} {d : ℕ} (S:Survey G H d) (x: R.Sites)

lemma samples_primary (u:T.Field G): fderiv ℝ (samples T S x) 0 u=spectra S x (T.covering u):=by
  rw [samples_deriv]; funext i; change R.curl (T.covering u) _=linearFace (slotPoint _ _) _; rw [angular,slot_wrap,R.curl_at]; rfl
lemma samples_m (u:T.Field G): ContDiffAt ℝ ω (fun t:ℝ=> samples T S x (t • u)) 0:= ContDiffAt.comp (g:=samples T S x) (f:=fun t:ℝ=> t • u) _ (by rw [zero_smul]; exact samples_smooth T S x) (line u)
lemma samples_secondary (u:T.Field G): term 2 (fun t:ℝ=> samples T S x (t • u))= accent S x (T.covering u):=by
  funext i; change (ContinuousLinearMap.proj i : GaugePanel G S.size →L[ℝ] G.Color) (term 2 (fun t:ℝ=> samples T S x (t • u)))=_
  rw [← term_linear _ ((samples_m T S x u).of_le le_top)]
  simp_rw [ContinuousLinearMap.proj_apply, samples_at,slots]; exact (carries_round (S.looks i) (fun t:ℝ=> T.links (t • u)) _ (fits_tree T u) x).curvature

lemma knit_c (i:Labels.Key G): constantCoeff (Bare.factor T S x i)= tea T (constantCoeff (knit S x i)):=by
  apply Taylor.from_real (T.basis G); intro u
  rw [factor_leading,log_path,constant_knit,pit_left, ← samples_deriv,samples_primary]; rfl
lemma knit_one (i: Labels.Key G): coeff 1 (Bare.factor T S x i)= tea T (coeff 1 (knit S x i)):=by
  let f:=labelFunction T S x (MvPolynomial.X i)
  have hf : ContDiffAt ℝ ω f 0:= label_smooth ..
  apply Taylor.from_real (T.basis G); intro u
  let A:=fun t:ℝ=>samples T S x (t • u); have h0 : A 0=0:=by simp [A]
  have hp : ContDiffAt ℝ ω A 0:= samples_m T S x u
  have hs : ContDiffAt ℝ ω (S.recover ∘ A) 0:= S.recover_smooth.contDiffAt.comp 0 hp
  have ht : ∀ t:ℝ,f (t • u) = (snapCoord d i) (S.recover (A t)):=by intro t; simp only [f,labelFunction, Labels.read,MvPolynomial.aeval_X]; rfl
  rw [Bare.factor,coeff_mk,Taylor.divided_eval,← along u _ hf,log_path,coefficient_knit,pit_right]; simp_rw [ht]
  have H : deriv A 0=spectra S x (T.covering u):= Eq.trans (Push.side _ ((samples_smooth T S x).differentiableAt (by simp)) u).deriv (samples_primary T S x u)
  calc _ = term 2 (fun t:ℝ=>snapCoord d i ((S.recover ∘ A) t)):=by unfold term; simp only [Complex.real_smul, Complex.ofReal_inv,Complex.ofReal_natCast]; rfl
       _ = _ := by rw [term_linear _ (hs.of_le le_top), term_vcomp_two S.recover_smooth.contDiffAt hp,H,h0, show term 2 A=_ from samples_secondary T S x u]; rfl

/-- Conserves the divided-coupling jet in the observable, on **ordinary** labels.
Use once after announcing the `insertW (-1)` columns. -/
lemma reconstruct_toy (K: Labels.Pol G): constantCoeff (Bare.raw T S x K)=tea T (constantCoeff (toy S x K)) ∧ coeff 1 (Bare.raw T S x K) = tea T (coeff 1 (toy S x K)):=by
  unfold raw toy
  induction K using MvPolynomial.induction_on with
  | C a=> simp [PowerSeries.algebraMap_apply,MvPolynomial.algebraMap_eq,tea]
  | add p q hp hq=> simp only [map_add,hp.1,hq.1,hp.2,hq.2,and_self]
  | mul_X p i hp=> simp only [map_mul,coeff_one_mul,MvPolynomial.aeval_X,knit_one,knit_c,map_add,hp.1,hp.2,and_self]
lemma reconstruct_product {Z : Type*} {A: Z→Series T G} {a:Z→PowerSeries (St (Per R.side) G)} (s:Finset Z) (h:∀ z∈s, constantCoeff (A z)=tea T (constantCoeff (a z)) ∧ coeff 1 (A z)=tea T (coeff 1 (a z))): constantCoeff (∏ z∈s,A z)=tea T (constantCoeff (∏ z∈s,a z)) ∧ coeff 1 (∏ z∈s,A z)=tea T (coeff 1 (∏ z∈s,a z)):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simp
  | insert i s hi ih=> obtain ⟨p,q⟩:= h i (by simp); obtain ⟨x,y⟩:= ih fun i hi=> h i (by simp [hi]); simp only [Finset.prod_insert hi,map_mul,coeff_one_mul,map_add,x,y,p,q,and_self]
lemma reconstruct1 {Z : Type*} {q:Z→ℕ} (v: ∀ i:Z,Survey G H (q i)) (k:∀ i:Z, Labels.Label G (q i)) (a: Z→ R.Sites) (s:Finset Z):
    let X:= ∏ i∈s, toy (v i) (a i) ((v i).insertW (-1) (k i)).val
    coeff 1 (Bare.normalized T G (∏ i∈s,column T (v i) (a i) (k i))) = blend (treeCov T G) 0 (coeff 1 X - cubic R G * constantCoeff X):=by
  dsimp only; simp_rw [column_formula]; let P:=∏ i∈s,toy (v i) (a i) ((v i).insertW (-1) (k i)).val
  exact order1 T G _ _ _ (reconstruct_product T s (fun i _=> reconstruct_toy T (v i) (a i) _)).1 (reconstruct_product T s (fun i _=> reconstruct_toy T (v i) (a i) _)).2
end YM.XSpace.Chart2
