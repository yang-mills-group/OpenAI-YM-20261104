import YM.Contacts.Milling.Mallet
import Mathlib.Algebra.Polynomial.Degree.Lemmas
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory Asymptotics
open Finset PertExtension.Series PertExtension.GaussianScore Pulse Pulse.Form Radial YM.Stationary
open scoped Topology BigOperators ContDiff Classical Polynomial
noncomputable section
variable {V E:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
local notation "Φ" => (ℝ×V)
namespace Ion
lemma jet_ana (F:V→ℝ) (n:ℕ)(x:V): AnalyticAt ℝ (Radial.jet F n) x := by
  have h:ContDiff ℝ ω (Radial.jet F n):=contDiff_const.mul (Tensor.diag_smooth (iteratedFDeriv ℝ n F 0) ω); exact h.contDiffAt.analyticAt
lemma loan_sum {F:E→(V→ℝ)}(s:Finset E)(hp:∀ i∈s, AnalyticAt ℝ (F i) 0)(j:ℕ)(x:V): jet (fun x=>∑ i∈s,F i x) j x=∑ i∈s,jet (F i) j x:= by
  unfold jet; rw [show (fun x=>∑ i∈s,F i x)=∑ i∈s,F i from funext fun x=> (Finset.sum_apply ..).symm, iteratedFDeriv_sum_apply, _root_.sum_apply, mul_sum]; exact fun i hi=>(hp i hi).contDiffAt
lemma jet_minus (f g:V→ℝ)(n:ℕ)(x:V)(h:AnalyticAt ℝ f 0)(he:AnalyticAt ℝ g 0): jet (f-g) n x=jet f n x-jet g n x:= by unfold jet; rw [iteratedFDeriv_sub_apply h.contDiffAt he.contDiffAt,_root_.sub_apply, mul_sub]
lemma valued {F G:V→ℝ}(k:ℕ)(h:AnalyticAt ℝ F 0)(hg:AnalyticAt ℝ G 0)(he:∀ x,∀ i<k, jet F i x=jet G i x): Rays k (F-G) := (jet_bridge (h.sub hg)).2 fun x i hi=> by rw [jet_minus _ _ _ _ h hg,he _ _ hi,sub_self]
def prepare (k:ℕ)(F:V→ℝ)(x:V):=∑ i∈Finset.range k,jet F i x
lemma prepared (k:ℕ)(F:V→ℝ)(x:V): AnalyticAt ℝ (prepare k F) x := by unfold prepare; exact ContDiffAt.analyticAt (ContDiffAt.sum (fun i _=> (jet_ana F i x).contDiffAt))
lemma jets (k:ℕ)(F:V→ℝ)(x:V)(i:ℕ): jet (prepare k F) i x= if i < k then jet F i x else 0 := by
  unfold prepare; rw [loan_sum _ (fun j _=> jet_ana F j 0)]; simp_rw [show ∀ j,jet (jet F j) i x=_ from fun j=>radiant (jet_ana F j 0) j i (fun x t=>jet_smul F j t x) x] -- underscore invalid
  simp_rw [Finset.sum_ite_eq]; simp
lemma dream (k:ℕ){F:V→ℝ}(h:AnalyticAt ℝ F 0) : Rays k (prepare k F-F):= valued k (prepared ..) h (fun x i hi=> by rw [jets,if_pos hi])
def conjunct (F:V→ℝ)(k:ℕ)(u:Φ) := u.1^k * F u.2
def stake (F:ℕ→V→ℝ)(k:ℕ)(u:Φ):=∑ i∈Finset.range k,conjunct (F i) i u
lemma conjunct_ana {F:V→ℝ}(h:AnalyticAt ℝ F 0)(k:ℕ) : AnalyticAt ℝ (conjunct F k) 0:= (ContDiffAt.mul (contDiffAt_fst.pow _) (h.contDiffAt.comp (f:=Prod.snd) _ contDiffAt_snd)).analyticAt
lemma joint (F:V→ℝ)(i j:ℕ) (x:Φ)(h:AnalyticAt ℝ F 0): jet (conjunct F j) i x= if j ≤ i then x.1^j*jet F (i-j) x.2 else 0:= by
  set f:= prepare (i+1) F; have he:=prepared (i+1) F 0
  have hv:Rays (i+1) (conjunct f j-conjunct F j):= by
    have hl:Rays 0 (fun x:Φ=>x.1^j):=rays_zero ((contDiffAt_fst.pow j).analyticAt)
    have hf:Rays (i+1) ((f-F) ∘ Prod.snd (α:=ℝ)) := merkin (he.sub h) (dream _ h) _ contDiffAt_snd.analyticAt rfl
    rw [show conjunct f j-conjunct F j=(fun x:Φ=>x.1^j)*((f-F)∘Prod.snd) from by ext; simp [conjunct,mul_sub]]; exact zero_add (i+1) ▸ hl.mul hf
  rw [← nightwalk (conjunct_ana he j) (conjunct_ana h j) hv i (by omega) x,show conjunct f j=(fun x:Φ=>∑ b∈Finset.range (i+1),conjunct (jet F b) j x) from funext fun x=> by simp [f,prepare,conjunct,mul_sum]]; rw [loan_sum _ (fun b _=>conjunct_ana (jet_ana F b 0) j)]
  have hm b : jet (conjunct (jet F b) j) i x= if b+j=i then conjunct (jet F b) j x else 0:= by rw [radiant (conjunct_ana (jet_ana F b 0) j) (b+j) _ ?_]; simp only [eq_comm (a:=i)]; intro u t; simp only [conjunct,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,jet_smul]; ring
  split
  next hx => rw [Finset.sum_eq_single (i-j),hm]; rw [if_pos (show i-j+j=i by omega)]; rfl; intro b hb hk; rw [hm,if_neg (by omega)]; intro h; rw [Finset.mem_range] at h; omega
  next hx=> exact sum_eq_zero fun b hb=> by rw [hm,if_neg (by omega)]
lemma stake_ana {F:ℕ→V→ℝ}{k:ℕ}(h:∀ i<k,AnalyticAt ℝ (F i) 0): AnalyticAt ℝ (stake F k) 0:= by unfold stake; exact ContDiffAt.analyticAt (ContDiffAt.sum (fun i hi=>(conjunct_ana (h i (mem_range.mp hi)) i).contDiffAt))
lemma good_spaces {F:ℕ→V→ℝ}{k n:ℕ}(hp:∀ i<k,AnalyticAt ℝ (F i) 0)(h:∀ i<k,Rays (n-i) (F i)): Rays n (stake F k) := (jet_bridge (stake_ana hp)).2 fun x m hx=> by
  unfold stake; rw [loan_sum _ (fun i hi=>conjunct_ana (hp _ (mem_range.mp hi)) i)]; apply sum_eq_zero; intro i hi; rw [joint _ _ _ _ (hp _ (mem_range.mp hi))]; split <;> first | rfl | rw [(jet_bridge (hp _ (mem_range.mp hi))).1 (h _ (mem_range.mp hi)) _ _ (by omega),mul_zero]
lemma contains {F:ℕ→V→ℝ}{k n:ℕ}(hp:∀ i<k,AnalyticAt ℝ (F i) 0)(h:Rays n (stake F k)): ∀ i<k,Rays (n-i) (F i) := by
  intro i hi; refine (jet_bridge (hp i hi)).2 fun x m hx=>?_ ; let D:=Finset.range k; let k':=m+i; let a (j:ℕ):= if j ≤ k' then jet (F j) (k'-j) x else 0
  let p:= ∑ j∈D, Polynomial.C (a j)*Polynomial.X^j
  have he (y:ℝ): p.eval y=0 := by
    have hh:= (jet_bridge (stake_ana hp)).1 h (y,x) k' (by unfold k'; omega); unfold stake at hh; rw [loan_sum _ (fun i hi=>conjunct_ana (hp _ (mem_range.mp hi)) i)] at hh; apply Eq.trans ?_ hh; unfold p; rw [Polynomial.eval_finsetSum]; apply Finset.sum_congr rfl; intro j hj; rw [joint _ _ _ _ (hp j (mem_range.mp hj)),Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]; unfold a; split_ifs<;> first | rfl | ring
  have hl : p=0:= Polynomial.funext (fun x=> by rw [he,Polynomial.eval_zero]); have heq : a i=0:= by -- syntax trans direction
    have hm:= congr_arg (fun p:Polynomial ℝ=>p.coeff i) hl; simp only [p,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_zero] at hm; simpa [hi,D] using hm
  unfold a k' at heq; rwa [if_pos (by omega),Nat.add_sub_cancel] at heq

-- homogeneous at all loop labels
structure Rung (n:ℕ)(F:V→ℝ) : Prop where
    exact : prepare n F=F
lemma rink {n:ℕ}{F:V→ℝ} (h:Rung n F)(c:V) : F c=∑ i∈Finset.range n, jet F i c:= (congr_fun h.exact c).symm
variable {k : ℕ}{F:V→ℝ}
lemma repeater (h:Rung k F)(L:V →L[ℝ] V) : Rung k (F ∘ L):= by
  refine ⟨?_⟩; funext i; unfold prepare; rw [comp_apply,rink h]; refine Finset.sum_congr rfl (fun a _=>?_)
  have hF : AnalyticAt ℝ F 0:= h.exact ▸ prepared k F 0
  rw [homogeneous_derivative _ i a (AnalyticAt.comp (f:=⇑L) (g:=F) (by rw [map_zero]; exact hF) (L.analyticAt _)).contDiffAt,homogeneous_derivative F _ a hF.contDiffAt]; simp_rw [Function.comp_apply,map_smul]
lemma instant {Q : V→ℝ}(hf:Rung k F)(hg:Rung k Q)(h : Rays k (F-Q)) : F=Q:= by funext x; rw [rink hf,rink hg]; exact sum_congr rfl fun i hi=> nightwalk (hf.exact ▸ prepared k F 0) (hg.exact ▸ prepared k Q 0) h _ (mem_range.mp hi) _ -- equality ▸ changes F inside
end Ion
end
end YM.Contacts.Milling
