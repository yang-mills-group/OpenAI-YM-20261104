import YM.QuadraticLocal.Sunrise.Floss
import YM.QuadraticLocal.Sunrise.Scatter
/-!
# Physical polar marker subset reading after real augmented kernel launch
 All sections.K. Rank projector Lens on extended alph; morning.Light maps to interpretation under
 original p. preserve coefficient.W.O.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise.Focus
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module Push AllOrder.Ink.Money
open Marker Multi Comparison.RG02
open scoped BigOperators Topology Classical ContDiff
variable {n:Side} {V ι α: Type}[Fintype α][Fintype ι][DecidableEq ι] [Fintype V][DecidableEq V] (T:Finset ι) (J:Census V) (p:ι→ Poly J)
local notation "I"=> (α⊕ι)
local notation "U"=>rule (α⊕ι) n
local notation "K"=> Leaf n (α⊕ι)
variable {a C D:ℝ}{k:ℕ}
local notation "ϑ"=> ι → ℝ
local notation "σ"=> sustain (α:=α) (n:=n)
local notation "Ξ"=> Scatter.transmit J p
variable (L:Slip (Leaf n (α⊕ι)))(v:rule (α⊕ι) n)
-- polynomial on ι cloud
lemma enters (i:K): Plausible (fun z:ϑ=> which z i.2)∧ Ξ (fun z:ι→ℝ=> which z i.2)= i.2.elim (fun x=>1) p := by
 obtain ⟨z,y|y⟩:=i
 · exact ⟨Plausible.atom _,Scatter.one ..⟩
 exact ⟨Plausible.line ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:ι=>ℝ) y).toLinearMap),Scatter.factor y⟩ -- check indentation; projection defeq which?
lemma mon : Plausible (fun z:ϑ=> paid ((σ z) v) L) ∧ Ξ (fun z:ι→ℝ=> paid ((σ z) v) L)=(Complex.ofReal (paid v L)) • ∏ i:ι, p i^tally L i:= by
 induction L with
 | nil=> refine ⟨Plausible.atom _,(Scatter.one J p).trans (by simp [paid,tally])⟩
 | cons i L ih=>
    have h1 (x:ι→ℝ) : paid ((σ x) v) (i::L)=(v i)*((which x i.2)*paid ((σ x) v) L):= by change _* paid _ _=_; rw [look_at,mul_assoc,mul_left_comm];
    obtain ⟨u,hu⟩:= ih; obtain ⟨y,hy⟩:= enters J p i;
    simp_rw [h1]; let Z:=(fun z:ϑ=> which z i.2); let f (z:ϑ):= paid ((σ z) v) L; change Plausible ((v i) • (Z*f)) ∧ Ξ ((v i) • (Z*f))= _; refine ⟨(y.mul u).scale _,?_⟩;
    rw [Scatter.mul _ _ _ (y.mul u),Scatter.carry y u,hy,hu,show paid v (i::L)= v i*paid v L from rfl]; simp_rw [stamped,pow_add]; rw [Finset.prod_mul_distrib, callPose, Complex.ofReal_mul]; -- smul_smul before mul?
    rw [mul_smul_comm]; rw [smul_smul]
-- expects packing p with square zero. Enumerates finite subsets on all ι; no assumptions others.S. rank lens.E.Ph pure enough.
def depicts {ι α V:Type}[DecidableEq ι](L:List (V×(α⊕ι)))(T:Finset ι) := Depicted T L
lemma depicts_unique (R S:Finset ι)(he:Depicted R L)(hf:Depicted S L):R=S:=by
 ext i; have hh:=he i; have hz:=hf i; by_cases h:i∈R <;> by_cases h':i∈S <;> simp [h,h'] at *; all_goals first| omega | skip
variable (hp:∀ i:ι,(p i)^2=0)
include hp
lemma voted (h:L.length≤ k) : Ξ (fun z:ι→ℝ=> paid ((σ z) v) L) = ∑ T:Finset ι,(Complex.ofReal (lens T k (fun w:U=> paid w L) v)) • ∏ i∈T,p i := by
 rw [(mon J p L v).2]; simp_rw [certified _ _ _ h]; let Q:=univ.filter (fun i=> tally L i >0); by_cases hz:∀ i, tally L i≤1
 · have hQ:Depicted Q L:= fun i=> by simp only [Q,mem_filter,mem_univ,true_and]; specialize hz i; split <;> omega; -- ; E.LT.Time
   rw [Finset.sum_eq_single Q,if_pos hQ]; swap; · intro b hb hn; rw [if_neg (show ¬ _ from fun h=> hn (depicts_unique L b Q h hQ))]; simp
   rotate_left; · simp
   apply congr_arg; simp_rw [show ∀ i,tally L i=if i∈Q then 1 else 0 from hQ,pow_ite]; simp [← prod_filter] -- pow_ite or apply_ite?
 push_neg at hz; obtain ⟨i,hi⟩:= hz; have hf:∏ j:ι,p j^tally L j=0:= Finset.prod_eq_zero (i:=i) (mem_univ _) (by rw [show tally L i=2+(tally L i-2) from (by omega),pow_add,hp,zero_mul]); rw [hf,smul_zero]; symm; apply Finset.sum_eq_zero;
 intro j _; rw [if_neg (show ¬ Depicted j L from fun h=>?_ )]; · simp
 specialize h i; split at h <;> omega
-- `anvils`: extend Rank; no need avoid P biases.Aug.S.
lemma lens_book {f:U→ℝ}(h:Rank (rule (α⊕ι) n) k f) : Plausible (fun z:ι→ℝ=> f ((σ z) v)) ∧ Ξ (fun z:ι→ℝ=> f ((σ z) v)) = ∑ T:Finset ι,(Complex.ofReal (lens T k f v)) • ∏ i∈T,p i := by
 have h':= Floss.realm f h; clear h; induction h' with
 | single L he=> exact ⟨(mon J p L v).1,voted J p L v hp he⟩
 | @plus f g _ _ hf hg =>
    let z (f:U→ℝ)(y:ι→ ℝ):= f ((σ y) v); refine ⟨hf.1.add hg.1,?_⟩; change Ξ (z f+z g)= _; rw [Scatter.sends hf.1 hg.1,hf.2,hg.2]; simp_rw [Focus.union,Pi.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
 | @scale y f _ h=>
    let g(z:ι→ℝ):= f ((σ z) v); refine ⟨h.1.scale _,?_⟩; change Ξ (y •g)= _; rw [Scatter.mul _ _ _ h.1,h.2]; simp_rw [Focus.scale,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,Finset.smul_sum,smul_smul]
-- with assignments. no discrepancy assumed.
end YM.QuadraticLocal.Sunrise.Focus
