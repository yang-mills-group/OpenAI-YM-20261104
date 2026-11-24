import YM.XSpace.OrthoActor
import YM.Next.RANK.Common
/-! # Color orbit testing -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial OJoint
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G:Gauge} {d:ℕ}
variable {T:HFields G d→ HFields G d}{H:4≤d}

abbrev Board (G:Gauge)(d:ℕ):= HFields G d × View G d

namespace Deliver
variable (ht:Deliver H T)
def visit (T:HFields G d→ HFields G d)(s:Board G d)(a:O G.ColorIndex):= displayAct T s.1 s.2 a
local notation "I" => id (α:=HFields G d)
local notation "μ" => prob G.ColorIndex

def piece (T:HFields G d→ HFields G d) (p:poly (Board G d))(a:O G.ColorIndex):= aeval (fun y=> visit T y a) p
lemma piece_cont (T:HFields G d→ HFields G d) (p:poly (Board G d)):Continuous (piece T p):=by
  induction p using MvPolynomial.induction_on with
  | C c=> rw [show piece T (C c)=fun x=> c from _root_.funext fun x=>by simp [piece]]; exact continuous_const
  | add p q hp hq=> unfold piece; simp_rw [map_add]; exact hp.add hq
  | mul_X p i hp=> unfold piece; simp_rw [map_mul, aeval_X]; exact hp.mul (display_alive T _ _)
lemma piece_fee (T:HFields G d→ HFields G d) (p:poly (Board G d)):Integrable (piece T p) (prob G.ColorIndex):= (piece_cont ..).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable (c:G.ColorIndex)
include ht c
lemma polished (P:poly (Board G d)) : (∫ s,piece T P s ∂μ)= ∫ s,piece I P s ∂μ:= by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq=>
    have hg (p q:poly (Board G d))(V) : ∀ x,piece V (p+q) x=piece V p x+piece V q x:= fun s=> map_add ..
    simp_rw [hg,integral_add (piece_fee _ _) (piece_fee _ _),hp,hq]
  | monomial u a =>
    obtain ⟨z,hz⟩:= Common.letter u
    have hp: monomial u a= a • (∏ i : Fin (u.sum fun _ n=>n), MvPolynomial.X (z i)):= by change _= a • glyphs z _; rw [← hz]; simp [MvPolynomial.smul_monomial]
    simp_rw [hp,piece, map_smul,map_prod,MvPolynomial.aeval_X,integral_smul]; exact congr_arg _ (ht.fairs c (fun i=> (z i).1) (fun i=> (z i).2))

lemma observed_family (S:Finset (Board G d)) : ∃ a:O G.ColorIndex,∀ i∈S, visit I i a=visit T i 1:= by
  by_contra! h
  let Y i:= visit T i 1
  let m (i:Board G d) := (MvPolynomial.X i-C (Y i))*(MvPolynomial.X (negating i.1,i.2) - C (star (Y i)))
  let Y₀:= ∑ i∈S, m i
  let f (U:HFields G d→HFields G d) (a:O G.ColorIndex):ℝ:=∑ i∈S, ‖visit U i a-Y i‖^2
  have hm (U : HFields G d→HFields G d) (hu : ∀ i:Board G d,∀ a,visit U (negating i.1,i.2) a=star (visit U i a)) s:
      piece U Y₀ s=(↑(f U s):ℂ):= by
    unfold f piece Y₀; rw [map_sum,Complex.ofReal_sum]; refine Finset.sum_congr rfl fun i _=> ?_; unfold m; rw [map_mul,map_sub,map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_X, aeval_C, aeval_C, hu i,Algebra.algebraMap_self_apply,Algebra.algebraMap_self_apply,← star_sub]; exact Eq.trans (Complex.mul_conj _) (congr_arg Complex.ofReal (Complex.normSq_eq_norm_sq _)) -- naming
  have hw (i:Board G d) a: visit I (negating i.1,i.2) a=star (visit I i a):= by unfold visit; simp_rw [display_spin]; exact even_stage ..
  have hu (i:Board G d) a: visit T (negating i.1,i.2) a=star (visit T i a):= ht.display_bar ..
  let X:=f T; let Z:= f I
  have hc (U : HFields G d→HFields G d): Continuous (f U):= continuous_finsetSum _ fun i _=> (((display_alive _ _ _).sub continuous_const).norm.pow 2)
  have hf:∀ a:O G.ColorIndex,0 ≤ X a := fun a=> Finset.sum_nonneg fun i _=>sq_nonneg _
  have hI:X 1=0:= by simp [X,f,Y]
  have hs:∀ a:O G.ColorIndex,0<Z a:= by
    intro a; obtain ⟨i,hi,hP⟩:=h a; exact Finset.sum_pos' (fun i _=>sq_nonneg _) ⟨i,hi,pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hP)) _⟩
  let V:=Set.univ (α:=O G.ColorIndex)
  have hv : IsCompact V:= isCompact_univ
  obtain ⟨α,hα,hC⟩:= hv.exists_isMinOn Set.univ_nonempty (hc I).continuousOn
  obtain ⟨A,hA⟩:= hv.bddAbove_image (hc I).continuousOn; obtain ⟨B,hB⟩:= hv.bddAbove_image (hc T).continuousOn; let D:=max (max A B) 1; have hD:0<D:= zero_lt_one.trans_le (le_max_right ..)
  have hU a:D-X a∈Icc 0 D:= ⟨sub_nonneg.mpr ((hB (mem_image_of_mem X (Set.mem_univ a))).trans ((le_max_right ..).trans (le_max_left ..))),sub_le_self _ (hf _)⟩
  let k(s:O G.ColorIndex):= Z α-X s
  obtain ⟨j,hj⟩:= (concentrating μ V hv (f:=k) (g:=fun a=>D-X a) (continuous_const.sub (hc T)) (continuous_const.sub (hc T)) hD (fun i _=> hU i) (fun i _ h=>by unfold k; rw [sub_eq_self.mp h, sub_zero]; exact hs α) (x:=1) (by simp [V]) (by rw [hI, sub_zero])).exists
  rw [show V=Set.univ from rfl,setIntegral_univ] at hj
  let Q:= (C (↑(Z α):ℂ)-Y₀)*(C (D:ℂ)-Y₀)^j
  have he (U:HFields G d→HFields G d)(U': O G.ColorIndex→ℝ)(e:∀ a,piece U Y₀ a=(↑(U' a):ℂ)): ∀ a:O G.ColorIndex,piece U Q a= (( (Z α-U' a)*(D-U' a)^j:ℝ ):ℂ):= by
    intro a; specialize e a
    unfold Q piece
    rw [map_mul, map_pow,map_sub,map_sub]
    rw [show MvPolynomial.aeval _ _= (↑(U' a:ℝ):ℂ) from e]; simp
  have h':(∫ s, k s * (D-X s)^j ∂μ)=(∫ s,(Z α-Z s)*(D-Z s)^j ∂μ):= by
    apply Complex.ofReal_inj.mp
    have hp:= ht.polished c Q; simp_rw [he T X (hm T hu), he I Z (hm I hw), integral_complex_ofReal] at hp; exact hp
  rw [h'] at hj
  refine hj.not_ge (integral_nonpos fun i=> ?_); refine mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hC (Set.mem_univ _))) (pow_nonneg ?_ _)
  exact sub_nonneg.mpr ((hA (mem_image_of_mem Z (Set.mem_univ _))).trans ((le_max_left ..).trans (le_max_left ..)))

lemma actor : ∃ B:O G.ColorIndex,∀ p:HFields G d, records G d (T p)=changing B (records G d p) := by
  let M (i:Board G d):= {x|visit I i x=visit T i 1}
  obtain ⟨b,h⟩:= isCompact_univ.inter_iInter_nonempty M (fun i=> isClosed_eq (display_alive I _ _) continuous_const) (fun z=>by obtain ⟨a,h⟩:=ht.observed_family c z; exact ⟨a,Set.mem_univ _, Set.mem_iInter.mpr fun i=> Set.mem_iInter.mpr fun hx=> h i hx⟩)
  refine ⟨b,fun p=>?_⟩; apply grid_full; intro x
  have hs:visit I (p,x) b=displayAct T p x 1:= Set.mem_iInter.mp h.2 _
  rw [display_spin,show swept 1 x=x from ?_] at hs; exact hs.symm
  apply PiLp.ext; intro i; exact congr_arg (fun y: VectorA G.ColorIndex=> y i.2) (spin_one _)
end Deliver
end YM.XSpace.Stab
