import YM.SchemeConversionRG11.FirstW.Invoice.Lie
import YM.Pert.First.Guests
/-! Borrow the very same joint finite Gaussian. Retain cap to avoid claiming conflicting equations before val projects. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory ProbabilityTheory Set Lattice Pert Warp Topology Maxwell
open scoped BigOperators Classical
variable {n : Side} {G : Gauge} {d r : ℕ}
abbrev Who (G : Gauge) (d : ℕ) := Full.CosKey G d
abbrev Part (G : Gauge) (d : ℕ) := Cache (Who G d)
abbrev Players (G : Gauge) (r d : ℕ) := Fin r→ Part G d
def uncap (k : Part G d) : Labels.Pol G := MvPolynomial.rename Subtype.val k
abbrev At (G : Gauge) (r d : ℕ) := Fin r × Who G d
def feed (p : Players G r d) : Cache (At G r d) := ∏ i, MvPolynomial.rename (Prod.mk i) (p i)
def dict (t : At G r d) (p : Players G r d) : Players G r d := update p t.fst (MvPolynomial.pderiv t.snd (p t.fst))
lemma d_feed (t : At G r d) (p : Players G r d) : MvPolynomial.pderiv t (feed p) = feed (dict t p) := by
  -- factor at t.1 only
  let R (s : Fin r) (q : Part G d) := MvPolynomial.rename (Prod.mk s) q
  have eh (s : Fin r) (q : Part G d) (he:s≠t.1): MvPolynomial.pderiv t (R s q)=0 := by
    induction q using MvPolynomial.induction_on with
    | C => simp [R]
    | add f g h k=> unfold R at *; rw [map_add,map_add,h,k,add_zero]
    | mul_X f a h=> have ht : (s,a)≠ t:=fun eq=>he (congrArg Prod.fst eq); unfold R at *; simp [ht,h]
  have H (q : Part G d) : MvPolynomial.pderiv t (R t.1 q)=R t.1 (MvPolynomial.pderiv t.2 q) := by
    rcases t with ⟨a,b⟩; clear eh; induction q using MvPolynomial.induction_on with
    | C => simp [R]
    | add f g h k=> unfold R at *; simp only [map_add]; rw [h,k]
    | mul_X f z h=> unfold R at *; simp only [map_mul,MvPolynomial.rename_X,Derivation.leibniz,map_add,h]; by_cases hx:b=z <;> simp_all
  let s:= t.fst
  let D : Finset (Fin r):= Finset.univ.erase s
  have hp (p : Players G r d) : feed p = R s (p s)* (∏ i∈D,R i (p i)) := by exact (Finset.mul_prod_erase Finset.univ (fun i=> R i (p i)) (Finset.mem_univ s)).symm
  have hg (D : Finset (Fin r)) (hs:s∉D) : MvPolynomial.pderiv t (∏ i∈D,R i (p i))=0 := by
    induction D using Finset.induction with
    | empty => simp
    | insert a D ht ih=> rw [Finset.prod_insert ht,Derivation.leibniz, ih (fun m=> hs (Finset.mem_insert_of_mem m)), eh a (p a) (fun eq=>hs (by rw [eq]; exact Finset.mem_insert_self ..))]; simp -- membership trans placeholder
  rw [hp p,hp (dict t p),Derivation.leibniz,hg D (Finset.notMem_erase _ _),smul_zero,zero_add,smul_eq_mul, mul_comm (∏ i∈D,_),H]
  apply congrArg₂ (· * ·)
  · unfold s; rw [dict,update_self]
  exact Finset.prod_congr rfl fun b hb=>by rw [dict,Function.update_of_ne (Finset.mem_erase.mp hb).1]
abbrev Ribs (G : Gauge) (n : Side) (r d : ℕ) := Warp.Hall r (Orb.Coords G n) (Full.Aux G d)
def teams (o : Full.Grid n r) (h : ℝ) (p : At G r d) : Query (Ribs G n r d) := node h o p.fst p.snd
variable (o : Full.Grid n r) (h : ℝ)
abbrev ZeroR (p : Players G r d) := PowerSeries.constantCoeff ((recipe d h o) (uncap ∘ p))
abbrev money (x : Orb.Coords G n) (i : Fin r) (u : Full.Aux G d) (p : Part G d) := PowerSeries.constantCoeff (Full.pairEval h (o i) x u (uncap p))
lemma money_eq (p : Part G d) (x : Ribs G n r d) (i : Fin r): spend (teams o h) (MvPolynomial.rename (Prod.mk i) p) x = money o h x.fst i (x.snd i) p := by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [spend, money,uncap, Full.pairEval]
  | add p q he hf=> simp only [spend,money,uncap, Full.pairEval,map_add] at *; rw [he,hf]
  | mul_X p a he=>
     have H : Full.pairEval h (o i) x.1 (x.2 i) (uncap (p*MvPolynomial.X a)) = Full.pairEval h (o i) x.1 (x.2 i) (uncap p)* Full.pairEval h (o i) x.1 (x.2 i) (MvPolynomial.X a.val) := by simp [uncap,Full.pairEval]
     unfold spend money at *; rw [H,map_mul,map_mul,map_mul,MvPolynomial.rename_X,MvPolynomial.eval_X,he,pair_aeval];rfl
lemma court (p : Players G r d) (f : Orb.Coords G n→ℂ) (hf:Orb.Tame f) :
    (∫ x:Ribs G n r d, f x.fst*spend (teams o h) (feed p) x ∂hall G n r d h) = ∫ x,f x * First.line Finset.univ o h (fun _=>d) (uncap ∘ p) x ∂Orb.data G n := by
  letI := Orb.isLaw (G:=G) (n:=n)
  letI := Full.auxGaussian (G:=G) (d:=d) h
  letI := hall_G G n r d h
  have hi (i : Fin r) (x : Orb.Coords G n) : First.tube o h (fun _=>d) (uncap ∘ p) x i = ∫ u : Full.Aux G d,money o h x i u (p i) ∂Full.auxLaw G d h := by
    rw [First.tube,First.lead,Full.auxiliary, Full.avg,← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_mk]; simp only [PowerSeries.coeff_zero_eq_constantCoeff]; rfl
  have hL : Orb.Tame (f ∘ (Prod.fst:Ribs G n r d→_)) := by obtain ⟨C,hC,k,hc⟩:=hf.2; refine ⟨hf.1.comp continuous_fst,C,hC,k,fun x=>?_⟩; change ‖f _‖ ≤ _; grw [hc]; gcongr;exact le_max_left ..
  have hw := price_tame (hall G n r d h) (Orb.Tame.mul hL (spend_A (teams o h) (feed p)))
  rw [hall,mixed, integral_prod (f:=fun x:Ribs G n r d=>f x.fst * spend (teams o h) (feed p) x) hw]; congr 1; funext x
  dsimp only; rw [integral_const_mul]; apply congrArg _; unfold First.line; simp_rw [hi]
  rw [← integral_fintype_prod_eq_prod]
  unfold spend feed; simp only [map_prod]; exact integral_congr_ae (Eventually.of_forall fun y=> Finset.prod_congr rfl fun i _ => money_eq o h (p i) (x,y) i)
lemma stand (p : Players G r d) : ZeroR o h p= Deck.dotF (hall G n r d h) (teams o h) (feed p) := by
  unfold ZeroR; rw [recipe_at,Full.amplitude,normalize_zero]; unfold Deck.dotF; symm
  have H:= court o h p (fun _=>1) (Orb.Tame.constant _); simp_rw [one_mul] at H; rw [H]; unfold First.line First.tube First.lead Full.product; simp only [Finset.prod_apply,map_prod]
end YM.RG11.FirstW.Deck
