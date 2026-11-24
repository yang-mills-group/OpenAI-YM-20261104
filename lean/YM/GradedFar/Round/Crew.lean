import YM.GradedFar.Physical.Away
import YM.FVA2.DerivD.Picture

/-!
# Formal point profiles in the given angular convention
 Budget shape (r-scaled first gradient before moving estimate) from Main.Match's
 genuine formal prescription, using FVA2.DerivD picture.
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h t : ℕ} {I:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
include H
variable {K:Set (Points n)}{S:Set (Points m)}(hK:IsCompact K)(hk:K⊆conf n)(hS:IsCompact S)(hs:S⊆ Outside m)
local notation "Ω"=>ordinary N
local notation "P"=>DerivD.exchangeP N M ν
lemma esteemed : DerivD.Influence P (ordinary N):=(DerivD.glory_X ν H.details.toServed.toPosted.toQuoted.toContract).parameter
lemma book_basis (a:Choices G (fun _:Fin n=>h))(x:Points n):
    boundary N (basisInputs a) x=ordinary N n x (roll a) := by
    unfold ordinary; by_cases hx:x∈conf n
    · rw [caring _ (d:=h) (fun i=> size_le (a i)) (H.separatedOPE ν).wilson.dimensions hx]; unfold boundary Jury.fxt; rw [dif_pos hx]; rfl
    unfold boundary Jury.fxt; rw [dif_neg hx,standardized _ _ _ hx]; ext i; unfold shop Reg.Point.story; simp
local notation "Γ"=>Choices G (fun _:Fin n=>h)
lemma teller_spells (a:Tags G h n)(x:Points n):
    boundary N a x=∑ j:Choices G (fun _:Fin n=>h), PowerSeries.C (combo a j)*ordinary N n x (roll j) := by
    ext i; rw [map_sum]; simp_rw [coeff_C_mul,← book_basis N M H]; unfold boundary shop Reg.Point.story; simp_rw [coeff_mk]; exact basis_spelling _ a

def ranker (j:ℕ) (a:Tags G h n) := fun x:Points n=> coeff j (boundary N a x)
lemma smooth_sail (j:ℕ) (a:Tags G h n){x:Points n}(hx:x∈conf n) :
    DifferentiableAt ℝ (ranker N j a) x := by
    unfold ranker; simp_rw [teller_spells N M H,map_sum,coeff_C_mul]; exact DifferentiableAt.fun_sum fun i _=> (((esteemed N M H) _ x hx (roll i) j).differentiableAt.const_mul _)
abbrev XSet (K:Set (Points n))(S:Set (Points m)):=↥K × ↥S
abbrev flute (i:XSet K S)(s:ℝ):= forest i.1.val (squeeze (-s) i.2.val)
include hK hk hS hs
lemma glory_value (u:Scan G (n+m))(p:ℕ) : Rain 0 (fun (i:XSet K S) s=> coeff p (ordinary N (n+m) (flute i s) u)) := by
    have hQ:u=Fin.append (u ∘ Fin.castAdd m) (u ∘ Fin.natAdd n):= by funext i; induction i using Fin.addCases <;> simp
    rw [hQ]; exact ((full_fare H _ _ hK hk hS hs p 0) p (Nat.lt_succ_self p)).size (by positivity)
local notation "Xₚ"=>XSet K S
lemma revenue (a:Tags G h (n+m))(p:ℕ) : Rain 0 (fun (i:XSet K S) s=>ranker N p a (flute i s)) := by
    unfold ranker; simp_rw [teller_spells N M H,map_sum,coeff_C_mul]
    exact Rain.sum Finset.univ fun i _=> Rain.scalar (glory_value N M H hK hk hS hs (roll i) p) _
omit H hK hk hS hs in
lemma shapes {E F:Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F]
    (A:E→L[ℝ] F){x:I→ℝ→E}{a:ℝ}(h:Rain a x) : Rain a (fun i s=> A (x i s)):= by
    obtain ⟨C,hC,k,h⟩:=h; refine ⟨(1+‖A‖)*C,by positivity,k,?_⟩
    filter_upwards [h,eventually_ge_atTop (0:ℝ)] with s h hs i
    apply ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h i) (norm_nonneg A))).trans
    rw [mul_assoc]; gcongr; first|exact mul_nonneg hC.le (post_at hs).le| exact le_add_of_nonneg_left zero_le_one
omit H hK hk hS hs in
private lemma der {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](f:E→ℂ)(x:E→L[ℝ] ℂ)(t:E) (ht:HasFDerivAt f x t): fderiv ℝ f t=x:= ht.fderiv
omit H hK hk hS hs in
private lemma derived {p:Scan G n}{A:Album G} {S:DerivD.Staff G}{t:Points n} (H:DerivD.Influence S A) (ht:t∈conf n) (k:ℕ) : fderiv ℝ (fun q=> coeff k (A n q p)) t= DerivD.Γ S (A n t) p k:= by
    have hh : HasFDerivAt (fun q=>coeff k (A n q p)) (DerivD.Γ S (A n t) p k) t:= H _ _ ht p k; exact der _ _ _ hh
omit H hK hk hS hs in
private lemma inf_diff {p:Scan G n}{A:Album G} {S:DerivD.Staff G}{t:Points n} (H:DerivD.Influence S A)(ht:t∈conf n)(k:ℕ): DifferentiableAt ℝ (fun q=>coeff k (A n q p)) t:= (H n _ ht p k).differentiableAt
omit H hK hk hS hs in
private lemma rain_eq {E:Type} {f gx:I→ ℝ→ E} [NormedAddCommGroup E](hf: Rain 0 f)(h: ∀ᶠ r in atTop,∀ i,gx i r=f i r): Rain 0 gx:=by
     exact Rain.raise hf (h.mono fun r h i=> (congrArg norm (h i)).le)

set_option maxHeartbeats 600000 in
lemma gradient_price (u:Scan G (n+m))(p:ℕ) : Rain 0 (fun (i:Xₚ) s=> fderiv ℝ (fun x=>coeff p (Ω _ x u)) (flute i s)) := by
    have hh (v:Fin (n+m))(j:Axis): Rain 0 (fun (i:Xₚ) s=> coeff p (DerivD.Raise P v j u (Ω _ (flute i s)))) := by
        unfold DerivD.Raise; simp_rw [LinearMap.coe_mk,AddHom.coe_mk,map_sum,coeff_mul]; apply Rain.sum; intro i _
        exact Rain.sum _ (fun k _=> Rain.scalar (glory_value N M H hK hk hS hs _ k.2) _)
    apply rain_eq (f:=fun (i:Xₚ) s=> DerivD.Γ P (Ω _ (flute i s)) u p)
    · unfold DerivD.Γ; exact Rain.sum _ (fun i _=> Rain.sum _ (fun j _=> shapes (DerivD.italy i j) (hh i j)))
    filter_upwards [eventually_conf hK hk hS hs] with s h i
    exact derived (t:=flute i s) (esteemed N M H) (h.1 _ i.1.property _ i.2.property) p
lemma rate (a:Tags G h (n+m))(p:ℕ) : Rain 0 (fun (i:XSet K S) s=> fderiv ℝ (ranker N p a) (flute i s)) := by
    let L (i:Choices G (fun _:Fin (n+m)=>h))(x:Points (n+m)):=coeff p (Ω _ x (roll i))
    have hf : ranker N p a=fun x=> ∑ j:Choices G (fun _:Fin (n+m)=>h), combo a j * L j x := by funext x; unfold ranker; rw [teller_spells N M H,map_sum]; simp_rw [coeff_C_mul]; rfl
    rw [hf]; apply rain_eq (f:=fun (i:Xₚ) (s:ℝ)=> ∑ j:Choices G (fun _:Fin (n+m)=>h), (combo a j) • fderiv ℝ (L j) (flute i s))
    · apply Rain.sum; intro i _; -- continuous real linear from smul
      exact shapes ((combo a i) • ContinuousLinearMap.id ℝ _) (gradient_price N M H hK hk hS hs (roll i) p)
    filter_upwards [eventually_conf hK hk hS hs] with s h i
    have he j : DifferentiableAt ℝ (L j) (flute i s) := inf_diff (t:=flute i s) (esteemed N M H) (h.1 _ i.1.property _ i.2.property) p
    rw [fderiv_fun_sum (fun j _=> (he j).const_mul _)]; apply Finset.sum_congr rfl; intro j _; exact der _ _ _ (((he j).hasFDerivAt).const_mul (combo a j))
end
end YM.FVA2.GradedFar.Physical.Round
