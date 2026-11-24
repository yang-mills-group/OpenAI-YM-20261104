import YM.GradedFar.Growth.Degree

/-! # Compact steps (uniform) and charges for each formal iteration -/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open Continuation
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d : ℕ} {I J E : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
local notation "ψ"=> GroupS.ψ N.criterion M ν
local notation "K"=> Kseries N M
open MS.Book.Program

def bend (s : ℝ) (p : ℕ) (t : ℂ) := blend (tells (GroupS.ψ N.criterion M (Teller.logNu 1) (-s))) p t
def crank (d : ℕ) (s : ℝ) (p : ℕ) (t : ℂ) := blend (names (Kseries N M d (-s))) p t
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H
variable (Q : Loft G I) (s : I → ℝ) (hs : Q.Mid s)
local notation "W"=> Q.board simple
variable (t : I→ℂ) (ht : Bill (Q.board simple) 1 0 t) (z : I → ℝ) (hz : Q.Mid z)

include ht hs
lemma bend_paid (p : ℕ) : Bill W 1 0 (fun i=>bend N M (s i) p (t i)) := by
  unfold bend blend; refine Bill.sum _ fun j hj=>?_ ; by_cases h0:j=0
  · subst j; simp_rw [tells,(tendsK N M H _).start, smul_zero]; exact Bill.from_zero W
  apply (?_ : Bill W 1 (0+0) _).mono_fee (by simp) le_rfl
  exact product_scalar _ ((Stock.powers W t ht j).mono_fee le_rfl (by omega : 1≤j)) (clock_terms N M H Q hs j) -- 1+0 defeq
lemma crank_paid (p d : ℕ) : Bill W 0 (-(d:ℝ)) (fun i=> crank N M d (s i) p (t i)) := Stock.cost W t ht
  (show Stock W p (-(d:ℝ)) (fun i=> names (K d (-s i))) from fun j _=> engine_terms N M H Q hs j d)

omit ht hs in
lemma lofty {p : ℕ} {a : ℝ} [NormedAddCommGroup E] {x : I → E} (h : Bill W p a x) (hv : 0 < p+Q.B*a) :
    Tendsto x Q.path (𝓝 0) := by
  cases H
  obtain ⟨C,hC,k,h⟩:= h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr; intro y hy; let c:=2*C/y; have hc : 0<c:= div_pos (by positivity) hy
  filter_upwards [h, Q.eventual_power simple (p:=p) (q:=0) (a:=a) (by exact_mod_cast hv) k c hc] with i h hi
  rw [pow_zero] at hi; rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  have he : C* (gYM G (Q.r i))^p * post a (Q.height i) k = y/2*(c*gYM G (Q.r i)^p*post a (Q.height i) k) := by unfold c; field_simp
  apply lt_of_le_of_lt h; change C*gYM G (Q.r i)^p*post a (Q.height i) k < _
  rw [he]; nlinarith only [hy,hi]

include hz
lemma relay_clock (p : ℕ) : Bill W (p+1) 0 (fun i=> bend N M (z i) p (bend N M (s i) p (t i)) - bend N M (s i+z i) p (t i)) := by
  simp_rw [bend,Lclock N M H , composition_tells _ _ (tendsK N M H _|>.start)]
  apply Stock.chopped (x:=fun i=> ψ (-s i)) W (p:=p) (fun j _=> clock_terms N M H Q hs j) (fun i=>(tendsK N M H _).start) t ht (y:=fun i=> tells (ψ (-z i)))
  intro j _; exact clock_terms N M H Q hz j
lemma relay_frame (p d : ℕ) : Bill W (p+1) (-(d:ℝ) + -(d:ℝ)) (fun i=> crank N M d (s i) p (t i)*crank N M d (z i) p (bend N M (s i) p (t i)) - crank N M d (s i+z i) p (t i)) := by
  let a i:=names (K d (-s i)); let b i:= names (K d (-z i)); let c i:=Program.substitute (ψ (-s i)) (b i)
  have hx : Stock W p _ (fun i=>tells (ψ (-s i))) := fun j _=> clock_terms N M H Q hs j
  have ha : Stock W p _ a:= fun j _=> engine_terms N M H Q hs j d
  have hb : Stock W p _ b:= fun j _=> engine_terms N M H Q hz j d
  have he := product_fe _ (crank_paid N M H Q s hs t ht p d) (Stock.chopped W hx (fun i=> (tendsK N M H _).start) t ht hb)
  rw [zero_add] at he; simp_rw [crank,bend] at *
  simp_rw [Lframe N M H,revenue_names,composition_names]
  refine (he.plus (Stock.past W t ht ha (Stock.charged W hx hb))).apply_eq (Eventually.of_forall fun i=>?_)
  unfold a b; rw [mul_sub]; abel
end
end YM.FVA2.GradedFar.Growth
