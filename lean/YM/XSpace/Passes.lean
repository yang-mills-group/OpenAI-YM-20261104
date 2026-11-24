import YM.XSpace.Felicity
/-!
# Angular divergence modulo two priced slots
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Gland
open Function Set Filter Relief Sail Lattice Trace Chart2 Outline Mu Chiral
open scoped Topology BigOperators Classical
variable {G:Gauge} (t:Axis)
local notation "W"=> G.ColorIndex
local notation "L"=> Axis × G.ColorIndex -- product
local notation "τ"=> hike t
local notation "P"=> Trace.volume (step t)
local notation "ΦΦ"=> Stamp G -- not ΦΦ? test
local notation "T"=> av
private lemma turnover (a:Stamp G): P a=a+τ a:=by change P a=a+(P a-a); abel
lemma alcove (i j k:L) : let a:= T i.1 i.2; let b:= T j.1 j.2; let c:= T k.1 k.2;
  τ (a*b*c) - (τ a*b*c+τ b*c*a+ τ c*a*b) ∈ More G:=by
  intro a b c; have ht(a b c:ΦΦ)(ha:a∈stem G 1)(hb:b∈stem G 1)(hc:c∈stem G 0): a*b*c∈ More G:= Submodule.mul_mem_mul (Submodule.mul_mem_mul ha hb) hc
  have hp:τ (a*b*c)= (a+τ a)*(b+τ b)*(c+τ c)-a*b*c:=by change P _-_= _; rw [map_mul,map_mul,turnover t a,turnover t b,turnover t c]; rfl
  rw [hp,show (a+τ a)*(b+τ b)*(c+τ c)-a*b*c-(τ a*b*c+τ b*c*a+τ c*a*b)=τ a*τ b*c+τ a*τ c*b+τ b*τ c*a+τ a*τ b*τ c from by ring]; have h:a∈ stem G 0:= lost _; have h': b∈stem G 0:= lost _; have hh:c∈stem G 0:=lost _; have ha:τ a∈ stem G 1:=hikes t _ i.2; have hb:τ b∈stem G 1:=hikes t _ j.2; have hc:τ c∈stem G 1:=hikes t _ k.2; exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (ht _ _ _ ha hb hh) (ht _ _ _ ha hc h')) (ht _ _ _ hb hc h)) (ht _ _ _ ha hb (k₁ hc))
private abbrev Ψ (a:L) := av a.1 a.2
private def loop (a b c:L):ℂ:= omega t a.1 b.1 c.1*(↑(br a.2 b.2 c.2):ℂ)
private def tick (a b c:L):ΦΦ := loop t a b c • (Ψ a * Ψ b * Ψ c)
def turnip (t:Axis)(G:Gauge): Stamp G:=∑ a:Axis×G.ColorIndex,∑ b:Axis×G.ColorIndex,∑ c:Axis×G.ColorIndex,tick t a b c
private lemma orbit (a b c:L): loop t a b c=loop t b c a:=by unfold loop omega; rw [br_turn a.2 b.2, e₂ t a.1 b.1 c.1,e₃ t b.1 a.1 c.1,neg_neg]
private def vane (a b c:L):ΦΦ := loop t a b c • (τ (Ψ a) * Ψ b* Ψ c)
def stepDown (t:Axis)(G:Gauge): Stamp G:= ∑ a:Axis×G.ColorIndex,∑ b:Axis×G.ColorIndex,∑ c:Axis×G.ColorIndex,vane t a b c
private lemma proclivity (a b c:L): τ (tick t a b c) - (vane t a b c+ vane t b c a+vane t c a b) ∈ More G:=by
  unfold tick vane; rw [map_smul,← orbit t a,orbit t c a b, ← smul_add, ← smul_add,← smul_sub]; exact Submodule.smul_mem _ _ (alcove t a b c)
private lemma orbit_sum (F:L→L→L→ΦΦ ) : (∑ i:L,∑ j:L,∑ k:L,F i j k)=∑ i:L,∑ j:L,∑ k:L,F j k i:=by
  conv_rhs=> rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _=>?_ ; rw [Finset.sum_comm]
lemma proclaimed : τ (turnip t G)-(3:ℂ) • stepDown t G∈ More G :=by
  let f:=vane t (G:=G); have hF(a b c):= proclivity t (G:=G) a b c; rw [show (3:ℂ) • stepDown t G= (∑ i:L,∑ j:L,∑ k:L,f i j k) + (∑ i:L,∑ j:L,∑ k:L,f j k i)+(∑ i:L,∑ j:L,∑ k:L,f k i j) from ?_]; swap; · rw [show (∑ i:L,∑ j:L,∑ k:L,f k i j)=_ from orbit_sum (fun i j k=> f k i j), ← orbit_sum f]; change (3:ℂ) • _ = stepDown ..+stepDown ..+stepDown ..; module
  unfold turnip; simp_rw [map_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]; exact Submodule.sum_mem _ fun i _=> Submodule.sum_mem _ fun j _=> Submodule.sum_mem _ fun k _=> hF i j k
lemma payable (t:Axis)(G:Gauge): turnip t G∈ Trio G 0 0 0:= by unfold turnip; apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _; apply Submodule.sum_mem; intro k _; exact Submodule.smul_mem _ _ (Submodule.mul_mem_mul (Submodule.mul_mem_mul (lost _) (lost _)) (lost _))
lemma course (G:Gauge): polyArc G=∑ t:Axis,stepDown t G:=by
  let F (a b c d:Axis)(i j k:G.ColorIndex):= vane a (b,i) (c,j) (d,k); have h(a b c d:Axis)(i:G.ColorIndex): arc a b c d i=∑ j:G.ColorIndex,∑ k:G.ColorIndex,F a b c d i j k:=by unfold arc mode Stk F vane loop; simp only [Finset.mul_sum, Finset.smul_sum,mul_smul_comm,mul_smul, mul_assoc]
  unfold polyArc stepDown; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm (s:=(Finset.univ:Finset G.ColorIndex)), Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro i _; simp_rw [h]; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro c _; rw [Finset.sum_comm (s:=(Finset.univ:Finset Axis))]; apply Finset.sum_congr rfl; intro j _; rw [Fintype.sum_prod_type]
def Mute (G:Gauge) : Levee G := More G ⊔ ⨆ t:Axis,(Trio G 0 0 0).map (hike t)
lemma pulse₁ (G:Gauge): propArc G ∈ Mute G:=by
  have he:(2:ℂ) • propArc G∈Mute G:=by
    rw [← collects,course]; apply Submodule.sum_mem; intro t _; rw [← inv_smul_smul₀ (x:=stepDown t G) (a:=(3:ℂ)) (by norm_num)]; apply Submodule.smul_mem; rw [← sub_sub_self (hike t (turnip t G)) ((3:ℂ) • stepDown t G)]; exact Submodule.sub_mem _ (((le_sup_right : (⨆ t:Axis,(Trio G 0 0 0).map (hike t)) ≤ Mute G)) (le_iSup (fun i:Axis=> (Trio G 0 0 0).map (hike i)) t (Submodule.mem_map_of_mem (payable t G)))) ((le_sup_left: More G ≤ Mute G) (proclaimed t)) -- fill
  rw [← inv_smul_smul₀ (x:=propArc G) (a:=(2:ℂ)) (by norm_num)]; exact Submodule.smul_mem _ _ he
theorem flung (G:Gauge): (∑ p:PlaqAxes,V3 G (tile p))- farMinus G∈Mute G:=by rw [← sub_add_sub_cancel _ (∑ i:PlaqAxes, εglows i G) _,← Finset.sum_sub_distrib, reward]; exact Submodule.add_mem _ ((le_sup_left: More G ≤ Mute G) (Submodule.sum_mem _ (fun i _=>incurred i))) (pulse₁ G)
end YM.XSpace.Gland
