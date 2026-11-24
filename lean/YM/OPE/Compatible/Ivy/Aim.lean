import YM.OPE.Compatible.Ivy.Nic
/-!
# Tape rebases through P.search. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E:Type} [Fintype I][Fintype J] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable {t c f:Side}{k m d e n:ℕ}{p:Phase}{s:Meeting}{S:Story I}
def moveC (A:Cross t I J)(x:Cover)(P:Curtain I):Curtain J:=fun i=> countermove A x (P i)
def moveS (A:Cross t I J)(x:Cover)(P:Spring I):Spring J:=fun i=>moveC A x (P i)
def costD (I:Type)[Fintype I](r d:ℕ)(b a:ℝ)(N:ℕ) :ℝ:= ∑ i∈Finset.range (N+1), max 0 (regionB I a b r i d)
lemma costD0 (I:Type)[Fintype I](r d:ℕ)(b a:ℝ)(N:ℕ):0 ≤ costD I r d b a N:=sum_nonneg fun _ _=> le_max_left ..
lemma leastD {a b:ℝ}(p q:ℕ)(h:k≤n): regionB I a b p k q ≤ costD I p q b a n:= (le_max_right ..).trans (single_le_sum (s:=Finset.range (n+1)) (f:=fun j=>max 0 (regionB _ _ _ _ j q)) (fun i _=>le_max_left ..) (mem_range.mpr (by omega)))
omit [Fintype I][Fintype J] in lemma lite0 (A:Cross t I J)(x:Cover): countermove A x (0: Script I k)=0:=by funext i; simp [countermove]
omit [Fintype I] in lemma moveP (A:Cross t I J)(x:Cover)(P:Curtain I)(a b c:ℝ)(m n:ℕ)(hp: A.strip a b)(ha:0<a)(hx: Volume P n m c)(K:ℕ)(hk:n ≤ K): Volume (moveC A x P) n m (c*costD J (size x) m b a K):=by
     have he(i)(hi:n < i): moveC A x P i=0:=by unfold moveC; rw [hx.1 i hi,lite0]
     have hv:0 ≤ c:= Sack.coins (hx.2 0); refine ⟨he,fun i=>?_⟩; by_cases h:i ≤ n
     · exact (counterflow hp ha (P i) x (hx.2 i)).tips (mul_le_mul_of_nonneg_left (leastD _ _ (h.trans hk)) hv)
     rw [he i (lt_of_not_ge h)]; exact Sack.zero (mul_nonneg hv (costD0 ..)) _
omit [Fintype I] in lemma rebound (A:Cross t I J)(x:Cover)(P:Spring I)(a b c:ℝ)(m n:ℕ)(hp:A.strip a b)(ha:0<a)(hx:Tide P n m c): Tide (moveS A x P) n m (c*costD J (size x) m b a (n+2)):=fun i=> moveP A x _ _ _ _ _ _ hp ha (hx i) _ (Nat.add_le_add_left (Nat.le_of_lt_succ i.isLt) _)
omit [Fintype I]
lemma convent (r:Ratio c f)(A:Cross r.count I J)(b:Cover)(P: Curtain I)(u:deck J c)(p:Site c)(d:ℕ)(h: Bins P)(ha:Whole A): Flair (moveC A b P) d u p= Flair P d ((installed r A)*ᵥ u) (r.embed p+wrap f b):=Finset.sum_congr rfl fun i _=>bridge_torque ha p b (P i) (h i) _
lemma movedV (r:Ratio c f)(A:Cross r.count I J)(b:Cover)(P:Spring I)(u:deck J c)(p: Site c)(d:ℕ)(h:∀ i,Bins (P i))(ha:Whole A): go (moveS A b P) d u p=go P d ((installed r A)*ᵥ u) (r.embed p+wrap f b):=by apply JetS.eta <;>first | exact convent r A b _ _ _ _ (h 0) ha| exact convent r A b _ _ _ _ (h 1) ha| exact convent r A b _ _ _ _ (h 2) ha
end YM.OPE.Libra.Char
