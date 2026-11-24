import YM.RG11Proof.Rigidity.Hivolt
import YM.RG11Proof.Rigidity.Prism.Averages

/-!
# Resolve spherical averages of top terms in the word deficit
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Prism
open scoped BigOperators Topology InnerProductSpace Classical
open Maxwell Maxwell.Free Function Set MeasureTheory Crowd

variable {G : Gauge}
abbrev Mirror (G : Gauge):=Desk (G.ColorIndex×G.ColorIndex)

-- Sampling frame, columns variable and variation independent of G matrices.
def wind (Θ : G.ColorIndex→Stream) (p : Pig G) : Mirror G := WithLp.toLp 2 fun t=>conduit (Θ t.2) t.1 p
lemma wind_price (Θ : G.ColorIndex→Stream) (p q : Pig G) : inner ℝ (wind Θ p) (wind Θ q)=dial Θ p q := by
  rw [PiLp.inner_apply,Fintype.sum_prod_type,Finset.sum_comm]
  unfold dial; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> (mul_comm ..)

lemma dial_wind (M : Mirror G) (Θ:G.ColorIndex→Stream) (p : Pig G) :
    inner ℝ (wind Θ p) M=∑ s:G.ColorIndex,M (p.dart.tone,s)*p.dart.mode (Θ s p.origin p.dart.degree) := by
  rw [PiLp.inner_apply,Fintype.sum_prod_type,Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  change (∑ s:G.ColorIndex, M (s,i)* (if p.dart.tone=s then _ else 0))=_; simp [mul_ite]

def airRaw (M : Mirror G) (Θ:G.ColorIndex→ Stream) (p : Word G) := hue (List.map (wind Θ) p) M
def air (M : Mirror G) (Θ:G.ColorIndex→ Stream) (N : ℕ) (p : Word G) := if cargo p=N then airRaw M Θ p else 0
lemma air_cont (Θ:G.ColorIndex→ Stream) (N : ℕ) (p : Word G) : Continuous (fun M=>air M Θ N p) := by
  unfold air airRaw; split_ifs; exact hue_cont _; exact continuous_const

lemma air_pay (i : G.ColorIndex)(Θ:G.ColorIndex→ Stream)(N : ℕ) (p : Word G) (hL : cargo p≤N) :
    (∫ M in circle (G.ColorIndex × G.ColorIndex), air M Θ N p)= ∑ m∈Finset.range (N+1),pace (i,i) m * roll N m Θ p := by
  have H : List.length p ≤ N := le_trans ?_ hL
  rotate_right
  · clear hL; induction p with
    | nil=> exact le_rfl
    | cons a p ih=> rw [cargo_step]; simp only [List.length_cons]; unfold weightF; omega
  by_cases hc : cargo p=N; swap
  · simp [air,hc,roll]
  unfold air airRaw; simp_rw [if_pos hc]
  change tour (List.map (wind Θ) p)= _
  by_cases ho : List.length p % 2 = 1
  · have hp : (List.map (wind Θ) p).length=2*(List.length p / 2)+1:=by rw [List.length_map]; omega
    rw [odd_meter _ _ hp]
    have hh (m:ℕ): roll N m Θ p=0:=if_neg (fun h=>by omega)
    simp [hh]
  let m := List.length p/2
  have hp : List.length p=2*m:=by unfold m; omega
  rw [sheet_meter (i,i) m _ (by rw [List.length_map]; exact hp),Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))]
  · rw [roll,if_pos ⟨hc,hp⟩,pair_transfer]
    congr 2; funext x y; exact wind_price ..
  intro d hd he; unfold roll; rw [if_neg (fun h=>by omega)]; ring

/-- Equality of all top feature-product moments on the full frame matrix
box rotated to a ball. -/
theorem fatal (c : G.ColorIndex) {S : Finset E4} {W : Crowd G} (h : Blind S W) (N : ℕ) (hN : ∀ t∈W,cargo t.2 ≤ N) (Θ : G.ColorIndex→Stream):
    (∫ M in circle (G.ColorIndex × G.ColorIndex), W.asks (air M Θ N))=0 := by
  have ht (W : Crowd G) (hN : ∀ t∈W,cargo t.2 ≤ N) :
    (∫ M in circle (G.ColorIndex × G.ColorIndex), W.asks (air M Θ N))= W.asks (fun p=>∑ m∈Finset.range (N+1),pace (c,c) m*roll N m Θ p) := by
    induction W with
    | nil=> simp
    | cons a W ih=>
      simp_rw [ask_one]
      rw [integral_add, integral_const_mul,air_pay c Θ N _ (hN a (List.mem_cons_self ..)), ih (fun t ht=> hN t (List.mem_cons_of_mem a ht))]
      · exact ((air_cont ..).continuousOn.integrableOn_compact (isCompact_closedBall ..)).const_mul _
      suffices he : Continuous (fun M=> asks W (air M Θ N)) from he.continuousOn.integrableOn_compact (isCompact_closedBall ..)
      clear hN ih
      induction W with
      | nil=>exact continuous_const
      | cons a l ih=>simp_rw [ask_one]; exact (continuous_const.mul (air_cont ..)).add ih
  rw [ht W hN,ask_sum]; apply Finset.sum_eq_zero; intro i _
  rw [ask_mul,privilege c h _ hN _,mul_zero]

end YM.RG11.Rigidity.Prism
