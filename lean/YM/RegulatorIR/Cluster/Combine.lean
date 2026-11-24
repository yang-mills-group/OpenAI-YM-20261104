import YM.RegulatorIR.Cluster.Extend
import YM.RegulatorIR.Diagram.Linear

/-! Compose outputs of independent heat, against the output for composite
mark. Subtraction sees only linearly the equation on the gap. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Finset Function Budget Budget.Packet Budget.Layer Budget.Tuple Diagram Filter
open scoped Topology BigOperators Classical ENNReal
variable {X Y:Type} {r s a b k e p:ℕ} {M:Tariff X} {t:ℝ≥0∞}{K:Layer X X}

lemma speeds (T:Orders X)(V: Rhythm X) (K:Layer X X) : metron (markHeat K V T)=Root (markHeat K V T) V K:=by
 ext1 k;ext1 e;ext1 r; rw [metron,Pi.smul_apply, markHeat_next, smul_smul,mul_inv_cancel₀ (by positivity : (k:ℝ)+1≠0),one_smul];rfl
lemma loop_minus (T U:Packet X (r+2)) (h:quota T 1≠⊤)(hh:quota U 1≠⊤)(hp:height K t)(ht:t≠⊤) : loop (T-U) K=loop T K-loop U K:=by
 ext1 z; rw [Pi.sub_apply,loop,loop,loop,← (loop_sums T z h hp ht).tsum_sub (loop_sums U z hh hp ht)]
 apply tsum_congr;intro x; rw [curve,curve,curve,Pi.sub_apply,mul_sub]
lemma knot_minus (T U:Packet X (r+1))(V:Packet X (s+1))(h:quota T 1≠⊤)(hh:quota U 1≠⊤)(hm:Enough V)(hp:row K M id id t)(ht:t≠⊤) : knot K (T-U) V = knot K T V -knot K U V:=by
 ext1 z
 have H:= knot_sums T V h hm hp ht z; have Q:= knot_sums U V hh hm hp ht z
 rw [Pi.sub_apply,knot_price T V K z H, knot_price U V K z Q,knot_price (T-U) V K z (knot_sums (T-U) V (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨h,hh⟩) (quota_sub ..)) hm hp ht z),← H.tsum_sub Q]
 apply tsum_congr;intro x; rw [lesson,lesson,lesson,Pi.sub_apply,sub_mul]
lemma match_minus (T U V:Ranked X)(u:ℕ×ℕ)(h:u.1+u.2=r)(he:quota (T (u.1+1)) 1 ≠ ⊤)(hx:quota (U (u.1+1)) 1≠⊤)(ht:Enough (V (u.2+1)))(hh:row K M id id t)(hm:t≠⊤) : matchTwo K (T-U) V r u=matchTwo K T V r u-matchTwo K U V r u:=by
 rw [← h]; simp only [matchTwo, ↓reduceDIte]; rw [Pi.sub_apply,knot_minus _ _ _ he hx ht hh hm,symmetry_sub,smul_sub]
lemma root_minus {T U V:Rhythm X}(h:Price T p)(hh:Price U p)(hv:Cost V p)(ht:row K M id id t)(hα:t≠⊤)(he:e≤p) : Root (T-U) V K k e= Root T V K k e - Root U V K k e:=by
 ext1 r; rw [Pi.sub_apply,Root,Root,Root,heating,heating,heating]
 change _ • symmetry (loop (T k e (r+2)-U k e (r+2)) K)+_= _
 rw [loop_minus _ _ (h k e he _) (hh k e he _) (row_to_sup ht) hα,symmetry_sub,smul_sub,add_sub_add_comm]
 apply congr_arg
 unfold drift carry force; rw [← sum_sub_distrib]; apply Finset.sum_congr rfl;intro i _
 rw [← sum_sub_distrib]; apply Finset.sum_congr rfl; intro j hj; rw [← sum_sub_distrib];apply Finset.sum_congr rfl; intro b hb;have hP:=mem_antidiagonal.mp hj; exact match_minus (T i.1 j.1) (U i.1 j.1) (V i.2 j.2) b (mem_antidiagonal.mp hb) (h _ _ (by omega) _) (hh _ _ (by omega) _) (hv i.2 j.2 (by omega) _) ht hα

def clash (T U:Orders X)(V: Rhythm X)(K:Layer X X) : Rhythm X := markHeat K V (accord T U) - composeT (markHeat K V T) (markHeat K V U)
lemma crest (T U:Orders X)(V: Rhythm X)(K:Layer X X) : clash T U V K 0=0:=by
 ext1 i;ext1 r; unfold clash; simp_rw [Pi.sub_apply,markHeat_first K V (accord T U)];simp [composeT,markHeat_first]
lemma wave {T U:Orders X}{V:Orders X}{f:Bool} (h: Vacuum V)(hs:gradedSymmetric V)(hm:∀ e,Within (e+a) (T e))(hh:∀ e,Within (e+b) (U e))(ht:gradedSymmetric T)(hu:gradedSymmetric U)(hK:∀ i j,K i j=K j i)(hx:row K M id id t)(hα:t≠⊤)(he:e≤p) : let Q:=logHeat K V f; let F:=markHeat K Q T; let G:= markHeat K Q U; Price F p → Price G p→ Price (markHeat K Q (accord T U)) p → Cost Q p → metron (clash T U Q K) k e=Root (clash T U Q K) Q K k e+ drift K F G k e:=by
 intro Q F G hF hG hT hQ; let P:=markHeat K Q (accord T U); let W:=composeT F G
 have hP:metron P=Root P Q K:=speeds _ Q K
 have H:= timeMark K V T h hm ht f; have H':= timeMark K V U h hh hu f
 have hp:metron W=composeT (Root F Q K) G+composeT F (Root G Q K) := by
   unfold W F G; rw [Brief.drafting H H',speeds T, speeds U]
 have hg : Root W Q K k e=metron W k e + drift K F G k e:=by
   rw [hp]; exact Ito_atom hQ hF hx hα H H' (timeVac V h hs f) hG hK k e he
 change metron (P-W) k e= Root (P-W) Q K k e+_
 rw [root_minus hT (price_product F G hF hG) hQ hx hα he, ← hP,hg]
 change (k+1:ℝ) • (P (k+1) e-W (k+1) e) = _ -((k+1:ℝ) • W (k+1) e + _) + _
 rw [smul_sub]; change _= ((k+1:ℝ) • P (k+1) e- _)+_; abel
end YM.RegulatorIR.Cluster
