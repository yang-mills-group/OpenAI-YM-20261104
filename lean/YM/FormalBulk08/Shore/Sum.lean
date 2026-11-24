import YM.FormalBulk08.Shore.Pal

/-! Pass perturbative gauge identity/connected Ward. DO NOT PASS
scalar constants. Difference two tilings of SAME boundary tensor. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Shore
open Lava Gorge Lattice Laurent Bloch Filter Set Function Wick Lotus Orb Series PowerSeries
open scoped BigOperators Classical ENNReal Topology
variable {I J U : Type*} {r : ℕ} [Fintype I]

def rancho (T : Pap I) (e : ℕ): Veil I:= fun r=> marble r (coeff e T)
-- fixed stage, m copies
abbrev shrink {m n : Side} (p : Pap (Tor (m*n) I)) := PowerSeries.map (MvPolynomial.rename (tray m n)).toRingHom p -- autoimplicit m issue
lemma copying (n : Side) (f : (m:Side)→ Pap (Tor m I)) (g : Pap (Tor n I)) (v : chain (Tor n I) r)
   (e : ℕ) (K : Tile (Biglot I) r) {η : ℝ} (hs : 0<η) (he : Kith η K (fun m=> rancho (f m) e r)) (i : Fin r)
   (ht : ∀ᶠ m in atTop,Up (rancho (f m) e r)) (h : rancho g e r=cum i n K) :
   Tendsto (fun m=> (Fintype.card (Site m):ℝ)⁻¹ * (rancho (shrink (n:=n) (f (m*n))) e r v)) atTop (𝓝 (rancho g e r v)) := by
   obtain ⟨u,C,ha⟩:=he
   rw [h]; refine (pupils_limit n i v hs u ha).congr' ?_
   filter_upwards [(onward n).eventually ht] with m hm
   unfold shrink rancho; rw [coeff_map];change _= _*marble r (MvPolynomial.rename _ _) _;unfold rancho at hm; rw [pebble,core_tally m n i v hm,←mul_assoc]; simp
-- compact criterion rank bound zero at all large r
lemma crema (P : TypeR I) (B : ℕ) (hp : ∀ r, B<r → marble r P=0) : ∑ i ∈ Finset.range (B+1),facade i (marble i P)= P := by
   simp_rw [marble_grade]
   let T:=max P.totalDegree B
   conv_rhs => rw [←cemento P (T+1) (by unfold T;omega)]
   exact Finset.sum_subset (Finset.range_mono (by unfold T; omega)) (fun r _ hr=>by simp only [←marble_grade,hp r (by simp at hr;omega),map_zero])
omit [Fintype I] in
lemma slime (P : Pap I) (a b : I→Pap J) (m : ℕ) :
     coeff m (roam ℝ a P)-coeff m (roam ℝ b P)=(∑ j∈Finset.range (m+1), (coeff m ((insertAt ℝ a (coeff j P) - insertAt ℝ b (coeff j P))*X^j))) := by
   unfold roam; rw [(liquid _ _ m).apex,(liquid _ _ m).apex]; simp only [sub_mul,map_sum,map_sub,Finset.sum_sub_distrib]
lemma lab (m j : ℕ) (a b : I→Pap J) (d : J→₀ℕ) (p : Side→Pap I) (t : Pap I)
    (Q : Side→ℝ) (N : ℕ) (he : ∀ᶠ n in atTop, ∀ l,N<l → marble l (coeff j (p n))=0) (ht : ∀ l,N<l→marble l (coeff j t)=0)
    (h : ∀ r,0<r → ∀ v,Tendsto (fun n=> Q n*marble r (coeff j (p n)) v) atTop (𝓝 (marble r (coeff j t) v))) : -- drop e, v_rank→0<
    let f(F:TypeR I) := MvPolynomial.coeff d (coeff m ((insertAt ℝ a F-insertAt ℝ b F)*X^j));
    Tendsto (fun n=> Q n * f (coeff j (p n))) atTop (𝓝 (f (coeff j t))) := by
   intro f
   have hf (P : TypeR I) (H : ∀ l,N<l→ marble l P=0) : f P = ∑ i∈ (Finset.range (N+1)).erase 0,∑ v:chain I i, marble i P v * f (cards v) := by
      have hz F G : f (F+G)=f F+f G := by unfold f; rw [map_add,map_add,add_sub_add_comm,add_mul,map_add,MvPolynomial.coeff_add]
      let F : TypeR I →+ ℝ:={toFun:=f,map_add':=hz,map_zero':=by simp [f]}
      have hu l (A : Tile I l) : f (facade l A)=∑ v:chain I l,A v * f (cards v):= by
         change F (facade l A)= _; rw [facade_eq,map_sum]; apply Finset.sum_congr rfl; intro v _
         change f _=_; unfold f; simp only [_root_.map_mul, insert_C,←mul_sub, mul_assoc]; rw [coeff_C_mul];simp
      have hF : f (facade 0 (marble 0 P))=0:=by unfold f;rw [marble_grade,MvPolynomial.homogeneousComponent_zero];simp
      change F P=_; nth_rw 1 [←crema P N H]; rw [map_sum,← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : 0<N+1)),show F _=_ from hF,zero_add];exact Finset.sum_congr rfl fun i _=> hu i _
   rw [hf _ ht];
   refine (tendsto_finsetSum _ (f:=fun i n=>∑ v:chain I i,(Q n * marble i (coeff j (p n)) v)*f (cards v)) (fun i hi=> tendsto_finsetSum _ (fun v _=> ((h _ (Nat.pos_of_ne_zero (Finset.mem_erase.mp hi).1) v).mul_const _)))).congr' ?_
   filter_upwards [he] with n hn; rw [hf _ hn]; simp_rw [Finset.mul_sum,mul_assoc]; -- make comp
end YM.FormalBulk08.Shore
