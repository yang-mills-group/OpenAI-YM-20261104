import YM.XSpace.Canary
/-!
# Primitive units at Wick mark anchors
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Graph3
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Structure1 Chiral Finsupp MvPolynomial Mu Next.Rank.Normal Stall Pages Source Foundation
open scoped Topology BigOperators RealInnerProductSpace Classical
variable {G:Gauge}
def Tint (c:G.ColorIndex): Submodule ℝ (Line G):= Submodule.span ℝ {u|∃ t:Edge Cover,u=needle (t,c)}
lemma tone (x:Edge Cover)(c:G.ColorIndex): needle (x,c)∈ Tint c:= Submodule.subset_span ⟨x,rfl⟩
lemma tint_walk {c:G.ColorIndex}{a:Line G}(h:a∈Tint c)(x:Cover): displace x a ∈ Tint c:=by
  induction h using Submodule.span_induction with | mem a h=> obtain ⟨t,rfl⟩:=h; rw [pin]; apply tone | zero=> rw [map_zero]; exact Submodule.zero_mem _ | add a b _ _ i j=> rw [map_add]; exact Submodule.add_mem _ i j| smul _ _ _ i=> rw [map_smul]; exact Submodule.smul_mem _ _ i
lemma tint_riff {c:G.ColorIndex}{a:Line G}(h:a∈Tint c)(x: Axis): riff x a∈ Tint c:=Submodule.sub_mem _ (tint_walk h _) h
lemma tint_gate {c:G.ColorIndex}{a:Line G}(h:a∈Tint c)(l:List Axis):gate l a∈ Tint c:=by induction l with | nil=> exact h | cons x l h=> exact tint_riff h x
lemma tint_hit {t a:G.ColorIndex}(h:t ≠ a)(u v:Line G)(p:u∈Tint t)(q:v∈Tint a): handshake u v=0:=by
  induction p using Submodule.span_induction with
  | mem u hU=> obtain ⟨x,rfl⟩:=hU; induction q using Submodule.span_induction with
               | mem v hV=> obtain ⟨y,rfl⟩:= hV; rw [handshake,baked,probes, rot,bead,if_neg]; simp [h]
               | zero=> simp [handshake]
               | add=> simp_all only [handshake,map_add,LinearMap.add_apply,zero_add]
               | smul=> simp_all only [handshake,map_smul,LinearMap.smul_apply,smul_zero]
  | zero=> simp [handshake]
  | add=> simp_all only [handshake,map_add,LinearMap.add_apply,zero_add]
  | smul=> simp_all only [handshake,map_smul,LinearMap.smul_apply,smul_zero]
lemma fare_off {u v:Line G}{t a:G.ColorIndex}(p:u∈Tint t)(q:v∈Tint a)(h:t≠a): col u v=0:=by rw [col,tint_hit h u v p q,Complex.ofReal_zero]
lemma col_comm (a b:Line G): col a b=col b a:=by rw [col,listening]
variable (W:Initialize G)(g:G.Simple)
lemma fares_on {d:ℕ}{H: Hol G} (S:Survey G H d)(σ:Bool)(p:Name G)(x:Cover): cable g S σ p x∈Tint p.2:=by
  unfold cable; apply tint_walk; unfold wickLine; apply Submodule.sum_mem; intro i _; refine (Tint _).smul_mem _ ?_; apply Submodule.sub_mem; exacts [tint_gate (tone _ _) _,tint_gate (tone _ _) _]
variable (x:Cover)
abbrev b_w:= slack W x (Bfield G)
abbrev u_w:= slack W x (Ufield G)
include g in
lemma b_power : Pages.Hom (b_w W x) 3:=by unfold b_w; rw [bold g]; apply IsWeightedHomogeneous.sum; intro i _; apply IsWeightedHomogeneous.sum; intro j _; apply IsWeightedHomogeneous.sum; intro k _; exact (Pages.rank 3 _).smul_mem _ (((strongs (b_line g W x i)).mul (strongs (b_line g W x j))).mul (strongs (b_line g W x k)))
def bstep (j:Name G)(v:Line G):ℂ := col (b_line g W x j) v
lemma bstep_off {c:G.ColorIndex}{v:Line G}(p:v∈Tint c)(a:Name G)(h:a.2≠c): bstep W g x a v=0:= fare_off (fares_on g (W.surveys 6) true a x) p h
lemma first_strike (v:Line G) : Ξ v (b_w W x)= ∑ i:Name G, ∑ j:Name G, ∑ k:Name G, (3*fuel i j k * bstep W g x k v) • (b_r g W x i * b_r g W x j):=by
  let f:=b_line g W x; let a(i j k:Name G): Stamp G:=(fuel i j k * col (f k) v) • (harp (f i)*harp (f j)); let s:=∑ i,∑ j,∑ k,a i j k
  have ht i j k: fuel i j k • Ξ v (harp (f i)*harp (f j)*harp (f k))= a i j k + a j k i+a k i j:=by
    unfold a; rw [← turn_fuel i j,turn_fuel k i]; rw [ξ_mul,ξ_mul]; simp only [ξ_harp]; simp only [← MvPolynomial.C_mul', map_mul]; ring
  rw [b_w,bold g]; simp_rw [map_sum,map_smul]; change (∑ i:Name G,∑ j:Name G,∑ k:Name G, fuel i j k • Ξ v (harp (f i)*harp (f j)*harp (f k))) = ∑ i:Name G,∑ j:Name G,∑ k:Name G,(3*fuel i j k*bstep W g x k v) • (harp (f i)*harp (f j)); simp_rw [ht, Finset.sum_add_distrib]; rw [← show s=∑ i,∑ j,∑ k,a j k i from (prime_pow _ _ (fun _ _ _=>rfl)).symm,← show s=∑ i,∑ j,∑ k,a k i j from prime_pow _ _ (fun _ _ _=>rfl)];
  unfold bstep; have he i j k: (3*fuel i j k*col (b_line g W x k) v) • (harp (f i)*harp (f j))=(3:ℂ) • a i j k:=by rw [mul_assoc,mul_smul]
  simp_rw [he,← Finset.smul_sum]; unfold s; module
lemma double_strike (v u:Line G) : Ξ u (Ξ v (b_w W x))=∑ i:Name G,∑ j:Name G,∑ k:Name G,(6*fuel i j k * bstep W g x j u * bstep W g x k v) • b_r g W x i:=by
  let f:=b_line g W x; let a(i j k: Name G):= (3*fuel i j k* bstep W g x k v *bstep W g x j u) • b_r g W x i; let s:=∑ i,∑ j,∑ k,a i j k
  rw [first_strike W g]; simp_rw [map_sum,map_smul]; have ht i j k:(3*fuel i j k* bstep W g x k v) • Ξ u (b_r g W x i* b_r g W x j)=a i j k+a j i k:=by
    unfold b_r; rw [ξ_mul,ξ_harp,ξ_harp]; unfold a bstep b_r; rw [swap_fuel j i k]; simp only [← MvPolynomial.C_mul',map_mul]; ring
  simp_rw [ht,Finset.sum_add_distrib]; rw [Finset.sum_comm (f:=fun x y : Name G=>∑ k:Name G,a y x k)]; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _=>?_ ; unfold a; rw [← add_smul]; congr 1; ring
include g in
lemma double_off {a:Line G}{c:G.ColorIndex}(h:a∈ Tint c): Ξ a (Ξ a (b_w W x))=0:=by
  rw [double_strike W g]; refine Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=> Finset.sum_eq_zero fun k _=>?_ ; by_cases ht:fuel i j k=0; simp [ht]
  have he:j.2≠c∨ k.2≠c:= not_and_or.mp (fun p=> (fuel_diff i j k ht).2.1 (p.1.trans p.2.symm)); rcases he with hZ|hZ <;> (first | simp [bstep_off W g x h j hZ] | simp [bstep_off W g x h k hZ])
end YM.XSpace.Graph3
