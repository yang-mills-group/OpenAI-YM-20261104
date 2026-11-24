import YM.XSpace.Ample
/-!
# Issued first-kernel &, even after engineering H frame costs, flat errors
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cirrus
open Filter Set Function Metric Lattice Expense Stall Structure1 Normalize Asymptotics PowerSeries Comets Probes Future Maxwell
open scoped Topology BigOperators Classical
variable {G:Gauge} (W:Initialize G){n:ℕ}(d:ℕ)(t:Tags G d n)(c:Shade.Cut)(z:Points n)
lemma Bloom.constantly {g f:Sample n→ℂ}(H:Likely (Gate z) g)(h:Bloom z f): Bloom z (fun i=>g i*f i):=by obtain ⟨C,_,H⟩:=H.bound; have he: Expense.Cap (Gate z) g:= Expense.Cap.of_bounds C H; intro k; exact ((show g=O[Gate z] _ from he).mul (h k)).congr_right fun i=> one_mul _
lemma passL (Q:Sample n→ Point G d n)(T:Sample n→FieldEnd G d)(h:Fees (a:=unit) (L:=Gate z) d T) (hh:∀ x,Bloom z fun i=> Q i x): Bloom z (fun i=> lot (Q i) (T i) t):=by
  simp_rw [lots]; intro k; apply IsBigO.sum; intro j _; let f:=Module.finBasis ℂ (Sec G d); let g (i:Sample n) := T i (t j); let L (a:ℕ):= Gate z -- remove
  let V i : Module.Dual ℂ (Sec G d):= (Q i).toLinearMap t j; let x (i:Sample n):= (unit i:ℂ); let ψ a i:= f.coord a (x i^(d+1) • g i); let b a i:=(x i)⁻¹^(d+1)*V i (f a) -- parser (x i)⁻¹?
  have he a: Likely (Gate z) (ψ a):=⟨_,h (t j) (f.coord a)⟩
  have ho a:Bloom z (b a):= Bloom.room z (hh (update t j (f a))) (d+1)
  refine (IsBigO.sum (s:=Finset.univ) (A:=fun a i=> ψ a i*b a i) (fun a _=> Bloom.constantly z (he a) (ho a) k)).congr_left fun i=> ?_
  change _=V i (g i); have hz:x i≠0:=by unfold x; exact_mod_cast (unit_pos i).ne'
  rw [← f.sum_repr (g i),map_sum]; apply Finset.sum_congr rfl; intro a _; unfold b ψ; rw [map_smul,map_smul,Module.Basis.coord_apply]; change (x i^(d+1)*_)*_=f.repr (g i) a * _; rw [inv_pow]; field_simp

def records (X:FieldEnd G d) (i:Sample n) : Point G d n:= live W d i 1-lot (live W d i 0) X

theorem adjusted_cost (T:Sample n→FieldEnd G d)(h:Fees (a:=unit) (L:=Gate z) d T): Bloom z (fun i=> records W d (T i) i t- adequate W (T i) (unit i) i.layout t):=by
  intro k; exact ((landscape1 W d z t k).sub (passL d t z (fun i=>live W d i 0-blossom0 W d (unit i) i.layout) T h (landscape0 W d z) k)).congr_left (fun i=>by simp only [records,adequate,sub_apply,lots, Finset.sum_sub_distrib]; abel)

def fallRecords (i:Sample n): Point G d n:= records W d ((harvest W c d (unit i)).val) i
def reportFall (i:Sample n): Point G d n:= adequate W ((harvest W c d (unit i)).val) (unit i) i.layout
lemma bond0 (j: Fin n→ℕ)(p:∀ i, HP G (j i))(h:∀ i,j i≤d): Senses (conf n) (fun i=> live W d i 0 (shells j p h)) (fun i=> scene i d (shells j p h)):=by
  intro i hi; obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp ((conf_open n).mem_nhds hi); let K:=closedBall i (r/2)
  obtain ⟨C,hC,X⟩:= Mesh.uniform W j (sprawl i) K (isCompact_closedBall ..) (Subset.trans (Metric.closedBall_subset_ball (half_lt_self hr)) H) p
  apply (Tendsto.congr_dist (f₁:=fun q=>Mesh.MaxwellPoint j p (familiar q)) _ _)
  · exact (Mesh.smoothMaxwell j p hi).continuousAt.tendsto.comp (senseG i)
  apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) _ (show Tendsto (fun s=>C*a grab s) _ _ from mul_zero C ▸ (sprawl i).endpt.const_mul C); filter_upwards [X,(senseG i).eventually (closedBall_mem_nhds _ (by positivity : 0<r/2)), welcomeG i] with z hz hK hv; rw [dist_comm,dist_eq_norm, lives]; exact hz _ _ hv hK
theorem notices : Senses (conf n) (fun i=> live W d i 0 t) (fun i=> scene i d t):=by intro i hi; simp_rw [calls (live W d _ _) t,calls (scene _ d) t]; exact tendsto_finsetSum _ fun j _=> bond0 W d _ _ _ i hi
lemma report_sprouts (hv: Cleared c z.ofLp Finset.univ)(h:z∈conf n): Likely (Gate z) (fun i=> reportFall W d c i t):=by
  have ht:= sprout W c d (stepG z) (Eventually.of_forall unit_pos) charts z.ofLp t (aims z h) hv; apply ht.congr; filter_upwards with i; unfold reportFall adequate; rw [show i.layout=(fun j=>home i+charts i j) from funext fun j=>by unfold charts; abel,reply_plus,blossom_plus]
lemma knows_fall (hv: Cleared c z.ofLp Finset.univ)(h:z∈conf n): Likely (Gate z) (fun i=> fallRecords W d c i t):=by
  have he:= Bloom.spends z (adjusted_cost W d t z _ (cost W c d (stepG z) (Eventually.of_forall unit_pos))); apply ((show Likely (Gate z) (fun i=> fallRecords W d c i t - reportFall W d c i t) from ⟨_,he⟩).add (report_sprouts W d t c z hv h)).congr; filter_upwards with i; rw [sub_add_cancel]
end YM.XSpace.Cirrus
