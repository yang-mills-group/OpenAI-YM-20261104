import YM.SchemeRG11.Wilson.Area
/-! Summations with cutoff powers kept. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G: Gauge} {I : Type*} {N:Side}
variable (s:Finset I)(p:I→ vellum G)
def Graft (t:I→ Site N) (i j:Axis) (x:Site N): ℝ:= (spray G N).avg (Tree.cost x i j * ∏ u∈s, adsorb (t u) (p u))
def turnup (t:I→ Cover) (i j:Axis) (x:Cover): ℝ:=(land G).avg (Tree.cost x i j * aerial s p t)

lemma avoidanceC(i j:Axis) : ∃ C>0,∀ (t:I→ Cover)(m:ℕ),(∀ u, diam (t u) ≤ m)→ ∀ (x:Cover), 4*(m+2) ≤ diam x →
 |turnup s p t i j x| * ((diam x:ℝ)^6) ≤ C:=by
 obtain ⟨W,hW,H⟩:= tailC p s i j
 refine ⟨W*4^6,by positivity,?_⟩; intro t m hm x hx
 let v:ℝ:=diam x
 have hv:0≤v:=Nat.cast_nonneg _; specialize H x t (v/4) (by positivity) (fun u=>?_)
 · have he: diam x ≤ diam (x - t u)+diam (t u):= by simpa only [sub_add_cancel] using diam_add (x-t u) (t u)
   have hy:diam x ≤ 4*diam (x-t u):=by have := hm u; omega
   have hy' : v ≤ (4:ℝ)*diam (x-t u):=by unfold v; exact_mod_cast hy
   linarith
 change |(land G).avg _| * v^6≤ W*4^6; linarith only [H]
lemma avoidanceO(i j:Axis): ∃ C>0,∀ {N:Side} (o:Site N)(t:I→ Site N)(m:ℕ),(∀ u, pdist (t u-o) ≤ m)→ ∀ x : Site N, 4*(m+2) ≤ orbitRank N o i j x →
 |Graft s p t i j x| * (orbitRank N o i j x:ℝ)^6 ≤ C:=by
 obtain ⟨W,hW,H⟩:=tailO s p i j
 refine ⟨W*4^6,by positivity,?_⟩; intro N o t m hm x hx; let r:= orbitRank N o i j x
 have hd : r≤pdist (x-o):= min_le_left ..; have he:r≤pdist (mirror i j x-o):= min_le_right ..
 have hr : 4*(m+2)≤ r:=hx
 specialize H (N:=N) x t ((r:ℝ)/4) (by positivity) (fun b=>?_) (fun b=>?_)
 · have ht : pdist (x-o) ≤ pdist (t b-x)+pdist (t b-o):=by
     have hv:= separation_triangle x (t b) o; rw [separation_comm x (t b)] at hv; exact hv
   have hm' := hm b
   have hh : r ≤ 4*pdist (t b - x):= by omega
   have hy : (r:ℝ) ≤4*pdist (t b-x):=by exact_mod_cast hh
   linarith only [hy]
 · let u:=t b-o; let a:=step (S:=Per N) i; let c:=step (S:=Per N) j
   have ht : pdist (mirror i j x-o) ≤ pdist (t b+x)+pdist u+2:=by
     rw [show mirror i j x-o=-(((t b+x)+(-u))+a+c) by unfold mirror c a u; abel,pdist_neg]
     have h1:= pdist_triangle (t b+x) (-u); rw [pdist_neg] at h1
     have h2:= pdist_triangle (t b+x + -u) a
     have h3:= pdist_triangle ((t b+x+ -u)+a) c
     have : pdist a ≤1:=stepP _; have : pdist c≤ 1:=stepP _; omega
   have hv: pdist u ≤ m:=hm b
   have hh:r ≤ 4*pdist (t b+x):=by omega
   have hy : (r:ℝ) ≤4*pdist (t b+x):=by exact_mod_cast hh
   linarith only [hy]
 change |(spray G N).avg _| * (r:ℝ)^6 ≤ W*4^6; linarith only [H]
lemma cargo (i j:Axis):∃ C>0,∀ (t:I→ Cover)(m:ℕ)(_H:∀ u,diam (t u) ≤ m)(k:ℕ),4*(m+2) ≤ k →
 Summable (turnup s p t i j) ∧ |(∑' x:Cover, turnup s p t i j x) - ∑ x∈box k,turnup s p t i j x|≤ C/(k:ℝ)^2:=by
 obtain ⟨C,hC,H⟩:=avoidanceC s p i j
 refine ⟨81*32*C,by positivity,?_⟩; intro t m ht k hν
 let F:= turnup s p t i j; let Y:=(box k: Set Cover); let f(c: ↑Yᶜ):= F c.val
 have hn(v: Cover)(h:v∉box k): k < diam v:= lt_of_not_ge (mt (wrapcost v) h)
 have hp : price (fun c: ↑Yᶜ=> diam c.val) 81:=by
   intro u k hk hh;rw [← Finset.card_image_of_injective u Subtype.val_injective]
   apply coverage _ hk; intro i hi; obtain ⟨v,hv,rfl⟩:= Finset.mem_image.mp hi; exact hh v hv
 have hy(c: ↑Yᶜ): k < diam c.val:= hn _ c.property
 have he(u: Finset ↑Yᶜ): (∑ a∈u,‖f a‖) ≤ 81*32*C/(k:ℝ)^2:= whorl hp (by norm_num) hC.le k (by omega) u (fun i _=> hy i) (fun i _=> H t m ht _ (le_trans hν (hy i).le))
 have hf : Summable (fun c: ↑Yᶜ=>‖f c‖):= summable_of_sum_le (fun i=> norm_nonneg (f i)) he
 have hs : Summable F:= by
   rw [← Finset.summable_compl_iff (s:=box k)]; exact Summable.of_norm hf
 have HH:= Summable.sum_add_tsum_compl (s:=box k) hs
 refine ⟨hs,?_⟩; change |(∑' i,F i)-_|≤_
 rw [← HH,add_sub_cancel_left]; exact (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_of_sum_le he)
lemma dispatch (i j:Axis):∃ C>0,∀ {N:Side}(o:Site N)(t:I→ Site N) (m:ℕ) (_H:∀ u,pdist (t u-o) ≤ m)(k:ℕ),4*(m+2) ≤ k →
 |∑ x:Site N with k < orbitRank N o i j x, Graft s p t i j x| ≤ C/(k:ℝ)^2:=by
 obtain ⟨C,hC,H⟩:=avoidanceO s p i j
 refine ⟨162*32*C,by positivity,?_⟩; intro N o t m ht k hh
 apply (Finset.abs_sum_le_sum_abs _ _).trans; exact whorl (places o i j) (by norm_num) hC.le k (by omega) _ (fun x hx=> (Finset.mem_filter.mp hx).2) (f:=Graft s p t i j) (fun x hx=> H o t m ht x (hh.trans (Finset.mem_filter.mp hx).2.le))
end YM.SchemeRG11.Acorn
