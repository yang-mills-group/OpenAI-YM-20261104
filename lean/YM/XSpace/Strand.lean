import YM.XSpace.Loom
/-!
# Cut of all ext-ext lines from bilocal testing

Whole diagonal blocks are zero; the cut consumes paired metric wires, not
changing color. Assert the full color contraction information supplied by
`Silent`. Work with smaller external subdomains first (may skip locations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G : Gauge}

-- one additional hanging color. Uses one additional location.
inductive Loose (G:Gauge) : Finset E4→(G.ColorIndex→Web G)→Prop
| single {B p x}(u:Flavor 0): x∉B → Thread G (insert x B) p → Loose G B fun i=>singleF x u i * p
| scale {B p}: Loose G B p→(t:ℂ)→ Loose G B (t • p)
| add {B p q}: Loose G B p→Loose G B q→ Loose G B (p+q)
| zero {B}:Loose G B 0
namespace Loose
variable {p:G.ColorIndex→Web G}{B B':Finset E4}
lemma mono (h:Loose G B p)(ht:B'⊆B):Loose G B' p:= by
  induction h generalizing B' with
  | single u he hu=> exact .single u (fun h=>he (ht h)) (hu.mono (Finset.insert_subset_insert _ ht))
  | scale hp t ih=> exact .scale (ih ht) t
  | zero=>exact .zero
  | add _ _ h q=>exact (h ht).add (q ht)

lemma plug {x:E4}(u:Flavor 0)(hx:x∉B)(hp:Loose G (insert x B) p): Thread G B (∑ i:G.ColorIndex, singleF x u i*p i):= by
  generalize he: insert x B=T at hp
  induction hp generalizing B with
  | @single t y v hg hQ=>
    subst_vars
    simp only [Finset.mem_insert,not_or] at hg
    rw [show (∑ i:G.ColorIndex,singleF x u i*(singleF y v i*t))=signFor x y u v G*t by unfold signFor; simp [Finset.sum_mul,mul_assoc]]
    rw [Finset.insert_comm y x] at hQ; exact Thread.join _ _ (Ne.symm hg.1) hx hg.2 hQ
  | scale h v ih=>
    simp only [Pi.smul_apply,mul_smul_comm, ← Finset.smul_sum]; exact .scale (ih hx he) v
  | add h t ih hh=> simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]; exact Thread.add (ih hx he) (hh hx he)
  | zero=> simpa using (Thread.zero (B:=B) (G:=G))

lemma weaves (x y:E4) (u v:Flavor 0)(h:x≠y)(hx:x∉B)(hy:y∉B)(hp:Loose G (insert x (insert y B)) p): Loose G B ((fun _:G.ColorIndex=>signFor x y u v G)*p):= by
  generalize he : insert x (insert y B)=T at hp; induction hp generalizing B with
  | @single q z k hk hh=>
    subst_vars; simp only [Finset.mem_insert,not_or] at hk
    have h₁ : x∉insert z B:= by simp [hx,Ne.symm hk.1];
    have h₂ : y∉insert z B:= by simp [hy,Ne.symm hk.2.1];
    let p(i : G.ColorIndex):= singleF z k i*(signFor x y u v G*q)
    have hp : Loose G B p:= Loose.single _ hk.2.2 (Thread.join _ _ h h₁ h₂ (by rw [Finset.insert_comm y z,Finset.insert_comm x z]; exact hh))
    convert hp using 1; funext i; exact mul_left_comm ..
  | scale hp t ih=> rw [mul_smul_comm]; exact .scale (ih hx hy he) t
  | add hp hq ih hg=> rw [mul_add]; exact .add (ih hx hy he) (hg hx hy he)
  | zero=> rw [mul_zero]; exact Loose.zero
end Loose
variable (G)

-- negative interactions external-external, for the cut

def outK (U:Finset E4): Normal.Symmetric (WebKey G):= ⟨fun i j=> if i.1∉U ∧ j.1∉U then -(net G).cov i j else 0, fun i j=> by rw [(net G).symm i j]; simp [and_comm]⟩

variable {G}
def forge (K:Normal.Symmetric (WebKey G)) (x:E4)(p: Flavor 0)(i:G.ColorIndex) := Finsupp.linearCombination ℂ K.cov (limbs x (flavor 0 i p))
def Sliq (K:Normal.Symmetric (WebKey G))(x:E4)(p:Flavor 0)(i:G.ColorIndex):= Normal.slit (forge K x p i)

section
variable {U:Finset E4}
local notation "O" => outK G U
local notation "D" => Sliq (outK G U)

private lemma read_spoiled (x y:E4)(hx:x∉U)(hy:y∉U) (u v:Flavor 0)(i j:G.ColorIndex): D x u i (singleF y v j)= - scrape x u i (singleF y v j):= by
  unfold Sliq scrape singleF factors Maxwell.symbol; simp only [map_sum,map_smul,post_X,C_mul']
  simp_rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [(slit _).map_smul,(slit _).map_smul,slit_X,slit_X,show forge O x u i (y,(⟨0,a⟩:Slot G))= - form x (flavor (G:=G) 0 i u) (y,(⟨0,a⟩:Slot G)) from ?_,map_neg, smul_neg]
  unfold forge form limbs; simp only [map_sum,Finsupp.linearCombination_single,Finset.sum_apply,outK, hx, hy, Pi.smul_apply]; simp
lemma D_single (x y:E4)(hx:x∉U)(hy:y∉U)(h:x≠y)(u v:Flavor 0)(c i j:G.ColorIndex) : D x u i (singleF y v j)= if j=i then C ((-fare c u v (x-y):ℝ):ℂ) else 0:= by
  rw [read_spoiled x y hx hy]; unfold singleF; rw [through_eqn h u v c]; split <;> simp

private lemma D_hits (x y z:E4)(hx:x∉U)(hy:y∉U)(hz:z∉U)(h:x≠y)(h':x≠z)(u v w:Flavor 0)(c i:G.ColorIndex):
    D x u i (signFor y z v w G)=((↑(-fare c u w (x-z)):ℂ)) • singleF y v i+(↑(-fare c u v (x-y)):ℂ) • singleF z w i:= by
  rw [signFor, map_sum]; simp_rw [(D x u i).leibniz];
  simp only [smul_eq_mul,D_single x y hx hy h u v c, D_single x z hx hz h' u w c,mul_ite,mul_zero,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]; rw [mul_comm, ← C_mul',← C_mul',mul_comm (singleF z w i)]

-- After consuming a contraction against a collection of bilocals
lemma sticky (c:G.ColorIndex){p:Web G}{B:Finset E4}{x:E4}(hx:x∉U)(h:x∈B)(he:U ⊆ B) (u:Flavor 0) (hp:Thread G B p): Loose G B fun i=> D x u i p:= by
  induction hp with
  | one=> simp; exact Loose.zero
  | scale H t ih=> simp_rw [(D x u _).map_smul]; exact (ih h he).scale t
  | add hp hq ih hh=> simp only [map_add]; exact Loose.add (ih h he) (hh h he)
  | @join B p y z v w hg hy hz H ih =>
    have ht:U⊆insert y (insert z B):= he.trans (fun k hk=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk))
    have hp := ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)) ht
    simp_rw [(D x u _).leibniz, D_hits x y z hx (Finset.notMem_mono he hy) (Finset.notMem_mono he hz) (ne_of_mem_of_not_mem h hy) (ne_of_mem_of_not_mem h hz) u v w c]
    have h₁: Loose G B fun i=> singleF y v i*p := .single v hy (H.mono (Finset.insert_subset_insert _ (Finset.subset_insert ..)))
    have h₂: Loose G B fun i=> singleF z w i*p := .single w hz (H.mono (Finset.subset_insert ..))
    simp only [smul_eq_mul,mul_add]; simp_rw [mul_smul_comm, show ∀ i j (b:Flavor 0), p*singleF j b i=singleF j b i*p from fun i j b=> mul_comm ..]; exact Loose.add (Loose.weaves y z v w hg hy hz hp) ((h₁.scale _).add (h₂.scale _))

lemma sticking (c:G.ColorIndex){B:Finset E4}{p:G.ColorIndex→ Web G}{x:E4}(hx:x∉U)(h:x∈B)(he:U⊆B) (u:Flavor 0) (hp: Loose G B p): Thread G B (∑ i:G.ColorIndex, D x u i (p i)):= by
  induction hp with
  | zero=> simp; exact Thread.zero
  | scale hp t ih=> simp_rw [Pi.smul_apply,(D x u _).map_smul, ← Finset.smul_sum]; exact (ih).scale t
  | add _ _ ih hh=> simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]; exact Thread.add (ih) (hh)
  | @single q y v hy hB=>
    have hd:= sticky c hx (Finset.mem_insert_of_mem h) (he.trans (Finset.subset_insert ..)) u hB
    simp_rw [(D x u _).leibniz]; simp only [smul_eq_mul,Finset.sum_add_distrib]
    apply Thread.add (Loose.plug v hy hd); simp_rw [D_single x y hx (Finset.notMem_mono he hy) (ne_of_mem_of_not_mem h hy) u v c]
    simp only [ite_true, Finset.sum_const, Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,mul_comm q, C_mul']; exact ((hB.mono (Finset.subset_insert ..)).scale _).scale _

lemma milk_one (x:E4)(p:Flavor 0)(i:G.ColorIndex)(q:Web G) : milk O (singleF x p i*q)= singleF x p i*milk O q+D x p i (milk O q):= by unfold singleF; rw [strokes,refresh]; rfl

lemma milk_ext (c:G.ColorIndex) {B:Finset E4}{p:Web G}(h:U⊆B)(hp:Thread G B p): Thread G B (milk O p):= by
  induction hp with
  | one=> rw [pure]; exact .one
  | add hp hq ih hh=> rw [_root_.map_add]; exact .add (ih h) (hh h)
  | scale hp t ih=> rw [_root_.map_smul]; exact (ih h).scale t
  | @join B p x y u v hw hx hy hp ih=>
    let L:= insert x B; have he:y∉L:= by simp [L,hy,Ne.symm hw]
    let ℓ:= milk O p
    have hℓ:Thread G (insert y L) ℓ:= by rw [show insert y L=insert x (insert y B) from Finset.insert_comm ..]; exact ih (h.trans (fun k hk=> Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk)))
    have ht: U ⊆ L:= h.trans (Finset.subset_insert ..)
    have hY : y∉U:= Finset.notMem_mono h hy
    let W (i:G.ColorIndex) := milk O (singleF y v i*p)
    have hh : Loose G L W:= by
      simp_rw [show W=(fun i=> singleF y v i* ℓ) + (fun i=> D y v i ℓ) from _root_.funext fun i=> milk_one y v i p]; exact Loose.add (.single v he hℓ) ((sticky c hY (Finset.mem_insert_self ..) (ht.trans (Finset.subset_insert ..)) v hℓ).mono (Finset.subset_insert ..))
    rw [signFor,Finset.sum_mul,map_sum]; simp_rw [mul_assoc,milk_one x u]
    rw [Finset.sum_add_distrib]; exact Thread.add (Loose.plug u hx hh) ((sticking c (Finset.notMem_mono h hx) (Finset.mem_insert_self ..) ht u hh).mono (Finset.subset_insert ..))
end
end YM.XSpace.Stab
