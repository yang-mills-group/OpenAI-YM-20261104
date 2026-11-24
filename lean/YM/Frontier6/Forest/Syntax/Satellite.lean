import YM.Frontier6.Forest.Syntax.Killing

/-!
# Projections from centered prices

Fixed detector rotation parameters move (also states). Preserve the quantifier order
on eventual thresholds for higher-fit precision by invoking all symmetric demands
on the same grade sets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V X:Type}{T:Fareway I}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book} (K:Final C H S)
   {P:Fabric I}{x:I→ E4}{d:ℕ}{A:Art S I}(p:Probe S) (g:I→ Ortho)
set_option quotPrecheck false
abbrev polled (K:Final C H S) (s:I→ StateIndex K) (f:Art S I) (i:I):ℂ:= poll S (state K (s i)) (f i)
abbrev inscription {C:Family G} (S:Table C.book)[Fintype V] (x:I→ V→ E4) (v:V→ S.Tag) : Art S I:= fun i=> assembly S (x i) v
-- at exterior attached to live frontier
def Query (T:Fareway I)(P:Fabric I)(K:Final C H S)[Fintype V][DecidableEq V] (v:V→ S.Tag) (A:Art S I)(a b:ℝ):Prop:=∀ (y:I→ V→ E4),Wide T y b → Cross T P (sheet y) b→∀ s:I→ StateIndex K, T.Costs (polled K s (A*inscription S y v)) a
variable {a b:ℝ}
def comet (x:I→ E4) : I→ Fin p.length→ E4:= fun i j=>(p.roll K (g i)).exterior j+x i
def floated (p:Probe S) : Fin p.length→ ℕ:=fun j=>(p.letter j).1
lemma comets : Wide T (comet K p g x) 0:=by
   intro i j hi b hb
   have ht:= highlights K p g (c:=x) (T:=T) (show some i ≠ some j from fun h=> hi (Option.some.inj h)) b hb; simp only [Option.elim_some] at ht; exact ht
lemma comet_cross {r:ℝ} (hh:clearC (2*r) p.exterior)(hr:0<r)(hf:∀ᶠ i in T.via,∀ y∈P i,‖y-x i‖≤r): Cross T P (sheet (comet K p g x)) 0:=by
   intro b hb; filter_upwards [hf,(T.minted (-b)).cheaper (T.minted_c r hr) (by linarith)] with i hi he y hy z hz; obtain ⟨k,rfl⟩:=hz; apply le_trans he.le

   have hh':= clear_exterior (roll_safe K p hh (g i)) k; let u:=(p.roll K (g i)).exterior k; change r ≤ ‖y-(u+x i)‖; rw [norm_sub_rev]; have hv: u+x i-y=u-(y-x i):= by abel
   rw [hv]; change 2*r < ‖u‖ at hh'; linarith only [hh',hi y hy,norm_sub_norm_le u (y-x i)]
lemma float_shines (Z : roles S (floated p)) : T.Costs (fun i=> medallion (floated p) (fun j i=>flying K p (g i) j) Z i) 0 := by
   have ht(i: Fin p.length): T.Costs (fun k=> flying K p (g k) i) 0:= Fareway.Costs.immured T (fun g:Ortho=> flying K p g i) ((continuous_apply i).comp (fly_cont K p)) g
   simpa only [Finset.sum_const_zero] using medallion_cost (floated p) (fun j i=>flying K p (g i) j) (p:=fun _=>0) ht Z -- arg?
lemma seen_by (i:Fin (d+1))(p:(hand K i.val).list)(b:Bool)(g:I→Ortho)(hc:Forest.Centered T P x K d)(h:let q:=p.val.flip K b; ∀ z:roles S (floated q), Query T P K (line (S:=S) (floated q) z) A a 0):
   T.Costs (fun j=>((p.val.flip K b).roll K (g j)).tip K (written K (x j) (A j))) a:=by
   let q:=p.val.flip K b; let U:= comets (T:=T) (x:=x) K q g; obtain ⟨r,hr,hp,hC⟩:= hc; have hv:= comet_cross K q g (flip_safe K p.val (hr i p) b) hp hC; let V(j:I):= flying K q (g j)
   let d':= floated q; let f(z:roles S d')(j):=poll S (state K none) (A j*assembly S (comet K q g x j) (line (S:=S) d' z))
   have hF(z: roles S d'):T.Costs (f z) a:= h z (comet K q g x) U hv (fun _=>none)
   let u(z:roles S d')(j:I):= medallion d' (fun k i=> flying K q (g i) k) z j
   let H(z:roles S d')(j):=u z j*f z j; have hU:T.Costs (fun j=>∑ z:roles S d', H z j) a:= Fareway.Costs.sum Finset.univ H (fun z _=>by simpa only [zero_add] using (show T.Costs (H z) (0+a) from (float_shines K q g z).mul (hF z)))
   refine hU.cf (Eventually.of_forall fun j=>?_); let F:= comet K q g x j
   change (∑ z:roles S d', H z j)=poll S (state K none) (A j * assembly S F (fun z=> ⟨d' z,flying K q (g j) z⟩)); rw [((deck_congr K d' F _).left K (A j)).done K none,mul_sum,map_sum]; simp_rw [mul_smul_comm,map_smul];rfl
lemma moonlit (hc: Forest.Centered T P x K d)(hv:∀ᶠ i in T.via, Visible K (x i) d (A i))(h:∀ (i:Fin (d+1))(p:(hand K i.val).list)(b:Bool),let q:=p.val.flip K b;∀ z:roles S (floated q), Query T P K (line (S:=S) (floated q) z) A a 0): T.Costs (fun i=> absorb K (x i) d (A i)) a:= (read_expenses K d hv (fun i p b g=> seen_by K i p b g hc (h i p b))).mapped (detector K d)
end YM.Frontier6.Forest
