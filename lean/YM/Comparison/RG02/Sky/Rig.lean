import YM.Comparison.RG02.Sky.Winding
import YM.Comparison.RG02.Sky.Traces
/-!
# Induced connected network for an entire graph, every true primitive valuation on cover
 Supplies graphs for `Wires` arithmetic, no assuming graph circulations priced by marker
 comparisons. Fk readiness will consume these local `Rig`s on a translation repeated forest (Theta
 independence used *once*, not claiming period price for random unrepeated tree). Bound proved
 using these sources of estimates at any perturbative order, any cover stiffness location grammar.
 Remember NO inverted-reg equivalence here, NOR transmission of the rendered norm through this
 operation. It purchases only anchored aggregation costs. It is important to require cover
 *coefficient* rates on the inputs for using this binder, not priced through the E Health lens.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sky.Rig
open Function Filter Lattice RG Push.AbsoluteSums Finset Next.Rank
open Flux (push Abs)
open Net
open scoped Classical Topology BigOperators
variable {J I V E : Type} {U : V →Type}
-- E all exteriors, π homes (mark roots & extra addresses & response test indices)
abbrev Pin (π:E→V)(i:V) := U i ⊕ {a:E//π a=i}
abbrev Leg (U:V→ Type):= Sigma U
abbrev Site' (U:V→ Type)(E:Type):= (V ⊕ Leg U) ⊕ E
abbrev post (p:V) : Site' U E:=.inl (.inl p)
abbrev lo (k : Leg U) : Site' U E:= .inl (.inr k)
abbrev receive (v:E) : Site' U E:= .inr v
variable (π:E→V)
abbrev Record (U:V → Type) := Traces.Path (Leg U)
-- attach arcs one per line, as directed (orientation registered even for self).
variable (f : Record U)
abbrev Node (_ : E→V)(f: Record U):= V ⊕ Fin f.length
abbrev arcs (s : Node π f): Type := Sum.rec (motive:=fun _=>Type) (Pin (U:=U) π) (fun _=>Unit) s
def dock1 (p : Node π f) : Site' U E := match p with
| .inl v=> post v
| .inr i=> lo (f.get i).1
def sees1 (v:V) (i:Pin (U:=U) π v) : Site' U E := match i with
| .inl i=> lo ⟨v,i⟩
| .inr i=> receive i.val
def dock2 : (p:Node π f) → (arcs π f p) → Site' U E := Sum.rec (motive:=fun _=> _→ _) (sees1 π) (fun i _=> lo (f.get i).2)
def plan : Net (Site' U E) (arcs π f) := ⟨dock1 π f,dock2 π f⟩

local notation "κ"=> plan π f

lemma foot (u: Leg U): Reaches (K:=κ) (post u.1) (lo u):= Net.spans (K:=κ) (.inl u.1) (Sum.inl u.2)
lemma seat (e:E): Reaches (K:=κ) (post (π e)) (receive e):= Net.spans (K:=κ) (.inl (π e)) (Sum.inr (α:=U _) (⟨e,rfl⟩:{x:E//π x=π e}))
lemma line (i: Fin f.length): Reaches (K:=κ) (lo (f.get i).1) (lo (f.get i).2):= Net.spans (K:=κ) (.inr i) (():Unit)
variable [Fintype V] [∀ i,Fintype (U i)] [DecidableEq V] [∀ i,DecidableEq (U i)]

-- `program` not parameterized by any geometry-size measurements; weights can carry prescribed E and U data.
def program (U:V→Type)[∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)] (v:V): List (Record U) := Traces.circle Sigma.fst univ {v} (Fintype.card (Leg U))

variable {v:V} (h : f ∈ program U v)
include h in
lemma reasoning (p:Site' U E): Net.Open κ p:= by
   suffices he : Net.Open κ (post v) from he.any p
   let s:= univ.filter (fun i=> Reaches (K:=κ) (post v) (post i))
   have hx : {v}⊆ s:= singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_univ _, Net.slips⟩)
   have hi : Traces.Travels Sigma.fst f s := by
       intro j hj hh
       obtain ⟨e,he⟩:= List.mem_iff_get.mp hj; subst j
       exact mem_filter.mpr ⟨mem_univ _,Net.through (mem_filter.mp hh).2 (Net.through (foot π f _) (Net.through (line π f e) (Net.again (foot π f _))))⟩
   have hv (z:V): Reaches (K:=κ) (post v) (post z) := (mem_filter.mp (Traces.floods Sigma.fst _ s hx _ _ f h hi z)).2
   rintro ((z|i)|d)
   · exact hv z
   · exact Net.through (hv i.1) (foot π f i)
   exact Net.through (hv _) (seat π f d)
variable [Fintype E]
-- explicit instances avoid global `Classical.propDecidable` burning arithmetic in pricing
instance arcFin (s:Node π f) : Fintype (arcs π f s):= Sum.rec (motive:=fun i=> Fintype (arcs π f i)) (fun v=> inferInstanceAs (Fintype (Pin (U:=U) π v))) (fun (_:Fin f.length)=> inferInstanceAs (Fintype Unit)) s
-- can choose path complexity independent of any sites or torus. In applying on many demands,
-- include them as primitive arity post-block estimates. All finite. Leg gauge color etc are types in
-- separate lists, *not* eliminating periodic sites before aggregation.
def issue (p:Site' U E): Guide κ p := Open.guide (reasoning π f h p)

abbrev Vertex (π:E→V)(U:V→Type) := Wires (Pin (U:=U) π) Cover
-- cov entry at each pair (no PSD requirement on unsupported valuations on cover). prepare covers
-- `Unit→Cover` means offset from first at its base. Distinct legs even for self.
abbrev Ground (U:V→Type):= Leg U → Leg U → (Unit→ Cover) → ℂ
variable (A : Vertex π U) (C : Ground U)

def surface : Wires (arcs π f) Cover := Sum.rec (motive:=fun i=> (arcs π f i→ Cover)→ℂ) A (fun i=> C (f.get i).1 (f.get i).2)

def volume (a:V→ℝ) (b:Leg U → Leg U →ℝ) : Node π f →ℝ:= Sum.elim a (fun i=> b (f.get i).1 (f.get i).2)

structure Bond (σ:ℝ)(π:E→V)[Fintype E][DecidableEq V](A:Vertex π U)(C:Ground U)(a:V→ℝ)(b:Leg U → Leg U →ℝ) : Prop where
   parent (v:V): SumBudget (fun d:Pin (U:=U) π v→ Cover => Real.exp (σ*mileage d)*‖A v d‖) (a v)
   line (j k): SumBudget (fun d:Unit→Cover=> Real.exp (σ*mileage d)*‖C j k d‖) (b j k)

omit [∀ i,DecidableEq (U i)] [Fintype V] in
lemma Bond.usable {σ a b} (h:Bond σ π A C a b): Ports.Offering (volume π f a b) σ (surface π f A C):= by
   rintro (v|i)
   · exact h.parent v
   exact h.line ..

-- rooted placements, spend for all remaining. read ordinary V jets after period contraction of
-- these networks (formal Wave), no mask.
variable {P:Site' U E}
def scan {X : Type*} [Zero X] (x : Options (Site' U E) X P): E→ X := fun e => x.val (receive e)
abbrev inspect (X:Type)[Zero X]:= E→ X
omit [Fintype V] [∀ i,Fintype (U i)] [DecidableEq V] [∀ i,DecidableEq (U i)] [Fintype E] in
lemma ride_heel (c:Side)(x: Options (Site' U E) Cover P): scan (toTorus c x)= tile c (scan x):= rfl

-- period ledger
variable (c:Side)
def cover (p:Site' U E) := push scan (climb (K:=plan π f) (o:=p) (surface π f A C))
def mirror (p:Site' U E) := push scan (hill (K:=plan π f) (o:=p) c (surface π f A C))
-- expose translation cos(p=mark x) and cover bound using star.
def cost (t:E→ Site c) := mileage (lift ∘ t)
lemma cost_bounds (x:E→Cover) : cost c (tile c x) ≤ mileage x:= sum_le_sum fun i _ => by exact_mod_cast FreeResolvent.wrap_size c (x i) -- namespace

variable (p:Site' U E) {σ m τ : ℝ}{a:V→ℝ}{b:Leg U→Leg U→ℝ}
private lemma travel_price (τ : ℝ) (ht:0 ≤ τ) (d) : τ * mileage (scan ((issue π f h p).arrive d)) ≤ τ*(issue π f h p).rate*(Fintype.card E:ℝ)*Net.toll d:= by
   let Y:= issue π f h p
   change τ * mileage (scan (Y.arrive d)) ≤ _
   have hh : mileage (scan (Y.arrive d)) ≤ ∑ _ : E,Y.rate* Net.toll d:= Finset.sum_le_sum fun i _=> le_trans (Y.cap d (receive i)) (mul_le_mul_of_nonneg_right (by linarith [Guide.enough Y]) (toll_nonneg d))
   simp only [sum_const,card_univ,nsmul_eq_mul] at hh
   apply (mul_le_mul_of_nonneg_left hh ht).trans_eq; change τ * (_*(Y.rate*_))=τ*Y.rate*_*_; ring
lemma established (hw: Bond σ π A C a b) (hs:0≤σ)(hm:0≤m)(ht:0≤τ)(he : τ*(issue π f h p).rate*(Fintype.card E:ℝ) ≤ σ-m*((issue π f h p).rate+1)): SumBudget (fun t:E→ Site c=>Real.exp (τ*cost c t)*‖mirror π f A C c p t-push (tile c) (cover π f A C p) t‖) (Real.exp (-m*c.val)*(∏ i, volume π f a b i)):= by
   apply Ports.world (issue π f h p) c scan scan (tile c) (fun t:E→ Site c=>Real.exp (τ*cost c t)) (Bond.usable π f A C hw) hs rfl (fun i=> (Real.exp_pos _).le) hm
   intro d; apply Real.exp_monotone; exact le_trans (mul_le_mul_of_nonneg_left (cost_bounds c _) ht) ((travel_price π f h p τ ht d).trans (mul_le_mul_of_nonneg_right he (toll_nonneg _)))
lemma magistrate (hw: Bond σ π A C a b)(hs:0≤σ)(ht:0≤τ)(he : τ*(issue π f h p).rate*(Fintype.card E:ℝ)≤ σ): SumBudget (fun x:E→Cover=>Real.exp (τ*mileage x)*‖cover π f A C p x‖) (∏ i, volume π f a b i):= by
   refine Ports.standard (issue π f h p) (p:=scan) (h:=?_ ) ?_ hs (fun i=> (Real.exp_pos _).le)
   · exact Bond.usable π f A C hw
   intro d; apply Real.exp_monotone; apply (travel_price π f h p τ ht d).trans (mul_le_mul_of_nonneg_right he (toll_nonneg _))
end YM.Comparison.RG02.Sky.Rig
