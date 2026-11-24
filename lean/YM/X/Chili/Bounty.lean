import YM.X.Chili.Clove
/-!
# Cost algebra for local dynamic symbols at variable frames. Ext gets actual shell admissible direction. Thick grade estimates, no limit required at z≈origin. Uses normalized ∗actual−subtract* residual Visa.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze MvPolynomial Finset LiftMark
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m n d:ℕ} {G:Gauge} {R:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
abbrev Rich (G:Gauge):= ℕ→Long G
abbrev Grasp (f:Rich G):Prop:= ∀ i:ℕ, Released (fun k=> f k i)
abbrev Deck (G:Gauge):= Mist (Curly G)
def emerge (q:ℕ+)(f:Rich G):Rich G:=fun i=>sauce (epsilon q i) (f i)
def wreath (i d:ℕ)(f:Rich G)(p:Deck G): Mist ℂ:= fun k z=> probeL (f k) (leaf (vapor G) i (trumpet (Okay G) (valP (G:=G)) d (p k z)))
def cake (d:ℕ)(f:Rich G)(p:Deck G): Mist ℂ:= fun k z=>probeL (f k) (bloom d (p k z))
def exitP (A:ℕ→ Brush G)(p:Deck G):Mist ℂ:=fun k z=>snap (A k) (p k z)
def grove (q:ℕ+)(R:ℝ)(A:ℕ→ Brush G)(B:Rich G)(d j:ℕ): Submodule ℂ (Deck G) where
    carrier := {p| (∀ f:Rich G,Grasp f→∀ i:ℕ,i≤d→Visa q R 0 ((i:ℤ)-j) (wreath i d f p)) ∧
       Visa q R (d+1:ℕ) (((d+1:ℕ):ℤ)-j) (exitP A p-cake d (emerge q B) p)}
    zero_mem' := by
        constructor; · intro f h i hi; rw [show wreath i d f 0 = 0 from by ext1 i; ext1 z; simp only [wreath,Pi.zero_apply,leaf,map_zero]]; exact Visa.zero
        rw [show exitP A 0 - cake d (emerge q B) 0 = 0 from by ext1 i; ext1 z;simp [exitP,cake]]; exact Visa.zero
    add_mem' := by
        rintro x y hx hy; constructor; · intro f h i hi; rw [show wreath i d f (x+y)=wreath i d f x + wreath i d f y from by ext1 i; ext1 z; simp only [wreath,Pi.add_apply,leaf,map_add]]; exact Visa.add (hx.1 f h i hi) (hy.1 f h i hi)
        let Y:=emerge q B; let sP (p) :=cake d Y p; have he : cake d Y (x+y)=sP x+sP y:=by unfold sP; ext1 i; ext1 z;simp only [cake,Pi.add_apply,map_add]
        have ht: exitP A (x+y)=exitP A x+exitP A y:= by ext1 i; ext1 z; simp only [exitP,Pi.add_apply,map_add]
        rw [ht,he,add_sub_add_comm]; exact hx.2.add hy.2
    smul_mem' := by
        rintro c x h; constructor; · intro f hx i he; rw [show wreath i d f (c • x)= c • wreath i d f x from by ext1 i; ext1 z; simp only [wreath,leaf,Pi.smul_apply,map_smul]]; exact Visa.smultC c (h.1 f hx i he)
        have hp : exitP A (c • x)=c • exitP A x:= by ext1 i; ext1 z; simp only [exitP,map_smul,Pi.smul_apply]
        let Y:= emerge q B; rw [hp,show cake d Y (c • x)=c • cake d Y x from ?_, ← smul_sub]; exact Visa.smultC c h.2
        ext1 i; ext1 z; simp only [cake,map_smul,Pi.smul_apply]
variable {A:ℕ→Brush G} {f B:Rich G} {p s:Deck G}
abbrev Grove (q:ℕ+)(R:ℝ)(A:ℕ→Brush G)(B:Rich G)(d j:ℕ)(p:Deck G):Prop:= p∈ grove q R A B d j
lemma imprint (h:Grove q R A B d n p)(he:Grasp f)(hx:k≤d): Visa q R 0 ((k:ℤ)-n) (wreath k d f p):=h.1 f he k hx
lemma impression (h:Grove q R A B d n p)(he:Grasp f)(hx:k≤d): Visa q R k ((k:ℤ)-n) (wreath k d (emerge q f) p):= by
    have hp := Visa.asPow (c:=(k:ℤ)) (imprint h he hx); simp only [add_zero] at hp
    unfold wreath; simp_rw [emerge,dinner, ← zpow_natCast]; exact hp
lemma exit_low (p:Deck G)(A:ℕ→ Brush G)(f:Rich G) : exitP A p= cake d f p+(exitP A p-cake d f p) := by abel
lemma wsum (v:Finset (ℕ×ℕ))(u:ℕ×ℕ→Mist ℂ)(h:∀ i∈v, Visa q R k m (u i)): Visa q R k m (∑ i∈v,u i):= Visa.counts v h
lemma cake_id (f:Rich G)(p:Deck G)(d:ℕ) : cake d f p=∑ i∈range (d+1),wreath i d f p := by funext k z; simp only [wreath, Finset.sum_apply]; change probeL (f k) (level (vapor G) d (trumpet _ _ _ _))=_; rw [trimmer,map_sum]
lemma wreath_mul {v:ℕ}(f:Rich G)(p s:Deck G)(he:v≤d) : wreath v d f (p*s)= ∑ i∈range (d+1),∑ k∈range (d+1), if i+k=v then (wreath i d f p)*(wreath k d f s) else 0:= by
   funext j z; simp only [Finset.sum_apply, wreath,Pi.mul_apply,map_mul]; rw [leaf_mul _ _ _ he,map_sum]; refine Finset.sum_congr rfl (fun _ _=>?_); rw [map_sum]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> first|rfl|rw [map_mul]; rfl|simp
lemma exit_high (f:Rich G)(p s:Deck G) (d:ℕ): cake d f p * cake d f s - cake d f (p*s)= ∑ i∈range (d+1),∑ j∈range (d+1), if d < i + j then (wreath i d f p)*(wreath j d f s) else 0:= by
   ext1 k; ext1 z; simp only [Finset.sum_apply,Pi.sub_apply,Pi.mul_apply]; change probeL (f k) (level (vapor G) d _) * probeL (f k) (level (vapor G) d _)-probeL (f k) (level (vapor G) d ((trumpet (Okay G) (valP (G:=G)) d) (p k z*s k z)))= _; rw [map_mul,← map_mul,← map_sub,AlgHom.toLinearMap_apply,AlgHom.toLinearMap_apply,level_high,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_sum]; apply Finset.sum_congr rfl; intro l _; split_ifs <;> first|rfl|rw [map_mul]; rfl|simp
lemma exit_mul (A:ℕ→Brush G)(p s:Deck G) : exitP A (p*s)=exitP A p* exitP A s:= by funext i z; exact map_mul (snap (A i)) _ _
include hq
lemma Grove.weaken (h:Grove q R A B d n p)(hy:0≤R)(he:m≤n):Grove q R A B d m p:= ⟨fun f hx i hp=> Visa.stretch hq (imprint h hx hp) hy le_rfl (by omega), Visa.stretch hq h.2 hy le_rfl (by omega)⟩
end YM.PositionX.Clove
