import YM.X.Chili.Bone
/-!
# Wick stencil inputs in charged mon hats
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze MvPolynomial Finset LiftMark Tensor Ocean
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m n d w:ℕ} {G:Gauge} {R T':ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "T"=> Reed.Horizontal G
variable (b:Bool)
lemma layer_power (i:ℕ)(S:Submodule ℝ (Fan G)){p:Curly G}(h:p∈verse S n): p^i∈verse S (i*n):= by induction i with| zero=> rw [pow_zero,Nat.zero_mul];apply verse_one| succ i IH=> rw [pow_succ,add_mul,Nat.one_mul]; exact verse_mul S IH h
lemma layer_prod {V:Type*} (l:Finset V)(w:V→ℕ)(p:V→Curly G)(S:Submodule ℝ (Fan G))(h:∀ i∈l,p i∈verse S (w i)): (∏ i∈ l,p i)∈verse S (∑ i∈l,w i):= by
    induction l using Finset.induction_on with
    | empty=>rw [Finset.prod_empty,Finset.sum_empty]; exact verse_one
    | insert i l hi IH=> rw [Finset.prod_insert hi,Finset.sum_insert hi];exact verse_mul S (h i (by simp)) (IH (fun j hj=> h j (by simp [hj])))
lemma layer_sub {V:Type*}(w:V→ℕ)(F: poly V→ₐ[ℂ] Curly G)(S:Submodule ℝ (Fan G)){p:poly V}(h:Strong w n p)(hx:∀ i:V,F (MvPolynomial.X i)∈ verse S (w i)): F p∈verse S n:= by
    nth_rw 1 [p.as_sum]; rw [map_sum]; apply Submodule.sum_mem; intro i hi; apply weaken_v (sturdy.mp h i hi); rw [MvPolynomial.monomial_eq,map_mul, show F (C (coeff i p))= C (coeff i p) from F.commutes _, Finsupp.weight_apply, ← Nat.zero_add (Finsupp.sum _ _), Finsupp.sum, Finsupp.prod]; rw [map_prod]; refine verse_mul _ (verse_C _) (layer_prod i.support (fun z:V=>i z • w z) _ _ ?_); intro j _; rw [map_pow]; exact layer_power _ _ (hx j)
lemma press_word (p:Word G): looking p∈verse T p.d:= by
    rw [← loom_eq p.d]; refine layer_sub Configuration.bear (assignP p.d) T (strong_world p (le_refl p.d)) ?_; intro i; rw [assign_post]; have he := plus₁ i; let f:=Configuration.bear i -1; have ht: Configuration.bear i=f+1:=by omega
    rw [ht]; exact verse_glyph (k:=f) (occ Heat.Ray.address p.d i) (omen Heat.Ray.address p.d i)
lemma press_loom (p:poly (Atom G)): loom p∈verse T 0:= by rw [← light (n:=0) p]; apply layer_sub (fun i=>0) (assignP 0) T Strong.first; intro i; rw [assign_post]; exact weaken_v (show 0≤0+1 by omega) (verse_glyph (f:= postP 0 i) (by rw [grade0]; simp) (omen Heat.Ray.address 0 i))
-- basic transfer of verse to static Jar
lemma playJ {S:Submodule ℝ (Fan G)}(l:List (Bone G S)): Jar b G q R (feelB l) (floatP b (playB l)):= by
    induction l with
    | nil=> change Jar _ _ _ _ 0 (floatP b 1); rw [map_one]; exact Jar.unit
    | cons a l IH=> change Jar _ _ _ _ (a.k+1+feelB l) (floatP b (glyph _ * playB l)); rw [map_mul, float_glyph]; exact (Jar.fume _ a.order).plus IH
lemma Jar.venue {S:Submodule ℝ (Fan G)}{p:Curly G}(h:p∈verse S n): Jar b G q R n (floatP b p):= by
    induction h using Submodule.span_induction with
    | mem p h=> obtain ⟨l,h,rfl⟩:=h; exact (playJ b l).weaken h
    | zero=> rw [map_zero];exact Jar.zero _
    | add a c x y ih ig=> rw [map_add]; exact Jar.add ih ig
    | smul a i h ih=> rw [map_smul];exact Jar.scale a ih

-- cubic heat insertion. translations of field. use S not horizontal
lemma dress_fire (p:PlaqAxes)(x:Cover): flashVertex (G:=G) (x,p)= dress x (vertex p):= by
    apply snap_ext; intro A; let y:= lowerP x A; let a:= p.val.1; let b:=p.val.2
    rw [flashVertex,dress_eval,mark_test,fired_top]; rw [Log.flame_root _ _ (by omega),if_neg (by decide),if_pos rfl]; dsimp only;
    have he(z:Cover)(j:Axis): y (z,j)=A (x+z,j):= rfl
    change Complex.ofReal (inner ℝ (Stems.curl _ _ _ _) (Log.fire _ x a b))=Complex.ofReal (inner ℝ (Stems.curl _ _ _ _) (Log.fire y 0 a b)); rw [show Log.fire y 0 a b= Log.fire A x a b from ?_]; congr 2; unfold Stems.curl; change _= y (0,a)+y (0+step a,b)-y (0,b)-y (0+step b,a); simp only [zero_add,he,add_zero]; rfl
    unfold Log.fire; simp only [zero_add,he,add_zero]
lemma verse_x (i:Hair G): MvPolynomial.X (R:=ℂ) i∈ verse (G:=G) ⊤ 1:= by rw [show MvPolynomial.X i= glyph (com (Finsupp.single i 1)) from by rw [com_text,blade,Finsupp.linearCombination_single,one_smul]]; exact verse_glyph (k:=0) (by rw [grade0]; simp) (by simp)
lemma fire_verse (p:PlaqAxes): vertex p∈ verse (G:=G) ⊤ 4:= by
    rw [trinity]; refine Submodule.sum_mem _ (fun i _=> Submodule.sum_mem _ (fun j _=> Submodule.sum_mem _ (fun k _=>?_))); refine Submodule.smul_mem _ _ (verse_mul ⊤ (n:=2) (k:=2) ?_ ?_)
    · rw [faceText, ← com_text]; let x:Address G:=(0,p,i); exact verse_glyph (k:=1) (arc_occ x) (by simp)
    unfold shiftProduct; simp only; repeat (first|apply Submodule.sub_mem|apply Submodule.add_mem|apply (verse_mul ⊤ (n:=1) (k:=1))|apply verse_x)
end YM.PositionX.Clove
