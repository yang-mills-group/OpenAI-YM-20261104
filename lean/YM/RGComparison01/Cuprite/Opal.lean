import YM.RGComparison01.Purity

/-!
# New permitted application in real support stars

 Uses real aggregated model `Trio.ornament` of itself *in full sized
 stencil*& auxiliary candidates. Because such summed V_i controls may
 not be invariant or phase-repeatable individually (torons outside), keep
 old receipt relation when NOT booking this syntax. On this new branch,
 STUDIO reconstructs through the unmarked logical comparison loading NO
 model at all into the soft steam. At z=same support scale as before.
 Doesn't charge the new projected model separately for occupying
 a different paper: it occupies exactly Title V for this choice, in the
 real volume. Log equality exposed via ordinary signed-log output.Cancellation
 *within that basis*. Future tensors at this A.Context need to justify any
 mask allocations/prices on these new V, no extra input physics implied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Purity
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Trio
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open RG.Supply RG.Shoot Push.Uniform Sienna Pane
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {U : Stars→Side} {g t V' u W m m' p θ : ℝ} {n k k' b z w r: ℕ} {c C F L:Side} {K : Teller G} {Y : ℝ} {Q : ConnectedActivityE6.Target G K} {o : Target.Order G Y}
section pencil
variable {f : Side} {S : StepData c f} {T : Tube G S} {R : RG.Rep G f} {κ : Chi}
  {H : Cash Y u t L Q o W T R} {ι:Type} (D : Cabinet ι H b) (P : BudgetPoint)
  (n k : ℕ) (g : ℝ) (κ : Chi) (A : ∀ i, (U i).val=2*(w+i.val)) (z : ℕ)
  (V M : ∀ i:Stars, Trio.Offer G (U i))
  (F : Trio.Offer G c)
set_option quotPrecheck false
local notation "h" => D.tot κ n k g
local notation "B" => Cabinet.studio b n (radiusB u)
local notation "oW" => (plusone H (selfA H) κ g)
local notation "Θ" => ((Beam.marquee H P).read)
local notation "P'" => D.leftward κ g n k
local notation "g'" => (h-F)
local notation "σ" => Trio.ornament (c:=c) A (V-M)
local notation "F₀"=> Trio.ornament (c:=c) A M
lemma shade_one (i:Stars)(x:Site c) : Slide.shape (Trio.pad A i) x (1:Config G c)= 1:= by
   funext j; unfold Slide.shape; split; rfl
   split; · simp
   rfl
lemma germ (x:Site c) : Trio.ornament (G:=G) (c:=c) A M x 1=0:=by
   rw [Trio.orchard]; rw [Finset.sum_apply]; refine Finset.sum_eq_zero fun i _=>?_; rw [Pi.smul_apply,Function.comp_apply, shade_one A]; simp [Boulevard.stillA]

lemma salute : Trio.ornament (c:=c) A (V-0) + 0= (σ)+F₀:=by
  simp only [sub_zero,add_zero]; ext x v; change Trio.ornament A V x v=_+_; simp only [Trio.orchard,Finset.sum_apply,Pi.smul_apply,Function.comp_apply]; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> ?_
  rw [← smul_add]; apply congr_arg (ray i • ·); unfold Trio.froth stillA; simp only [Pi.sub_apply, Finset.sum_sub_distrib]; ring
lemma orthodox : Trio.Mirrors (G:=G) (c:=c) 0:=by exact fun i s t V=>rfl
lemma firstStar : Trio.CompatibleP («Y»:=U) (G:=G) P r (0:Trio.Offer G c) 0:=by exact ⟨fun i s b j t=> rfl,fun i j x y u V _ _ _=> rfl,fun i x y V t _ _ _=> rfl,fun x y v hx=>rfl⟩
-- same invoice PRICE_B. Local.Supply.R.K. Standing Proof on new calls.
def dispatch := if F=Trio.ornament (c:=c) A M then steam D P n k g κ A z V 0 0 else steam D P n k g κ A z V M F
local notation "Σv" => dispatch D P n k g κ A z V M F
variable (ho: Collection.Local (Beam.marquee H P) P (plusone H (selfA H) κ g) m m')
    (hM : F≠ Trio.ornament (c:=c) A M → Trio.Mirrors F) (hH: P.B=radiusB u) (hA : 2*Cabinet.studio b n (radiusB u) ≤ w) (he:w+4≤z)
include ho hM
lemma pressed (x : Config G c) : (Θ oW).additive P x= (Θ P').additive P x+
    Fintype.card (Site c)*g' 0 1 + (∑ i, masked P.threshold (neighbors z i) ((σ+F) i) x) + ∑ i, Σv i x:= by
   unfold dispatch; split
   next hF=>
      simp only [hF]; rw [← salute]; refine Eq.trans (transfers D P n k g κ A z V 0 0 ho orthodox x) ?_
      have hh : (h- Trio.ornament (c:=c) A M) (0:Site c) 1=(h-0) 0 1:= by simp [Purity.germ];
      rw [hh] -- hF may rewrite ht in transfers inference
   next hF=> exact transfers D P n k g κ A z V M F ho (hM hF) x
omit ho hM
include hH hA he
lemma irritable (i:Site c) (hx:4*B+16≤c.val) (ht : Trio.CompatibleP P B h V) (hu:F ≠ Trio.ornament (c:=c) A M→ Trio.CompatibleP P B F M) (X : Config G c) (hm:Healthy P.threshold (neighbors (2*z) i) X) : Σv i X=0:= by
   unfold dispatch; split
   next hzz=> exact resolves D P n k g κ A z V 0 0 hH hA he i hx ht (firstStar P) X hm
   next hzz=> exact resolves D P n k g κ A z V M F hH hA he i hx ht (hu hzz) X hm
variable (hZ : ∀ x,P.Regular (neighbors z x) (F x)) (hq : ∀ i j,P.Regular univ (V i j)) (hp : ∀ i j,P.Regular univ (M i j))
include hZ hq hp ho
lemma mile (i:Site c) : Trio.Tidy P (neighbors (2*z) i) (Σv i) := by
   unfold dispatch; split
   next hzz=> exact Purity.tides D P n k g κ A z V 0 0 ho hH hA he (fun _=> CouplingShape.reg_const _) hq (fun _ _=>CouplingShape.reg_const _) i
   next hzz=> exact Purity.tides D P n k g κ A z V M F ho hH hA he hZ hq hp i
omit hp hq hZ hA
lemma salary (x:Site c)(v:Stars→ℝ)(hV0 : F=Trio.ornament (c:=c) A M → (0 ≤ p ∧ ∀ i (y:Config G (U i)), flags P.threshold y=∅→∀ x, ‖V i x y‖≤ v i))
    (hf : F≠Trio.ornament (c:=c) A M → (∀ i,P.supBounds i (neighbors z i) (F i) p) ∧ (∀ i (y:Config G (U i)), flags P.threshold y=∅→∀ x, ‖(V-M) i x y‖≤ v i))
    (Y : Config G c) : ‖Σv x Y‖ ≤ let f:=(ballCost B:ℝ)*m; f+p+(f+p)+ ∑ i:Stars, |Slide.ray i| *((Fintype.card (Site (U i)):ℝ)*(v i+v i)) := by
   unfold dispatch; split
   next hx=> exact Purity.desk D P n k g κ A z V 0 0 ho hH he x v (fun i=> VerifiedReset.sup_le (CouplingShape.sup_const _) (show |(0:ℝ)| ≤ p from (abs_zero (α:=ℝ)).symm ▸ (hV0 hx).1)) (fun i v hV t=> by rw [sub_zero]; exact (hV0 hx).2 i v hV t) Y -- edit
   next hx=> exact Purity.desk D P n k g κ A z V M F ho hH he x v (hf hx).1 (hf hx).2 Y
end pencil
end YM.RGComparison01.Purity
