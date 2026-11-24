import YM.FullVolume.Nectar.Barons

/-
# Why we can bill only quadratic on any step (except the one-marker-set transfer)

Switch-price s-stature for any incidence per hat (many hats may share same mode, same Wing). The **jet** is exactly multi-affine in switched *radii* through all mergers and contractions, because Models current multiplication at positive t loses cross terms as t approaches zero (don't claim the pre-jet functions have this property). Use even for force-calendar entries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Switch
open PhysicalNext.Repeat FullVolume.Ray Function Filter Finset
open scoped Topology BigOperators Classical
variable {A T:Type}[Fintype A]
local notation "𝕎"=> (A→ℝ)→ Ways A

def Pods (f:(A→ℝ)→Ways A): Prop:= (∀ v,∃ g, Switch.Models (f v) g) ∧ ∀ s (v c:A→ℝ), jet (f (c*v)) s=(∏ i∈s,c i)*jet (f v) s
namespace Pods
omit [Fintype A] in
lemma clicked (h:ℝ)(s:Finset A) : Pods (fun v=> click s ((∏ i∈s,v i)*h)):=by
   refine ⟨fun v=>⟨_,modelClick ..⟩,fun t v c=>?_⟩
   simp_rw [fun p=> (modelClick s p).exact]; unfold bench; split
   next ht=>rw [ht]; simp only [Pi.mul_apply,prod_mul_distrib,mul_assoc]
   rw [mul_zero]
omit [Fintype A] in
lemma fixed (c:ℝ):Pods (fun _:A→ℝ=>fun _ _=>c):=by convert! clicked c (∅:Finset A) using 1; ext; simp [Switch.click]
variable {F G: (A→ℝ)→ Ways A}
omit [Fintype A] in
lemma add (h:Pods F) (he:Pods G): Pods (F+G):=by
   choose f hf using h.1; choose g hg using he.1; refine ⟨fun p=>⟨_,(hf _).add (hg _)⟩,fun s v c=>?_⟩
   have hz (s x): jet ((F+G) x) s=jet (F x) s+jet (G x) s:=by dsimp only [Pi.add_apply]; rw [((hf x).add (hg x)).exact,(hf x).exact,(hg x).exact]; rfl
   simp_rw [hz,h.2 s v c,he.2 s v c,mul_add] -- check
lemma mul (h:Pods F) (he:Pods G): Pods (F*G):=by
   choose f hf using h.1; choose g hg using he.1; refine ⟨fun p=>⟨_,(hf _).mul (hg _)⟩,fun s v c=>?_⟩
   have hz x: jet ((F*G) x) s=comb 0 (jet (F x)) (jet (G x)) s:=by dsimp only [Pi.mul_apply]; rw [((hf x).mul (hg x)).exact,(hf x).exact,(hg x).exact]
   rw [hz,hz]; unfold comb; rw [Finset.mul_sum]; apply sum_congr rfl; rintro ⟨p,q⟩ _; split_ifs with hx; swap; · rw [mul_zero]
   subst s; by_cases hp:Disjoint p q
   · rw [prod_union hp,disjoint_iff_inter_eq_empty.mp hp,Finset.card_empty,h.2,he.2]; ring
   have h: 0<(p∩q).card:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (disjoint_iff_inter_eq_empty.not.mp hp)); rw [zero_pow h.ne']; ring
lemma pow (h:Pods F)(i:ℕ):Pods (F^i):=by
   induction i with | zero=>rw [pow_zero]; exact fixed 1 | succ i ih=> rw [pow_succ];exact ih.mul h
lemma hom (h:Pods F)(x:ℝ): Pods (x • F):= (fixed x).mul h
omit [Fintype A] in
lemma sum (f:T→ (A→ℝ)→ Ways A)(s:Finset T)(h:∀ i∈s,Pods (f i)): Pods (∑ i∈s,f i):=by
   induction s using Finset.induction_on with
   | empty=>simp only [Finset.sum_empty]; exact fixed 0
   | insert i s hi ih=> rw [sum_insert hi];exact (h i (mem_insert_self ..)).add (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma prod (f:T→ (A→ℝ)→ Ways A)(s:Finset T)(h:∀ i∈s,Pods (f i)): Pods (∏ i∈s,f i):=by
   induction s using Finset.induction_on with
   | empty=>simp only [Finset.prod_empty]; exact fixed 1
   | insert i s hi ih=> rw [prod_insert hi];exact (h i (mem_insert_self ..)).mul (ih fun i hi=> h i (mem_insert_of_mem hi))

end Pods
end YM.Merge.Switch
end
namespace YM.Merge.Palette
noncomputable section
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat Greenbelt Lotus Merge Merge.Palette Merge.Switch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {A:Type} [Fintype A] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Gas Ursell Trees Multiple Letter OmitClusters Ovens Ovens.Pipes
open Progress.DirectedRecipe Rack Mallow
variable (H:Cash W x μ L Q o C T R) (M:A→Lotus.Leaf R) (i:ℕ) (U:Config G c)(χ:Chi)
local notation "X₀"=> sign M S
lemma podVote (s:Molecule S) : Pods (fun v=> Palette.vote M H χ v s U):=by
   let f (i:Tickets (sign M S)) (v:A→ℝ):= click i.val ((∏ j∈i.val,v j)*Palette.act M H χ U s i); have he(v:A→ℝ)(l:ℝ)(i:Finset A): Palette.vote M H χ v s U l i=∑ j,f j v l i:=by
      unfold Palette.vote Palette.color; apply sum_congr rfl; intro j _; rw [Palette.amplitudes]; unfold f click; split_ifs <;> ring
   rw [show (fun (v:A→ℝ)=> Palette.vote M H χ v s U)=∑ j,f j from funext fun t=> funext fun l=> funext fun i=> by rw [he]; simp]; exact Pods.sum f _ fun i _=> Pods.clicked ..
lemma podSong (s:H.fragrances) : Pods (fun v=>Palette.song M H χ v s U):=by
    let z:= (s.1+1).factorial; let a:=coefficient H.seam s.2/(z:ℝ); let f k (v:A→ℝ):= Palette.vote M H χ v (s.snd k).val U
    have he: (fun v=> Palette.song M H χ v s U)=a • (∏ i,f i):=by
       funext t x y; simp only [Pi.smul_apply,Finset.prod_apply, smul_eq_mul]; unfold Palette.song Cash.trainedMill Gas.term; change coefficient H.seam s.snd*(∏ i,f i t x y)/(z:ℝ)= _; unfold a; ring
    rw [he]; exact Pods.hom (Pods.prod f _ (fun i _=>podVote H M U χ _)) _
lemma podE (s:H.fragrances) : Pods (fun p=>Photo.tones M H χ p s U):=by
    let f(p:A→ℝ):=Palette.song M H χ p s U; have hp(p:A→ℝ): Palette.ways p 0 ∅=fun _=>0:=by funext i; simp [Palette.ways]
    let a:=H.trainedMill (H.spawn χ U) s; rw [show (fun t=> Photo.tones M H χ t s U)=f+(fun _ _ _=>-a) from funext fun t=>funext fun i=>funext fun l=>by unfold Photo.tones; change f t i l-Palette.song M H χ t s U 0 ∅=f t i l+-a; unfold Palette.song; rw [hp,muted]; exact sub_eq_add_neg ..]; exact (podSong H M U χ s).add (Pods.fixed _)
lemma podColony (j:H.Chapter) : Pods (fun v=>fun l s=>H.cologneMill (fun i=>Palette.vote M H χ v i U l s) j):=by
    rcases j with i|i; exact podVote H M U χ _
    let f(p:A→ℝ):=Palette.song M H χ p i U; have hv: Pods ((-1:ℝ) • f):= Pods.hom (podSong H M U χ i) _
    convert hv using 1; ext; simp; rfl
lemma podFete (j:H.Chainbook) : Pods (fun p=> Palette.fete M H χ p j U):= by
    unfold Palette.fete Cash.smilesMill; split_ifs
    · let n(i:↥j.1):= j.2 i+1; let e(i:↥j.1):ℝ:=((n i).factorial:ℝ)⁻¹; let f(i:↥j.1)(v:A→ℝ)(l:ℝ)(s:Finset A):= H.cologneMill (fun j=>Palette.vote M H χ v j U l s) i.val; let g i:=e i • ((f i)^(n i));
      have hp(i): Pods (g i):= ((podColony H M U χ _|>.pow (n i)).hom _)
      convert Pods.prod g Finset.univ (fun i _=>hp i) using 1; ext t y l; simp only [Finset.prod_apply];apply Finset.prod_congr rfl; intro i _; change (f i t y l) ^(n i)/(n i).factorial= e i*_; simp only [Pi.pow_apply]; unfold e; ring
    exact Pods.fixed _
lemma podPole (j:ℕ){R':RG.Rep G f}(Y:Cash W x μ L Q o C T R')(D:Match.Alliance Y H 1 0): Pods (fun v=>fun t p' => Palette.shoot M H χ v Y D t p' j U):=by
    unfold Palette.shoot Palette.shootK; by_cases he: j∈Set.range (Refrain.visa Y D)
    · obtain ⟨i,rfl⟩:=he; simp_rw [Progress.DirectedRecipe.stuffed]; exact podFete H M U χ _
    simp_rw [Progress.DirectedRecipe.blank _ _ he]; exact Pods.fixed _
variable (p:(A→ℝ)→ ℝ→ Finset A→ Code G c)(P':BudgetPoint)
private lemma consac (D:Pipes G c)(E:ℕ≃ D.Pellet)(F : Tap G c) (h:∀ i U,Pods (fun t y s=> p t y s i U)) : Pods (fun t y s=>solid E P' (spice F (p t y s)) i U):=by
    unfold solid; split_ifs
    · let g (j:Ovens.Label)(t:A→ℝ)(y:ℝ)(s:Finset A):=reach (spice F (p t y s)) j U
      have hv(k):Pods (g k):=by rcases k with l|l; exact h _ _; exact Pods.fixed (Real.exp (F.logarithm l U)-1)
      convert! Pods.prod g (E i).val (fun i _=> hv i) using 1; ext; simp [g]
    exact Pods.fixed _
private lemma saun (D:Pipes G c) (F:Tap G c) (h:∀ i U,Pods (fun t y s=> p t y s i U)): Pods (fun t y s=> final.frigid D F (fun y=>p t y s) P' y i U):=by
   change Pods (fun t y s=>solid (folio G c) P' (spice (widen D F) (stuff (upK D) (p t y s))) i U); refine consac _ U _ _ _ _ _ ?_
   intro i U; by_cases he: i∈Set.range (upK D)
   · obtain ⟨k,rfl⟩:=he; simp_rw [stuffed];exact h k U
   simp_rw [Progress.DirectedRecipe.blank _ _ he]; exact Pods.fixed _
open Testing FullVolume PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Jams PhysicalNext.Repeat.Rain PhysicalNext.Repeat.Mallow
open Push.PriceCompiler Supply Next.Scheduling Input Org Progress.DirectedRecipe Marlin Rack Roof
variable {X: Metals G} {D: Rolls X.p} {A':Alloy X D} {R:Roost.Factor A'}{N n m:ℕ}{t:ℝ}
lemma podK (Y:Chord R N m n t t) (U':Chord.Flight A' N m n) (P:A→Leaf U'.val) (i:ℕ)(u:Config G _): Pods (fun p y s=> Cryst.brands Y U' P p y s i u):=by
    let f(p:A→ℝ) (y:ℝ)(s: Finset A):= Merge.Palette.shoot P (Y.sight U') Chi.canonical p (Y.sight U') (Y.termF U') y s
    have ht:∀ i U, Pods (fun t y s=>f t y s i U):= fun i U=> podPole (Y.sight _) P U Chi.canonical i _ _
    exact saun _ u (fun x y s=>solid _ (A'.B.a.budget m) (spice (Cryst.store Y U') (f x y s))) (A'.B.a.budget m) _ _ (fun j V=> consac j V f _ _ _ _ ht)
end
end YM.Merge.Palette
