import YM.FormalBulk08.Kemp.Loop

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree Wine
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J X: Type*} {η θ A B : ℝ} {l i u j t r D d : ℕ}{K: KernelChoices}{a:Loc G 1}{s: Signed}
variable {Y X T Z:Anthem D G}
lemma Son.add (h:Son Y X l s)(e:Son T Z l s)(hy:Wade a Y l)(hz:Wade a X l)(hY:Wade a T l)(hZ:Wade a Z l): Son (Y+T) (X+Z) l s:= by
    intro n p I i f g k hf hg h0 h1 hk hp he; simp only [Pi.add_apply]; rw [banner_add _ _ _ _ (hy.summable _) (hY.summable _),banner_add _ _ _ _ (hz.summable _) (hZ.summable _),map_add,map_add]; exact congr_arg₂ _ (h n p I f g k hf hg h0 h1 hk hp he) (e n p I f g k hf hg h0 h1 hk hp he)
lemma Son.launch (p:Pence)(h:Son Y X l s)(hy: Wade a Y l)(hx: Wade a X l): Son (launch p Y) (launch p X) l s:= by
    intro n f I i u v k U V a b hz ht hi; rw [banner_mul hy, banner_mul hx,map_mul,map_mul,worm_roam,worm_roam, h n f I u v k U V a b hz ht hi]
lemma son_zero : Son (0:Anthem D G) 0 l s:= by intro n x I i f g k _ _ _ _ _ _ _; rw [Pi.zero_apply,Pi.zero_apply, banner_zero,map_zero,map_zero]
lemma launch_lin (b:Pence) (h:IsLinearMap ℝ Y): IsLinearMap ℝ (launch b Y) := by
    refine ⟨fun x y=>?_,fun c x=>?_⟩
    · funext i j p; unfold launch surf; rw [h.map_add]; simp [Finset.sum_add_distrib]
    funext i j p; unfold launch surf; rw [h.map_smul]; simp only [Pi.smul_apply,Finset.sum_apply, smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _;ring
structure Clef (a: Loc G 1) (Y: Anthem D G)(l:ℕ): Prop extends IsLinearMap ℝ Y where
    fare:Wade a Y l
    ward: Solo Y l
lemma Clef.launch (p:Pence)(h:Clef a Y l): Clef a (launch p Y) l:= ⟨launch_lin p h.toIsLinearMap,h.fare.launch p,h.ward.launch p h.fare h.fare⟩ -- field notation? Solo
lemma Clef.add (h:Clef a Y l)(e:Clef a X l):Clef a (Y+X) l:= by
    refine ⟨⟨fun x y=>?_,fun c x=>?_⟩,h.fare.add e.fare,h.ward.add e.ward h.fare h.fare e.fare e.fare⟩
    · simp only [Pi.add_apply,h.map_add, e.map_add]; abel
    simp only [Pi.add_apply,h.map_smul,e.map_smul,smul_add]
lemma Clef.smul (h:Clef a Y l)(c:ℝ): Clef a (c • Y) l:=by rw [←launch_C]; exact h.launch _
lemma Clef.neg (h:Clef a Y l): Clef a (-Y) l:= by simpa using h.smul (-1)
lemma Clef.sub (h:Clef a Y l)(e:Clef a X l): Clef a (Y-X) l:=sub_eq_add_neg Y X ▸ h.add e.neg
lemma Clef.base : Clef a (0:Anthem D G) l:= ⟨⟨by simp,by simp⟩,wade_zero,son_zero⟩
lemma Clef.sum {I:Type*}(S:Finset I)(P:I→Anthem D G)(h:∀ i∈S,Clef a (P i) l): Clef a (∑ i∈S,P i) l:= by
    induction S using Finset.induction with
    | empty=>simp only [Finset.sum_empty]; exact Clef.base
    | @insert i S he ih=> rw [Finset.sum_insert he];exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))

variable (a)(P:Flight j t)(V:Lodge P.patch)(Y: Anthem D G)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)
    (hp: Clef a Y l)(hv: Story W (pink K.penalty P.wing))(hr: LocalRatio ρ)(hL:2≤P.L.val)
    (ht:4≤t)
include hp hv hr ht
lemma linear_step (d:ℕ): Clef a (quick P V W Y ρ h hL d l) l:= by
   let k n:=Classical.choice (chooseable n _ (primary P.patch K n));
   let Z (x:Dawn.Studio D) (n:Side):= quickP P V W Y ρ h hL d l x n (k n);let T:= quick P V W Y ρ h hL d l;
   have he (e r p): Light (T p e r) (fun n=>rancho (Z p n) e r):=((brig a P V Y W ρ h hp.fare hv hr hL ht le_rfl k e r d).choose_spec.2.1 p).1
   refine ⟨⟨fun x y=>?_, fun c x=>?_⟩,quick_Wade a P V Y W ρ h hp.fare hv hr hL ht le_rfl d,son_step a P V Y Y W ρ h hp.fare hv hr hL ht hp.fare 1 hp.ward d⟩
   · have hx n: Z (x+y) n=Z x n+Z y n := by
        let K :=preQ a P V W ρ h hp.fare hL (le_refl l) k;unfold Z; simp_rw [K]; rw [←mul_add,← Finset.sum_add_distrib]; apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_add,hp.map_add,banner_add _ _ _ _ (hp.fare.summable _) (hp.fare.summable _), resite,map_add,tossed_pp];rfl
     funext e r v; refine tendsto_nhds_unique (he e r (x+y) v) ((((he e r x v).add (he e r y v))).congr' (.of_forall (fun n=>?_)))
     simp only [hx,rancho,map_add,marble_add];rfl
   have hx n : Z (c • x) n=worm _ (C c) * Z x n:= by
       unfold Z; rw [←PactQ a P V W _ h hp.fare hL (le_refl l) k, preQ a P V W _ h (hp.launch _).fare hL le_rfl k, launch_C,preQ a P V W _ h hp.fare hL (le_refl l) k]; apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_ ; simp only [map_smul,hp.map_smul,Pi.smul_apply]
   funext e r v; apply tendsto_nhds_unique (he e r (c • x) v) (((he e r x v).const_mul _).congr' (.of_forall (fun n=>?_)))
   simp only; rw [hx,worm,PowerSeries.map_C]; change c * marble r (coeff e _) _= marble r (coeff e _) _; rw [coeff_C_mul,←MvPolynomial.smul_eq_C_mul, ← canyon_eq,←canyon_eq,map_smul]; rfl
end YM.FormalBulk08.Kemp
