import YM.OPE.Compatible.Plains.Pyre
/-!
# Leading finite Wick polynomial. transport H⊆...
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{U:Gloam}{d k j r w e m:ℕ}{I:Type}[Fintype I] {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
open Drift Finset
abbrev impress (v:Bead G d e)(i:Fin (e+1)):partX G i.val (e-i.val) d:=(coordinateQ G d e i.val).symm (v i)
abbrev master (v:Bead G d e)(u:Maxwell.TaylorTower G):ℝ:= ∑ i:Fin (e+1), (impress v i).val (fun _=>life u d)
variable {T S: Type}
abbrev visit (p:Seat k m T):Prop:=∀ i:ℕ, Brief (lilies m k T p i)
lemma blankV :Brief (0:Script T k):=⟨∅,fun _ _=>rfl⟩
abbrev manySame {Q H:ℕ} (v:Saga G Q k){h:Q=H}:Saga G H k:= h ▸ v
lemma castPlain {Q H:ℕ}(v:Saga G Q k)(h:Q=H){n:Side}(x: Site n): (manySame v (h:=h)).plain x=v.plain x:=by subst H;rfl
lemma castTer {Q H:ℕ}(v:Saga G Q k)(h:Q=H): (manySame v (h:=h)).terra=v.terra:=by subst H;rfl
lemma newV (h:e ≤m)(hp:e≤k)(x:Bead G d e): ∃ p:bed G k m,p∈fillet G k m e (by omega) ∧stepRead G d e k m h p=x ∧ visit p.val∧ ∃ v:Saga G e k,(∀ n:Side,∀ y:Site n, Strike k (worldR m k y _ p.val)=v.plain y)∧∀ u:Maxwell.TaylorTower G,Maxwell.probe u v.terra = (master x u:ℂ):=by
      let F:= Fin (e+1)
      let A(i:Fin (e+1)):= impress x i
      choose q hx H using fun i: Fin (e+1)=> crystal (A i).val; choose C' hC using fun i=> briefFee (hx i) m; have ht(i):=grammar (A i) (hC i) (H i)
      have hb(i):q i ∈ cope G i.val m:= ⟨⟨_,hC i⟩,(ht i).2.1,(ht i).2.2,(ht i).1⟩
      let f:=∑ i: Fin (e+1),Shell.throw (q i); have hf(i:F): f i.val=q i:=by
           unfold f; rw [Finset.sum_apply,sum_eq_single i]; exact Pi.single_eq_same _ _; exact fun j _ hj=> hubbub (Ne.symm (Fin.val_injective.ne hj)); simp
      have hh(i:ℕ)(hx:e < i): f i=0:=by unfold f; rw [Finset.sum_apply]; exact sum_eq_zero fun j _=> hubbub (by omega)
      let c:=∑ i,C' i; have hc(i):0 ≤ C' i:=Sack.coins (hC i); have hπ :0 ≤ c:=sum_nonneg fun _ _=>hc _; have hg: Volume f k m c:=by
           refine ⟨fun i hi=>hh i (by omega),fun i=>?_⟩; by_cases hx:e < i; rw [hh i hx]; exact Sack.zero hπ _; let j:Fin (e+1):=⟨i,by omega⟩; rw [show f i= q j from hf j]; exact (hC j).tips (single_le_sum (f:=C') (fun i _=>hc i) (mem_univ _))
      let u:=fundus f c hg; have hu:u∈bed G k m:=by intro i; rw [sproutsX]; by_cases hx:e < i; rw [hh _ hx]; exact Submodule.zero_mem _; let j:Fin (e+1):=⟨i,by omega⟩; erw [hf j]; exact hb j
      let a:bed G k m:=⟨u,hu⟩; have hy(i): lilies m k _ a.val i=f i:=congr_fun (sproutsX _ hg) i; refine ⟨a,(decrement a).2 (fun i=>?_),funext (fun i=>?_) ,fun i=>by rw [hy]; by_cases ht:e < i; rw [hh _ ht]; exact blankV; let j:Fin (e+1):=⟨i,by omega⟩; erw [hf j]; exact hx j,?_⟩
      · rw [hy]; by_cases HT:e < i; rw [show e-i=0 by omega]; exact fun _ l hl=>by omega
        let j:Fin (e+1):=⟨i,by omega⟩; erw [hf j]; exact graded_horizon (A j) (hC j) ((Nat.sub_le ..).trans h) (H j)
      · let i':=i.val; let b:= terrace G k m i.val a; have he:b=⟨q i,hb i⟩:=Subtype.ext ((hy i.val).trans (hf i)); change coordinateQ G d e i.val (Flume.Script.tiller G i.val m (e-i.val) _ d b)=_; rw [show Flume.Script.tiller _ _ _ _ _ _ b= A i from ?_]; swap; · rw [he]; exact Subtype.ext (earns (A i) (hC i) (by omega) (H i))
        exact (coordinateQ G d e i.val).apply_symm_apply _
      have hv(i:F):∃ v:Saga G e k,(∀ n: Side,∀ x: Site n, ∀ Y:Ice G n,Flume.Script.value x (f i.val) Y=v.plain x Y) ∧ ∀ u:Maxwell.TaylorTower G, Maxwell.probe u v.terra=((A i).val (fun _=>life u d):ℂ) :=by
           obtain ⟨v,h,hπ⟩:= scenery (A i) k (show i.val≤k by omega); have hk: e-i.val+i.val=e:=Nat.sub_add_cancel (by omega); -- via helper cast
           let V:= manySame v (h:=hk); refine ⟨V,fun n x Y=>?_ , fun u=>by rw [show V.terra=v.terra from castTer ..]; exact hπ u⟩; rw [show V.plain x=v.plain x from castPlain v _ x,hf]; let a':fieldX (Shade G):=fun b=>Y (x+wrap _ b.1,b.2); change scribe x (q i) (fun _=>Y)=v.plain x Y; rw [show scribe _ _ _=wholeX (q i) (fun _=>a') from ?_, H]; exact (h n x Y).symm
           unfold scribe; rfl -- univ product positions coincide
      choose V hV H' using hv; obtain ⟨v,hν,hv⟩:= Saga.ree Finset.univ V
      refine ⟨v,fun n x=>funext fun i=>?_,fun u=>by rw [hν,map_sum];simp_rw [H']; exact (Complex.ofReal_sum ..).symm⟩; rw [hv,Finset.sum_apply,← cadillac]; unfold Flair; simp_rw [show ∀ i,lilies m k _ a.val i= _ from hy, ← hV] 
      rw [show (∑ j:F, (Flume.Script.value x (f j.val) i)) = ∑ j∈ Finset.range (e+1),(Flume.Script.value x (f j) i) from Fin.sum_univ_eq_sum_range (fun j=>Flume.Script.value x (f j) i) (e+1)]
      symm; apply sum_subset (range_mono (by omega)); intro j hj hg; have ht:e<j:=by simp only [Finset.mem_range,not_lt] at hg;omega
      rw [hh j ht]; simp [Flume.Script.value,scribe]
end YM.OPE.Prairies
