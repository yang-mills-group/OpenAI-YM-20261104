import YM.OPE.Compatible.Kiwi.Way
/-! # Wick product estimates forest. Merge two ordered sets -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew Maxwell Maxwell.Free
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{U:Gloam}{P:ChartRatio G}{d k j r w e e' m:ℕ} {I J V:Type}{ℓ:Filter V}[LinearOrder I][LinearOrder J]{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
open Finset
abbrev SubX (V:Crew U)(a:Reed G): Match U G:= ⟨a.1,V,a.2⟩
lemma ship_sub (V:Crew U)(a b:Reed G): rootW (SubX V a) (SubX V b)=firm a b:=by
    unfold firm rootW SubX; simp
-- parse bug
variable (u v:Crew U)(H:∀ p,Even (U.M p).val)
local notation "E!"=> IpT H G
lemma sceneMon (A:Fin r→Reed G)(B:Fin m→Reed G)(ht:rung A Finset.univ=e)(hs:rung B Finset.univ=e')(hp:u≠v)(hx: SpareW u v)(hy: SpareW v u): Vine H (e+e') ((fun i=>PK 0 A Finset.univ (H i) (u.val i))*(fun i=>PK 0 B Finset.univ (H i) (v.val i)) : E!) :=by
    let TC (i:Fin (r+m)): Match U G:= Fin.addCases (SubX u ∘ A) (SubX v ∘ B) i
    let f:= Fin.castAdd m (n:=r); let g:= Fin.natAdd r (m:=m); have hf(i):TC (f i)=SubX u (A i):=by simp [TC, f]
    have hg(i):TC (g i)=SubX v (B i):=by simp [TC,g]; -- parsing
    let p:=Finset.univ.image f; let q:=Finset.univ.image g; let S:=p∪q; let P: E!:=fun i=> fauna (ship TC) (fun j=>ps (TC j) i (H i)) S
    have hA(i)(hi:i∈p): ∃ a,f a=i:= (Finset.mem_image.mp hi).imp fun j h=>h.2; have hB(i)(hi:i∈q): ∃ a,g a=i:= (Finset.mem_image.mp hi).imp fun j h=>h.2
    have hb(i:Fin r)(j:Fin m): f i < g j:=by change i.val<r+j.val;omega
    have hC i(hi:i∈p) j(hj:j∈q):i<j:=by obtain ⟨i,rfl⟩:= hA _ hi; obtain ⟨j,rfl⟩:=hB _ hj; exact hb ..
    have hD:Disjoint p q:= Finset.disjoint_left.mpr fun {i} hi hJ=> lt_irrefl i (hC i hi i hJ)
    have h:S= S:=rfl
    have hW:Wood TC S:=by
      intro a ha b hb h; obtain ha|ha:=Finset.mem_union.mp ha
      · obtain ⟨i,rfl⟩:= hA _ ha; obtain hb|hb:=mem_union.mp hb
        · obtain ⟨b,rfl⟩:= hA _ hb; rw [hf,hf]; exact spunC0 u H
        obtain ⟨b,rfl⟩:= hB _ hb; rw [hf,hg]; exact hx
      obtain ⟨i,rfl⟩:=hB _ ha; obtain hb|hb:=mem_union.mp hb
      · obtain ⟨b,rfl⟩:=hA _ hb; rw [hg,hf]; exact hy
      obtain ⟨b,rfl⟩:=hB _ hb; rw [hg,hg]; exact spunC0 v H
    have he:bud S (wool TC)=e+e':=by unfold bud; rw [Finset.sum_union hD, ←ht, ←hs, Finset.sum_image, Finset.sum_image]; unfold wool; simp_rw [hf,hg]; exact fun _ _ _ _ h=>Fin.natAdd_injective _ _ h; exact fun _ _ _ _ h=> Fin.castAdd_injective _ _ h
    refine _root_.cast (congr_arg (Vine H (e+e')) ?_) (Vine.herm S TC hW he); change P=_; funext i; unfold P; rw [Pi.mul_apply]; let F(j):= ps (TC j) i (H i); have hβ(a)(ha:a∈p) b(hb:b∈q):ship TC a b=0:=by obtain ⟨a,rfl⟩:=hA a ha; obtain ⟨b,rfl⟩:=hB b hb; unfold Shrew.ship; rw [hf,hg]; exact if_neg (fun h=>hp h.2)
    have hρ(j):F (f j)=poseT (H i) (u.val i) (A j).2 (A j).1:=by unfold F; rw [hf]; rfl -- ok
    have hτ(j):F (g j)=poseT (H i) (v.val i) (B j).2 (B j).1:=by unfold F; rw [hg];rfl
    rw [show _=_ from gum_merge (ship TC) F _ _ hC hβ, show fauna (ship TC) F p= _ from gum_lift _ _ f (show StrictMono f from fun i j h=>h) univ, show fauna _ _ q=_ from gum_lift (ship TC) F g (show StrictMono g from fun i j h=> Nat.add_lt_add_left h r) univ, show F ∘ f= _ from funext fun j=> hρ j, show F ∘ g = _ from funext fun j=>hτ j]; unfold Shrew.ship; simp_rw [hf,hg,ship_sub]
end YM.OPE.Prairies
