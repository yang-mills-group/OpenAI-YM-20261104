import YM.MS.Cylinder.Composite
import YM.MS.Cylinder.Blend
import YM.MS.Color.Group
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Coh
/-!
# Compact color substitution

Paint all variables in root generator algebra, not active ones only. Cylinder→cylinder on
 any `I` background. Universal rule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder
open Function Filter Finset Set Koszul Color Landau Taylor Slim
open scoped Topology ContDiff
variable {G: Gauge} {A P I J X:Type*}(N: A≃ (I×CI G))(u:G.El)(M:J ≃ (P×CI G))
open Classical in
def tintR (N: A≃ (I×CI G))(u:G.El) (x y:A):ℝ:= if (N x).1=(N y).1 then weight u (N x).2 (N y).2 else 0

def tintC (x y:A):ℂ:= tintR N u x y
lemma glow (x:A) i (j): tintC N u (N.symm ((N x).1,i)) (N.symm ((N x).1,j)) = wc u i j:= by simp [tintC,tintR,wc]
lemma offR (x y:A)(h:(N x).1 ≠ (N y).1): tintR N u x y=0:=if_neg h
lemma offC (x y:A)(h:(N x).1 ≠ (N y).1): tintC N u x y=0:=by simp [tintC,offR _ _ _ _ h]
lemma slender : Slim (tintC N u):=fun i=> (Set.finite_range (fun j:CI G=> N.symm ((N i).1,j))).subset (fun x h => ⟨(N x).2, by
     refine N.injective ?_; simp only [Equiv.apply_symm_apply]; refine Prod.ext ?_ rfl; exact Classical.byContradiction (fun he=> h (offC _ _ x i (Ne.symm he)))⟩)
def paint (N: A≃ (I×CI G))(u:G.El): Cyl A ℂ→ₗ[ℂ] Cyl A ℂ:= arrive (tintC N u) (slender N u)
lemma hint (i : I)(a b:CI G): tintC N u (N.symm (i,a)) (N.symm (i,b))=wc u a b:= by simp [tintC,tintR,wc]
-- compute generator transformation. no power
lemma stroke (i:I)(j:CI G): paint N u (single (N.symm (i,j)))=∑ k:CI G, wc u k j • single (N.symm (i,k)):= by
    apply Subtype.ext; apply ext_D; · simp [paint,single,atLetter]
    intro x; obtain ⟨⟨s,b⟩,rfl⟩:=N.symm.surjective x; simp_rw [paint,lands,names,sum_stack,smul_stack,map_sum,map_smul]
    by_cases he:s=i; swap
    · rw [offC _ _ _ _ (by simpa using he),zero_smul]; exact Eq.symm (Finset.sum_eq_zero fun i' _=> by rw [show D _ (single _).val=0 from unheard (N.symm (i,i')) (by simp [he]),smul_zero]) -- simp injection
    subst s; rw [Finset.sum_eq_single b]; rw [hint,show D (N.symm _) (single _).val=_ from hear (N.symm (i,b))]; -- orientation
    · intro c hc ht; rw [show D _ (single _).val=_ from unheard (N.symm (i,c)) (by simp [ht.symm]),smul_zero]
    simp
lemma mood {p:Sector A}(hp:∀ i j,(N i).1=(N j).1→p i=p j): Tie p p (tintC N u):= by
    intro i j hh; apply hp; exact Classical.byContradiction fun he=> hh (offC N u j i (Ne.symm he))
lemma paint_couple {p:Sector A} (hp: ∀ i j,(N i).1=(N j).1→p i=p j) (F H:Cyl A ℂ): paint N u (couple p F H)= couple p (paint N u F) (paint N u H):= (slender _ _).connect (mood _ _ hp) ..
lemma paint_pass (r:A→J)(s:I→P)(H:∀ i j,r (N.symm (i,j))=M.symm (s i,j))(F:Cyl A ℂ): Ferry r (paint N u F)=paint M u (Ferry r F):= by
   refine Subtype.ext ((slender N u).commute (K:=tintC N u) (T:=way r) (U:=way r) (L:=tintC M u) (way_thin r) F (fun i=> ?_))
   obtain ⟨⟨a,c⟩,rfl⟩:= N.symm.surjective i; suffices Ferry r (paint N u (single (N.symm (a,c))))=paint M u (Ferry r (single (N.symm (a,c)))) from congr_arg Subtype.val this
   rw [escort,H]; simp_rw [stroke,map_sum,map_smul,escort,H]

variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
section
variable [Fintype A]
lemma homesick (W:A→ E)(i:I)(c:CI G): ∑ x:A,tintR N u (N.symm (i,c)) x • W x=∑ j:CI G, weight u c j • W (N.symm (i,j)):= by
   classical
   -- I maybe infinite if G.color cardinal zero. c witnesses
   haveI : Finite I:= by letI : Fintype (I×CI G):= Fintype.ofEquiv A N; exact Finite.of_injective (fun i:I=>(i,c)) (fun _ _ h => congr_arg Prod.fst h)
   letI := Fintype.ofFinite I
   -- sum via N equiv expects same Fintype as sum_prod. remove previous
   rw [← Equiv.sum_comp N.symm , Fintype.sum_prod_type]; simp [tintR,ite_smul]
lemma tint_ink {f:E→ℝ} (h:germ f)(V W:A→E)(hp:∀ i j,W (N.symm (i,j))=∑ c:CI G, weight u j c • V (N.symm (i,c))): (paint N u (region.symm (ink V f))).val=ink W f:= (scale_pos V W (tintR N u) (fun i=>by obtain ⟨⟨s,a⟩,rfl⟩:= N.symm.surjective i; rw [homesick,hp s a]) h).symm
end
lemma palette (i:I)(k:CI G)(F:Cyl A ℂ): enter (N.symm (i,k)) (paint N u F)=∑ j:CI G, wc u k j • paint N u (enter (N.symm (i,j)) F):= by
    classical
    obtain ⟨s,hs⟩:=fromCyl F; let e: CI G ↪ A:= ⟨fun j=>N.symm (i,j),fun _ _ h=> congr_arg Prod.snd (N.symm.injective h)⟩; let s' := Finset.univ.map e
    unfold paint; rw [(slender N u).drop _ _ (s:=s' ∪ s) (hs.mono (by simp)),map_sum]; simp_rw [map_smul];
    rw [← Finset.sum_subset (Finset.subset_union_left (s₁:=s')) ?_]; swap
    · intro j _ hj; rw [offC N u _ j ?_,zero_smul]
      intro hh; apply hj; refine Finset.mem_map.mpr ⟨(N j).2, Finset.mem_univ _, N.injective ?_⟩; change N (N.symm (i,(N j).2))=_; exact Prod.ext (by simpa using hh) (by simp)
    unfold s'; rw [Finset.sum_map]; apply Finset.sum_congr rfl; intro j _; change tintC N u (N.symm _) (N.symm _) • _=wc u k j • _; rw [hint]; rfl
end YM.MS.Cylinder
