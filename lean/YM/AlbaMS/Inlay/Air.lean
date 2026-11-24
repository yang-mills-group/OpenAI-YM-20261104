import YM.AlbaMS.Inlay.Mural

/-! # color shift identity. Needs nodes undropped. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Inlay.Net
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil
variable {V I : Type*}{G:Gauge}[Fintype V][Fintype I]
variable {R J : Type*} [CommRing R] [CommRing J] (w:Flit G I→R)

def air {R:Type*} [CommRing R](w:Flit G I→R): Module.End R (Heave G V I R):= ∑ i:Flit G I,w i • DC i
omit [Fintype V] in
lemma air_ap (F : Heave G V I R): air w F=∑ i:Flit G I,w i • DC i F:=by simp_rw [air, LinearMap.sum_apply,LinearMap.smul_apply]
omit [Fintype V] in
lemma air_simple (F:Heave G V I R)(h:∀ i,DC i F=0): air w F=0:=by simp [air_ap,h]
omit [Fintype V] in
lemma air_prod (F Q:Heave G V I R): air w (F*Q)=air w F *Q+plane true F * air w Q:=by
  have hh i: DC i (F*Q)=DC i F*Q+ plane true F*DC i Q:=rfl; simp_rw [air_ap,hh, Finset.sum_mul,Finset.mul_sum,smul_add,smul_mul_assoc,mul_smul_comm, Finset.sum_add_distrib]
omit [Fintype V] in
lemma air_move (T:R→+*J)(F:Heave G V I R): Wind _ T (air w F)=air (fun x=>T (w x)) (Wind _ T F):=by rw [air_ap,air_ap,map_sum]; refine Finset.sum_congr rfl (fun i _=>?_); rw [Wind_smul]; rfl
omit [Fintype V] in
lemma air_step (z:R)(k:ℕ)(F:Heave G V I R): air w (loom z (k+1) F)=loom z k (air w F):=by rw [air_ap,air_ap,map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul]; congr 1; ext l; simp only [DC, D_read,looms, List.length_cons,Nat.add_sub_add_right]
omit [Fintype V] in
lemma air_rig (Z : Leaf G V I → R)(v:R)(F:Heave G V I R)(h:∀ i,Z (Place.c i)=v): air w (weft Z F)=v • weft Z (air w F):=by simp_rw [air_ap,map_sum,DC,weftD,h,map_smul,Finset.smul_sum,smul_comm (w _) v]

-- real color generator derivative. Before redefinitions. See `fresh`.
variable (Ω : Net V I)(c:G.Color)
def Runs (Ω : Net V I):Prop:= ∀ x, Ω.head x≠none ∧ Ω.foot x≠none
def fill (j:Flit G I):= coefQ j.2 c
def turn (x y:Flit G V):= stip x (adI (fun _=>c) (slabQ y))
def hill : Heave G V I ℝ:=
 (∑ i: Flit G V,K ℝ i * ∑ j:Flit G V, turn c i j • A ℝ j)+(∑ i:Flit G I,L ℝ i*∑ j:Flit G I, turn c i j • C ℝ j)
lemma height : Heg 2 (hill (V:=V) (I:=I) c):=by
  unfold hill; exact (Heg.sum _ _ (fun i _=> (Heg.var _).mul (Heg.sum _ _ fun j _=> ((Heg.var _).smul _)))).add (Heg.sum _ _ fun i _=> (Heg.var _).mul (Heg.sum _ _ fun j _=> ((Heg.var _).smul _))) -- Ω unused
omit [Fintype V] in
private lemma airDK (q:Flit G V): air (fill (I:=I) c) (K ℝ q)=0:=air_simple _ _ (fun i=>by simp [DC,K, Place.k,Place.c])
omit [Fintype V] in
private lemma airDL (q:Flit G I): air (fill c) (L (E:=Flit G V) ℝ q)=0:=air_simple _ _ (fun i=>by simp [DC,L,Place.l,Place.c])
omit [Fintype V] in
private lemma airC (q:Flit G I): air (fill c) (C (E:=Flit G V) ℝ q)= put ø (fill c q):=by rw [air_ap, Finset.sum_eq_single q]; simp only [C,DC,varD,if_true, ← put_smul_left,mul_one]; intro a _ ha; simp [C,DC,ha, Place.c]; simp
omit [Fintype V] in
private lemma airG (j:Flit G I): air (fill c) (rod (E:=Flit G V) (grit G I) j)= -∑ i:Flit G I,turn c j i • C ℝ i:=by
  simp_rw [air_ap, rodD, smul_neg, Finset.sum_neg_distrib]; congr 1; simp_rw [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [← Finset.sum_smul]; congr 1
  have hu : ∀ k:Flit G I,stip k (fun _=>c)=fill c k:=fun _=>rfl
  let F: ink G I→ₗ[ℝ] ℝ:= coefQ j.2 ∘ₗ (G.ad.flip ((slabQ i) j.1)) ∘ₗ LinearMap.proj j.1
  change _= F (fun _ => c); rw [← slab_total (fun _=> c),map_sum]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [map_smul, grit_price]; rfl
lemma BeamC (R:Runs Ω)(e: Flit G V): air (fill c) (beam Ω.chat e)= -∑ j:Flit G V,turn c e j • A ℝ j:=by
  let C:=pathof G V I; let L: ink G V→ₗ[ℝ]ℝ:= stip e ∘ₗ LinearMap.pi (fun i=> G.ad c ∘ₗ LinearMap.proj i); let T:Grove (ink G V):=⟨L,L.toContinuousLinearMap.contDiff.contDiffAt⟩
  have he : (∑ j:Flit G V,turn c e j • A ℝ j)= C.shine T:=by
    rw [show T=⟨L.toContinuousLinearMap,_⟩ from rfl,C.lit_sheet L.toContinuousLinearMap Finset.univ (by simp)]; simp only [Fintype.sum_sum_type, C, map_zero,zero_smul,Finset.sum_const_zero,add_zero]; rfl
  have hH : (∑ j: Flit G I, fill c j • Ω.chat j e)= - C.shine T:=by
    let X:ink G I:=fun _=>c
    have hx: ( (-1:ℝ) • T).val=ᶠ[𝓝 0] ∑ i:Flit G I,(fill c i • Ω.spotG i e).val:=by
      filter_upwards [tide (G:=G) (V:=V)] with y hy
      have ht (i) (h : i≠(none:Option I)): pads i X=c:=by cases i; exact False.elim (h rfl); rfl
      have hv : arch (y e.1) (coast Ω e.1 X)= G.ad (y e.1) c:= (by rw [show coast Ω e.1 X=(c,c) from Prod.ext (ht _ (R e.1).1) (ht _ (R e.1).2)]; exact (hy e.1).regain c)
      suffices -L y= stip e (current Ω y X) by
        rw [Finset.sum_apply]; change (-1:ℝ)*L y=_; rw [neg_one_mul,this,← slab_total X]; simp_rw [map_sum,map_smul]; rfl
      rw [stip_at, Ω.current_apply, hv, ad_flip (y e.1), map_neg]; rfl
    have hh:=C.flash _ _ _ hx; simp_rw [Brook.gleam_smul] at hh; simp only [neg_one_smul] at hh; exact hh.symm
  unfold beam; rw [map_sum]; simp_rw [air_prod, show ∀ i,air (fill c) (Ω.chat i e)=0 from fun i=>air_simple _ _ (bare_simple _).2, mul_zero,add_zero, airC, put_smul_left]; rw [he]; exact hH
lemma shift_force (h : Runs Ω)(F:Grove (ink G V)): air (fill c) (superb (grit G I) Ω.chat (bare F))=hill c:=by
  have ht (v:Flit G V) : air (fill c) (K ℝ v * beam Ω.chat v) = K ℝ v * ∑ j:Flit G V, turn c v j • A ℝ j:=by rw [air_prod,BeamC Ω c h,airDK, (var_tone (ρ:=ø) (Place.k v)).pl, zero_mul,zero_add,show sting (true && ø _) (K (B:=Flit G I) ℝ v)= -K ℝ v from rfl,neg_mul_neg]
  unfold superb feeds; simp_rw [map_sub,map_add,map_sum,air_simple (fill c) (bare F) (bare_simple F).2,ht,air_prod, airDL,airG, show ∀ j:Flit G I,plane true (L (E:=Flit G V) ℝ j)= L ℝ j from fun i=>(var_tone (R:=ℝ) (ρ:=ø) (Place.l i)).pl true]; simp [hill,Finset.sum_neg_distrib]
end YM.MSBar.Inlay.Net
