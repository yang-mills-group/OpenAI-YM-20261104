import YM.SchemeConversionRG11.FirstW.Lien.Phase
/-! Triangular interpolation, no surjectivity of the Taylor map assumed. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels
open scoped BigOperators Classical
variable {G:Gauge} {i j k:ℕ} (p: Rhythm G)
lemma poem (q:Reel G) : ∃ L:Rhythm G,∀ u v:la G,L u v=chord u.val v.val q.val:=by
 obtain ⟨P,hp⟩:=bills q; let R:la G →ₗ[ℝ] Field4 G := (cabin G 4).subtype; exact ⟨(P.comp R).compl₂ R,fun u v=>by simp only [LinearMap.comp_apply,LinearMap.compl₂_apply,R,Submodule.subtype_apply]; exact hp _ _⟩
lemma choir (i:ℕ)(h:i+1+(i+1)=k)(hf:k≤4)(e:ToneR p k): ∃ q:Reel G,∀ x y:la G,x.val∈cabin G (i+1) → y.val∈cabin G (i+1) → p x y=chord x.val y.val q.val := by
 have hp : i+1≤4:=by omega
 obtain ⟨L,B,q,u,hL,HB⟩:=chooses_pair p e hf i i h hp hp
 refine ⟨q,fun x y ha hb=>?_⟩
 let X:Nu G (i+1):= ⟨x.val,ha⟩; let Y:Nu G (i+1):=⟨y.val,hb⟩; have hx: boards _ hp X=x:=Subtype.ext rfl; have hy:boards _ hp Y=y:=Subtype.ext rfl
 have hxX : X.val=x.val:=rfl; have hyY:Y.val=y.val:=rfl
 rw [←hxX,←hyY]
 rw [u,hL X,hL Y,HB X Y,HB Y X,pin,pin,hx,hy,(e y x).1]; ring
-- weight i+2 with one native lower-gradient test; suppress the reflected interpolation response *on both legs with smaller first-slot weight*
lemma flips (i:ℕ) (h:i+1+1=k) (hK:k≤4) (H:ToneR p k) (hr : pastR p k) (he:1 ≤ i) :
    ∃ q:Reel G, (∀ x y:la G,x.val∈cabin G (i+1) → y.val∈cabin G 1 → p x y=chord x.val y.val q.val) ∧
      ∀ x y:la G,x.val∈cabin G i → y.val∈cabin G i → chord x.val y.val q.val=0 := by
  have hi : i+1≤4:=by omega
  have hj:0+1≤4:=by decide
  obtain ⟨L,B,q,u,hL,hB⟩:= chooses_pair p H hK i 0 h hi hj
  let P:= patchR p _ _ hi hj
  have hp (x:la G) (hx:x.val∈cabin G i) (Y:Nu G (0+1)) : P (L x.val) Y = 0 := by
    let X:Nu G (i+1):=⟨x.val,stepped (Nat.le_succ _) hx⟩
    have hw:boards (i+1) hi X=x:=Subtype.ext rfl
    unfold P; rw [← show X.val=x.val from rfl]
    rw [hL X Y,pin,hw]; apply hr x _ i (0+1) (by omega) hx; rw [boards_val]; exact Y.property
  refine ⟨(2:ℂ) • q,fun x y hx hy=>?_, fun x y hx hy=>?_⟩
  · have he : P (L x.val) (B y.val)=p x y := by
       let D:Nu G (i+1):=⟨x.val,hx⟩; let E:Nu G 1:=⟨y.val,hy⟩
       unfold P; rw [← show D.val=x.val from rfl,← show E.val=y.val from rfl]
       rw [hL D,hB D E,pin, show boards _ hi D=x from Subtype.ext rfl, show boards _ hj E=y from Subtype.ext rfl]
    rw [SetLike.val_smul,map_smul,u, he, show patchR _ _ _ _ _ (L y.val) _ =0 from hp y (stepped ‹1 ≤ i› hy) (B x.val)]; change _=(2:ℂ)*_; ring
  rw [SetLike.val_smul,map_smul,u]; change (2:ℂ)*((1/2:ℂ)*(P (L x.val) _+P (L y.val) _))=_
  rw [hp x hx,hp y hy];ring
lemma togetherR (hk:k≤4) (h:ToneR p k) (e:pastR p k) : ∃ q:Reel G,ripple G p q k:=by
  by_cases hf:k≤1; · exact ⟨0,pursues p h _ (fun i j hi hj H _ _ _ _=>by omega)⟩
  rcases (show k=2 ∨ k=3 ∨ k=4 by omega) with rfl|rfl|rfl
  · obtain ⟨q,hq⟩:= choir p 0 rfl hk h
    refine ⟨q,pursues p h q fun i j hi hj ha x y hx hy=>?_⟩
    exact hq _ _ (stepped (by omega : j≤0+1) hy) (stepped (by omega) hx)
  · obtain ⟨q,hq,_⟩:= flips p 1 rfl hk h e le_rfl
    exact ⟨q,pursues p h q fun i j hi hj ha x y hx hy=> hq _ _ (stepped (by omega : j≤1+1) hy) (stepped (by omega) hx)⟩
  · obtain ⟨q,hq⟩:= choir p 1 rfl hk h; obtain ⟨L,H⟩:=poem q
    let R:= p-L; have hR (x y:la G): R x y=p x y-chord x.val y.val q.val := by unfold R; rw [LinearMap.sub_apply,LinearMap.sub_apply,H]
    have ht : ToneR R 4:=fun x y=> ⟨by rw [hR,hR,(h x y).1,chord_com],fun a b he hx hy hc=> by rw [hR,(h x y).2 a b he hx hy hc, dead_note x hc q,sub_zero]⟩
    have hm (x y:la G)(hx:x.val∈cabin G 2)(hy:y.val∈cabin G 2): R x y=0:=by rw [hR,hq x y hx hy,sub_self]
    have hP:pastR R 4:=by
      intro a b i j hij ha hb
      rcases Nat.eq_zero_or_pos i with hi|hi
      · subst i; exact (ht a b).2 _ _ hij.le ha hb (steady0 a ha)
      rcases Nat.eq_zero_or_pos j with hj|hj
      · subst j; rw [(ht a b).1]; exact (ht b a).2 0 i (by omega) hb ha (steady0 b hb)
      exact hm _ _ (stepped (by omega : i ≤ 2) ha) (stepped (by omega) hb)
    obtain ⟨m,Hm,hM⟩:= flips R 2 rfl hk ht hP (by decide)
    refine ⟨q+m,pursues p h _ fun i j hi hj he x y hx hy=>?_⟩
    change _= chord y.val x.val (q.val+m.val); rw [map_add]; by_cases ht:j≤2
    · have hx1:= stepped (by omega : i ≤ 2) hx; have hh:=stepped ht hy; rw [hM y x hh hx1,add_zero]; exact hq _ _ hh hx1
    have hy1:= stepped (by omega : j≤3) hy; have hx1:= stepped (by omega : i ≤ 1) hx
    rw [←Hm y x hy1 hx1,hR];abel
end YM.RG11.FirstW
