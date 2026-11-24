import YM.MS.Theater.Well
import YM.MS.Local.Fac
/-!
# Product laws for arity and grading
algebra on the true even part of raw symbol.Net.Stripped. `Carry` rank.P.Weak profile.End.Use all sym, no reconstruction on phase.X.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset MeasureTheory Real Maxwell
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A:Type}{p:Sector A} {G:Gauge}{i r:ℕ}{u x v y h q:ℤ}
    {F H:Law G} {g f:Grade G}
local notation "K"=> field ( Landau.parity ( A:=Axis ) ( C:=G.ColorIndex) ( P:=FourP ) ) -- parameter type p.B
local notation "KΩ"=> (field (P:=FourP) ( Landau.parity ( A:=Axis ) ( C:=G.ColorIndex) ) )
abbrev Dark (p:Sector A): Submodule ℂ (Koszul.Raw A ℂ):={
   carrier:={F|Pure p false F}, zero_mem':=Pure.zero, add_mem':=Pure.add, smul_mem':=fun a x h=> Pure.smul a h }
set_option quotPrecheck false
local notation "Dκ"=> ↥( Dark p )
local infix:70 " ⋆ "=> product p
instance : One Dκ := ⟨ ⟨ coin 1, coin_pure _ ⟩ ⟩
instance : Mul Dκ:= ⟨ fun x y=> ⟨ x.val ⋆ y.val,Pure.prod x.property y.property ⟩ ⟩
lemma turn (a b:Dκ): a*b=b*a:= Subtype.ext ( Pure.central (F:=a.val) a.property _ ) -- name.
lemma oneRule (a:Dκ): 1*a=a:= Subtype.ext ( Eq.trans (coin_product ..) ( one_smul .. ) )
instance : CommRing Dκ:= { (inferInstance : AddCommGroup Dκ), (inferInstance : One Dκ), (inferInstance : Mul Dκ) with
  one_mul:=oneRule, mul_one:=fun a=> by rw [turn,oneRule]
  mul_assoc a b c:= Subtype.ext ( times_assoc a.val b.val c.val )
  left_distrib a b c:= Subtype.ext ( map_add ( product p a.val ) b.val c.val )
  right_distrib a b c:= Subtype.ext ( map_add ( (product p).flip c.val ) a.val b.val )
  zero_mul a:= Subtype.ext ( map_zero ( (product p).flip a.val ) )
  mul_zero a:= Subtype.ext ( map_zero ( product p a.val ) )
  mul_comm:=turn }
instance : Algebra ℂ Dκ:= Algebra.ofModule (fun c (x y : Dκ)=> Subtype.ext (map_smul ( (product p).flip y.val ) c x.val ) ) (fun c (x y:Dκ)=> Subtype.ext (map_smul ( product p x.val ) c y.val ) )
@[simp] lemma dark1 : (1:Dκ).val=coin 1:=rfl
@[simp] lemma darkM (f g:Dκ): ( f*g ).val=f.val ⋆ g.val:=rfl
lemma cash1 (x:ℂ): (algebraMap ℂ (↥(Dark p)) x).val=coin x:= by rw [Algebra.algebraMap_eq_smul_one]; ext l; cases l with| nil=>exact mul_one x| cons i l=>exact mul_zero x
-- `plantation'.
local infix:70 " ★ "=> product KΩ
local notation "ζ"=> Koszul.mono
lemma lying (he:f∈ yields u x): Pure KΩ ( Local.parity x ) ( ζ f ):= by
   intro w hv; rcases w with _|⟨i,_|_⟩ <;> first| rfl | (exact Classical.byContradiction fun h=> hv ( Eq.trans (show degree KΩ [i]=_ from (by simp)) ( par_seed (g:=f) he i h ) ))
lemma symθ : Koszul.Symm KΩ ( ζ f ):= by intro l i j r; cases l <;> simp [mono]
private lemma legD (i:A)(f:A→ℂ): Koszul.D i ( ζ f )= coin ( f i ):= funext fun l=> by cases l <;> rfl
lemma tides (h:f∈ yields u x)(he:g∈ yields v y): ζ f ★ ( bud g H )= bud f ( bud g H )+ ( cross (Local.parity y) (Local.parity x):ℂ ) • bud g ( ζ f ★ H ):= by
    ext l; cases l with| nil=> simp [Koszul.mono]| cons i l=>
       obtain hp:=lying h; have hm : Koszul.D i ( bud g H )= g i • H:= rfl; rw [ D_eval i (product _ _ _), D_product, hp.signs,hm,legD,coin_product]; simp only [ Pi.add_apply, bud_cons,map_smul,LinearMap.smul_apply,Pi.smul_apply, smul_eq_mul ]; by_cases ht:g i=0; simp [ht]; rw [( show KΩ i=Local.parity y from par_seed he i ht )]; ring
lemma unitθ : hit (A:=Branch G Axis) (P:=FourP) = coin 1:= by ext l; cases l <;> simp [hit,coin]
lemma dawnB (g:Grade G) : bud g hit= ζ g:=by ext l; rcases l with _|⟨a,_|_⟩ <;> simp [mono]
lemma closeAt (X:Raw A ℂ): X ⋆ (coin 1)= X := Eq.trans ( Eq.symm ( Pure.central ( coin_pure 1 ) X ) ) ( Eq.trans ( coin_product .. ) ( one_smul .. ) )
-- Carry covariant
lemma inside0 : (hit:Law G)∈ Carry G 0 0:= subset_span (mem_setOf.mpr ⟨fun (i:Fin 0)=>i.elim0,fun (i: Fin 0)=>0,(fun i=>i.elim0),(by simp),rfl⟩)
lemma ci0 : (hit: Law G)∈ Bed G 0 0 0:= fare G 0 0 inside0
lemma carry_panto (he:Horizontal f u)(hp:F∈ Carry G v r): bud f F∈ Carry G (u+v) (r+1):= by
   suffices he : Carry G v r ≤ comap ( place _ _ f ) ( Carry G (u+v) (r+1) ) from he hp
   rw [Carry,span_le]; rintro x ⟨p,k,h,hk,rfl⟩; subst v; refine subset_span (mem_setOf.mpr ⟨Fin.cons f p, Fin.cons u k,fun i=> Fin.cases ?_ (fun i=>?_) i, by simp [Fin.sum_univ_succ],?_⟩); exact line_cons ..; exact he; exact h i
lemma continue_C (he:Horizontal f u): Carry G v r ≤ Submodule.comap ( product KΩ ( ζ f ) ) ( Carry G (u+v) (r+1)):= by
   induction r generalizing v with| zero=> rw [Carry,span_le]; rintro F ⟨a,y,h,h0,rfl⟩; simp at h0; subst v; rw [SetLike.mem_coe,Submodule.mem_comap,line_zero, unitθ,closeAt, ← dawnB ]; exact carry_panto he inside0 | succ r ih=>
      rw [Carry, span_le]; rintro F ⟨p,y,h,rfl,rfl⟩; let V:= Local.line r (p ∘ Fin.succ); let w:= ∑ i: Fin r,y i.succ; have hp: V∈ Carry G w r:= subset_span (mem_setOf.mpr ⟨ p∘Fin.succ, y∘Fin.succ, (fun i=> h i.succ),rfl,rfl⟩); rw [SetLike.mem_coe,Submodule.mem_comap,line_bud,Fin.sum_univ_succ,tides he.1 (h 0).1]; apply add_mem ( carry_panto he ( carry_panto (h 0) hp ) ); apply smul_mem; rw [add_left_comm u]; exact carry_panto ( h 0 ) ( ih hp ) -- ambiguous line
lemma continue_B (he:f∈ yields u x): Bed G v y r ≤ Submodule.comap ( product KΩ ( ζ f )) ( Bed G (u+v) (x+y) (r+1) ):= by
    induction r generalizing v y with| zero=> refine bed_le _ (fun p a b h hv hh hz=>?_); rw [Submodule.mem_comap, line_zero,unitθ,closeAt,← hv,← hh,Fin.sum_univ_zero,Fin.sum_univ_zero, ← dawnB ]; exact planting he ci0 | succ r ih=>
      refine bed_le _ (fun p a b h hv hh hz=>?_); subst v y; let A':=∑ i:Fin r,a i.succ; let B':= ∑ i:Fin r,b i.succ; let L:= Local.line r ( p ∘ Fin.succ ); have hL:L∈Bed G A' B' r:= tileCub.mpr ( line_in mslug ghostNo ( fun i:Fin r=> seedStar.mp (h i.succ) ) ); rw [Submodule.mem_comap,line_bud, Fin.sum_univ_succ, Fin.sum_univ_succ, tides he ( h 0 ) ]; apply add_mem ( planting he (planting ( h 0 ) hL ) ); apply smul_mem; rw [add_left_comm u,add_left_comm x]; exact planting ( h 0 ) ( ih hL )
end YM.MS.Theater
