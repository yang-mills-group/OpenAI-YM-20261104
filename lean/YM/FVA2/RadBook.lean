import YM.FVA2.Cardinal
/-!
# Signed reading in radial cone. Use exact normalization lifts. 
-/
set_option autoImplicit false
set_option maxHeartbeats 540000
noncomputable section
namespace YM.MS.RadL
open Set Function Filter Finset MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Book.Convolve
open Theater Mach Lifting Pole Color Spray Arts Pilot Spin Motif Literal Halo Rock Path Oceans Pearl
open FVA2 FVA2.ArchTurn
open Complex (I)
open scoped Topology Classical ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{d h k n m:ℕ}
namespace Spray
variable (s:Signed)(p:Spray) (i:p.Λ)
private abbrev sprung (s:Signed)(p:Spray) : Spray:= ⟨ p.k, s.perm.symm p.ν, WithLp.toLp 2 (fun a:Axis=> catar s ( s.perm a ) * p.y (s.perm a)) ⟩
def money : p.Λ ≃ (sprung s p).Λ := Equiv.prodCongr s.perm.symm ( Equiv.piCongrRight ( fun _: Fin p.k=> s.perm.symm ) )
lemma border : flight s (p.plaq i)=(sprung s p).plaq ( money s p i ):= by unfold plaq flight money; simp only [List.map_ofFn]; rfl
private lemma amt_h (h:List Axis): ( List.map ( catar s ) h ).prod= (List.map (catar s) h).prod:= rfl
-- factor transforms by tax and leading ν flip.ℝ.Stream.Y canonical diagonal.
private lemma η (i:Axis): catar s i * catar s i=1:= by unfold catar; cases h: s.flip _ <;> simp [Koszul.cross]
lemma line (j:Axis): (sprung s p).y ( s.perm.symm j )= catar s j*p.y j:= by unfold sprung; change _*_= _; simp
lemma front_s : (p.factor i)* Spun s (p.plaq i) = catar s p.ν * (sprung s p|>.factor (money s p i)):= by
    rcases i with ⟨x,y⟩; let v:=money s p (x,y); let t:=sprung s p;
    unfold factor; have hc(k:Fin p.k): t.y ( (money s p (x,y)).2 k )=catar s (y k) * p.y (y k):=line s p ( y k );
    rw [show ( t).y ( v.1 ) = _ from line s p x ]; -- occurrence.C.L
    simp only [Spun,plaq,List.map_ofFn,List.prod_ofFn]
    simp_rw [show ∀ k:Fin p.k,s.perm (((money s p) (x,y)).2 k)=y k from fun k=> s.perm.apply_symm_apply _, comp_apply, Finset.prod_mul_distrib ]; ring -- k discrep.
variable (T:Fin m→Spray)
private abbrev rebased (T:Fin m→Spray):roles T≃ roles (sprung s ∘ T):= Equiv.piCongrRight (fun i=> money s (T i))
private lemma spun_s (T:Fin m→Spray)(z:ℂ)(σ:Lifting.Grid G m)(K:roles T): canto s ((cost T K:ℂ) • Pole.saint m (mint T K) σ z)=
    (( ∏ i: Fin m,catar s ( T i ).ν :ℝ ):ℂ ) • ((cost ( sprung s ∘ T ) ( rebased s T K ):ℂ) • Pole.saint m ( mint (sprung s ∘ T) (rebased s T K) ) σ z):= by
    rw [map_smul, ArchTurn.rotation, show flight s ∘ mint T K=mint (sprung s ∘ T) (rebased s T K) from funext fun i=> border ..,smul_smul,smul_smul,← Complex.ofReal_mul, ← Complex.ofReal_mul ]; apply congr_arg (fun t:ℝ=> (t:ℂ) • Pole.saint m _ σ z); unfold cost; rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib ]; exact Finset.prod_congr rfl (fun i _=> front_s ..)
lemma radiance (T:Fin m→Spray)(σ: Lifting.Grid G m): ∃ (T':Fin m→ Spray)(v:ℝ), bill T'=bill T ∧ ArchTurn.tickW s ( Word G T σ )= v • Word G T' σ:= by
    let T':=sprung s ∘ T; let v:= ∏ i:Fin m,catar s ( T i ).ν; refine ⟨ T',v,rfl,?_⟩; funext z; change canto s _= (v:ℂ) • _; unfold Word; rw [ map_sum, Finset.smul_sum ]; simp_rw [ spun_s ]; exact Equiv.sum_comp ( rebased s T ) (fun i=> ( v:ℂ ) • ( ( cost T' i:ℂ ) • Pole.saint m (mint T' i ) σ z))
end Spray
open Menus Land Sail
variable (s:Signed){A: Booked (ColorCode.wings G)} (V: Warehouse G)
lemma framed {X: ℂ→ Mob G}(hp:X∈ Dome G d m): ArchTurn.tickW s X∈Dome G d m:= by
   refine Submodule.span_induction (p:=fun x _=> tickW s x∈Dome G d m) ?_ ?_ ?_ ?_ hp
   · rintro X ⟨Y,σ,h,rfl⟩; obtain ⟨T,v,hT,he⟩:= Spray.radiance s Y σ; rw [he, ←h, ← hT ]; exact Submodule.smul_mem _ _ ( RadL.slotD T σ )
   · rw [map_zero ]; exact Submodule.zero_mem _
   · intro v w _ _ hv hw; rw [map_add ]; exact add_mem hv hw
   intro c x _ hx; rw [show ArchTurn.tickW s (c • x)= _ from LinearMap.map_smul_of_tower ( ArchTurn.tickW s ) c x ]; exact Submodule.smul_mem _ _ hx
-- Owner matching exact M.Request
set_option quotPrecheck false
variable {B: Local.Physical.Deck G}
def Reg (B':Booked B) : Prop:= ∀ (h:ℕ)(i:Land.Plaid B h),( fun z=> Literal.value (Mob G) z (B'.optics h i))∈ Dome G h (Land.read i).grade
lemma radial (h:Reg A): Reg (ArchTurn.angular A V):= by
   intro r i; let C:ℝ:=( ↑(Fintype.card Signed):ℝ)⁻¹; let n:= ( Land.read i ).grade;
   let Y(s:Signed):= fun z=> Literal.value (Mob G) z ( pactV A V s i ); have hx (s:Signed): Y s∈Dome G r n:= by
       let G':= Mob G; let X(i: Plaid (ColorCode.wings G) r) z:= Literal.value ( Mob G ) z ( A.optics r i );
       let f(j:Plaid (ColorCode.wings G) r):ℝ:= ColorCode.fee V.F s.ortho r i j; let U:= ∑ j: Plaid (ColorCode.wings G) r,f j • X j; have he:Y s=tickW s U:= by
           funext z; unfold Y pactV polar; rw [linear_v ]; simp_rw [ map_sum, map_smul]; unfold U; -- calculate RHS.Ω.kernel.
           change (∑ j: Plaid (ColorCode.wings G) r,(f j:ℂ) • ArchTurn.canto s (X j z))= canto s _; rw [Finset.sum_apply,map_sum ]; refine Finset.sum_congr rfl (fun i _=>?_ ); rw [ show ( f i • X i ) z= ( f i:ℂ ) • X i z from ?_,map_smul ]; rfl -- cast lemma.
       rw [he]; apply framed s; refine Submodule.sum_mem _ (fun j _=>?_ ); by_cases hv: n=(Land.read j).grade; · exact Submodule.smul_mem ( Dome G _ n ) _ (hv.symm ▸ h _ j)
       have hh:f j=0:= Complex.ofReal_injective ( by rw [ show (↑(f j):ℂ)= _ from ColorCode.held_real ..]; rw [ ColorCode.shown_off ]; rw [ Complex.ofReal_zero ]; exact fun q=> hv (congr_arg Prod.snd q) ); rw [hh,zero_smul]; exact Submodule.zero_mem _
   have hp : ( fun z=> value _ z ((angular A V).optics r i))= ∑ s:Signed,C • Y s:= by
        funext z; rw [angular,map_sum, Finset.sum_apply ]; simp_rw [map_smul ]; refine Finset.sum_congr rfl fun i' _=>?_ ; rw [ ← Complex.ofReal_natCast, ← Complex.ofReal_inv ]; rfl -- edit
   rw [hp]; exact Submodule.sum_mem _ (fun i _=>Submodule.smul_mem (Dome G _ n) _ ( hx i ) )
-- actual continuation choices now precisely hit.Syntax.Nested.
open Local.Physical
variable (B)
lemma picks : ∃ T: Booked B, Reg T:= by
   have ht (h:ℕ)(i: Plaid B h): ∃ V, RadOK V ( Land.read i ).grade h ( Land.read i ).read:= radial_possible _ ( by change B.raw _ _ _∈ _; exact B.le (B.form _ _ _); ) -- fill
   choose V H using ht; exact ⟨ ⟨ V, fun i j=> optic ( H i j )⟩,fun i j=> ( H i j).lift⟩
end YM.MS.RadL
