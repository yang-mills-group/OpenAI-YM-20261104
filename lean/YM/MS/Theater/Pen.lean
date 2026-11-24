import YM.MS.Theater.Bread
/-!
# Exponential character probes on the finite graded symbol algebra.
 On each horizon use a linear reader (may vary horizon). Then contraction.V.Idea.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n r:ℕ}{u x v:ℤ}{p b:Pol G}{F H:Law G}{f:Local.BV.Grade G}
local notation "KΩ"=> hands G
local notation "ζ"=> Koszul.mono
local infix:70 " ⋆ "=> product KΩ
abbrev Probe (G:Gauge):= Local.BV.Grade G →ₗ[ℂ] ℂ
variable {C:Probe G}{U:Labels.Jet G}{X: Maxwell.TaylorTower G}
-- horizon range. sector all terms ≤ total dimension.unphysical calibration.Masks.H
structure Board (C:Probe G)(h:ℤ)(U:Labels.Jet G): Prop where
    shut {i q} (hp:i≤ h) (he:q≠0){f}: f∈ yields i q→ C f=0
    runs (k:ℕ)(L:Witness G k): (k:ℤ)+2≤h→ C ( RowLeg G k L )=L ( U k )
noncomputable section
local notation "K'"=> Finset.Icc 0
-- preserve choose_grade. linear ℂ.Linear extension.
abbrev parse (x:Labels.Taylor G k): Probe G:= {
    toFun t:= ( (RowLeg G k).leftInverse t ) x
    map_add' u v:= by simp
    map_smul' c v:= by simp }
lemma at_parse (x:Labels.Taylor G k)(L:Witness G k): parse x ( RowLeg G k L )= L x:= by unfold parse; dsimp only [ LinearMap.coe_mk, AddHom.coe_mk ]; rw [ LinearMap.leftInverse_apply_of_inj ( LinearMap.ker_eq_bot.mpr ( bright G k ) ) L ]
lemma covers (h:ℕ)(X:Labels.Jet G): ∃ P,Board P h X:= by
   let s:= K' ( h:ℤ ); choose P hp using fun i:ℤ=>choose_grade G i s; let A: Probe G:= ∑ k∈Finset.Iic h,( parse ( X k ) ∘ₗ P ( k+2 ) ∘ₗ Local.BV.mask ( G:=G ) 0 ); refine ⟨ A,⟨ ?_,?_ ⟩⟩; · intro w q he ht f hx; unfold A; simp_rw [ LinearMap.sum_apply,LinearMap.comp_apply,caught _ hx, if_neg ( Ne.symm ht ),map_zero,Finset.sum_const_zero ]
   intro k L hu; let f:= RowLeg G k L; let hf: f∈ yields (k+2) 0:= ( wholeℓ L ).1; have he (x:ℕ):P (x+2) f= if x=k then f else 0:= by rw [ hp _ (k+2) ( Or.inr ( Finset.mem_Icc.mpr ⟨ by omega, hu ⟩ ) ) 0 f hf ]; split_ifs <;> first | rfl| omega
   change A f=L _; unfold A; -- sum functional stuck
   simp_rw [ LinearMap.sum_apply,LinearMap.comp_apply,caught _ hf,if_true,he ]; rw [Finset.sum_eq_single_of_mem k (Finset.mem_Iic.mpr (by omega)), if_pos rfl ]; exact at_parse ..; intro i hi hv; rw [if_neg hv,map_zero] -- he orientation.Need ↑x
end
lemma mask_b {i:ℤ}(hp:Board C u U)(hx:f∈ yields i x)(hi:x≠0)(he:i≤u): C f=0:= hp.shut he hi hx
lemma end_eye (hp:Board C h (fun i=> gaugeJet (X i)))(hx:f∈ yields v x)(he:v≤h): C ( Q f )=0:= by
   by_cases hm:x=-1; swap; · exact hp.shut he (by omega : x+1≠0) (stays _ _ _ hx)
   subst x; obtain hf:Horizontal ( Q f ) v:= ⟨ stays _ _ _ hx,Q_zero _ ⟩; by_cases ht:v<2; · rw [ liftZ ht hf,map_zero ]
   obtain ⟨k,hk⟩:∃ k:ℕ, v=(k:ℤ)+2:= ⟨( v-2 ).toNat,by omega⟩; subst v; obtain ⟨Z,hZ⟩:= archiveA k (Q f) hf; rw [ hZ,hp.runs _ _ he ]; exact DFunLike.congr_fun (( isoLeg Z ).mpr ⟨ f,hx,hZ⟩ ) ( X k )
-- n probes.Rates powers.
variable (C)
def back : ℕ→ ( Law G →ₗ[ℂ] ℂ )| 0=> LinearMap.proj (R:=ℂ) []| n+1=> {
    toFun f:= C (fun x=> back n ( Koszul.D x f ))
    map_add' u v:= by simp only [map_add]; rw [← map_add]; rfl
    map_smul' a p:= by simp only [map_smul,RingHom.id_apply]; rw [← map_smul]; rfl }
lemma budget_b (g:Local.BV.Grade G)(n:ℕ): back C (n+1) (bud g F)= C g*back C n F:= by
    change C (fun i=>back C n ( Koszul.D i _ ))=_; simp_rw [ show ∀ i,Koszul.D i (bud g F)=g i • F from fun i=>rfl,map_smul ]; rw [ show ( fun i=>g i • back C n F )= back C n F • g from funext fun i=> mul_comm ..,map_smul ]; exact mul_comm ..
lemma θchar (n:ℕ)(h:f∈ yields x 0): back C (n+1) (ζ f ⋆ F)= (n+1:ℂ)* C f * back C n F:= by
    let P:= product ( R:=ℂ ) KΩ; let g:= ζ f; have hc (x) (F:Law G): Koszul.D x ( P g F )= f x • F+ P g ( Koszul.D x F ):= by
       rw [ ( D_product ( p:=hands G ) x g F ), show Koszul.D x g= coin ( f x ) from funext fun l=> by cases l <;> rfl, (lying h).signs, Local.par_zero,cross_false',one_smul, coin_product ]; -- reducibility
    have he (X: Law G)(n:ℕ): back C (n+1) ( P g X )= C f*back C n X+C (fun x=> back C n ( P g ( Koszul.D x X ) )):= by
        change C _= _; simp_rw [ hc, map_add,map_smul ]; rw [show C f*back C n X=C (fun i=> f i • back C n X ) from ?_, ← map_add ]; swap; · rw [ show (fun i=>f i•back C n X)= back C n X • f from funext fun _=>mul_comm ..,map_smul ]; exact mul_comm ..
        rfl
    change back C _ ( P g F )=_; induction n generalizing F with| zero=> rw [he, show (fun x=> back C 0 (P g ( Koszul.D x F )))=0 from funext fun _=> Eq.trans (times_nil ..) (zero_mul _),map_zero,add_zero ]; simp | succ n ih=>
       rw [he]; simp_rw [ih]; rw [ show (fun x=> _ * back C n ( Koszul.D x F )) =( (n+1:ℂ)*C f ) • (fun x=> back C n ( Koszul.D x F )) from rfl, map_smul ]; let z:= back C (n+1) F; push_cast; change C f*z + _ * z=_; ring
variable {C}
lemma headQuiet (hp:Board C h (fun i=> gaugeJet (X i)))(hq:u≤h)(he:H∈Bed G u x r): back C r (natQ H)=0:= by
    suffices hh: Bed G u x r ≤ LinearMap.ker ( back C r ∘ₗ natQ ) from LinearMap.mem_ker.mp (hh he); clear he; induction r generalizing u x with | zero=> refine bed_le _ fun p a b hv he hp hx=>?_ ; rw [LinearMap.mem_ker,line_zero, LinearMap.comp_apply,show natQ (hit:Law G)=0 from MatrixLet.no Gof]; exact map_zero _| succ n ih=>
       refine bed_le _ ( fun p x y hx hu hz hq' =>?_ ); subst u; let G':= Local.line n (p∘ Fin.succ); have hm:= LinearMap.mem_ker.mp ( ih (by rw [ Fin.sum_univ_succ ] at hq; obtain hp:=hq' 0; omega) ( show G'∈ Bed G ( ∑ i:Fin n,x i.succ ) ( ∑ i: Fin n,y i.succ ) n from tileCub.mpr ( line_in mslug ghostNo ( fun i:Fin n=> seedStar.mp (hx i.succ))) ) ); -- syntax .. invalid; h etc
       rw [LinearMap.mem_ker,Local.line_bud,LinearMap.comp_apply]; rw [ show natQ (_:Law G)=_ from ( Woven.parity_bud ( F:=G' ) ( V:=Gof ) (hx 0)), map_add, map_smul, budget_b,budget_b,end_eye hp ( hx 0 ) ( v:=x 0 ) (by apply le_trans _ hq; rw [Fin.sum_univ_succ]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> hq' _)), show back C n ( Gof.Q G' )=0 from hm ]; simp -- simp does coercions
end YM.MS.Theater
