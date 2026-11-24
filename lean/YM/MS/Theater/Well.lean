import YM.MS.Local.Curls
import YM.MS.Theater.Life
/-!
# Active dual radial quotient
 Computable shape interfaces nonnegative weight.All. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset MeasureTheory Real Maxwell
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{k h i r n:ℕ}{u:ℤ}
  {p:FourP}{f:Grade G}{X: Look G h}
abbrev Witness (G:Gauge)(h:ℕ):= RealP (Labels.Taylor G h)
def RowLeg (G:Gauge)(h:ℕ): Witness G h →ₗ[ℂ] Grade G where
    toFun x:= StarView (h+1) false ( x.comp ( yard G h ) )
    map_add' := fun x y=> map_add ( shutter G (h+1) false ) ( x.comp ( yard G h ) ) ( y.comp ( yard G h ) )
    map_smul' a X:= map_smul ( shutter G (h+1) false ) a ( X.comp ( yard .. ) )
lemma wholeℓ (f: Witness G h) : Horizontal ( RowLeg G h f ) ( h+2 ):= by
    refine ⟨?_,(?_: Q ( StarView (h+1) false (f.comp (yard G h)) )=0 )⟩; · change shutter G (h+1) false _ ∈ _; convert! seedA ( f.comp ( yard G h ) ) using 1
    apply (capQ _).mpr; ext X; change f _=_; rw [ dustG, map_zero ]; rfl
lemma homeR (h:ℕ)(X:Look G h)(hr:X.comp (gradS G h)=0)(Y:Feet G h): X ( carve G h Y )=X Y:= by rw [ carveΩ,map_sub,map_smul,show X ( gradS G h _ )=0 from DFunLike.congr_fun hr (radialX G h Y), smul_zero, sub_zero ]
lemma bright (G:Gauge)(i:ℕ): Injective ( RowLeg G i ):= by
    apply LinearMap.ker_eq_bot.mp; apply eq_bot_iff.mpr; intro x hx; have h:x.comp (yard G i)=0:= quietly (show shutter _ _ false _=0 from LinearMap.mem_ker.mp hx); apply (Submodule.mem_bot _).mpr; ext v; exact coastY v ▸ ( show x ( yard G i ( step_in G _ v ) )= _ from DFunLike.congr_fun h ( step_in G _ v ) ) -- syntax ↑x
lemma archiveA (h:ℕ)(F:Grade G)(hp: Horizontal F (h+2)): ∃ X:Witness G h, F=RowLeg G h X:= by
   obtain ⟨X,rfl⟩:= tune_K (h:=h+1) ( f:=F ) ( by convert! hp.1 using 1); have hr := (capQ X).mp hp.2; refine ⟨ X.comp ( step_in G _ ), congr_arg (StarView ( h+1 ) false) ?_⟩; apply LinearMap.ext; intro Y; change X Y=X ( step_in _ _ ( yard G h Y )); rw [ taxiY, homeR _ _ hr Y ]
-- weights <2.Anti at <3
lemma pulseZ (h1: u<3)(h:f∈ yields u (-1)): f=0:= by
   ext z; rcases z with ⟨⟨⟨_|i,_|_⟩,s⟩,p⟩ <;> first | (solve| refine (seedStar.mp h).real' _ ?_; norm_num [ghostNo, ghostChannel])| skip
   exact congr_fun (((seedStar.mp h).form (anti i,s) ).charge ( show u-mslug (anti i,s)<0 from (by rw [ show mslug (anti i,s)=3 from rfl ]; omega) )) p
lemma liftZ (hp:u<2)(he:Horizontal f u): f=0:= by
   by_cases hu:u=1; · subst u; obtain ⟨X,rfl⟩:= tune_K (f:=f) ( h:=0 ) (by exact_mod_cast he.1); have hp := (capQ X).mp he.2; change shutter G 0 false X=_; rw [ show X=0 from ?_, map_zero ]; apply LinearMap.ext; intro x; rw [← homeR _ _ hp, show carve G 0 x=0 from ?_,map_zero ]; rfl; exact (Submodule.mem_bot ℝ).mp (weightT G ▸ house x)
   ext x; by_cases hz:f x=0; exact hz; obtain ⟨a,k,p,rfl⟩:= Tall_l he x hz; exact congr_fun (((seedStar.mp he.1).form (Landau.gauge a,k)).charge (show u-mslug (Landau.gauge a,k)<0 from by rw [show mslug (Landau.gauge a,k)=1 from rfl]; omega)) p
-- relation x−orbit. nonparam one slot
lemma cut_Reset {A E:Type}[AddCommGroup E][Module ℝ E][AddCommGroup A][Module ℝ A] (L:E→ₗ[ℝ] ℂ) (Y:E→ₗ[ℝ] A)(hp:LinearMap.ker Y≤ LinearMap.ker L) : ∃ X:A→ₗ[ℝ]ℂ, L=X.comp Y:= by
    let R:=LinearMap.range Y; let P:= Y.ker.liftQ L hp; refine ⟨ (P.comp Y.quotKerEquivRange.symm.toLinearMap).comp R.subtype.leftInverse,?_⟩; ext a; let d:R:= ⟨ Y a, LinearMap.mem_range_self ..⟩; change L a=P ( Y.quotKerEquivRange.symm ( R.subtype.leftInverse ( R.subtype d ) ) ); rw [ LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr R.subtype_injective) d ]; unfold d; rw [ Y.quotKerEquivRange_symm_apply_image ]; rfl -- Seal
local notation "Ω"=> gaugeJet (G:=G)
theorem isoLeg (X: Witness G h) : X.comp Ω=0↔∃ f∈ yields (G:=G) (h+2) (-1), Q f=RowLeg G h X:= by
   cases h with
   | zero=>
    constructor
    · intro h; have he : X=0:= by apply LinearMap.ext; intro x; obtain ⟨Y,rfl⟩:= ( centring x ).mpr ( paid0 x ); exact DFunLike.congr_fun h Y
      rw [he,map_zero]; exact ⟨0,zero_mem _,map_zero _⟩
    rintro ⟨f,h,hf⟩; rw [ pulseZ ( by norm_num ) h,map_zero ] at hf; rw [ (show X=0 from bright G 0 ( hf.symm.trans (map_zero _).symm )),LinearMap.zero_comp ]
   | succ h =>
      let v:= X.comp ( yard G (h+1) ); let k:= Hess G h; let w:= RowLeg G (h+1) X; constructor
      · intro hz; have h1 (Y:Feet G (h+2))(he:k Y=0): v Y = 0:= by
           let u:= yard G (h+1) Y; obtain hr: takeCurl u∈ onShell G.Color (h+1) := ( attended u ).mpr ( by unfold u; change k _=0; rw [ taxiY, carveΩ, map_sub, he, map_smul, show k ( gradS G ( h+2 ) (radialX G _ Y))=0 from ( DFunLike.congr_fun ( grad_pays (h:=h) (G:=G) ) (radialX G _ Y) ), smul_zero,sub_self ] );
           obtain ⟨p,hp⟩:= (centring u).mpr hr; change X u=_; rw [hp]; exact DFunLike.congr_fun hz p
        obtain ⟨U,hV⟩:= cut_Reset v k (fun a h=>h1 a h); refine ⟨ StarView h true U,?_,?_⟩; convert! seedB U using 1
        rw [ pair_core ]; change _ = StarView (h+2) false v; rw [ hV ];
      rintro ⟨ f,hf,ht⟩; obtain ⟨t,rfl⟩:= turn_K ( f:=f ) ( h:=h ) ( by convert! hf using 1 ); rw [pair_core] at ht; have hv : t.comp k = v:= lift_inj G (h+2) false ht; ext Y; let Z := step_in G _ (Ω Y); change X ( gaugeJet Y )= _; rw [ ← coastY (Ω Y), show X ( yard G _ _ )=t ( k Z ) from (DFunLike.congr_fun hv Z).symm]; unfold k; rw [ ( attended ( gaugeJet Y ) ).mp ( ( centring ( gaugeJet Y ) ).mp ⟨ Y,rfl ⟩ ), map_zero ]; rfl
end YM.MS.Theater
