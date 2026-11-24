import YM.MS.Swirl.Pact
/-!
# The accumulated heat equation realizes the Wick operators
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Filter Set Finset MeasureTheory Real
open Koszul Plane Orbit Orbit.Cog Orbit.LogReal Book Convolve Program Puff Engine SplitP Actors Dynamics
open scoped Topology ContDiff Interval
variable {A I:Type}[Fintype A]{P L:Lines A}{K:Grain A}{p:Sector A}{F H:BL A}{X Y:OM A}{h n:ℕ}{u v:ℝ}
-- line recipes coefficientwise limits
structure Wellness (p:Sector A)(P L:Lines A)(K:Grain A): Prop where
    basis : P 0=0
    tip a b t: HasDerivAt (fun s=> P s a b) ( L t a b ) t
    clear t: Clear p ( P t )
    target a b: Tendsto (fun s=> P s a b) atTop (𝓝 ( K a b ))
namespace Wellness
variable (hW: Wellness p P L K)
include hW
local notation "wΩ"=> frame ( P u )
local notation "κΩ"=> frame ( L u )
lemma energyT (he:Lead X F u): Lead (fun s=> frame ( P s ) ( X s )) (frame ( L u ) ( X u )+ frame ( P u ) F) u:= by
    intro l; simp_rw [fpΩ,Finset.sum_apply]; rw [Pi.add_apply]; simp_rw [Finset.sum_apply]; -- simp maybe; 
    simp_rw [ ← Finset.sum_add_distrib ]; exact HasDerivAt.fun_sum fun i _=> HasDerivAt.fun_sum fun j _=> ( hW.tip i j u ).mul ( he ( i::j::l ) )
lemma powerR (hp:Symm p F)(n:ℕ): Lead (fun s=> tep ( P s ) ( n+1 ) F ) ( κΩ ( tep ( P u ) n F ) ) u:= by
    induction n with
    | zero=>
        have he := energyT hW (u:=u) ( X:=fun _=> F ) ( F:=0 ) (fun _=>hasDerivAt_const ..); simp_rw [map_zero,add_zero] at he; simp only [teen,Nat.cast_zero,zero_add,inv_one,one_smul,rise]; exact he
    | succ n ih=>
        have H:= energyT hW ih; intro l; -- xi growth
        have hm : κΩ (tep ( P u ) (n+1) F)+ wΩ (κΩ (tep ( P u ) n F))=(n+1+1:ℂ) • κΩ (tep (P u) (n+1) F):= by
            rw [ ← survey (P u) (hW.clear u) (te2 (P u) hp), show wΩ (tep ( P u ) n F)=(n+1:ℂ) • tep (P u) (n+1) F from ?_,map_smul ]; swap; · rw [ teen, smul_inv_smul₀ (zeroN' n) ]
            module
        rw [ hm ] at H; simp_rw [ teen ( n:=n+1 ), Nat.cast_succ ]; convert! ( H l ).const_mul (( n+1+1:ℂ )⁻¹) using 1;
        all_goals first| rfl| simp only [Pi.smul_apply,smul_eq_mul]; field_simp [show ( ( n:ℂ )+1+1 )≠0 from (by convert! zeroN' (n+1) using 1; push_cast; rfl)]
-- hV(0). eq only, derivative effect with n+1
lemma leadΩ (hp:Symm p F)(hx: Limit F n): Status (fun s=> effect ( P s ) ( n+1 ) F) (fun s=> Static L (fun t=> effect ( P t ) ( n+1 ) F) s):= by
    constructor; · refine ⟨ n,fun t=> by rw [effect,LinearMap.sum_apply]; exact Limit.sum _ ( f:=fun i=>tep ( P t ) i F ) (fun i hi=> Limit.up (te2H ( P t ) hx) (by omega)) ⟩ -- need effect explicit
    intro i l; change HasDerivAt _ ( frame ( L i ) (effect ( P i ) ( n+1 ) F ) _ ) i; rw [← ahead ( P i ) hx ( by omega : n≤n+1 ) ]; have he (n:ℕ)(i:ℝ): effect ( P i ) n F=∑ j∈Finset.range (n+1),tep ( P i ) j F:= LinearMap.sum_apply ..;
    simp_rw [ he,map_sum ( frame ( L i ) ),Finset.sum_apply, Finset.sum_range_succ' ( n:=n+1 ),rise ];
    let f(s:ℝ):= ∑ c∈Finset.range (n+1),tep (P s) (c+1) F l; let Q:=∑ c∈Finset.range (n+1),frame ( L i ) ( tep ( P i ) c F ) l; change HasDerivAt (fun s=> f s+F l) Q i; exact ( ( show HasDerivAt f Q i from HasDerivAt.fun_sum (fun c _=> hW.powerR hp c l) ).add_const ( F l ) )
lemma heatB (hp: F∈ FeeP p): Fill L F (fun t=> Shot ( P t ) F) 0:= by
    obtain ⟨h,k,hk⟩:=fee_spec hp; have H:∀ t,Shot (P t) F=effect ( P t ) (k+1) F:= fun t=> dawn _ ( hk.up (by omega) ); rw [ Fill ]; simp_rw [H,add_zero,hW.basis]; refine ⟨ ?_, leadΩ hW h hk ⟩; rw [effect, Finset.sum_range_succ', Finset.sum_eq_zero,zero_add,rise]; rfl
    intro n hn; simp [tep,frame]
omit hW in
lemma clerk {t:Filter I} {X:I→ Grain A}{L:Grain A}{U:I→BL A}( h:∀ i j,Tendsto (fun u=>X u i j) t (𝓝 (L i j)))( hp:∀ l,Tendsto (fun f=> U f l) t (𝓝 ( F l )))(l:List A): Tendsto (fun f=> frame (X f) ( U f ) l) t (𝓝 ( frame L F l )) := by
    simp_rw [fpΩ,Finset.sum_apply]; exact tendsto_finsetSum _ fun i _=> tendsto_finsetSum _ fun j _=> ( h i j ).mul ( hp ( i::j::l ) )
lemma teeth (k:ℕ)(l:List A): Tendsto (fun t=>tep ( P t ) k F l ) atTop (𝓝 (tep K k F l)):= by induction k generalizing l with| zero=> simp_rw [rise]; exact tendsto_const_nhds| succ k ih=> simp_rw [teen]; exact (clerk hW.target ih l).const_smul ( (k+1:ℂ)⁻¹ )
lemma riseΩ (hp:Fill L F X 0)(he:F∈FeeP p): Tendsto (fun u=> X u []) atTop (𝓝 ( View K F )):= by
    rw [expertise hp (heatB hW he)]; obtain ⟨hh,k,hk⟩:= fee_spec he; change Tendsto _ atTop (𝓝 (Shot K F [])); simp_rw [ dawn K hk, show ∀ t, Shot ( P t ) F= effect ( P t ) k F from fun t=> dawn _ hk, effect,LinearMap.sum_apply,Finset.sum_apply ]; exact tendsto_finsetSum _ fun i _=> teeth hW i []
end Wellness
end YM.MS.Swirl
