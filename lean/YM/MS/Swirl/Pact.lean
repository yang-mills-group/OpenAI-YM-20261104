import YM.MS.Swirl.Shred
/-!
# Formal identity of the Wick maps on dressed and bare integrands.

Includes determinant multiple which we will not calculate explicitly (it has unit leading coefficient).
This formulation avoids inverses of the ghost Gaussian on longitudinal/residual pieces and works for
both tori, at each fixed mesh. Need only supplies `Green`, twist reads of S₂,
 and pure/even leading for S₂ etc. Also no flow estimate assumptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Filter Set Finset MeasureTheory Real
open Koszul Plane Cylinder Orbit Orbit.Cog Orbit.LogReal Book Convolve Program Puff Engine SplitP Actors Dynamics Puff.Mom
open PowerSeries (coeff)
open scoped Topology ContDiff Interval
variable {I E J A:Type} [AddCommGroup E][Module ℂ E]
variable {p:Sector A}{V:A→Cn}{x F H:BL A}{n:ℕ}{S:Actors E}{K:Grain A}(P:SplitP I)
local infix:70 " ⋆ "=> product p
local notation "R"=> PermV p
local notation "M"=> actor p
local infix:70 " ★ "=> Actors.core ( R )
abbrev FeeP (p:Sector A): Submodule ℂ ( BL A ):={
    carrier:={F | Symm p F∧ F∈Mini A}
    zero_mem':= ⟨Symm.zero,(Mini A).zero_mem⟩
    add_mem':= fun hu hv=> ⟨ hu.1.add hv.1, (Mini A).add_mem hu.2 hv.2 ⟩
    smul_mem':= fun c _ h=> ⟨h.1.smul c,(Mini A).smul_mem c h.2⟩ }
lemma fee_spec (h:x∈ FeeP p): Symm p x∧ x∈ Mini A:=h
lemma feeUnit : (actor p).unit∈ FeeP p:= ⟨ coin_symm _, minH ( coinN _ ) ⟩ -- name
lemma fee_pair {f h:BL A}(he:f∈FeeP p)(hp:h∈ FeeP p): f ⋆ h∈ FeeP p:= ⟨ he.1.times hp.1, miPair he.2 hp.2 ⟩
abbrev Γ (F: T (BL A))(p:Sector A): Prop:= F∈ allIndex ( FeeP p ) ℕ
section Actor
variable {B:Submodule ℂ E}{F H:I→E}
-- some general lift even and over with MINI. Need πE.Tether stability later
lemma costCheer (hp:S.unit∈ B)(hv:∀ u∈B,∀ v∈B, S.core u v∈B)( h: F∈allIndex B I ) : S.Cheer P F∈ allIndex B I := by
    have he(j:ℕ): (S.stack P).power F j∈allIndex B I:= by induction j with| zero=> apply (universe0 B).mpr; intro i; change P.refineV S.unit i∈ B; unfold SplitP.refineV; split; exact hp; exact B.zero_mem| succ k ih=> exact stays0 P _ _ _ hv h ih
    intro i _; unfold Cheer cheers wages; rw [Finset.sum_apply]; exact B.sum_mem (fun j _=> B.smul_mem _ ( he j i ( Set.mem_univ _ ) )) -- `i Set.univ`
lemma refineπ (f:E) (h:f∈ B): P.refineV f∈ allIndex B I:= by intro i _; unfold refineV; split; exact h; exact B.zero_mem
end Actor
variable {x':T (BL A)}
lemma ΤΓ_pair {x y:T ( BL A )}(hv:Γ x p)(hh: Γ y p): Γ (x ★ y) p:= stays0 useN ( product p ) _ _ (fun _ h _ he=> fee_pair h he) hv hh
lemma min_taxi (h:Γ x' p)(V:A→Cn): Γ ( taxi V x' ) p:= by
    intro i _; let A:= allIndex ( FeeP p ) ℕ; rw [sl_taxi,slΩ]; refine ( FeeP p ).sum_mem (fun j _=>?_); obtain ⟨he,k,hk⟩:= fee_spec ( h j.2 ( Set.mem_univ _ ) ); refine ⟨fun l i u r=>?_, minH (v:=k) (fun l hl=> by rw [offer, hk l hl,mul_zero])⟩; simp only [ offer,List.map_append,List.map_cons,List.prod_append,List.prod_cons ]; rw [he l i u r]; rw [ mul_left_comm (V u) ( V i ) ]; ring
lemma expΓ (h:Γ x' p): Γ ( Cheer M useN x' ) p := costCheer useN feeUnit (fun _ h _ he=> fee_pair h he) h
-- $Θ
local notation "u"=> useN
abbrev shiftH (V:A→Cn)(H:BL A):= taxi V ( useN.refineV H )- useN.refineV H
abbrev Stuff (p:Sector A)(V:A→Cn)(H:BL A):= Cheer ( actor p ) useN ( shiftH V H ) -- Σ powers
local notation "B0"=> shiftH V H
local notation "U"=> taxi V
local infix:70 " △ "=> Actors.core Trunk
variable [Fintype A]
local notation "σ"=> Stuff p V H
abbrev ℶV (K:Grain A):= pointL ℕ (View K)
local notation "sL"=> ℶV K
variable {b:A→Cn} (he:Clear p K)(hv:Cog.Sym p K)
    (ha:∀ i,Low ( V i )) (hm:Carrier V b)(hΓ:∀ i,Green (Carrier.fees b i) K H)
    (hx:H∈ FeeP p)(hp:Pure p false H)(ht: Book.rank 2 H)
set_option quotPrecheck false
local notation "Pφ"=> ( actor p ).stack u
local notation "𝕎"=> ModeT ( Carrier.fees b )
omit [Fintype A] in
lemma clock_U (F:E): clock useN E ( useN.refineV F )=0:= by
    funext i; rw [ cloak, refineV ]; split
    next h=> rw [ h,( useN.zeroC useN.origin ).mpr rfl,Nat.cast_zero,zero_smul ]; rfl
    next _=> rw [ smul_zero ]; rfl -- layout
include ha
omit [Fintype A] in
lemma χ0 : Happy u B0:= by unfold Happy shiftH; rw [Pi.sub_apply, show (U ( useN.refineV H )) useN.origin= _ from (taxi0 V ha ..), show useN.origin=0 from rfl,sub_self]
include hp
omit ha [Fintype A] in
lemma πZ : B0∈ (Pφ).guard:= (Pφ).guard.sub_mem ( taxiP V ( refineπ u H hp (B:=Center p) ) ) ( refineπ u H hp ( B:=Center p ))
-- θ derivative & Euler.Stuff arbitrary fixture.X∈ FeeP
abbrev Bill (K:Grain A)(b:A→Cn)(H:BL A): T ℂ:= fun i=> billT K ( Carrier.fees b i ) H
local notation "T∂"=> Bill K b H
local notation "νƵ"=> clock u ( BL A )
omit hp

include hm
lemma billPH: Happy u T∂:= by
    have he : Carrier.fees b useN.origin=0:= by
        ext i; obtain he:= hm i; unfold Carrier.fees; change coeff 0 ( b i )=0; have hz:= congr_arg (coeff ( 0:ℕ ) ) he; rw [ paysD,PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,Finset.sum_singleton, show coeff 0 (V i)=1 from ha i,mul_one,Nat.cast_zero,mul_one ] at hz; exact hz.symm
    unfold Happy Bill billT; rw [he]; simp
include hp
omit [Fintype A] in
lemma Euler_ST (F:BL A): let J:= U ( useN.refineV F ); νƵ ( σ ★ J )= 𝕎 ( σ ★ J ) + (𝕎 ( useN.refineV H ) ★ (σ ★ J)) := by
    intro J; have hz: Happy u ( shiftH V H ) := χ0 ha; let C:= turn_clock u M; let w:= latchT ( p:=p ) ( Carrier.fees b ); have Hq:shiftH V H∈ allIndex (M).guard ℕ:= πZ hp; change νƵ _ = _; rw [C.earns,show νƵ J=_ from hm.tilted F,w.earns]; unfold Stuff; rw [ C.idea Hq hz,w.idea Hq hz ];
    have hh : νƵ B0=𝕎 B0+𝕎 ( useN.refineV H ):= by unfold shiftH; rw [map_sub,hm.tilted,map_sub, clock_U,sub_zero]; abel
    rw [ hh,map_add, LinearMap.add_apply,map_add,LinearMap.add_apply,( actor p|>.stack u ).star_a (𝕎 ( useN.refineV H )) ]; abel
include he hv hx hΓ ht
omit ha hm in
lemma ζemp {g: T ( BL A )}(hc:Γ g p)(hh: νƵ g=𝕎 g+(𝕎 ( useN.refineV H ) ★ g)): clock u ℂ ( sL g )= T∂ △ sL g := by
   have h1 : ℶV K ( clock u ( BL A ) g )= clock u ℂ (ℶV K g):= by funext i; exact map_smul ( View K ) (i:ℂ) _
   rw [ ← h1, hh ]; funext l; let A i:= (Carrier.fees b i); have hm' i: 𝕎 ( useN.refineV H ) i= Tick ( A i ) H:= look_c u ( Tick ∘ A ) i H;
   change View K ((∑ i∈antidiagonal l, Tick ( A i.1 ) ( g i.2 ))+(∑ i∈ antidiagonal l,( 𝕎 ( useN.refineV H ) i.1 ) ⋆ g i.2 ))=_; rw [← Finset.sum_add_distrib,map_sum ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [hm']; obtain ⟨hα,hβ⟩:= fee_spec (hc i.2 ( Set.mem_univ _ ) ); exact wage he hv hα hβ ( hΓ i.1 ) ht (fee_spec hx).1 hp -- args order
local notation "ξ"=> sL σ
lemma αH (F:BL A)(h:F∈FeeP p): let Ξ:= σ ★ U ( useN.refineV F ); ℶV K Ξ= ξ △ useN.refineV ( View K F ) := by
    intro Ξ; let W:= T∂; have hh: Γ σ p:= expΓ ((allIndex ( FeeP p ) ℕ).sub_mem ( min_taxi ( refineπ u H hx ) V ) ( refineπ u H hx )); have hp' : Γ Ξ p:= ΤΓ_pair hh ( min_taxi ( refineπ u F h ) V ); have hx' := Euler_ST (p:=p) ha hm hp F -- order;
    have hcore : νƵ σ=𝕎 σ+(𝕎 (useN.refineV H) ★ σ):= by obtain he:= Euler_ST ha hm hp (actor p).unit; change νƵ ( σ ★ U ( R ).unit ) = 𝕎 (σ ★ U (R).unit) + (𝕎 (useN.refineV H) ★ (σ ★ U (R).unit)) at he; rw [taxiUnit, (Pφ).identityR ] at he; exact he
    have hv0 : ξ 0=1:= Eq.trans (congr_arg ( View K ) (Stencil.simple_E M _ u ( χ0 ha ))) ( minView K _ );
    apply tick_agree u Toy (billPH ( K:=K ) ( H:=H ) ha hm); -- likely params many
    · obtain hc : Ξ useN.origin=F:= by
           change useN.Lift (product p) _ _ _=F; rw [ useN.loan,useN.home, Finset.sum_singleton ]; rw [ show σ _=( actor p ).unit from Stencil.simple_E M _ _ (χ0 ha),show U ( useN.refineV F ) useN.origin= useN.refineV F useN.origin from taxi0 V ha _ ]; rw [refineV, if_pos rfl ]; exact ( actor p ).identityK _
      change View K _= Trunk.core _ _ _; rw [hc]; change _=useN.Lift Toy.core _ _ _; rw [useN.loan,useN.home,Finset.sum_singleton,refineV,if_pos rfl]; change _= ξ 0 * _; rw [hv0,one_mul]
    · exact ζemp he hv hΓ hx hp ht hp' hx'
    let w:= turn_clock u Toy; rw [w.earns,clock_U,map_zero,add_zero,ζemp he hv hΓ hx hp ht hh hcore]; exact Trunk.star_a ..
-- extend through T
local notation "SF"=> (fun g=> SL useN ( Tick ∘ Carrier.fees b ) g )
lemma every_T (x':T (BL A))(h:Γ x' p): sL ( σ ★ U x' )= ξ △ sL x':= by
    have hP : ∃ L:T (Linear ( BL A ) ℂ),∀ v,sL ( σ ★ U v)= SL u L v:= by
       let A:=fun i=>(actor p).core (σ i); let V':= merit V; let Y:= fun i:ℕ=>∑ j∈useN.pieces i,( A j.1 ).comp ( V' j.2 ); refine ⟨ fun i=>( View K ).comp ( Y i ),?_⟩; intro v; change sL ( useN.Lift ( actor p ).core _ _ )=_; rw [ slides u,sl_taxi, borrow, ← repayment ]; -- v proof
    have hV : ∃ L:T (Linear ( BL A ) ℂ),∀ v, ξ △ sL v= SL u L v:= by
       refine ⟨fun i=>(Toy.core ( ξ i )).comp (View K),fun _=> rfl⟩ -- rfl composition
    obtain ⟨L,hL⟩:= hP; obtain ⟨T,hT⟩:= hV; rw [hL,hT]; apply continueM u L T _ _ ( (universe0 (FeeP p)).mp h ); intro i hi; rw [← hL, ← hT]; obtain he:= αH he hv ha hm hΓ hx hp ht i hi; rw [he]; congr 1; funext a; change _= View K ( useN.refineV i a ); unfold SplitP.refineV; split; rfl; exact ( map_zero _ ).symm
end YM.MS.Swirl
