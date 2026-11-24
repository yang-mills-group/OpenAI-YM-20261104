import YM.SignedWilsonExpansion.Belfry.Bridge
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SignedWilsonExpansion.Belfry
open Function Set Filter Asymptotics PowerSeries Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Menus MS.Book MS.Book.Program MS.Book.Convolve MS.Puff MS.Puff.Actors
open XSpace XSpace.Structure1 XSpace.Normalize FVA2 FVA2.Scale FVA2.Reg FVA2.Dframe
open WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK MarqueQ.Crops MarqueQ.Crops.Taught
open Dancer Commission Belle Belle.Path Belle.Buffet Future
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{ι σ κ κ':Type}{n q m d:ℕ}{L:Filter ι}{θ ε g:ι→ℝ}
namespace ScaleFits
open XSpace.Normalize Scale FVA2.Scale.Level Dancer.SeatsW
-- fitted attribute.Change budget along small θ path.
open private stand_unit_inverse from YM.XSpace.Deck
abbrev adm (T:FieldEnd G d): Prop:= ∃ V:Normalize.Change G d, stand V = T
lemma ad_sub (T:FieldEnd G d)(p:T-1∈Normalize.Change G d): adm T:=⟨⟨T-1,p⟩,by change 1+(T-1)=_; abel⟩
lemma ad_id : adm (1:FieldEnd G d):=⟨0,stand0 d⟩
lemma adm.mul {T U:FieldEnd G d}(p:adm T)(q:adm U):adm (T*U):=by
    obtain ⟨V,rfl⟩:=p; obtain ⟨W,rfl⟩:=q; exact (stand_times V W).imp (fun _ h=> h.symm)
lemma adm.inv (T:(FieldEnd G d)ˣ)(p: adm (T:FieldEnd G d)) : adm (↑T⁻¹:FieldEnd G d):=by
    obtain ⟨V,h⟩:=p; exact ( stand_unit_inverse T V h ).imp fun i hp=> hp.symm
lemma adm.Dial (t:ℝ)(d:ℕ): adm (Dial (G:=G) d t):=by
    refine ad_sub _ ( (?_)); rw [may_change]; simp only [LinearMap.sub_apply, Module.End.one_apply]; exact ⟨ by rw [ Dial_leaf,sub_self ],fun i hi x h=> (show ((_ :Sec G d)-_).val∈ shellSector G i from Submodule.sub_mem _ ( Dial_band (d:=d) t i hi x h ) h), fun p=>by rw [Dial_real,map_sub],fun s p=>by rw [Dial_ori,map_sub] ⟩
lemma adm.young {F:Guard G d}(H:Base F)(t:ℝ)(q:ℕ): adm (young q t F):=by
      induction q with
      | zero=> simpa only [yearP,zero_add,Finset.range_one,Finset.sum_singleton,pow_zero,one_smul,H.zero] using ad_id (G:=G) (d:=d)
      | succ i ih=>
        obtain ⟨V,h⟩:=ih; have u:= (XSpace.Normalize.Change G d).smul_mem (t^(i+1)) (H.high (i+1) (Nat.succ_ne_zero _)); refine ad_sub _ (?_); rw [yearP,Finset.sum_range_succ, ← yearP,← h]; unfold stand; rw [add_assoc,add_sub_cancel_left (1:FieldEnd G d)]; -- likely wrong assoc inspect
        refine Submodule.add_mem _ V.property (show _ from ?_)
        rwa [ ← Complex.ofReal_pow, show (↑( t^(i+1) ):ℂ) • coeff _ F= _ from (IsScalarTower.algebraMap_smul ℂ ( t^(i+1) ) ( coeff (i+1) F )) ]
-- star budget. include real.instances.
variable {w w':ι→ Normalize.Change G d}{F Q:ι→ FieldEnd G d}
local instance capFinite : FiniteDimensional ℝ (FieldEnd G d) := Module.Finite.trans ℂ _
lemma shine {K:Type}[NontriviallyNormedField K][AddCommGroup κ][Module K κ]{x:ι→κ}: SeatsW.Discount K L 1 x ↔ By K L x 0:= by
    constructor <;> (intro p T; have h:=p T); · rw [map_zero]; exact (isLittleO_one_iff ℝ).mp h
    rw [map_zero] at h; exact (isLittleO_one_iff ℝ).mpr h
lemma guideT (u:By ℂ L (fun i=>stand (w i)) 1) : Tendsto (guide G d ∘ w) L (𝓝 0):=by
    have h:By ℝ L (fun i=> (w i).val) 0:=by
       have hu:= subY u (constant (1:FieldEnd G d)); simp only [sub_self] at hu; refine viaY (payReal hu) (Eventually.of_forall fun i=> ?_); change 1+ (w i).val-1= _; exact add_sub_cancel_left (1:FieldEnd G d) (w i).val
    let f(T:Module.Dual ℝ (FieldEnd G d)):= T.comp (Submodule.subtype (Normalize.Change G d)); have hw: By ℝ L w 0:= redeemBy f (fun u x=> Subtype.ext ( Veto.zero_guard (K:=ℝ) u.val (fun k=> x k) )) (fun i=> by rw [map_zero,← map_zero i]; exact h i); rw [← map_zero (guide G d)]; exact Stock (Module.finBasis ℝ (Change G d)) hw
lemma nominated (T: FieldEnd G d): adm T↔∃ A:Normalize.Change G d, stand A=T:= Iff.rfl
lemma numeral (u:∀ᶠ i in L,adm (F i)): ∃ A:ι→Normalize.Change G d, ∀ᶠ i in L,stand (A i)=F i:=by
    let A(i:ι):Normalize.Change G d:= if h:adm (F i) then ( ( nominated _ ).mp h ).choose else 0; exact ⟨A,u.mono fun i hi=> by unfold A; rw [dif_pos hi]; exact Classical.choose_spec ( ( nominated _ ).mp hi )⟩
-- Generic stage solve for Ξ^-1 C.Lookup.S.
structure Admits (L:Filter ι) (Q:ι→ FieldEnd G d):Prop where
    dawn : By ℂ L Q 1
    fits : ∀ᶠ i in L,adm ( Q i )
variable (H:Admits L F)
include H
lemma Admits.unital : ∀ᶠ i in L, IsUnit (F i) :=by
    obtain ⟨A,a⟩:= numeral H.fits; have hp:= ( guideT ( viaY H.dawn (a.mono fun _ h=> h.symm) ) ).eventually ( Fray.safe_pegs (G:=G) (d:=d) ); filter_upwards [hp,a] with i hi hv; apply ( Module.End.isUnit_iff _ ).mpr; rw [←hv]; simpa only[Function.comp_apply, Fray.box,LinearEquiv.symm_apply_apply] using hi
lemma discount_div (p:Admits L Q) (v:∀ᶠ i in L,F i * (stand (w i))= Q i) : SeatsW.Discount ℂ L 1 (fun i=>(w i).val):=by
    let u(x:Module.Dual ℂ (FieldEnd G d))(i:ι): Module.Dual ℂ (FieldEnd G d):= x ∘ₗ LinearMap.mulLeft ℂ (F i)
    have he(x:Module.Dual ℂ (FieldEnd G d))(Y:FieldEnd G d): Tendsto (fun i=> u x i Y) L (𝓝 (x Y)):= (by obtain v:= H.dawn ( x ∘ₗ LinearMap.mulRight ℂ Y ); rw [LinearMap.comp_apply,show LinearMap.mulRight ℂ Y 1 = Y from one_mul Y ] at v; exact v ); refine Veto.guard (fun u h=> Veto.zero_guard (K:=ℂ) u h) (fun i x=> u x i) he (fun x=>?_); apply IsLittleO.congr' (shine.mpr (ByZero p H) x) (v.mono fun i hi=> (?_)) (.refl ..); dsimp only; rw [←hi,stand, mul_add,mul_one,add_sub_cancel_left (F i)]; rfl
where ByZero (p:Admits L Q)(H:Admits L F): By ℂ L (fun i=> Q i-F i) 0:=by simpa using subY p.dawn H.dawn
lemma divorce (p:Admits L Q): ∃ V:ι→ XSpace.Normalize.Change G d, (∀ᶠ i in L,F i * stand (V i)=Q i) ∧ By ℂ L (fun i=>stand (V i)) 1:=by
    obtain v : ∀ᶠ i in L,∃ f:XSpace.Normalize.Change G d,F i * stand f= Q i:= by
         filter_upwards [H.unital,H.fits,p.fits] with i hi p q; rcases hi with ⟨V,t⟩; obtain ⟨F',hF'⟩:= (adm.inv V (t.symm ▸ p)).mul q; exact ⟨F',by rw [hF',←t,←mul_assoc,Units.mul_inv, one_mul]⟩
    let S(i:ι):= if h:∃ f:XSpace.Normalize.Change G d,F i * stand f= Q i then h.choose else 0; have ht:∀ᶠ i in L,F i*stand ( S i )=Q i:= v.mono fun i h=> by unfold S; rw [dif_pos h]; exact Classical.choose_spec h
    exact ⟨ S,ht,by simpa only [stand, add_zero] using addY (constant (1:FieldEnd G d)) (shine.mp (discount_div H p ht))⟩
omit H in
lemma cropAdm (h:Tendsto θ L (𝓝 0)){Q:ι→Guard G d}(p:Budget L Q)(w:∀ i, Base ( Q i ))(b:ℕ) : Admits L (fun i=> young b (θ i) ( Q i )) := ⟨ youngster h p w,Eventually.of_forall fun i=> adm.young (w i) _ _ ⟩
end ScaleFits
end YM.SignedWilsonExpansion.Belfry
