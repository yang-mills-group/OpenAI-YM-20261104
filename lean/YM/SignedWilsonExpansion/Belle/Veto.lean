import YM.SignedWilsonExpansion.Belle.Spend
/-! # Projection.Regularize vector auxiliary comparison only, physical V legend same.Pal.
 No Frame lift identity at finite regulator invoked; expenses repay cap commutation.
 Mixed-use.Also leading W alignment after restricting period filter to elected.Stamp.
-/
set_option autoImplicit false
set_option maxHeartbeats 51000
noncomputable section
namespace YM.SignedWilsonExpansion.Belle
open FVA2 FVA2.Scale FVA2.Dframe Dancer Dancer.Drawing Dancer.SeatsW
open Dancer.Shell Dancer.Fort
open Asymptotics Filter Function XSpace XSpace.Structure1 Normalize Gauge
open MS MS.Local.Physical MS.High MS.Land MS.Native MS.Fleet Maxwell Maxwell.Free Maxwell.Wick
open Commission.Gram Path WilsonCoeffUV.Mer.Xa MarqueQ PorchK Future
open scoped Topology BigOperators Classical
variable {G:Gauge}{ι κ R M F K:Type} {L:Filter ι}{θ:ι→ℝ} {d t e:ℕ}
namespace Veto
-- Gram uses second partner, spanning left min. Linear maps.Stagger.Council
abbrev F0 (G:Gauge)(d:ℕ):=FieldEnd G d
variable {x:ι→ Sec G d} {y:ι→F0 G d} {P:ι→ Point G d 2}
local instance : FiniteDimensional ℝ (F0 G d):= Module.Finite.trans ℂ _
section transfer
variable [NontriviallyNormedField K][CompleteSpace K][AddCommGroup M][Module K M][FiniteDimensional K M][NormedAddCommGroup F][NormedSpace K F][FiniteDimensional K F]
lemma guard {u:ι→M}{P:κ→ M →ₗ[K] F}(h:∀ t:M,(∀ i,P i t=0)→t=0)(Q:ι→κ→M→ₗ[K]F)(v:∀ i (x:M), Tendsto (fun j=> Q j i x) L (𝓝 (P i x))) (cost:∀ i,(fun j=>Q j i (u j))=o[L] θ) : Discount K L θ u:=by
     let B:=Module.finBasis K M; obtain ⟨C,s,f⟩:= Commission.Foundation.projects _ _ h v B; let I:= ↑(Commission.Foundation.cuts _ h).choose; let Y(j:ι)(s:I):= Q j s.val (u j); have hx : (fun i=> B.equivFun (u i))=o[L] θ:= ( IsBigO.trans_isLittleO (IsBigO.of_bound (g:=Y) C (f.mono fun i hi=> hi _)) ( isLittleO_pi.mpr (fun i=> cost i.val) ) ); intro x; let C':= LinearMap.toContinuousLinearMap ( x.comp B.equivFun.symm.toLinearMap ); refine ( ( ( C'.isBigO_id _ ).comp_tendsto Filter.tendsto_map ).trans_isLittleO hx ).congr_left (fun i=>?_); exact congr_arg (fun y=> x y) (B.equivFun.symm_apply_apply (u i))
lemma zero_guard (u:M)(p:∀ k:Module.Dual K M,k u=0): u=0:=by apply (Module.finBasis K M).equivFun.injective; rw [map_zero]; exact funext fun i=> p ((Module.finBasis K M).coord i)
end transfer
variable {V:Axis}
lemma manikin (I:Shell.Emblem V L P)(u:∀ q:Sec G d,By ℂ L (fun i=> y i q) q) (h:∀ f:Sec G d,(fun i=> Paar (P i) (x i) (y i f))=o[L] θ) : Discount ℂ L θ x:= by
     refine guard (P:=fun w:Sec G d=> Commission.Gram.acts (GramW G d V) w) (fun i hi=> ?_) (fun i q=> Commission.Gram.acts (P i) (y i q)) (?_) h
     · exact Shell.onPeak V _ (hi (mirrorB V i))
     intro j p; exact Shell.p_emit I (constant p) (u j)
-- Cap system. t>0 allowed; W weights including true full unit.Now.
abbrev caps (G:Gauge):=∀ d,F0 G d
variable {z:ι→caps G} {U:ι→Point G d 2}
structure Civic (L:Filter ι)(θ:ι→ℝ)(y:ι→F0 G d): Prop where
     paid : θ=O[L](1:ι→ℝ)
     limits (v:Sec G d): By ℂ L (fun i=>y i v) v
     spin (s:Signed)(v:Sec G d): Discount ℂ L θ (fun i=>y i (ori s.ortho d v)-ori s.ortho d (y i v))
     reo (v:Sec G d): Discount ℂ L θ (fun i=>y i (reel d v)-reel d (y i v))
     unit : Discount ℂ L θ (fun i=>y i (leaf G d)-leaf G d)
structure Marque (a:Axis)(L:Filter ι)(θ:ι→ℝ)(z:ι→caps G)(P:ι→Point G d 2):Prop extends Shell.Emblem a L P, Civic L θ ( fun i=>z i d ) where
     nest (t:ℕ) (p:0<t)(s:t≤d) (x:Sec G t)(y':Sec G d): (fun i=> Paar ( P i ) (z i d ( Normalize.up s x )) (z i d y')- Paar ( P i ) (Normalize.up s ( z i t x )) (z i d y'))=o[L] θ
variable (S:Marque V L θ z P)
include S in
lemma weightM (p:0<t)(u:t≤d)(x:Sec G t): Discount ℂ L θ (fun i=> z i d (Normalize.up u x)-Normalize.up u (z i t x)):= manikin S.toEmblem S.limits fun y=> by
    let f:= S.nest t p u x y; exact f.congr_left (fun i=> (map_sub (Commission.Gram.acts (P i) (z i d y)) _ _).symm )
-- bundle of all scalar constraints. include ℝ spin placement.
abbrev aulter (x:Sec G d): F0 G d →ₗ[ℝ] Sec G d:= (LinearMap.applyₗ (R:=ℂ) x).restrictScalars ℝ
inductive Ballot (G:Gauge)(d:ℕ): Type
| unit
| stay (s:ℕ)(t:0<s)(v:s≤d)(x:Sec G s)
| spin (σ:Signed)(x:Sec G d)
| real (x:Sec G d)
-- pullField.A motion real only
abbrev recycle (u:t≤d) (G:Gauge) : F0 G d:= (Normalize.up u).comp ( PorchK.prune t d )
lemma recycle_id (u:t≤d)(x:Sec G t): recycle u G (Normalize.up u x)=Normalize.up u x := by rw [recycle,LinearMap.comp_apply,pruned_up x u]
def poll : Ballot G d→ F0 G d →ₗ[ℝ]Sec G d
| .unit => aulter (leaf G d)
| .stay n _ h x=> let u:= aulter (Normalize.up h x); u- (( recycle h G ).restrictScalars ℝ).comp u
| .spin s x=> aulter (ori s.ortho d x)- ((ori s.ortho d).restrictScalars ℝ).comp (aulter x)
| .real x=> aulter (reel d x)-(reelR d).comp (aulter x)
-- Weight0 only genuine unit.Sp. proof stock uses invariant basis (includes side t fixed), no Simple required.
lemma pass0 (T:F0 G d)(h:T (leaf G d)=0)(x:Sec G 0): T (Normalize.up (Nat.zero_le d) x)=0 := by
    rw[← (Logo G 0).sum_repr x,map_sum,map_sum]; apply Finset.sum_eq_zero; intro i _; obtain ⟨t,ht⟩:= zero_orig i (Nat.le_zero.mp (size_le i)); rw [ht]; simp_rw [map_smul]; rw [show (Normalize.up (Nat.zero_le d)) (leaf G 0)=leaf G d from rfl,h]; simp
lemma polling (x:F0 G d): x∈Change G d ↔ ∀ i: Ballot G d,poll i x=0 :=by
    constructor
    · rintro ⟨v,u,h,w⟩ i; cases i with | unit=> exact v | spin s i=> exact sub_eq_zero.mpr (w s i) | real i=> exact sub_eq_zero.mpr (h i) | stay t s m i=>
      let X:= u t m (Normalize.up m i) i.property; refine sub_eq_zero.mpr (?_); change x (Normalize.up m i)= recycle m G (x ( Normalize.up m i)); let t':Sec G t:= ⟨_, X⟩; exact (recycle_id m t').symm -- defeq
    intro h; have h₀:x (leaf G d)=0:=h (.unit); refine ⟨h₀,fun l hl p v=> ?_, fun p=> sub_eq_zero.mp (h (.real p)),fun s p=> sub_eq_zero.mp (h (.spin s p))⟩
    let q:Sec G l:=⟨p.val,v⟩; have he:Normalize.up hl q=p:= rfl; by_cases j:0<l; · exact ( he ▸ (show (x (Normalize.up hl q)).val∈ shellSector G l from congr_arg Subtype.val (sub_eq_zero.mp (h (.stay l j hl q))) ▸ ( PorchK.prune l d (x (Normalize.up hl q))).property) )
    have ho:l=0:=Nat.eq_zero_of_not_pos j; subst l; rw [← he,pass0 x h₀ q]; exact Submodule.zero_mem _
-- current Marque implies all. distortion applied.
private lemma splice_ {M:Type} [AddCommGroup M][Module ℝ M][FiniteDimensional ℝ M](V: Submodule ℝ M)(x:M): x-spillP V x ∈ V := Submodule.sub_projection_mem (Submodule.exists_isCompl V).choose_spec.symm _
def deform (T:F0 G d): Change G d:= ⟨(T-1)-spillP (Change G d) (T-1),  (by exact splice_ (Change G d) (T-1) )⟩
lemma spell (x:F0 G d) : Normalize.stand (deform x)=x-spillP (Change G d) (x-1):=by change 1+(x-1-_) = _; abel
include S
lemma civic_sign (t:Ballot G d): Discount ℂ L θ (fun i=> poll t (z i d-1)) := by
     cases t with
     | unit=> exact S.unit
     | spin w y=>
         refine sameSalary ( S.spin w y ) ( Eventually.of_forall fun i=>?_ ) (.refl ..); change _ = z i d _ - ori w.ortho d y - ori _ d (z i d y-y); rw [map_sub]; abel
     | real y=>
         refine sameSalary ( S.reo y ) ( Eventually.of_forall fun i=>?_ ) (.refl ..); change _= z i d _- reel d y -reel d ( z i d y-y ); rw [map_sub]; abel
     | stay t s h x=>
         let f:= Normalize.up h (G:=G); let y:= f x; let U(i):= z i d y; let r(i):= f ( z i t x ); let m:= recycle h G; let u:= weightM S s h x; refine sameSalary (belowCeiling u (cheapens u m)) ( Eventually.of_forall fun i=>?_ ) (.refl ..); change U i-r i - m (U i-r i) = U i-y-m (U i-y); rw[map_sub,map_sub,show m (r i)=r i from recycle_id _ _, show m y=y from recycle_id _ _]; abel
omit S
lemma supplyReal {θ':ι→Sec G d}(h: Discount ℝ L θ θ'): Discount ℂ L θ θ':=by
     intro T; have hr:=h (Complex.reCLM.toLinearMap.comp (T.restrictScalars ℝ)); have hv:= h (Complex.imCLM.toLinearMap.comp (T.restrictScalars ℝ)); let f:=Complex.ofRealCLM; refine ( ( ( ( (f.isBigO_id _).comp_tendsto Filter.tendsto_map ).trans_isLittleO hr ).add ((((f.isBigO_id _).comp_tendsto Filter.tendsto_map).trans_isLittleO hv).const_mul_left Complex.I) ).congr_left (?_)); intro i; change ↑( T (θ' i) ).re + Complex.I * ↑( T (θ' i) ).im= _; rw [mul_comm]; exact Complex.re_add_im _
abbrev cut (p: Ballot G d × Module.Dual ℝ (Sec G d)) : Module.Dual ℝ (F0 G d):= p.2.comp (poll p.1)
lemma normC (T:F0 G d): T∈Change G d ↔ ∀ p: Ballot G d × Module.Dual ℝ (Sec G d), Veto.cut p T=0:= by
     rw [polling]; exact ⟨(fun h p=>by change p.2 ((poll p.1) T)=0; rw [h p.1,map_zero]), fun h p=> zero_guard (K:=ℝ) _ (fun k=> h ( p,k ))⟩
include S
attribute [local irreducible] spillP
lemma repair : Discount ℝ L θ (fun i => spillP (Change G d) (z i d-1)):=by
     let cut0:= Veto.cut (G:=G) (d:=d); have hp (i: Ballot G d × Module.Dual ℝ (Sec G d)): (fun j=> cut0 i (z j d-1))=o[L] θ:= by
        let H: Discount ℝ L θ (fun j=> (poll i.1) (z j d-1)):=castReal (civic_sign S i.1); exact H i.2
     exact pours (P:=fun i=> z i d-1) (Change G d) (F':=cut0) hp normC
lemma actReform (x:Sec G d): Discount ℂ L θ (fun i=> z i d x-Normalize.stand (deform (z i d)) x):=by
     refine sameSalary (supplyReal (cheapens (repair S) (aulter x))) (Eventually.of_forall fun i=> ?_) (.refl ..); dsimp only; rw[spell,LinearMap.sub_apply]; change _ = z i d x-(z i d x- _); rw [sub_sub_cancel]; rfl
lemma steered (x:Sec G d): By ℂ L (fun i=>Normalize.stand (deform (z i d)) x) x:= by
     refine viaY (x:=x) (by simpa only [sub_zero] using subY (S.limits x) (sunrise (actReform S x) S.paid)) (Eventually.of_forall fun i=> by abel )
lemma stake : Tendsto (fun i=> guide G d (deform (z i d))) L (𝓝 0):=by
     let f(i):=deform (z i d); have h(x:Sec G d): By ℝ L (fun i=>f i|>.val x) 0:=payReal ( by refine viaY (x:=0) (by simpa only [sub_self] using subY (steered S x) ( constant x )) (Eventually.of_forall fun i=> ?_); rw[stood]; exact add_sub_cancel_left ..)
     let p (q:Sec G d× Module.Dual ℝ (Sec G d)):= q.2.comp ((aulter q.1).comp (Submodule.subtype (Change G d)))
     have W: By ℝ L f 0:= redeemBy p (fun u h=> Subtype.ext ( DFunLike.ext _ _ (fun x=> zero_guard _ (fun k=> h ( x,k ))) )) ( fun j=> by rw [map_zero]; rw [←map_zero j.2]; exact h j.1 j.2); rw[← map_zero (guide G d)]; exact Stock (Module.finBasis ℝ (Change G d)) W
end Veto
end YM.SignedWilsonExpansion.Belle
