import YM.SignedWilsonExpansion.F9.Radical
/-!
# Stable section at ground. Blueprint map via finite geometric sum
 Lerona sold on effective level clock. Need preserves unity through document.Conv stage.
-/
set_option autoImplicit false
set_option maxHeartbeats 290000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.Stair
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
open Cirrus
open Normalize (Sec Formal Change)
open Tape
section control
local notation "leaf"=> Normalize.leaf
local notation "re"=> Normalize.reel
local notation "orI"=> Normalize.ori
structure GuardT (M: Module.End ℂ (Sec G h)) (z:ℂ): Prop where
    unit : M (leaf G h)= z • leaf G h
    height (d:ℕ) : d ≤ h→∀ x∈ Folia G d h,M x∈ Folia G d h
    real (x): M (re h x)= re h (M x)
    signed (s:Signed) x: M (orI s.ortho h x)= orI s.ortho h (M x)
structure Gift (M: Sec G h→ₗ[ℂ]Label G h): Prop where
    unit : M (leaf G h)= Labels.unit G h
    height (d:ℕ) : d≤h→∀ x∈ Folia G d h, (M x).val∈ localFields G d
    real (x): M (re h x)=realBar (M x)
    signed (s:Signed)(x): M (orI s.ortho h x)=Labels.tensor s.ortho (M x)
variable {f:Sec G h→ₗ[ℂ]Label G h}{g: Label G h→ₗ[ℂ] Sec G h}{M' N':Module.End ℂ (Sec G h)}{x y:ℂ}
lemma Gift.calls (p:Gift f)(v:Trustee g x): GuardT (g ∘ₗ f) x:=by
   unfold Trustee at v; refine ⟨?_,?_,?_,?_⟩
   · rw [LinearMap.comp_apply,p.unit,v.1]
   · intro d u x y; exact v.2.1 d u _ (p.height d u x y)
   · intro x; rw [LinearMap.comp_apply, p.real,v.2.2.1]; rfl
   intro s x; rw [LinearMap.comp_apply,p.signed s,v.2.2.2 s]; rfl
lemma Gift.turn (p:Gift f)(z:GuardT M' 1): Gift (f ∘ₗ M'):= by
   refine ⟨?_,fun d u x y=> p.height d u _ (z.height d u x y),?_,?_⟩
   · rw [LinearMap.comp_apply,z.unit,one_smul,p.unit]
   · intro x; rw [LinearMap.comp_apply,z.real,p.real]; rfl
   intro s x; rw [LinearMap.comp_apply,z.signed s,p.signed]; rfl
lemma ladderT (h:ℕ): Gift (G:=G) (ladderS h):=by
    refine ⟨Subtype.ext (map_one XSpace.On.lifting), fun d a x p=> ?_, fun x=> XSpace.On.section_real _ _ (rfl), fun s x=> XSpace.On.section_turn s x _ rfl⟩
    let y:Sec G d:=⟨x.val,p⟩; exact (XSpace.On.sectionMap d y).property
lemma GuardT.member (p:GuardT M' 0): M'∈ Change G h:=⟨(p.unit.trans (zero_smul ..)),p.height,p.real,p.signed⟩
lemma GuardT.one : GuardT (G:=G) (h:=h) 1 1:= ⟨(one_smul ..).symm, fun _ _ _ h=> h,fun _=>rfl,fun _ _=>rfl⟩
lemma GuardT.diff (p:GuardT M' x)(v:GuardT N' x) : GuardT (M'-N') 0:= by
    refine ⟨by rw [LinearMap.sub_apply,p.unit,v.unit,sub_self,zero_smul], fun d u x y=> Submodule.sub_mem _ (p.height d u x y) (v.height d u x y), fun t=> ?_,fun s t=>?_⟩ <;> simp only [LinearMap.sub_apply,p.real,v.real,p.signed,v.signed,map_sub]
lemma GuardT.reverse (p:GuardT M' 1)(h1:M'*N'=1)(h2:N'*M'=1) : GuardT N' 1:=by
    let e(t):= DFunLike.congr_fun h1 t; let z(t):= DFunLike.congr_fun h2 t; have H:= (show LeftInverse N' M' from fun t=>z t).injective; refine ⟨?_,fun d u x y=>?_,fun x=>?_,fun s x=>?_⟩
    · apply H; rw [one_smul,p.unit,one_smul]; exact e _
    · let S:=Folia G d h; let L:=M'.restrict (fun x (h:x∈ S)=> p.height d u x h); have hu: Injective L:=fun x y h=>Subtype.ext (H (congr_arg Subtype.val h)); let x':S:=⟨x,y⟩; obtain ⟨t,b⟩:= (LinearMap.surjective_of_injective hu) x'; have hp:N' x=t.val:= H ((e x).trans (congr_arg Subtype.val b).symm); rw [hp]; exact t.property
    · apply H; rw [p.real]; exact (e _).trans (congr_arg (re h) (e x)).symm
    apply H; rw [p.signed]; exact (e _).trans (congr_arg (orI s.ortho h) (e x)).symm
lemma GuardT.leader (M:Normalize.Guard G h)(p:Formal M): GuardT (coeff 0 M) 1:=by
    constructor
    · obtain ⟨u,rfl⟩:= p.actions; rw [coeff_zero_eq_constantCoeff_apply,Normalize.const_deck,Normalize.solitary,one_smul]
    · exact (tapeHeight M p 0).1
    · exact (tapeHeight M p 0).2.1
    exact (tapeHeight M p 0).2.2
end control
section portfolio
variable (W:Initialize G){A'' :∀ h,Rays G h W.hol}{Ω:Council F}{P':Normalize.Store G}
variable (q': Stair Ω (launch F W.hol W.surveys A'' k) A Ñ m c c h e k u Z)
-- formula via nil inverse, no singular inverse beyond first-meet.
def booth (T:Label G h→ₗ[ℂ] Sec G h): Module.End ℂ (Sec G h):= ∑ i∈Finset.range (h+1), (upsTurn T)^i
variable (Q:Normalize.Store G)(t':Mesh)(ρ:ℝ)
def porter : Sec G h→ₗ[ℂ] Label G h:= ladderS h ∘ₗ (booth (q'.originalT W t' ρ 0) ∘ₗ coeff 0 (Normalize.deck (Q.layout W t' h)))
lemma guardsMul (U V: Normalize.Guard G h)(v:U*V=1): coeff 0 U*coeff 0 V=1:=by simp_rw [coeff_zero_eq_constantCoeff_apply, ←map_mul, v,map_one]
lemma safe_booth (V: Label G h→ₗ[ℂ] Sec G h)(p:upsTurn V^(h+1)=0): (V ∘ₗ (ladderS h))* booth V=1∧ booth V*(V ∘ₗ (ladderS h))=1:=by
    let x:= upsTurn V; let M:= V ∘ₗ ladderS h; have hx:1-x=M:=by unfold x M upsTurn; abel
    exact ⟨(Eq.trans (congr_arg (fun m=>m * booth V) hx.symm) ((mul_neg_geom_sum x (h+1)).trans (by rw [show x^(h+1)=0 from p]; exact _root_.sub_zero (1:Module.End ℂ (Sec G h))))), (Eq.trans (congr_arg (fun m=>booth V*m) hx.symm) ((geom_sum_mul_neg x (h+1)).trans (by rw [show x^(h+1)=0 from p]; exact _root_.sub_zero (1:Module.End ℂ (Sec G h)))))⟩
include q'
variable (u_eq:t'.spacing=sizeT A ρ c)
include u_eq
lemma booth_turn : GuardT (booth (q'.originalT W t' ρ 0)) 1:= by have hv:= safe_booth _ (q'.radicalNil W t' ρ u_eq); exact GuardT.reverse ((ladderT h).calls (by simpa using q'.authorize W t' ρ 0)) hv.1 hv.2
lemma porter_gift (p:Q.Meets W t' h): Gift (q'.porter W Q t' ρ):= ((ladderT h).turn (q'.booth_turn W t' ρ u_eq)).turn (GuardT.leader _ p.1) -- associative defeq
lemma serveT (p:Q.Meets W t' h)(l:ℕ)(f:Sec G h): q'.publish W t' ρ Q l 0 (q'.porter W Q t' ρ f)=f:=by
   rw [first_pass]; let Y:= q'.originalT W t' ρ 0; let T:= Normalize.deck (Q.layout W t' h); let U:= coeff 0 (inverseH W Q t' h); let t:= coeff 0 T
   have H:= safe_booth _ (q'.radicalNil W t' ρ u_eq); have he: (Y (ladderS h (booth Y (t f))))=t f:= DFunLike.congr_fun H.1 (t f); change U (Y (ladderS h (booth Y _ )))= _; rw [he]; exact DFunLike.congr_fun (guardsMul _ _ (ladderH W t' h p.1).1) f
end portfolio
end YM.WilsonCoeffUV.Mer.Xa.Stair
