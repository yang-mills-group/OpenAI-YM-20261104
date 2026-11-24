import YM.SignedWilsonExpansion.Dancer.CashDesk
import YM.SignedWilsonExpansion.Purchase.Cadet
/-!
# Numerical Momentum on the launched corpus. Coherence discounts & rank signs paid from the same θ as births.
 Normalize.hologram high-d implemented in `Dancer/Dream`. Adjust to real convention only after. 
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer.Coats
open XSpace Structure1 Normalize Future Gauge Filter Function Matrix
open Asymptotics WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ Stair
open SeatsW Commission Shell Lights Fort
open FVA2 Dframe Maxwell Maxwell.Free Maxwell.Wick
open PorchK WilsonCoeffUV Precision Wilson RG Source WardBin
open scoped BigOperators Topology Classical
variable {G:Gauge} {e b d h t w n k u:ℕ}{a:Axis}{ι:Type}{L:Filter ι}
-- apparel Coat.L
abbrev CutNet (F: Labels.Frames G) := ∀ p:ℕ, Sec G p→ₗ[ℂ] (F.level p).Coeff
variable {A:Credit}{R:Realm G (e+1) A}{F:Labels.Frames G}
variable {X:Hol G} {W':Initialize G} {Ω:Council F}{Q:∀ h,Rays G h W'.hol}
variable (Wn: Normalize.Store G)(z:ι→ PorchK W' F Q Ω R h k u){Y μ ν ε ℊ:ι→ ℝ} (N:ι→CutNet F)
structure Net (z:ι→PorchK W' F Q Ω R h k u)(N:ι→CutNet F)(d:ℕ)(L:Filter ι)(Y μ ν θ:ι→ℝ): Prop where
     cost (p:ℕ)(hp:0<p)(hv:p≤d)(x:Sec G p) : SizeW L μ ( F.level p ) (fun i=> N i p x)
     unitE (p:ℕ)(hp:0<p)(hv:p≤d): (fun i=> N i p (Normalize.leaf G p)) =ᶠ[L] fun i=> ( ( (z i).markW:ℂ)^p ) • ( F.level p ).e0
     fairM (t:ℕ)(ht:0<t)(p:t≤d)(j:Toon G t)(hx:j.size=t) : ∃ y v, Crest L Y ν v (F.level t) (fun i=> N i t (Logo G t j)) j.grade y ∧ Logo G t j=bulb G t (( F.level t ).coords.symm y)
     spinM (p:ℕ)(hp:0<p)(hx:p≤d)(x:Sec G p)(s:Signed)(n:ℕ)(t:(F.level p).Index) : Wage L μ (θ^n) (fun i=> ( N i p (ori s.ortho p x) - (F.level p).act s.ortho ( N i p x)) t )
     payM (p:ℕ)(hp:0<p)(hx:p≤d)(x:Sec G p)(n:ℕ)(t:(F.level p).Index) : Wage L μ (θ^n) (fun i=> ( N i p (reel p x) - star ( N i p x)) t )
-- horizon.tau μ.Calendar Slack `𝓻∼measure.Ret` via sale.
variable (ρ:ι→ℝ)(hp: TimeQ L ℊ ρ)
structure Cranking (Wn:Normalize.Store G)(X: Hol G)(z:ι→PorchK W' F Q Ω R h k u)(b d:ℕ)(L:Filter ι)(Y μ ν θ ε ρ:ι→ℝ): Prop where
     h0: 0<d
     hd: d≤h
     crop_b:b≤e
     purity : ∀ i,Bid.pop (Ω i)
     cleared : ∀ i,( Ω i ).Sound X
     scope : FrontQ z L Y θ μ ν
     time : TimeQ L θ ρ
     arc : ∀ᶠ i in L,0<θ i
     small : ε=O[L] (1:ι→ℝ)
     wageT (l:ℕ): l≤e → Across L Y ℂ (fun i=> (z i).toEpic.tenor W' Wn l)
     fee (p:ℕ)(hp:p≤d) : ∃ b:ℕ,∀ n:ℕ,(fun i=> μ i^n*((z i).billSize p*θ i^b))=o[L] ε
     pruning (n:ℕ) : (fun i=> μ i^n*(z i).markW)=o[L] ε
variable (C: Cranking Wn X z b d L Y μ ν ℊ ε ρ)(V: Net z N d L Y μ ν ℊ)
def stamped (b d:ℕ)(i:ι) : Sabre d h G := fun t=> gown (z i) Wn b (Ω t) (ρ i) ∘ₗ N i t -- argument order
include C
local notation "Ψ"=> stamped Wn z N ρ b d
lemma hew (p:t≤d)(v:0<t)(f:ι→ (F.level t).Coeff)(hF:∀ (u:(F.level t).Index) (n:ℕ), Wage L μ (ℊ^n) ( fun j=> f j u )): Discount ℂ L ε (fun i=> (z i).gown Wn b (Ω t) (ρ i) (f i)):=by
    intro T; obtain ⟨e,h⟩:= C.fee t p; let S(i):=((z i).gown Wn b (Ω t) (ρ i)); let B:= Pi.basisFun ℂ (F.level t).Index; let x(i) u:= T ( S i ( B u )); let k(i):=( z i ).billSize t; have he(i):T (S i (f i))=∑ u:( F.level t ).Index,x i u * f i u:=by nth_rw 1 [← B.sum_repr (f i)]; rw [map_sum,map_sum]; refine Finset.sum_congr rfl fun u _=>?_ ; rw [map_smul,map_smul,smul_eq_mul]; exact (mul_comm ..).trans (congr_arg (x i u * ·) ( Pi.basisFun_repr .. )) -- check
    have hw (u:( F.level t ).Index):Wage L μ k (fun i=>x i u):= PorchK.hewn_full z Wn C.wageT C.scope ρ C.arc C.time (C.cleared t) (C.purity t) (p.trans C.hd) (⟨fun y=> Wage.unitC _⟩:SizeW _ _ (F.level t) (fun _=>B u)) b C.crop_b T
    change (fun i=> T (S i _))=o[L] ε; rw [funext he]; apply IsLittleO.sum; intro i _; exact (Wage.mul (hw i) (hF i e)).spend (g:=ε) h
include V
lemma tiltsR (p:ℕ)(x:Sec G p)(hx:0<p)(hp:p≤d): Discount ℂ L ε (fun i=> Ψ i p ( reel p x ) - reel h (Ψ i p x)):=by
    let F(i):= N i p (reel p x) - star ( N i p x ); refine sameSalary (hew Wn z ρ C hp hx F (fun u n=> V.payM p hx hp x n u)) (Eventually.of_forall fun i=> ?_) (.refl ..) -- order
    dsimp only; rw [ show (z i).gown Wn _ _ _ _= _ from (show ( z i ).gown Wn b (Ω p) (ρ i) (F i)= _ from map_sub _ _ _), titleReal Wn (x:=z i) ( C.cleared p ) ( C.purity p ) ( hp.trans C.hd ) ]; rfl
lemma tiltsO (p:ℕ)(x:Sec G p)(hx:0<p)(hp:p≤d)(s:Signed): Discount ℂ L ε (fun i=> Ψ i p (ori s.ortho p x)- ori s.ortho h ( Ψ i p x)):=by
    let F'(i):= N i p (ori s.ortho p x) - ( F.level p ).act s.ortho ( N i p x ); refine sameSalary (hew Wn z ρ C hp hx F' (fun u n=> V.spinM p hx hp x s n u)) (Eventually.of_forall fun i=> ?_) (.refl ..)
    dsimp only; change (z i).gown Wn b (Ω p) (ρ i) (F' i)=_; unfold F'; rw [map_sub,titleSpin Wn (x:=z i) (C.cleared p) (C.purity p) (hp.trans C.hd) s]; rfl
lemma tapers (p:ℕ)(x:Sec G p)(hx:0<p)(hp:p≤d): Discount ℂ L ε (fun i=> Ψ i p x - Normalize.up (hp.trans C.hd) (distill p (Ψ i) x)) := fun T=> Wage.spend ( PorchK.cloth_tithe z Wn C.wageT C.scope ρ C.arc C.time (C.cleared p) (C.purity p) (hp.trans C.hd) (V.cost _ hx hp x) b C.crop_b T) C.pruning
lemma merited : Lights.Gleam F L Ψ :=by
    constructor
    · intro t a b₀; refine viaY ( constant _) (?_); filter_upwards [V.unitE t a b₀] with i hi; change N i t _= _ at hi; simp only [stamped,LinearMap.comp_apply,hi,titleUnit Wn (x:=z i) (C.cleared t) (C.purity t) ( b₀.trans C.hd ) ] -- κ
    intro t p ht j y hj hy hz; obtain ⟨ξ,bv,c,bh⟩:= V.fairM _ p ht j hj; have hx:= PorchK.body_poll z Wn C.wageT C.scope ρ C.arc C.time (C.cleared t) (C.purity t) (ht.trans C.hd) (V.cost t p ht (Logo G t j)) c b C.crop_b y hz hy; conv=> arg 3; rw [bh]
    exact hx
lemma incurs (G':ι→Point G h 2)(W:Shell.Emblem a L G')(hV:∀ (t:ℕ)(u:0<t) (p:t≤d) (w:ℕ) (q:0<w)(v:w≤d)(x:Sec G t)(y:Sec G w), Tendsto (fun i=> Paar (G' i) (Ψ i t x) (Ψ i w y)) L (𝓝 (Paar (GramW G h a) (Rise (p.trans C.hd) x) (Rise (v.trans C.hd) y)))) : Lights.Horizon a L G' Ψ :=by
    refine {W with pos:= C.h0, space:= C.hd,orbit_bound:= fun t p w x=>?_, mix:=fun u p w v x y=> hV _ u p _ w v x y, hewn:= fun t p w x=>?_ }
    · let K(i):= ( Ψ i t (reel t x)- ( reel h ( Ψ i t x ) ) ); have h₁:= tiltsO Wn z N ρ C V t (reel t x) p w (Signed.mirror a); have h₂: Discount ℂ L ε K:= tiltsR Wn z N ρ C V _ x p w; apply sunrise ( sameSalary (aboveCeiling h₁ (cheapens h₂ (ori (Signed.reflect a) h))) (?_) (.refl ..)) C.small; apply Eventually.of_forall; intro i; change (_ - ori _ h _)+ori (Signed.reflect a) h (_-_) = _; simp_rw [map_sub]; unfold mirrorB Commission.Gram.flipE Signed.reflect; abel
    have hB:= sunrise (tapers Wn z N ρ C V t x p w) C.small; rw [show (0:Sec G h)=0-0 from (sub_self (0:Sec G h)).symm]; refine viaY (subY ( constant 0 ) hB) (Eventually.of_forall fun i=> ?_); simp only [zero_sub]; abel
end YM.SignedWilsonExpansion.Dancer.Coats
