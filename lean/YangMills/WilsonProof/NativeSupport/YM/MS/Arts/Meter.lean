import YM.MS.Arts.Meter
import YangMills.WilsonProof.NativeSupport.YM.MS.Arts.Rare
/-!
# Sector count for an ordinary trc term

No real part conditions. Advance by weighted difference of trc at m,m+1.
 Upper rank arbitrary. Need jet compatibility. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Pilot Spin
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{R A:Type}[Fintype A][DecidableEq A]{m n k:ℕ}{b:Bool}{F:Mob G}{U:Rip G}
variable (h:m≤n)

lemma more {ℋ:Type}[AddCommMonoid ℋ](u:Cfield G n→ℋ): (∑ i:Cfield G n,u i)=(∑ i:Cfield G m,u (embA (rises h) i))+∑ i: Apart m n,∑ s:Bool,∑ c:G.ColorIndex, u (vleg s (aside h i) c):= by
   simp only [Fintype.sum_prod_type,Fintype.sum_option]; rw [cut_sum h (fun i=>∑ v: Bool,∑ a:G.ColorIndex, u ((some i,v),a))]; unfold embA; simp [vleg]; abel -- h perhaps $Bool.sum not simp
lemma pairedU (K:Spin (L n))(he:∀ p, K.turn (Left h p)=Left h p)(HF:Sturdy b F) {i j k l:L n} {z w:ℝ}
 (hs: K.turn (spray i)=z • spray j)(hp:K.turn (spray k)=w • spray l)(s t:Bool)(f g:G.ColorIndex)(p:SectorP m)(x:Legs (Shore G m)):
    F n ((vleg s i f,Left h p)::(vleg t k g,Left h (-p))::lift h x)= (z:ℂ)*(w:ℂ)* F n ((vleg s j f,Left h p)::(vleg t l g,Left h (-p))::lift h x):= by
    nth_rw 1 [←HF.turn n K (fixedLeft h he)]; change (leggo _ K).beam _ _=_; rw [cols hs, cols hp, he, he]; change _*( (w:ℂ) * ((flagS K G).beam _ (lift h x)))=_; rw [beam_only h K he, mul_assoc]; rfl
variable {h}

/-! Distant sectors pair across both loops only if same. -/
variable {i j: Apart m n}{s t:Bool}{c d:G.ColorIndex} {x:SectorP m}{l: Legs (Shore G m)}
variable (HF: Sturdy b F) (HU: Ruddy b U)
include HF
lemma fleck_zero (h:m≤n)(hm:i≠j): fleck h U F i j s t c d x l=0:= by
   unfold fleck; rw [← map_neg]; apply mul_eq_zero_of_right; let y:=(aside h) i; let z:=(aside h) j; have he : y≠z:= fun hw=> hm ((aside h).injective hw)
   have h0 : (spark y).turn (spray y)=(-1:ℝ) • spray y:= (sees_p y).trans (by simp); have h1 : (spark y).turn (spray z)=(1:ℝ) • spray z:= (sees_away he).trans (one_smul ..).symm
   have hk:= pairedU h (spark y) (lightOn h i) HF h0 h1 s t c d x l; push_cast at hk; rw [mul_one,neg_one_mul] at hk; exact neg_eq_self.mp hk.symm
include HU
lemma fleck_moves (h:m≤n): fleck h U F i i s t c d x l=fleck h U F j j s t c d x l:= by
    have hp (i : Apart m n): Momentum.sq (spray i)=1:= by rw [sq_eq,zap,if_pos rfl]
    obtain ⟨X,hX,H⟩:= fit h (spray i) (spray j) (by rw [hp,hp]); let y:= (aside h) i; let z:=(aside h) j; have he : X.turn (spray y)=(1:ℝ) • spray z:= by simpa only [Right,one_smul,send_spray] using H
    have hx : X.within b := fixedLeft h hX; obtain hP := trace_leg (C:=G.ColorIndex) (HU.turn n X.back (X.within_back hx)) s t c d he he (Left h x); simp only [Complex.ofReal_one,one_mul,hX] at hP
    obtain hL:= pairedU h X hX HF he he s t c d x l; simp only [Complex.ofReal_one,one_mul,map_neg] at hL; exact congr_arg₂ _ hP hL
end YM.MS.Arts
