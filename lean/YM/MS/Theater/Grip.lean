import YM.MS.Theater.Pen
/-!
# Fourier shadow law faithful. Recover Null relative before Color and Bright.S.OneLift
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n r:ℕ}{u x v:ℤ}{p q:Pol G}{F H:Law G}{f:Local.BV.Grade G}
local notation "KΩ"=> hands G
local notation "ζ"=> Koszul.mono
local infix:70 " ⋆ "=> product KΩ
abbrev Mem0 (L:Law G)(u:ℤ)(k:ℕ): Prop:= L∈ Carry G u k∧ Woven.sym L
lemma KP (P:Probe G)(X:Labels.Jet G)(hc:Board P k X)(hp:At p (h,r))(hQ:h≤k): back P r ( orbit G p ) = ( r.factorial:ℂ )* Labels.read X p:= by
    let Q(i:ℕ×ℕ)(v:Pol G): Prop:= i.1≤ k→ back P i.2 ( orbit G v )=(i.2.factorial:ℂ)* Labels.read X v;
    refine axisI Q hp ?_ ?_ ?_ ?_ hQ; · intro c _; rw [cus, Labels.read,MvPolynomial.aeval_C, show ((0:ℕ×ℕ).2.factorial:ℂ)=1 from (by simp),one_mul ]; rfl -- cast reducibility
    · intro i _; simp
    · intro i j F hv hi he; rw [ bags,cusp ]; rcases j with ⟨j,d⟩; change back P (1+i.2) ( ζ _ ⋆ _ )= (((1+i.2).factorial:ℂ)*_); rw [ add_comm 1, θchar P i.2 (shadow_ω ⟨j,d⟩|>.1), hi, Nat.factorial_succ, map_mul, Labels.read, MvPolynomial.aeval_X ]; -- constraints
      · rw [ show P (lamp (G:=G) ⟨j,d⟩) = pick (G:=G) ⟨j,d⟩ ( X j ) from ( hc.runs j _ ?_ ) ]; · push_cast; rw [show coord X ⟨j,d⟩= pick (G:=G) ⟨j,d⟩ ( X j ) from rfl]; unfold pick; simp only [ LinearMap.comp_apply, Function.comp_apply, ContinuousLinearMap.coe_coe ]; ring
        change j+2+i.1 ≤ k at he; exact_mod_cast (show j+2≤k from by omega)
      change j+2+i.1≤k at he; omega
    intro p f g he hf hF hG h; rw [map_add,map_add,map_add,hF h,hG h,mul_add]
lemma soundless (hp:At p (h,r))(he:orbit G p=0): p=0:= by
   apply Labels.eval_ext; intro A; obtain ⟨Q,hQ⟩:= covers h A; obtain hr:= KP Q A hQ hp ( le_refl _ ); rw [he,map_zero] at hr; rw [map_zero]; exact (mul_eq_zero.mp hr.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero r)
lemma opaqueL (hp:At p (h,r))(hq:At q (h,r))(he:orbit G p=orbit G q): p=q:= by apply sub_eq_zero.mp; apply soundless ( sub_mem hp hq ); rw [ map_sub, he,sub_self ]
/-- Null image estimate. -/
abbrev PastDue (G:Gauge)(h:ℤ)(r:ℕ) : Submodule ℂ ( Law G ):= Submodule.map natQ ( Bed G h (-1) r ) -- refine later sym
lemma clocked (hF:At p (h,r))(hP:orbit G p∈ PastDue G h r): Maxwell.reduceEq p=0:= by
    obtain ⟨L,hL,h⟩:=hP; apply Maxwell.equalPol; intro u; let U:=fun i=> gaugeJet ( u i ); obtain ⟨P,hP⟩:= covers _ U; obtain hh:= KP P U hP hF ( le_refl _ ); rw [ ← h, headQuiet (X:=u) hP (by exact le_rfl) hL ] at hh; rw [Maxwell.jet_value,map_zero]; exact (mul_eq_zero.mp hh.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero r)
-- $Q composite.Energie.Sym on primitive.Need reverse use PastSym strictly.Prove.
def SymC (G:Gauge): Submodule ℂ ( Law G ):={ carrier:={F| Woven.sym F}, zero_mem':=Koszul.Symm.zero, smul_mem':=fun i _ h=> h.smul i, add_mem':=fun a b=> a.add b }
abbrev GradePast (G:Gauge)(u:ℤ)(r:ℕ):= (Bed G u (-1) r) ⊓ SymC G
abbrev PastSym (G:Gauge)(u:ℤ)(r:ℕ):= Submodule.map natQ (GradePast G u r)
-- Leibniz.Prior charges for mono.
lemma pawn_1 (he:f∈ yields u x): natQ ( ζ f )= ζ (Q f):= by rw [← dawnB f, show natQ (bud f hit)= _ from Woven.parity_bud ( V:=Gof ) he,dawnB (Q f),MatrixLet.no]; rw [← place_at,map_zero]; simp
lemma tim_1 (he:Horizontal f u) (hq: H∈ PastSym G x r): ζ f ⋆ H∈ PastSym G (u+x) (r+1):= by
   obtain ⟨K,hk,rfl⟩:=hq; have hh : natQ (ζ f ⋆ K)= ζ f ⋆ natQ K:= by
       change Gof.Q _=_; obtain hP:= Gof (G:=G) |>.product_rule (ζ f) K; rw [ show Koszul.sign _ true _=( ζ f ) from Eq.trans ( Pure.signs ( lying he.1 ) true ) ( one_smul _ _ ),show Gof.Q ( ζ f )=0 from (pawn_1 he.1|>.trans ( he.2 ▸ zero_mono )),map_zero, LinearMap.zero_apply,zero_add ] at hP; exact hP -- sign cast One
   refine ⟨ _,⟨?_, symθ.times ( show Woven.sym K from hk.2 )⟩, hh ⟩; exact ( ( by rw [ zero_add ] : Bed G (u+x) (0+(-1)) (r+1)=Bed G (u+x) (-1) (r+1) ) ▸ ( show ζ f ⋆ K∈_ from continue_B he.1 hk.1 ) ) -- refine bind
lemma time_q (he:f∈ yields u (-1))(hp:F∈ Carry G x r)(hs:Woven.sym F): ζ ( Q f ) ⋆ F∈ PastSym G (u+x) (r+1):= by
   have hv : natQ ( ζ f ⋆ F )= ζ (Q f) ⋆ F:= by obtain hh:= pawn_1 he; change Gof.Q ( ζ f )= _ at hh; change Gof.Q _=_; rw [ Shift.product_rule,hh,show Gof.Q F=0 from carry_pure hp,map_zero,add_zero ]
   refine ⟨ _,⟨ (?_: ζ f ⋆ F∈_), (symθ (f:=f)).times hs ⟩, hv ⟩; exact ( by rw [ ← add_zero ( -1:ℤ ) ]; exact continue_B he (fare G x r hp) ) -- parentheses
end YM.MS.Theater
