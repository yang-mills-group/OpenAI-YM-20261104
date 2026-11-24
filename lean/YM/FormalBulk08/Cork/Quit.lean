import YM.FormalBulk08.Cork.Net

/-! Low jets from formal horizontal and ISOTROPY. Integral tests on every
root (not just transverse specializations in units of period). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Cork
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {n: Side} {k : ℕ} {A σ : ℝ}

def Grad (T : Slopes G) := ∀ i x,riverP i x T=0

def frow (f : Cover→ℝ)(b:Axis)(v:Cover):= f (v+step b)-f v
lemma cash_grad {T : Slopes G}(h:Grad T)(hp:Purse T)(f:Cover→ℝ)(H:Pad f)(a i j):∑ b:Axis,net T b a i j (frow f b)=0 := by
   let p : Fin 1 → edgeL G := ![(0,coord a,j)]
   have he (v:Cover) : ∑ b : Axis, (hem T b a i j v-hem T b a i j (v-step b))=0 := by
      have hh:=congr_fun (h i v) p; simp_rw [riverP,Finset.sum_apply,Pi.sub_apply,Pi.zero_apply] at hh;rw [←hh]; refine Fintype.sum_equiv axisEquiv _ _ fun b=>?_
      rw [backwards, axisEquiv.symm_apply_apply]; rfl
   have hs (b:Axis): Summable (fun v:Cover=>hem T b a i j (v-step b)*f v) := by
      let u:=Equiv.addRight (step b:Cover); refine Equiv.summable_iff u|>.mp ?_
      refine (hp.sum b a i j (H.shift (step b))).congr (fun v=> ?_); simp [u]
   have ht (b):net T b a i j (frow f b)= ∑' v,(hem T b a i j (v-step b)*f v-hem T b a i j v*f v):= by
      rw [net]; simp_rw [frow,mul_sub]; rw [(hp.sum b a i j (H.shift (step b))).tsum_sub (hp.sum b a i j H),(hs b).tsum_sub (hp.sum b a i j H)];congr 1; rw [←Equiv.tsum_eq (Equiv.addRight (step b:Cover)) (fun v:Cover=>hem T b a i j (v-step b)*f v)]; simp
   simp_rw [ht]; rw [←Summable.tsum_finsetSum]; swap;· intro b _;exact (hs b).sub (hp.sum b a i j H)
   rw [tsum_congr (g:=fun _=>0),tsum_zero]; intro v; have hh:= he v; rw [Finset.sum_sub_distrib] at hh; rw [Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.sum_mul,sub_eq_zero.mp hh,sub_self]

lemma direct_zero {T : Slopes G}(h:Grad T)(hp:Purse T)(a b i j) : net T b a i j 1=0 := by
    have he:=cash_grad h hp (ch b) (Pad.ch b) a i j;rw [Finset.sum_eq_single b,show frow (ch b) b=1 by funext; simp [frow,ch]] at he; exact he
    · intro k _ hk; have ht : frow (ch b) k=0:= by funext; simp [frow,ch,Ne.symm hk]
      rw [ht];simp [net]
    simp

-- rotation on slots p/p' before projection
lemma hem_sign {T : Slopes G} (h: Sworn T)(hp: Up T)(b a i j)(s: Signed)(v): hem T (s.perm b) (s.perm a) i j (s.act v+posStat s b-posStat s a) = hem T b a i j v* (banner s b*banner s a) := by
    have hh:=h s (![(v,coord b,i),(0,coord a,j)]); simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, show ∀ b,axisEquiv.symm (coord b)=b from axisEquiv.symm_apply_apply] at hh
    unfold hem; rw [←hh,←hp (posStat s a)]; congr 1; funext k; fin_cases k <;> simp [Lotus.tint,dart,show ∀ b,axisEquiv.symm (coord b)=b from axisEquiv.symm_apply_apply]

def statue (s:Signed)(b a:Axis): Cover≃ Cover:= (s.actEquiv (R:=ℤ)).toEquiv.trans (Equiv.addRight (posStat s b-posStat s a))
lemma statue_eq (s:Signed)(b a:Axis)(v): statue s b a v=s.act v+posStat s b-posStat s a:= by dsimp [statue,Signed.actEquiv]; abel
lemma sign_net {T : Slopes G}(h: Sworn T)(hp: Up T)(b a i j)(s: Signed)(f:Cover→ℝ): net T (s.perm b) (s.perm a) i j f=(banner s b*banner s a)*net T b a i j (f ∘ statue s b a):= by unfold net; rw [← Equiv.tsum_eq (statue s b a) (fun v=>hem T (s.perm b) (s.perm a) i j v*f v),← tsum_mul_left]; refine tsum_congr fun v=> ?_; rw [comp_apply,statue_eq,hem_sign h hp b a]; ring

def reverseS : Signed:= ⟨1,fun _=>true⟩
lemma switch_ch (b a k:Axis)(s: Signed): ch (s.perm k) ∘ statue s b a=banner s k • ch k + fun _ => ch (s.perm k) (posStat s b)-ch (s.perm k) (posStat s a) := by
    funext v;rw [comp_apply,statue_eq];simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,ch, Signed.act_at,smul_eq_mul,Int.cast_sub,Int.cast_add];unfold banner; split <;> simp <;> ring
lemma direct_line {T: Slopes G} (H : Grad T)(h : Sworn T)(hp: Up T)(hf:Purse T)(b a i j k): net T b a i j (ch k)=0:= by
    have he:=sign_net h hp b a i j reverseS (ch (reverseS.perm k)); rw [switch_ch b a k,add_net hf _ _ _ _ ((Pad.ch k).smul _) (flat_pad _),smul_net] at he
    have ht (w:ℝ) : net T b a i j (fun _=>w) = 0:= by rw [show (fun _ : Cover=>w)=w • 1 by ext;simp,smul_net,direct_zero H hf,mul_zero]
    rw [ht] at he; change net T b a i j (ch k)=(-1)*(-1)*((-1)* net T b a i j (ch k)+0) at he; linarith only [he]

def mir (T : Slopes G)(b a:Axis)(i j:hue G)(u v: Axis):= net T b a i j (ch u * ch v)
lemma turn_mir {T : Slopes G}(H : Grad T)(h : Sworn T)(hp: Up T)(hf:Purse T)(b a i j u v)(s: Signed) : mir T (s.perm b) (s.perm a) i j (s.perm u) (s.perm v) = (banner s b*banner s a*banner s u*banner s v)*mir T b a i j u v := by
    let y := statue s b a; let D := net T b a i j
    have hh (X Y P Q:ℝ) : D ((X • ch u+(fun _=>P))*(Y • ch v+(fun _=>Q)))= X*Y*D (ch u*ch v) := by
       let K:=ch u*ch v
       rw [show (X • ch u+(fun _=>P))*(Y • ch v+(fun _=>Q))= (X*Y) • K + ((P*Y) • ch v+(X*Q) • ch u)+(P*Q) • 1 by ext; simp [K]; ring]; unfold D
       have he:= (Pad.ch u).mul (Pad.ch v); rw [add_net hf _ _ _ _ ((he.smul _).add (((Pad.ch v).smul (P*Y)).add ((Pad.ch u).smul (X*Q)))) ((show Pad (1: Cover→ℝ) from flat_pad 1).smul _),add_net hf _ _ _ _ (he.smul _) (((Pad.ch v).smul (P*Y)).add ((Pad.ch u).smul (X*Q))), add_net hf _ _ _ _ ((Pad.ch v).smul _) ((Pad.ch u).smul _)]
       simp_rw [smul_net,direct_line H h hp hf, direct_zero H hf,mul_zero,add_zero]
    rw [mir,sign_net h hp]; change (banner s b*banner s a)* D _=_; rw [show (ch (s.perm u)*ch (s.perm v))∘(y:Cover→Cover)=(ch (s.perm u)∘ (y:Cover→Cover))*(ch (s.perm v) ∘ (y:Cover→Cover)) from rfl];unfold y; rw [switch_ch,switch_ch,hh]; change _=_* D (ch u*ch v); ring
end YM.FormalBulk08.Cork
