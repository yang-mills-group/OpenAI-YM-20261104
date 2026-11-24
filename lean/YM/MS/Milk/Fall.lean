import YM.MS.Milk.Cave
import YM.Next.RANK.GaussLeg
import YM.MS.Awning.Press
/-!
# Free Wilsonian solution ($MS physics$) in coordinate kernel.Design any actual alphabet
 and full cost constraints. Use signed Wick polynomial operations (Next.RANK.NORMAL).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell
open Tensor (diagonal)
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A X:Type}{G:Gauge}{n d r:ℕ}{s:ℝ}{f:ℝ→ℂ}
local infix:70 " ⋆ "=> product (field Landau.parity)
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
variable {W E I:Type}{L:Album X G}{U V:ℝ→Law G}{g:X→Normal.poly X}
variable {u v:ℝ→ Normal.Symmetric X}{Q:Normal.Symmetric X}
-- root χ
open Labels Awning Logarithm
open Rake.Geo
open Alps Wire Outlook Polynomial
variable {p q:Poly}{g Q':ℤ}
lemma tarn (u:ℤ)(hu:u < 0) (p:Poly) : Tendsto (fun i:ℝ=>p.eval i * pale u i) atTop (𝓝 0):= by
    have hx : Tendsto (pale (u+1)) atTop (𝓝 (if u+1=0 then 1 else 0)):= by split_ifs with he; simp only [he]; unfold pale; simp_rw [ zpow_zero ]; exact tendsto_const_nhds; exact ( tendsto_zpow_atTop_zero (show u+1<0 from (by omega)) ).comp tendsto_exp_atTop
    induction p using Polynomial.induction_on' with
    | monomial n a=>
        let k(t:ℝ):= t^n; have he : Tendsto (fun i:ℝ=> k i / exp i ) atTop (𝓝 0):= by simpa using tendsto_div_pow_mul_exp_add_atTop 1 0 n (by norm_num);
        have ht := ((he.const_mul a).mul hx); simp only [mul_zero,zero_mul] at ht; simp_rw [ Polynomial.eval_monomial ]; refine ht.congr (fun t=>?_); unfold k pale; rw [ zpow_add₀ ( exp_pos t|>.ne' ), zpow_one ]; field_simp
    | add p q hp hq=> simp_rw [ Polynomial.eval_add, add_mul ]; convert hp.add hq using 1; simp
lemma tarnα (h:f∈ Bowl Q')(η:ℝ)(p:Poly)(hp:Q'+g<0): Tendsto (fun i:ℝ=> (p.eval (η+i)* pale g i) • f (exp i)) atTop (𝓝 0):= by
    refine Submodule.span_induction (p:=fun f _=> Tendsto (fun i=> (p.eval (η+i)* pale g i) • f (exp i)) atTop (𝓝 0)) ?_ ?_ ?_ ?_ h; -- f binder ℝ→ℂ?
    · rintro f ⟨i,hi,rfl⟩; let u:Poly:=p.comp ( Polynomial.C η + Polynomial.X ); have hu(t:ℝ): u.eval t=p.eval (η+t):= by simp [u]
      have hv:= tarn (g+i) (by have he:=( is_ig Q' i).mp hi; omega) u; simp_rw [ poseX,Complex.real_smul ]; have ht: Tendsto (fun x=> ( ((u.eval x * pale (g+i) x):ℝ) :ℂ ) ) atTop (𝓝 0):= by convert Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hv using 1; rfl; norm_num
      refine ht.congr fun x=>?_ ; unfold pale; rw [hu,zpow_add₀ (exp_pos _|>.ne' ),zpow_natCast ]; push_cast; ring
    · simp_rw [Pi.zero_apply,smul_zero]; exact tendsto_const_nhds
    · intro f g _ _ hf hg; simp_rw [Pi.add_apply,smul_add ]; simpa only [zero_add] using hf.add hg
    intro c u hv hu; simp_rw [Pi.smul_apply,smul_comm (p.eval _ * _ ) c ]; simpa only [smul_zero] using Tendsto.const_smul hu c
-- spent.Wig¬. Arch Mark determined via `Rent`. stash.Shadow.Ray exponent.
open Pearl Train _root_.YM.MS.Shine Land Local.Physical Mach Menus Arts Hem Mell
variable {B:Deck G}{M:Booked B} (A:MS_Data G M) (t:Plaid B n) (y:ℝ)
local notation "Z0"=> (A.marks n t 0)
lemma heart (w:Legs (Lane4 G))(hw:w.length < ( Land.read t ).grade): Tendsto (fun i:ℝ=> four n Z0 (y,i) w ) atTop (𝓝 0):= by
    let z:= Z0; let d:= n; let V(u:ℝ)(v:ℝ):= fieldVal ( four d z (u,0) ) (ray w) v; let r:=(Land.read t).grade; obtain ⟨p,hp⟩:= tallP ( Moony.toast (Emit.Host.host ( Dock.gang ( A.markOK n t 0 ) )|>.bill) ); have he: Stay n z:= ( Dock.gang ( A.markOK n t 0 ) ).dost; have hv (u:ℝ): hereZ n z 0 u= Press z p p u:= by rw [Outlook.vertical hp he,add_zero, Alps.posing ];
    let g:ℤ:= mass (m:=0) w - n; let x:=ray w; have hx(t':ℝ): V t' ∈ Bowl (-(g+1)):= by
       have hl: mass (m:=0) x= mass (m:=0) w:= ray_dim _; have hz := Value0 A t 0 t' (0:ℕ) ℝ x 0 1; change (fun v:ℝ=> V t' (0+v • 1))∈ Bowl ( PriceR (m:=0) ((n:ℤ)-r) x ) at hz; simp only [smul_eq_mul,mul_one,zero_add] at hz; have ht:x.length=w.length:= ray_len _; change w.length<r at hw; exact bowl_more (by unfold PriceR g; omega) hz
    obtain ⟨k,hK⟩:= press_ready p ( n:=p ) ( F:=z ); have hu (s:ℝ): four n Z0 (y,s) w = ∑ i∈ Finset.range k, (( Logarithm.plate k i ).eval ( y+s )* pale g s) • V i (exp s):= by
       let T:= hereZ n z s y; change T 0 w=_; unfold T; rw [Outlook.vertical hp he, interpret hK ( y+s ), Logarithm.evaluate]; let P:=plower ( G:=G ) (-(n:ℂ)) s; have hm {f:ℝ}{X:Mob G}: P (f • X)=f • P X:= ( P.restrictScalars ℝ ).map_smul ..; simp_rw [← Alps.cert,map_sum]; change (∑ j∈ Finset.range k,P _ ) 0 w=_;
       simp_rw [hm,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i hi; rw [mul_smul]; -- phase.valley.Val
       have hh : (ray w).length=w.length:= ray_len w
       unfold V;
       let U:=Press z p p (i:ℝ); change ( (Logarithm.plate k i).eval (y+s) ) • P U 0 w= _ • pale g s • fieldVal ( hereZ n z 0 (i:ℝ) 0 ) x ( exp s ); apply congr_arg ( ( (Logarithm.plate k i).eval (y+s) ) • · )
       obtain hU:= s_p_vector U ( m:=0 ) x (1:ℝ) s (-(n:ℂ)); change P U 0 ( sail x 1 )=_ at hU; rw [show sail x 1=w from ray_sail _, smul_eq_mul,mul_one] at hU; rw [hU, hv, Complex.real_smul]; refine congr_arg ( · * (fieldVal (U 0) x ( exp s )) ) ?_; have he : mass (m:=0) x= mass (m:=0) w:= ray_dim w; unfold Drops.pale; rw [Rake.a_e s g,show -(n:ℂ)+( mass (m:=0) x:ℂ )=( ( g:ℝ ):ℂ ) from (by unfold g; rw [ he ]; push_cast; ring), amount_mint, mul_comm (g:ℝ)]
    simp_rw [hu]; convert tendsto_finsetSum (Finset.range k) (fun i _=> tarnα (hx i) y (Logarithm.plate k i) ( g:=g ) (by omega)) using 1; simp -- η.Real
end YM.MS.Milk
