import YM.MS.Vibe.Nest
/-!
# Ward constant and rank proof. A theorem on full Laurent Time spectrum

Even evanescent/anomaly: seed Obl.Absolute defined for D.OE continuation. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F: T (Flats G)}{J N L:Flats G}{f g p q:T (Coat G)}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ}
lemma guardX (hx:leader G X f g)(ht:∀ i<n, CleanP true ( PB X i)): Guard ( PB X n ) 5 true:= by
   let A:= PB X; let P (n):=Host.host (gang (hx n)); have hz:= Host.Pose_p (h:=4) P P n ((2:ℂ)⁻¹); intro r hr; change Blink true (Pose n _ X X) (r+2) at hr; filter_upwards [ start hx n, hr,(eventually_all_finset (Finset.range n) (p:=fun j x=>∀ k,Equal true (PB X j k x) 0)).mpr (fun j hj=> ht j (Finset.mem_range.mp hj)), high0, Moony.march hz.bill 5] with i hi hB hR hF hV m l hM hl s y;
   obtain H:=hi s y m l (hl rfl)
   have h0 : File i s y 4 X 0=0:= by unfold File; rw [(hx 0).2 rfl,pageZ]; rfl
   have ht := noLives (s:=s) (y:=y) (n:=n) (v:=File i s y 5 (PB X)) hF h0 (fun j hj=> Emit.orbit (hR j (Finset.mem_range.mpr hj)) _) (hV y s) (level hB _); rw [ht.passes m l hM hl] at H; exact H
lemma RootF {P:Prop}(he:sings b t h (f n) P J L ( p n)): Joint h (J+step0 G L) L (f n) (p n) := by obtain ⟨⟨r,H, H'⟩,hX⟩:=he; exact H
-- mark second
lemma guardM (hx:leader G X f g)(hp: comet h r X p Y q)(hP:∀ i,CleanP true (PB X i))(he:∀ i<n,CleanP false ( PM X Y i)): Guard (PM X Y n) (h+1) false := by
    let H(n):= Host.host (gang (hx n)); let W(n):= Host.host (gang (hp n)); have hs := Host.Pose_p H W n 1; intro t ht; filter_upwards [pinion hx hp n,ht,high0, (eventually_all_finset ( Finset.Iic n) (p:=fun j x=> ∀ k, Equal true ((PB X j) k x) 0)).mpr ( fun i hi=> hP i),( eventually_all_finset ( Finset.range n) (p:=fun j x=>∀ k, Equal false ((PM X Y j) k x) 0)).mpr ( fun j hj=> he j ( Finset.mem_range.mp hj)), Moony.march hs.bill (h+1)] with i hi hx' hW hF hG hb m l hM hl s y; have hK : File i s y 4 X 0=0:= by unfold File; rw [(hx 0).2 rfl,pageZ]; rfl
    have he := hi s y m l; rw [Pi.add_apply,show pairW ( Grid i y s G).X ((File i s y 5 (PB X))) ( File i s y h Y) n=0 from noExtra ( D:=A0 G s) (fun i hi=>Emit.orbit (hF i ( Finset.mem_Iic.mpr hi)) _)] at he -- expand Pi.add
    have hv := noLives (s:=s) (y:=y) (n:=n) (v:=File i s y (h+1) (PM X Y)) hW hK (fun j hj=> Emit.orbit (hG j ( Finset.mem_range.mpr hj)) _) (hb y s) (level hx' _); rw [add_zero,hv.passes m l hM hl] at he; simpa using he -- hβ extension parens
variable {U V:T (Mob G)}
abbrev Council (U: T (Mob G)): Prop:= ∀ n,Equal true (BasisC U U ((2:ℂ)⁻¹) n) 0
abbrev Trill (F H:T (Mob G)): Prop:= ∀ n, Equal false (BasisC F H 1 n) 0
-- bundle Ward pair Proofs
lemma wardLeader (hx: leader G X (gloss U) p)(hp:Council U)(n:ℕ): CleanP true (PB X n) ∧ Clean (RootM (gloss U+p) (gloss U+p) ((2:ℂ)⁻¹) n) true:= by
    let H(i):=Host.host (gang (hx i)); have hK (i): Return (X i) ( (gloss U+p) i ) 4:= (RootF (hx i)).sip; have hf(i): Cool (p i):= (RootF (hx i)).ice
    induction n using Nat.strong_induction_on with | h i ih=> exact full ( Host.Pose_p H H i _) (turn hK hK _) ( burn0 hf hf (hp i)) ( guardX hx ( fun j hj=> (ih j hj).1)) -- burn0 parameters
lemma wardMark (hx:leader G X ( gloss U) p)(hp: comet h t X ( gloss V) Y q)(hv: Council U)(hm:Trill U V)(n:ℕ): CleanP false ( PM X Y n)∧ Clean (RootM (gloss U+p) (gloss V+q) 1 n) false:= by
    induction n using Nat.strong_induction_on with
    | h n ih=> exact full (Host.Pose_p (fun i=> Host.host (gang (hx i))) (fun i=> Host.host (gang (hp i))) n _) (turn (fun i=> ( RootF (hx i)).sip ) (fun i=> (RootF (hp i)).sip) _) ( burn0 (fun i=> (RootF (hx i)).ice) (fun i=> (RootF (hp i)).ice) (hm n)) ( guardM hx hp (fun i=>(wardLeader hx hv i).1) (fun j hj=>(ih j hj).1)) -- defeq RootM.Bound.B.Error
end YM.MS.Emit
