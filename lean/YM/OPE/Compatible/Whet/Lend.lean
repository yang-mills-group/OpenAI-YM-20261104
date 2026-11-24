import YM.OPE.Compatible.Whet.Rampage
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {W:Type}{X:W→Type}[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℝ (X i)]
variable (n:W→Side)(H:∀ i,Even (n i).val)(Y:∀ i,Plot (H i))
local notation "C'" i=> Libra.Keys G (Stand.Free (Y i))
-- budget ≥4
variable {v v' b b':W→ℝ}(A:(j:W)→Alps K T i (v j))(Z:(l:W)→Alps K T j (v' l))
variable (L:∀ i,Bor (H i) (A i) (b i))(V:∀ i,Bor (H i) (Z i) (b' i))
variable {q s:W→ℝ}
local notation "AΞ"=>vL n H Y A L
local notation "DΞ"=>vL n H Y Z V
local notation "Wµ" i=>Chart.tangent G (Stand.Free (Y i))
lemma subV_d {u w:ℕ}(ht:4≤ i)(hk:4≤ j)(hs:G.Simple)(hz:WindZ n r u q (fun i=> Impact (AΞ i) (DΞ i)))(hp:0 ≤ q)(hv:0 ≤ s)(f g:(i:W)→ScriptJ (C' i))(hh:WindT n e w s f)(hy:WindT n e w (q*s) (f-g))(h':WindT n e w s g):
    Permit n (8+(r+e)+4*(u+w+(u+w))) (q*s) (fun i=> draw (f i) (AΞ i) (Wµ i) - draw (g i) (DΞ i) (Wµ i)):=by
       let F(i):= draw (f i) (AΞ i) (Wµ i)-draw (f i) (DΞ i) (Wµ i); let R(i):=draw (f i-g i) (DΞ i) (Wµ i); let D:=8+(r+e)+4*(u+w+(u+w)); rw [show (fun i=>draw _ _ _-draw _ _ _)=F+R from ?_]; swap
       · funext i; have he:draw (f i-g i) (DΞ i) (Wµ i)=draw (f i) (DΞ i) (Wµ i)-draw (g i) (DΞ i) (Wµ i):=by apply JetS.eta<;>first|exact Stranded.curb _ _ _ _ ((hh 0).zon i) ((h' 0).zon i)|exact Stranded.curb _ _ _ _ ((hh 1).zon i) ((h' 1).zon i)|exact Stranded.curb _ _ _ _ ((hh 2).zon i) ((h' 2).zon i)
         simp only[Pi.add_apply,F,R,he]; abel
       refine Permit.add n (fun i=>?_) (Permit.gauge n (weightsP Z n H Y V (f-g) hy (fun i=>mul_nonneg (hp i) (hv i)) hk hs) (fun i=>mul_nonneg (hp i) (hv i)) le_rfl (show 4+e+4*w ≤ D by unfold D;omega)); fin_cases i<;>first|exact RushV _ _ _ A Z L V ht hk hs hz hp hv _ (hh 0)|exact RushV _ _ _ A Z L V ht hk hs hz hp hv _ (hh 1)|exact RushV _ _ _ A Z L V ht hk hs hz hp hv _ (hh 2)
lemma Permit.neg {p:W→Token} (h:Permit n m q p):Permit n m q (-p):=by intro i; fin_cases i<;>first|exact gold_minus n (h 0)|exact gold_minus n (h 1)|exact gold_minus n (h 2)
lemma pseat {u v:W→Token}(h:Permit n k q (u-v))(hx:Permit n l 1 u)(hy:Permit n l 1 v)(hv:0 ≤ q)(he:∀ i,(u i).s=1)(hw:∀ i,(v i).s=1): Permit n (l+l+k+(l+l)) q (u⁻¹-v⁻¹):=by
     have H: u⁻¹*u=1:=funext fun i=> JetS.uniting (show (u i).s≠0 from (he i).trans_ne one_ne_zero); have ht:v*v⁻¹=1:=by rw [mul_comm]; exact funext fun i=> JetS.uniting (show (v i).s≠0 from (hw i).trans_ne one_ne_zero)
     have he' :u⁻¹-v⁻¹= -(u⁻¹*(u-v)*v⁻¹):=by rw [mul_sub,sub_mul,H,one_mul,mul_assoc,ht,mul_one]; abel
     rw [he']; apply Permit.neg; simpa only [one_mul,mul_one] using Permit.mul n ((Permit.inv n hx he).mul n h zero_le_one) (Permit.inv n hy hw) (show 1*q ≥0 from by simpa using hv)
abbrev payV (r k l:ℕ):=8+(r+8)+4*(k+6+(k+6))+2*(4+8+4*6) +2*(4+8+4*6)+4*(l+l)+128
lemma channelD {f g:(i:W)→ScriptJ (C' i)}(u:(i:W)→ScriptJ (C' i))(hF: WindT n 8 6 1 f)(hG: WindT n 8 6 1 g)(hp:∀ i j,(f i j).s=1)(hq:∀ i j,(g i j).s=1)(hS: WindZ n r k s (fun i=>Impact (AΞ i) (DΞ i)))(hz:0 ≤ s)(he:WindT n 8 6 s (f-g))(h:WindT n 0 l q u)(hv:0 ≤ q)(ht:4 ≤ i)(ht':4 ≤ j)(hs:G.Simple):
   Permit n (payV r k l) (s*q) (fun i=>fair (Wµ i) (AΞ i) (f i) (u i)-fair (Wµ i) (DΞ i) (g i) (u i)):=by
       let C:= s*q; have hC:0 ≤ C:=fun i=> mul_nonneg (hz i) (hv i); let F(i):= draw ((f*u) i) (AΞ i) (Wµ i); let E(i):=draw (f i) (AΞ i) (Wµ i); let X(i):=draw ((g*u) i) (DΞ i) (Wµ i); let Y'(i):=draw (g i) (DΞ i) (Wµ i); let d:= payV r k l
       have hf:WindT n 8 (6+l) q (f*u):=by simpa only [one_mul] using hF.prod h zero_le_one
       have hg:WindT n 8 (6+l) q (g*u):=by simpa only [one_mul] using hG.prod h zero_le_one
       have hz' :Permit n (8+(r+8)+4*(k+(6+l)+(k+(6+l)))) C (F-X):= by
            apply (show _ from subV_d n H Y A Z L V ht ht' hs hS hz hv _ _ hf _ hg); rw [←sub_mul]; exact he.prod h hz
       have hY: Permit n (4+8+4*(6+l)) q X:= weightsP Z n H Y V (g*u) hg hv ht' hs
       let a:= 4+8+4*6; have hE : Permit n a 1 E:= weightsP A n H Y L f hF zero_le_one ht hs; have hX: Permit n a 1 Y':=weightsP Z n H Y V g hG zero_le_one ht' hs
       have hE' :Permit n (8+(r+8)+4*(k+6+(k+6))) s (E-Y'):=by convert! subV_d n H Y A Z L V ht ht' hs hS hz zero_le_one f g hF (show WindT n 8 6 (s*1) (f-g) from by simpa only [mul_one] using! he) hG using 1; rw [mul_one]
       have hy(i): (E i).s=1:= Shift.headD _ _ _ (hp i); have hV:= pseat n hE' hE hX hz hy fun i=>Shift.headD _ _ _ (hq i); rw [show (fun i=>_)= (F-X)*E⁻¹+(E⁻¹-Y'⁻¹)*X from ?_]; swap
       · funext i; unfold fair; simp only[Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.inv_apply,JetS.dv,F,E,Y',X]; rw [mul_comm (u i),mul_comm (u i)]; -- simplify Pi product expanded in F defs?
         ring
       refine Permit.add n ?_ ?_
       · have hh:Permit n (8+(r+8)+4*(k+(6+l)+(k+(6+l)))+(a+a)) C ((F-X)*E⁻¹):=by simpa only [mul_one] using Permit.mul n hz' (Permit.inv n hE hy) hC
         exact Permit.gauge n hh hC le_rfl (show _≤d by unfold a d payV; omega)
       convert! Permit.gauge n (Permit.mul n hV hY hz) hC le_rfl ?_; show _ ≤ payV r k l; unfold a payV;omega
end YM.OPE.Quit.PriceZ
