import YM.OPE.Compatible.Straws.Flame
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded Shift
variable {F:Fiber E G I}{X:Path E G D}(u:Keys G D){p:Keys G D→ℝ}(Z:F.SeriesUp X p) {P:ChartRatio G}(R:LocalRatio P)
namespace SeriesUp
local notation "δ0"=> δAre F X u
local notation "μ0"=> cloth F P
local notation "ωμ"=> Chart.tangent G I
local notation "JΘ"=> crossT ωμ F.Q
local notation "mΘ"=> (Z.C.hat P)
omit Z [BorelSpace E] in
lemma clothes (q: ScriptJ (E × Keys G I))(hq:q.B)(s:Y!): Caul X q (camp F X (u,s))=usher δ0 (X.timber u) (q ∘ drape E Y! F.M) s:=by
     obtain ⟨a,b,h⟩:= candle F X u; let p':= drape E Y! F.M
     let V(t:ℝ):=p' (X.timber u t,s-δ0 t); have hp:Gael V:=Gael.up (Gael.union (Timber X u) (show Gael (fun t:ℝ=> s-δ0 t) from Exists.intro _ ((Reads.constants s).minus h))) p'.toContinuousLinearMap
     apply Gael.chooses ((Fitted.take (p:=q∘V) ((Fitted.arose V q hp hq))).cong ?_); filter_upwards [Tested.eventually_pos] with t (ht:0<t); change (q (t⁻¹ • _)).atK t= (q (p' _)).atK t; rw [fieldP u s t ht]
include R
omit [BorelSpace E] in
lemma choir (q: ScriptJ (E×Keys G I))(hq:q.B)(y:Y!)(a b:Y!)(h: Reads δ0 ⟨0,a,b⟩):
     let T:=trill fun i=>Z.horsa u i P
     let s:= F.camp X (u,y)
     (Caul X q s)* mΘ s=T*(Warp F.Q a b y*usher δ0 (X.timber u) ((q ∘ drape E Y! F.M)* μ0) y) :=by
         intro T s
         rw [show s= _ from (show s=camp F X (u,y) from rfl),clothes u q hq y, campH u Z R a b h]; let v:=X.timber u; let g:E× Keys G I→Token:= q∘drape E Y! F.M; have hv:ScriptJ.B g:=fun i=>(hq i).compLinear (drape E Y! F.M).toLinearMap; have ht:ScriptJ.B μ0:= fun i=> (curlingB F.H (F.signB R) i).compLinear (drape E Y! F.M).toLinearMap; let j(i:ℝ):E×Keys G I:= (v i,y-δ0 i); have hu:Gael j:=Gael.union (Timber X u) ⟨_,(Reads.constants y).minus h⟩; change mine (g∘j)*(T*Warp F.Q a b y*mine (μ0 ∘ j))=T*( _ * mine ((g ∘ j)*(μ0 ∘ j))); rw [Fitted.slopes (p:=g∘j) (q:=μ0 ∘ j) (Fitted.arose j _ hu hv) (Fitted.arose j _ hu ht)];ring
-- normalization auxiliary part
omit [BorelSpace E] in
lemma jewelry (q:ScriptJ (E×Keys G I))(hq:q.B):
     let G':= (q ∘ drape E Y! F.M)* μ0
     JΘ ((Caul X q * mΘ) ∘ camp F X) u= trill (fun t=> Z.horsa u t P)*mine fun t=>JΘ G' (X.timber u t):=by
          intro G'; obtain ⟨a,b,h⟩:=candle F X u; let w:=usher δ0 (X.timber u) G'; let k:=trill fun t=> Z.horsa u t P; let M:= Warp F.Q a b; have hv: ScriptJ.B G':= ScriptJ.height (p:=q ∘ drape E Y! F.M) (s:=μ0) (fun i=>(hq i).compLinear (drape E Y! F.M).toLinearMap) (fun i=> (curlingB F.H (F.signB R) i).compLinear (drape E Y! F.M).toLinearMap); obtain ⟨hl,H⟩:=cider ωμ F.Q h (Timber X u) _ hv; change draw _ F.Q _= k * _; rw [show (fun i:Y!=> ((Caul X q *Z.C.hat P) ∘ camp F X) (u,i)) = (fun i:Y!=>k*(M*w) i) from funext (fun s=> choir u Z R q hq s a b h), drips ωμ F.Q (M*w) k (ScriptJ.height (warpB F.Q a b) hl)]; exact congr_arg (fun q=>k*q) (Gael.chooses H).symm
omit [BorelSpace E] in
lemma jewelVac :
     JΘ (mΘ ∘ camp F X) u= trill (fun t=> Z.horsa u t P)*mine fun t=>JΘ μ0 (X.timber u t) :=by
          have hx:= jewelry u Z R 1 (Bfray (E:=E×Y!) _)
          rw [show Caul X (1: ScriptJ (E×Y!))= (1:ScriptJ K!) from funext fun i=> Gael.chooses (Reads.selves _),one_mul] at hx; convert! hx using 2; rw [show (1:ScriptJ (E×Y!)) ∘ drape E Y! F.M=1 from rfl,one_mul]
omit Z R [BorelSpace E] in
lemma JewelA (Y:E×Y!→Token)(h:ScriptJ.B Y)(hp:∀ x,(Y x).s=1):
      let W(x:E):Token:= JΘ Y x
      (mine (W ∘ X.timber u)).s=1:=by
           intro W'; have ha : ScriptJ.B W':=crossB _ _ _ h; have hx:=Fitted.arose _ _ (Timber X u) ha; let k:= X.timber u; have ht (x:E) : (W' x).s=1:= Shift.headD _ _ _ fun y=>hp (x,y)
           rw [Fitted.totals (p:=W' ∘ X.timber u) (by exact (Reads.constants (1:ℝ)).cong (Filter.Eventually.of_forall fun t=> ht (k t))) (Gael.oath hx.B) (Gael.oath hx.C)]; simp [assembleJ,ski]
omit [BorelSpace E] in
lemma costs0 :(trill (fun t=> Z.horsa u t P)).s=1:=by
     have hb:ScriptJ.B μ0:= fun i=>(curlingB F.H (F.signB R) i).compLinear (drape E Y! F.M).toLinearMap
     have ht := JewelA (F:=F) (X:=X) u μ0 hb (fun x=> Adhesion.curT (h:= F.signPay R) _); let q(x:E):= JΘ μ0 x; change (mine (q ∘ X.timber u)).s=1 at ht; have ha: (JΘ (mΘ ∘ camp F X) u).s=1:= Shift.headD _ _ _ fun y=> Z.C.hat_full R _
     rw [jewelVac u Z R,ml_s, show (mine (fun t=> JΘ μ0 (X.timber u t))).s=1 from ht,mul_one] at ha; exact ha
end SeriesUp
end Fiber
end YM.OPE.Libra
