import YM.OPE.Compatible.Melon.Bends
/-!
# Expose stand and product bilinear gauge 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} {A:Alps B Q i l} {H: Even n.val}
local notation "Lf" => Tested.germ
local notation "TK" => Keys G (Limb H)
variable (T:Plot H) (X:Lit H A b) (R:Bor H A b)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
local notation "W" => Chart.tangent G T.Stable
local notation "Tμ" => Chart.tangent G T.Free
local notation "Pμ" => Chart.tangent G (Limb H)
variable {P:ChartRatio G} {I:Type}[Fintype I]
open ScriptJ
lemma obligation (L:Lid G I):∃ A: Law (Keys G I), ∀ x, jet L.f 2 x=A.P x x/2:=by
     let C:= Keys G I; let T:= iteratedFDeriv ℝ 2 L.f 0; let D(x y:C):ℝ:= (T ![x,y]+ T ![y,x])/2; have hh(x:C):∃ A:Dual' C,D x=A:=by
         refine ⟨{toFun:=D x,map_add':=?_,map_smul':=?_},rfl⟩
         · intro a b; unfold D; rw [show T ![x,a+b]= _ from DFunLike.congr_fun (((T.curryLeft x).curryLeft).map_add a b) (![]), show T ![a+b,x]=_ from DFunLike.congr_fun (T.curryLeft.map_add a b) (![x])]; change ((T ![x,a]+T ![x,b])+(T ![a,x]+T ![b,x]))/2=_;ring
         · intro c a; unfold D; rw [show T ![x,c • a]= _ from DFunLike.congr_fun (((T.curryLeft x).curryLeft).map_smul c a) (![]), show T ![c • a,x]=_ from DFunLike.congr_fun (T.curryLeft.map_smul c a) (![x])]; change (c*T ![x,a]+c*T ![a,x])/2=c*_; ring
     obtain ⟨Z,hZ⟩:= giraffe_addendum hh (fun x y=> by unfold D;ring)
     have hu(x): jet L.f 2 x=Z x x/2:=by rw [hZ]; unfold jet D; rw [show (fun _:Fin 2=>x)=![x,x] from funext fun i=>by fin_cases i<;>rfl]; unfold T; norm_num;ring
     refine ⟨Libra.giraffe Z (fun x y=>by rw [hZ,hZ]; unfold D;ring) (fun x hx=>?_),hu⟩
     have ht : 0<jet L.f 2 x:=by obtain ⟨a,ha,h⟩:= L.bright; exact (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hx))).trans_le (h _)
     rw [hu] at ht; linarith only [ht]
def penon (L:Lid G I):= Classical.choose (obligation L)
lemma penon_shape (L:Lid G I)(x: Keys G I) : jet L.f 2 x=(penon L).P x x/2:= Classical.choose_spec (obligation L) x
lemma jointW (p: FD×DK)(h:4≤ i) : (penon (ballow T X h)).P (compass H T G p) (compass H T G p) = (united (penon (R.L T)) (fond H T G)).P p p:=by
      rcases p with ⟨x,y⟩; let u:= compass H T G (x,y); have hp: jet (ballow T X h).f 2 u= jet (R.L T).f 2 x+(fond H T G).P y y/2:=by rw [glowN T X R,show T.slab G u=x from firstC .., flare T]
      rw [penon_shape (ballow T X h), penon_shape (R.L T)] at hp; rw [united_shape]; change _ = _ + (fond H T G).P y y; unfold u at hp; dsimp only at *; linarith only [hp]
lemma tarn (p:ScriptJ TK)(hp:(Pond H).Marbles p) (x:TK): Reads (fun t=> p (t⁻¹ • (T.skews G).gradient (t•x)) |>.atK t) (p (T.rollX (T.slab G x))):=by
      have he:=hp.honors (T.pathZ x); unfold Reads; refine he.neg_left.congr' ?_ Filter.EventuallyEq.rfl
      filter_upwards [Tested.eventually_pos] with t ht; simp only [Pi.sub_apply,map_smul,inv_smul_smul₀ (ne_of_gt ht),neg_sub]
lemma bornPaid (v:ChartRatio G)(V:LocalRatio v)(p:ScriptJ TK)(hp:(Pond H).Marbles p)(h:4≤ i): X.s.pay v p=(ballow T X h).pay v ((T.charted p) ∘ (T.slab G)):=by
       symm; let K:= T.skews G; have he: Dimes.Globe K (ballow T X h) X.s:=⟨mast H T X h,K.chore X.s,rfl,rfl⟩; exact Dimes.congr_charge _ he hp.toll (tarn T p hp) V
end YM.OPE.Cascade.Glass
