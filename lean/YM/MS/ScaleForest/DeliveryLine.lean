import YM.MS.ScaleForest.ClosingTwo
import YM.MS.ScaleForest.TestScale
/-!
# Solve the triangle outside the R-pole at four-dimensional specialization

Position reading and IR limit, for any choices of arms. Also solve the
similar **undressed** family (only two points, free order), so we can
inspect the negative-handed Rose contraction without the pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Triangle
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle Snap XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic
open scoped Topology ContDiff
variable {G : Gauge} {I:Type} (X Y:Pupil) (x:E4) (s:ℝ)
local notation "K"=> cursor false
abbrev subDot (z:Ω G)(s:ℝ) := dotV X Y x z s * moonV X Y x z s + sunV X Y x z s * dotM X Y x z s
abbrev billSum (G:Gauge) (F:Ω G→ℂ) := ∑ z:Ω G, premium X Y z* F z

def χPay (G:Gauge) (s:ℝ) := billSum X Y G fun z=> sunV X Y x z s * moonV X Y x z s
def ξPay (G:Gauge) := billSum X Y G fun z=> (sunLimit X Y z.1 z.2 x)^2

lemma loops (z:Ω G): let f(p:QP):= salute' X Y z.1 z.2 x p s* proofWalk X Y x s p (-p) z; Integrable f planeF ∧ (∫ p,f p∂planeF) = subDot X Y x z s := by
    intro f; let g(p:QP):= salute' X Y z.1 z.2 x p s; let h(p:QP):= salute₂ X Y z.1 z.2 x p s; let U:= sunV X Y x z s; let T:= moonV X Y x z s;
    have he(p:QP): f p=g p*T+h p*(2*U):= by unfold f g h T U proofWalk shiftedX salute₂; rw [high_parity (m:=0)]; ring
    obtain hv:= Integrable.mul_const (f:=g) (sunSupported ..) T; obtain h':= Integrable.mul_const (f:=h) (moonSupported ..) (2*U); rw [funext he]; refine ⟨ hv.add h',?_⟩;
    rw [integral_add hv h']; simp_rw [ integral_mul_const ]; change _=(∫ p,g p∂planeF)*T+U*(2*∫ p,h p∂planeF); ring

lemma looping (z:Ω G): ∀ p:QP, proofWalk X Y x s p (-p) z=proofWalk X Y x s (-p) (- -p) z:= by intro p; unfold proofWalk shiftedX; rw [neg_neg, add_comm (Highβ ..)]

variable [TopologicalSpace I] [FirstCountableTopology I]{A:I→QP}(μ:ℝ)(y:I) (h:AdmittedGap A) (he : Theater.out x=A y)
    (g:G.Simple)
include g he h
lemma settled_cost : D μ X Y A G 0 s y 0 []=χPay X Y x G s := by
    let V:= vertex (ghostR G); let P:= nearX X Y A V; let S:= nearY X Y A V; let T:= nearB X Y A V; let L:= cleanJet G s; let H:= hiredWalk X Y A V h
    let J(W:Planted G I true) (s:ℝ):= absNom μ (Planted.U K W) s y 0 []
    have prog (t:ℝ) : HasDerivAt (fun t=> D μ X Y A G 0 t y 0 []) (billSum X Y G (fun z=> subDot X Y x z t)) t:= by
        let Dσ(W:Planted G I true):=closeG (cleanJet G t) 0 μ (absNom μ W t y) 0 []
        have h'(W)(hW : W∈streets X Y A V): HasDerivAt (J W) (Dσ W) t:= by
            obtain hh:= Speed μ t y (m:=0) [] (V:=Planted.U K W) (H W hW); rw [pushedC μ t y _ (H W hW),prim_0 G t] at hh; exact hh
        have hP : P∈streets X Y A V:= by simp [P,streets]
        have hS : S∈streets X Y A V:= by simp [S,streets]
        have hT : T∈streets X Y A V:= by simp [T,streets]
        have hp(W)(ht:W∈ streets X Y A V):= (Planted.observing μ t y W (H W ht)).1
        let R(W:Planted G I true):= absNom μ W t y
        obtain hx:= (((h' P hP).add (h' S hS)).add (h' T hT)); convert! hx using 1;
        · funext t; unfold D nominal triangle streets; rw [List.map_cons,List.map_cons]; change _= J P t+J S t+J T t; simp only [ absNom,J,backing_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero, Pi.add_apply,add_assoc]; rfl
        unfold Dσ; let Q:LineRule G:=K; -- use general linear law on pulse.H
        have hK: Knot false (cleanJet G t):= prim_0 G t ▸ fze (Q.ok.forms false) 4 t;
        have hv(X Y:Mob G)(hx:Form0 false X)(hY: Form0 false Y) : closeG (cleanJet G t) 0 μ (X+Y)= closeG (cleanJet G t) 0 μ X+closeG (cleanJet G t) 0 μ Y:= by simp_rw [closeG_eq]; rw [ oceanR hK hx hY pit,smul_add ];
        have hh : closeG (cleanJet G t) 0 μ (R P+R S+R T)=closeG (cleanJet G t) 0 μ (R P)+closeG (cleanJet G t) 0 μ (R S)+closeG (cleanJet G t) 0 μ (R T):= by
          rw [hv _ _ ((hp P hP).add (hp S hS)) (hp T hT),hv _ _ (hp P hP) (hp S hS)]
        -- exposed derivative at this step.
        change _= (closeG (cleanJet G t) 0 μ (R P)+closeG (cleanJet G t) 0 μ (R S)+closeG (cleanJet G t) 0 μ (R T)) 0 []
        rw [← hh, cog_full X Y x t μ (((hp P hP).add (hp S hS)).add (hp T hT)) (φ:=fun p=> proofWalk X Y x t p (-p)) (fun p => funext fun i=>funext fun j=> rankTwo X Y x p (-p) i j t y μ he h g)
           (fun p=> funext fun z=> looping X Y x t z p) (fun z=> (loops X Y x t z).1) ]; simp_rw [show ∀ z:Ω G,(∫ p:QP,salute' X Y z.1 z.2 x p t * proofWalk X Y x t p (-p) z ∂planeF)=_ from fun z=> (loops X Y x t z).2]
    refine congr_fun (ode_solver (H:=χPay X Y x G) prog (fun t=>?_) ?_ ?_) s
    · exact HasDerivAt.fun_sum (fun z _=> ((sunSpeed X Y z.1 z.2 x t).mul (moonSpeed X Y z.1 z.2 x t)).const_mul _)
    · have he(W:Planted G I true): Tendsto (fun t:ℝ=> resolve μ W 0 t y 0 []) atBot (𝓝 0):= by obtain hp:= StartZero μ y (V:=W) (m:=0) []; simpa only [absNom,backing_nil] using hp
      unfold D nominal triangle streets; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Pi.add_apply]; simpa only [add_zero] using! ((he (Planted.U K P)).add ((he (Planted.U K S)).add (he (Planted.U K T))))
    obtain hT:= point_gap x y he h; unfold χPay billSum; simpa only [mul_zero,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun (z:Ω G) _=> ( (sunStart X Y z.1 z.2 x hT).mul (moonStart X Y z.1 z.2 x hT)).const_mul (premium X Y z))
lemma complete_cost : WindowIR (D μ X Y A G) 0 0 y= Coupling G*ξPay X Y x G := by
   unfold WindowIR; simp_rw [fun t=>settled_cost X Y x t μ y h he g]
   unfold χPay ξPay billSum; apply Tendsto.limUnder_eq; convert! tendsto_finsetSum Finset.univ (fun (z:Ω G) _=> Tendsto.const_mul (premium X Y z) ((sunSets X Y z.1 z.2 x).mul ( moonSets X Y z.1 z.2 x)) ) using 1; congr 1; rw [ Finset.mul_sum ]; exact Finset.sum_congr rfl (fun i _=> by ring)

-- undressed family
variable (A) in
def onlyTwo (G:Gauge):= Planted.U (cursor false) (mid X Y A G)
omit g in
lemma only_cost (G:Gauge): resolve μ (onlyTwo X Y A G) 0 s y 0 []=(2:ℂ)⁻¹ * billSum X Y G fun z=> sunV X Y x z s^2 := by
    let T:= mid X Y A G; rw [← backing_nil (F:=resolve μ (onlyTwo X Y A G)) ];
    let f(t:ℝ):= absNom μ (Planted.U K T) t y 0 []; let F(t:ℝ) := billSum X Y G fun z=> dotV X Y x z t * sunV X Y x z t; obtain hp: T.Stand:= mid_walk X Y h
    let W(s:ℝ):= (2:ℂ)⁻¹ * billSum X Y G (fun z=>sunV X Y x z s^2)
    have hu (t:ℝ): HasDerivAt f (F t) t:= by
       obtain hx := Speed μ t y (m:=0) [] (V:= Planted.U K T) hp; rw [pushedC μ t y _ hp,prim_0 G t] at hx
       convert! hx using 1; rw [ cog_full X Y x t μ (Planted.observing μ t y T hp).1 (fun p=> funext fun i=> funext fun j=> mid_progress X Y x p (-p) i j t y μ he h) (φ:=fun _ z=> sunV X Y x z t) (fun _=> rfl) (fun z=>(sunSupported X Y z.1 z.2 x t).mul_const _) ]; simp_rw [ integral_mul_const ]; rfl
    have hC(t:ℝ): HasDerivAt W (F t) t:= by
       let L:= Ω G
       unfold W F billSum; convert! HasDerivAt.const_mul (2:ℂ)⁻¹ (HasDerivAt.fun_sum (fun (z:Ω G) (h:z∈Finset.univ)=> HasDerivAt.const_mul (premium X Y z) ( (sunSpeed X Y z.1 z.2 x t).pow 2))) using 1; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _=>?_ ; unfold dotV sunV; norm_num; ring
    have hZ z := Tendsto.const_mul (premium X Y (z:Ω G)) ((sunStart X Y z.1 z.2 x (point_gap x y he h) ).pow 2)
    exact congr_fun (ode_solver hu hC (StartZero μ y _) (by unfold W billSum; simpa only [ne_eq, OfNat.ofNat_ne_zero,not_false_eq_true, zero_pow,mul_zero,Finset.sum_const_zero] using ((tendsto_finsetSum Finset.univ (fun (z:Ω G) _=> hZ z)).const_mul (2⁻¹:ℂ)) )) s
omit g in
lemma complete_only (G:Gauge): Tendsto (fun s=>resolve μ (onlyTwo X Y A G) 0 s y 0 []) atTop (𝓝 (2⁻¹*ξPay X Y x G)):= by simp_rw [ fun t=>only_cost X Y x t μ y h he G ]; unfold ξPay billSum; exact Tendsto.const_mul _ (tendsto_finsetSum _ fun z _=> ((sunSets ..).pow 2).const_mul _)
end YM.MS.ScaleForest.Triangle
