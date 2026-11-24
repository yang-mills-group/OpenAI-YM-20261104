import YM.FormalBulk08.Bank.Tee

/-! One marked variation at a site. Two distinct local stencils per positive
link; compare as analytic germs only. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.City
open Reef Lattice Exterior Wilson Filter Function Orb Wick Series Jets Work.F05 PowerSeries
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (i : G.ColorIndex)

abbrev hue (G : Gauge):=G.ColorIndex
abbrev dah (V : Type):= V⊕Unit
def boxL (V : Type) [Fintype V] : Rays V→L[ℝ] Rays (dah V) := LinearMap.toContinuousLinearMap {
   toFun:= fun x => Sum.elim x 0
   map_add':= fun x y => funext fun t=>by cases t <;> simp
   map_smul':= fun k x=> funext fun t=>by cases t <;> simp }
def cheekL (V : Type) [Fintype V] : Rays (dah V) →L[ℝ] Rays V:=LinearMap.toContinuousLinearMap {
   toFun:=fun x=> x ∘ Sum.inl
   map_add':=fun _ _=>rfl
   map_smul':=fun _ _=>rfl }

def moon (G : Gauge) : Rays (hue G)≃L[ℝ] G.Color:=LinearEquiv.toContinuousLinearEquiv {
   toFun:=fun a=>WithLp.toLp 2 a
   invFun:=fun a i=>a i
   map_add':=fun _ _=>rfl
   map_smul':=fun _ _=>rfl
   left_inv:=fun _=>rfl
   right_inv:=fun _=>rfl }

def lantern (t:ℝ) : G.El := G.lieExp (t • moon G (dotI i))
def yellow (l:Bool) (x:Rays (dah (hue G))) : G.El:= let A:= G.lieExp (moon G (cheekL (hue G) x)); let L:=lantern i (x (.inr ())); if l then L*A else A*L⁻¹
def curtain (l : Bool) : Rays (dah (hue G))→Rays (hue G):=fun x=> (moon G).symm (G.plog (G.mat (yellow i l x)))
@[simp] lemma lantern_home : lantern i 0=1:=by simp [lantern]
@[simp] lemma curtain_home (l : Bool) : curtain i l 0=0:= by simp [curtain,yellow]
lemma yellow_diff (l : Bool) : ContDiff ℝ ω (fun x=>G.mat (yellow i l x)) := by
   have h : ContDiff ℝ ω (fun z:Rays (dah (hue G))=>G.mat (lantern i (z (.inr ())))) := G.exp_jet.comp  (f:=fun z:Rays (dah (hue G))=> z (.inr ()) • moon G (dotI i)) (by fun_prop)
   have ht := (starL ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.comp h
   have ha := G.exp_jet.comp ((moon G).contDiff.comp (cheekL _).contDiff)
   cases l
   · change ContDiff ℝ ω (fun z:Rays (dah (hue G))=>G.mat (G.lieExp (moon G (cheekL (hue G) z))*(lantern i (z (.inr ())))⁻¹))
     simp_rw [G.mat_mul,G.mat_inv]; exact ha.mul ht
   change ContDiff ℝ ω (fun z:Rays (dah (hue G))=>G.mat (lantern i (z (.inr ()))* G.lieExp (moon G (cheekL (hue G) z))))
   simp_rw [G.mat_mul]; exact h.mul ha
lemma curtain_diff (l : Bool) : ContDiffAt ℝ ω (curtain i l) 0 := by
   unfold curtain; refine (moon G).symm.contDiff.contDiffAt.comp _ (ContDiffAt.comp (g:=G.plog) (f:=fun z=>G.mat (yellow i l z)) _ ?_ (yellow_diff i l).contDiffAt); simp only [yellow,map_zero, Gauge.mat_lieExp_zero, Pi.zero_apply, lantern_home, inv_one, one_mul,ite_self,G.mat_one]; exact G.plog_diff
lemma go_yellow (l : Bool) : ∀ᶠ x in 𝓝 0,G.lieExp (moon G (curtain i l x))= yellow i l x := by
    simp_rw [curtain,(moon G).apply_symm_apply]
    have he : Continuous (yellow i l) := ?col
    have hp : Tendsto (yellow i l) (𝓝 0) (𝓝 1) := by
       have hp := he.continuousAt (x:=0); rw [ContinuousAt,show yellow i l 0=1 by simp [yellow]] at hp; exact hp
    exact hp.eventually G.plog_right
    case col=>cases l <;> unfold yellow lantern <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
lemma lit_curtain (l : Bool): curtain i l ∘ boxL (hue G)=ᶠ[𝓝 0] id := by
   filter_upwards [(show Tendsto (moon G) (𝓝 0) (𝓝 0) by simpa using! (moon G).continuous.continuousAt (x:=0)|>.tendsto).eventually G.plog_left] with x hx
   rw [Function.comp_apply, curtain,yellow]
   rw [show cheekL (hue G) _=x from rfl,show boxL (hue G) x (.inr ())=0 from rfl,lantern_home,one_mul,inv_one,mul_one,ite_self,hx]; exact (moon G).symm_apply_apply _

def will (l:Bool) (b:G.ColorIndex) (z:Rays (hue G)) := fderiv ℝ (fun x=>curtain i l x b) (boxL (hue G) z) (dotI (.inr ()))
lemma will_diff (l:Bool) (b) : ContDiffAt ℝ ∞ (will i l b) 0 := by
   refine ContDiffAt.comp (g:=fun x=> fderiv ℝ (fun x=>curtain i l x b) x (dotI (.inr ()))) (f:=boxL (hue G)) 0 ?_ (boxL (hue G)).contDiff.contDiffAt
   rw [(boxL (hue G)).map_zero]; exact ContDiffAt.clm_apply (f:=fderiv ℝ (fun x=>curtain i l x b)) (g:=fun _ => dotI (.inr ())) ((coord_diff _ ((curtain_diff i l).of_le le_top) b).fderiv_right (by norm_num)) contDiffAt_const
lemma will_at (l : Bool) (b) : will i l b 0= (if l then 1 else -1)*dotI i b := by
   let c:ℝ := if l then 1 else -1
   let f:= fun t:ℝ=> t • dotI (I:=dah (hue G)) (.inr ())
   have he (t) : yellow i l (f t)=G.lieExp (moon G ((c*t) • dotI i)) := by
      unfold yellow; dsimp only; rw [show cheekL _ (f t)=0 by ext j; change t*dotI _ (.inl j : dah (hue G))=0; simp [dotI],map_zero,G.mat_lieExp_zero,show f t (.inr ())=t by simp [f,dotI],one_mul,mul_one,lantern]; cases l <;> simp only [Bool.false_eq_true,c,↓reduceIte,neg_one_mul,one_mul, map_smul,neg_smul]; rw [map_neg, map_smul,Work.F03.exp_neg_color]
   have hz : Tendsto (fun t:ℝ=>moon G ((c*t) • dotI i)) (𝓝 0) (𝓝 0) := by
      have hp : Continuous (fun t:ℝ=>moon G ((c*t) • dotI i)) := by fun_prop
      simpa using! hp.continuousAt (x:=0)|>.tendsto
   have hx : (fun t:ℝ=>curtain i l (f t) b)=ᶠ[𝓝 0] fun t=>t * (c*dotI i b) := by
      filter_upwards [hz.eventually G.plog_left] with t ht; rw [curtain,he,ht,(moon G).symm_apply_apply]; simp [mul_comm c,mul_assoc]
   have hf : HasDerivAt f (dotI (.inr ())) 0 := by simpa only [f,one_smul] using! ((hasDerivAt_id' (0:ℝ)).smul_const (dotI (.inr () : dah (hue G))))
   have hA : f 0=0:= zero_smul ..
   have hh : HasDerivAt (fun t:ℝ=>curtain i l (f t) b) (will i l b 0) 0 := by
      have ha := (coord_diff _ ((curtain_diff i l).of_le le_top) b).differentiableAt (by decide)
      unfold will; rw [map_zero]; exact HasFDerivAt.comp_hasDerivAt _ (l:=fun x=>curtain i l x b) (f:=f) (hA.symm ▸ ha.hasFDerivAt : HasFDerivAt _ (fderiv ℝ (fun x=>curtain i l x b) 0) (f 0)) hf
   exact (hh.congr_of_eventuallyEq hx.symm).unique (by simpa only [one_mul] using! ((hasDerivAt_id' (0:ℝ)).mul_const (c*dotI i b)))
end YM.FormalBulk08.City
