import YM.FVA2.Rank.Kappa
/-!
# Even brush on native symbols.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Parity.Screen
open Function Set Filter Finset Lattice
open MS MS.Koszul MS.Plane MS.Book MS.Native MS.Native.Orient MS.Native.Chart
open MS.Native.Sew MS.Cylinder MS.Cylinder.Lab MS.Landau MS.Color MS.Native.Paint
open MS.Momentum MS.Menus MS.Native.Wilsonian MS.Arts MS.Outlook MS.Tone MS.Logarithm
open MS.Book.Program MS.Book.Convolve MS.Tone.Frame Hue.Agent Hue.Agent.Kappa Position
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type}{m n d i:ℕ}{G:Gauge}{p: Team}
variable {R:Type}
local notation "V"=> Dot G R
abbrev grey (G:Gauge)(R:Type): Dot G R→ₗ[ℂ]Dot G R:= graffiti (fun _=> (-1:ℂ))
local notation "φ"=>grey G R
lemma penetrate (F: V) (i:LightMode G R) : enter i (φ F)= -(φ (enter i F)):= by rw [grey, tagged_s]; exact neg_one_smul ℂ (φ (enter i F))
lemma tag (F:V): (φ F).val= Hue.flip _ F.val:= by
    funext l; rw [grey,landc,Hue.flip_at,Cylinder.rent]; simp [Hue.σ] -- syntax
lemma colors (F:V)(q:G.El) : φ ( dye q F )= dye q ( φ F ):= by
    apply Subtype.ext; funext l; induction l generalizing F with
    | nil=> simp only [tag,Hue.flip_at,List.length_nil,Hue.s0,one_mul,dye_rep]; simp
    | cons i l ih=> rcases i with ⟨⟨a,c⟩,p⟩; simp only [D_eval ((a,c),p) (Subtype.val _), ← enterp, penetrate, solok, map_sum,map_neg,map_smul, sum_stack, smul_stack, Finset.sum_apply, Pi.smul_apply, Submodule.coe_neg,Pi.neg_apply, ih,smul_neg,Finset.sum_neg_distrib ] -- check enter order
variable [Fintype R]
lemma under_c (X:V): φ ((Spectrum G).Lap X)= (Spectrum G).Lap (φ X):= by
    simp only [Bonded.lap_at,map_sum,map_smul,heart_all,penetrate,map_neg,neg_neg]

variable [AddCommGroup R]

omit [Fintype R] in
private lemma hit (w:R)(X:V): φ (Shift w X)= Shift w (φ X):= by exact ( ferry_rent (Cylinder.Lab.post fun i=> w+i) (fun _=> (-1:ℂ)) X ).symm
private lemma under_home (X:V): φ (sumHome X)= sumHome (φ X):= by unfold sumHome; simp only [LinearMap.sum_apply,map_sum,hit]
lemma under_t (F X:V) : φ ((Spectrum G).touch F X)= (Spectrum G).touch (φ F) (φ X):= by
    let B:=Spectrum G; let Z:On ( Branch G Axis ) R ℂ:=B.Lap
    have he(F H:Dot G R): B.touch F H= (Z (couple (field parity) (sumHome F) H)-couple (field parity) (Z (sumHome F)) H)-couple (field parity) (twisted (field parity) true (sumHome F)) (Z H):= by apply Subtype.ext; simp only [B.t_here,B,Z,Spectrum,Bonded.lap_here,coupled,twistp,Submodule.coe_sub,link] -- imports
    rw [show (Spectrum G).touch F X=_ from he F X, show (Spectrum G).touch (φ F) (φ X)=_ from he ..]; unfold grey; simp only [B,Z,map_sub,tag_grows, ← tag_sign]; -- continue
    rw [ under_c,under_c,under_c,under_home ]; rw [grey,tag_grows,under_home]
local notation "γ"=>grey G Cover
lemma showing (n:Side)(F:Dot G Cover): shown n (γ F)=grey G (Site n) (shown n F):=by exact ferry_rent (Cylinder.Lab.post (wrap n)) (fun _=> (-1:ℂ)) F
lemma bumperC (X:Dot G Cover): γ (( Spectrum G ).Lap X)= ( Spectrum G ).Lap (γ X):= by
    refine (markEq ..).mp ?_; filter_upwards [soon_heart (Spectrum G) (γ X),soon_heart (Spectrum G) X] with n hn hx; rw [hn,showing,showing,hx,under_c]
lemma bumperT (X Y:Dot G Cover): γ (( Spectrum G ).touch X Y)= ( Spectrum G ).touch (γ X) (γ Y):= by
    refine (markEq ..).mp ?_; filter_upwards [soon_root (Spectrum G) (γ X) (γ Y),soon_root (Spectrum G) X Y] with n hn hx; rw [hn,showing,showing,showing,hx,under_t]
lemma perfect (F:Dot G Cover)(h:Hue.only i F.val) : γ F= Hue.σ i • F := by apply Subtype.ext; rw [ tag ]; exact ( Hue.test_p .. ).mp h
lemma mainB (p:Team)(h:Correct p)(x:ℝ) (i:ℕ): γ (style G p x i)=Hue.σ i • style G p x i:= by
    apply perfect; simpa only [style,zero_add] using (bill_p (p:=p) (X:=core G) (m:=0) x (k:=i) (fun i _=>h.tone i) (fun i _=>by rw [zero_add]; exact location i G) i i.le_refl)
end YM.FVA2.Parity.Screen
