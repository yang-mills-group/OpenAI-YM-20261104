import YM.MSbar.Recur.Progress
/-! Representation for homogeneous outputs and defect-antifield balance. Canonical tables
instantiated by physical transformation later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play.Produce
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Deck Work Diagram.WardOps
open scoped Classical Topology BigOperators
variable {C:Type} {W:Edition C}

structure Shield (X: Pulse W) where
   R : Sites C -- Linearized BRS including equations of motion, kernel Ward derivative
   D : Sites C -- BRS heat low line
   E : Sites C -- its dilation derivative
   Dk : ℝ
   Ek : ℝ
   hw : Pilot univ 0 W 1 (liftS R)
   hd : Window W 1 Dk D
   he : Window W 1 Ek E
   emerges : ∀ i, E i=Loops.shift (W.binary i) (W.members i) 1 (R i) (X.P i)
namespace Shield
variable {X:Pulse W}(A:Shield X)
variable {c d e l:Bit} {f g:Functionals C} {v i k j n:ℕ}{z:ℂ}{F G:ListV C}
abbrev R0 (A:Shield X): Mono W 0 1:= arrow (by simp) A.hw
abbrev D0 (A:Shield X): Mono W 0 1:= Work.loop A.hd (by simp)
abbrev E0 (A:Shield X): Mono W 0 1:= Work.loop A.he (by simp)
abbrev B0 (A:Shield X): Poly W 0 0 1:= Work.tree A.hd (by simp)
abbrev C0 (A:Shield X): Poly W 0 0 1:= Work.tree A.he (by simp)
abbrev Desk (W:Edition C)(d:Bit):= Form (Deck W d)
def engine(z:ℂ): Machine (Deck W 0) (Deck W 1):=
   ⟨Produce.L X z, Work.loop X.pay (show (1:Bit)=0+1 by simp) z,A.D0 z,A.E0 z,T X z, Work.tree X.pay (d:=0) (e:=1) (by simp) z,A.B0 z,A.C0 z,A.R0 z⟩
lemma current (z:ℂ): Calculus (engine A z):=by
   refine ⟨fun a b=>Subtype.ext ?_,fun a b=> Subtype.ext ?_,fun x=>Subtype.ext (unary z X.pay A.hd x.property),fun x=>Subtype.ext ?_,fun x=>Subtype.ext (tandem z X.pay A.hd x.property),fun x=>Subtype.ext (third z X.pay A.hd x.property),fun x=>Subtype.ext (expected z X.pay A.he A.hw A.emerges x.property)⟩
   · exact (boreal z X.pay a.property b.property).trans (by simp only [sign_zero,one_smul];rfl)
   · exact (boreal z A.hd a.property b.property).trans (by simp only [sign_zero,one_smul];rfl)
   exact sub_eq_iff_eq_add'.mp (quality z X.pay A.he A.hw A.emerges x.property) -- order
-- scale generator for V and for the anomaly
abbrev inc (M:SizeLaw C):SizeLaw C:= fun t=> M t+1
def theta (W:Edition C)(d:Bit)(α:Mass C): Homo (Deck W d) (Deck W d):= {
   toFun:=fun x=>⟨Scale.tick α x.val,tick_live x.property⟩
   map_add':=fun x y=>Subtype.ext (tick_add x.property y.property)
   map_smul':=fun y x=>Subtype.ext (tick_scale x.property y) }
lemma theta_here {W:Edition C}{d:Bit}{α:Mass C}(x:Deck W d):(theta W d α x).val=Scale.tick α x.val:=rfl
def high (z:ℂ)(M:SizeLaw C)(d:Bit):= Category.Twist.stretch (theta W d (Scale.mass M 0 0)) (2*z)
-- W not included? def above implicit W unused? set via explicit arg later
lemma wake (x:Desk W d) (v:ℕ) (M:SizeLaw C): (high (W:=W) z M d x v).val= Scale.tick (Scale.mass M v z) (x v).val:=by
   simp only [high, Category.Twist.stretch,LinearMap.add_apply, Pi.add_apply,Twist.nel, act_val,Submodule.coe_add,Submodule.coe_smul_of_tower,theta_here]; rw [Crest.lift_equal (M:=M) (F:=liftV (x v).val) (z:=z) (x v).property v]; congr! 2; unfold Scale.slope; ring

-- Need honest curvature, prove in analysis of lines. assumption localized for now.
abbrev Dynamic (A:Shield X) := ∀ z:ℂ, Twist (engine A z) (theta W 0 (Scale.mass X.law 0 0)) (theta W 1 (Scale.mass (inc X.law) 0 0)) (2*z)
lemma progress (hD:Dynamic A) (z:ℂ): Twist (propagate (engine A z) true) (high z X.law 0) (high z (inc X.law) 1) 0:= by simpa only [↓reduceIte,sub_self] using! Twist.next (A.current z) (hD z) true (2*z)
end Shield
end YM.MSbar.Play.Produce
