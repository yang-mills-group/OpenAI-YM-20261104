import YM.MS.Class.Common
import YM.MS.Roles
import YangMills.WilsonProof.NativeSupport.YM.MS.Color.Components
/-!
# Low-dimension integrated classification: the problem

Use the usual sign/order convention and the continuum linear BV differential.
No antifields eliminated, no use of strictly closed under full Q, no ∆ assumption. Momentum
holds only up to translation integration. Colors fixed real G. Need below even at disconnected G.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect
open Function Filter Set Finset Plane Koszul Real Momentum Wire
open scoped Topology ContDiff InnerProductSpace
variable {G : Gauge}

variable {F H : Law G}

structure Class (F : Law G) (h:ℤ): Prop where
    solid : Solid true F 0
    closed (w) (hw:net w=0) : natQ F w=0
    graded : Form F wfield h true
    signed : SignedScope true F

variable {h : ℤ}
lemma Class.add (X:Class F h) (Y:Class H h): Class (F+H) h:= ⟨X.solid.add Y.solid, fun w hw=> by simp only [map_add,Pi.add_apply,X.closed w hw,Y.closed w hw, add_zero], X.graded.add Y.graded, X.signed.add Y.signed⟩
lemma Class.scalar (X:Class F h) (c:ℝ): Class ((c:ℂ) • F) h:= ⟨X.solid.scalar c,fun w hw=> by rw [map_smul]; simp [X.closed w hw],X.graded.scalar _, X.signed.scalar _⟩
lemma Class.sub (X:Class F h) (Y:Class H h): Class (F-H) h:=by simpa [sub_eq_add_neg] using X.add (Y.scalar (-1))

-- Names common

lemma Class.swap (X:Class F h) l i j k (he: net (l++i::j::k)=0) : F (l++i::j::k)=cross (parity i.1) (parity j.1)*F (l++j::i::k):= X.solid.symm l i j k (fun _=>he)
lemma Class.ne (X:Class F h) w (he:net w=0) (ha: fieldDim ghostNo w≠0) : F w=0:=X.solid.ghost w (fun _=>he) ha
lemma Class.tall (X:Class F h) w (he:net w=0) (hc: h<fieldDim wfield w): F w=0:= X.graded.no_tall w (fun _=>he) hc
lemma Class.single (K:G.Simple) (X:Class F h) (w : Lane4 G) (he:net [w]=0): F [w]=0:= by
   rcases w with ⟨⟨w,c⟩,z⟩; refine Landau.single K (p:=fun i=> F [qnote w i z]) ?_ c
   exact fun g i=> X.solid.color [qnote w i z] (fun _=>he) g

section flux
open Complex (I)
-- action of Q backwards. Momentum q same. real sign charge not center.
end flux
end YM.MS.Landau.Detect
