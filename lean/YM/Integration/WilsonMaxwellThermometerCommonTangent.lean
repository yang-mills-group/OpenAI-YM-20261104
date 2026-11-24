import YM.Integration.WilsonMaxwellThermometerOriginal
import YM.Integration.WilsonMaxwellThermometerInteracting

/-! The common frame correction differentiates all three slots of the
actual tested Maxwell ground. Keep each translated proper face in that jet. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonMaxwellThermometerCommonTangent
open Function Finset Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose XSpace.Chiral
open WilsonMaxwellThermometerFaces WilsonMaxwellThermometerSignedAxes
open WilsonMaxwellThermometerOriginal (lower)
open WilsonMaxwellThermometerInteracting (first)
open scoped BigOperators Classical
variable {G:Gauge}{V:Normalize.Store G}(K:Pick V)

abbrev Equivariant (T:Module.End ℂ (Sec G 4)):Prop:=
  ∀s:Signed,∀p:Sec G 4,ori s.ortho 4 (T p)=T (ori s.ortho 4 p)

private theorem fixed (T:Module.End ℂ (Sec G 4))(law:Equivariant T)(c:P)(i j:Axis):
    ori (frame c i j).ortho 4 (T (lower G))=T (lower G):=by
  rw [law]
  apply congrArg T
  apply Subtype.ext
  change reflectPol _ (((Rose.f:ℂ)^2) • Chiral.U G)=((Rose.f:ℂ)^2) • Chiral.U G
  rw [WilsonMaxwellThermometerOriginalChirality.original]
  simp only [map_smul,WilsonMaxwellThermometerLower.preserved]

def payout (u:Sec G 6)(p q:Sec G 4):ℂ:=
  (Rose.test K).applyTo (fun x=>connected x
    (Graph3.trip u (up (by decide : 4≤6) p) (up (by decide : 4≤6) q)))

theorem separate (g:G.Simple)(u:Sec G 6)(P Q:Module.End ℂ (Sec G 4))
    (a:Equivariant P)(b:Equivariant Q):
    payout K u (P (lower G)) (Q (lower G))=0:=
  WilsonMaxwellThermometerOriginal.original g K u _ _
    (fun c i j=>congrArg Subtype.val (fixed P a c i j))
    (fun c i j=>congrArg Subtype.val (fixed Q b c i j))

def correction (u du:Sec G 6)(p dp q dq:Sec G 4):ℂ:=
  payout K du p q+payout K u dp q+payout K u p dq

theorem first_frame (g:G.Simple)(u du:Sec G 6)(P dP Q dQ:Module.End ℂ (Sec G 4))
    (a:Equivariant P)(b:Equivariant dP)(c:Equivariant Q)(d:Equivariant dQ):
    correction K u du (P (lower G)) (dP (lower G)) (Q (lower G)) (dQ (lower G))=0:=by
  unfold correction
  rw [separate K g du P Q a c,separate K g u dP Q b c,separate K g u P dQ a d]
  simp only [add_zero]

theorem curve (g:G.Simple)(U:ℂ→Sec G 6)(P Q:ℂ→Module.End ℂ (Sec G 4))
    (a:∀z,Equivariant (P z))(b:∀z,Equivariant (Q z))(z:ℂ):
    HasDerivAt (fun t=>payout K (U t) (P t (lower G)) (Q t (lower G))) 0 z:=by
  have h:(fun t=>payout K (U t) (P t (lower G)) (Q t (lower G)))=fun _:ℂ=>(0:ℂ):=
    funext fun t=>separate K g _ _ _ (a t) (b t)
  rw [h]
  exact hasDerivAt_const ..

end YM.Integration.WilsonMaxwellThermometerCommonTangent
