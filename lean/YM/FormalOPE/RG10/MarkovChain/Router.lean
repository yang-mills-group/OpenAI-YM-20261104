import YM.FormalOPE.RG10.MarkovChain.Anchor
/-!
 # Plane router. A two-row criterion for real formal Marks in a blocking local chart.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {S:StepData c f} {H:S.patch.Branches S.kernel G}{t:S.Choices}{hf:_root_.Even f.val}{L:Fabric G c} {C:Cloth L}{P:Inside S.ratio}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (S:=S) (H:=H) (t:=t) (hf:=hf) (C:=C) (P:=P)
variable {L':Fabric G n}(T:Cloth L')
namespace Router
 def Present (u:Ticket (Field T.choose)): Prop:= Heads T.choose fun x=> Stack.read x u
lemma nowFirst (x y): send (T0).choose (d (x,y)) = send (T0).choose (d (x,0)):= by change send (P.join C.choose H t hf) ((sector S H t hf L P C.choose) _) = send (P.join C.choose H t hf) ((sector S H t hf L P C.choose) _); rw [Line.first,Line.first]
lemma vaulted {v:Ticket (Field T.choose)}(h:Present T v): Vault T v:= by
 cases T with
 | floor=> trivial
 | @inLayer c f S H t hf L P C=>
   let D:= Pathway (H:=H) (t:=t) (hf:=hf) (P:=P) (C:=C)
   have he (x:Cross (G:=G) S P)(y z:Field C.choose): Stack.read (D (x,y)) v = Stack.read (D (x,z)) v:= h _ _ ((nowFirst x y).trans (nowFirst x z).symm)
   rw [Vault]; refine ⟨fun x y z _=> congr_arg₂ _ (he x y z) (he 0 z y),?_⟩
   rw [show boost (coarse D) v = carry (Stack.read (D (0,0)) v) from by apply into; intro x; rw [caught,load]; exact he _ _ _]
   exact Vault.fromFixed _
 def transmit (u:Ticket (Head T.choose)): Ticket (Field T.choose):= boost (send _) u
 def toRow (u:Ticket (Field T.choose)): Ticket (Head T.choose):= boost (importTop _) u
lemma written (u:Ticket (Head T.choose)): Present T (transmit T u):= by intro x y h; unfold transmit; dsimp only; rw [caught, caught,h]
lemma available {u:Ticket (Field T.choose)}(h: Present T u): transmit T (toRow T u)=u:= by apply into; intro x; unfold transmit toRow; rw [caught,caught]; exact h _ _ (send_place ..)
-- for any two-row germ ticket
 def Adjacent (u:Ticket (Field ((T0).choose))): Prop:= ∀ x:Cross (G:=G) S P, Heads C.choose fun y:Field C.choose=> Stack.read (d (x,y)) u
lemma presently {u:Ticket (Field ((T0).choose))}(h: Present T0 u): Adjacent u:= fun x y z _=> h _ _ ((nowFirst x y).trans (nowFirst x z).symm)
lemma receive {u v: Ticket (Field ((T0).choose))}(h:Adjacent u)(g:Adjacent v): Adjacent (u*v):= by intro x y z hZ; dsimp only; simp_rw [_root_.map_mul,h x y z hZ,g x y z hZ]
lemma rOut (u:Ticket (Field C.choose)) (x y): Stack.read (d (x,y)) (Ancestor u)=Stack.read y u:= by unfold Ancestor; rw [caught]; simp
lemma rOut_succ (u:Ticket (Field C.choose)): boost (coarse d) (Ancestor u)=u:= by apply into; intro y; rw [caught]; exact rOut (H:=H) (t:=t) (P:=P) (hf:=hf) _ _ _
lemma rBack {u:Ticket (Field C.choose)} (h: Vault C u): Vault T0 (Ancestor u):= by rw [Vault,rOut_succ]; exact ⟨fun x y z _=>by simp_rw [rOut]; exact mul_comm _ _,h⟩
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 def Return (u:Ticket E): Ticket E:= PowerSeries.invOfUnit u 1
lemma spend_it {u:Ticket E} (h: incline u): u*Return u=1:= by rw [Return,PowerSeries.mul_invOfUnit ..]; exact h
lemma worth {u:Ticket E}(h:incline u): IsUnit u:= IsUnit.of_mul_eq_one _ (spend_it h)
lemma investment {u:Ticket E}(h:incline u): incline (Return u):= by have hh:= spend_it h; replace hh:= congr_arg constantCoeff hh; rw [map_mul,h,map_one,one_mul] at hh; exact hh
lemma pool {u v:Ticket E}(h:incline u)(hv: incline v): incline (u*v):= by unfold incline; rw [map_mul,h,hv,one_mul]
end
 def handle (u:Ticket (Field ((T0).choose))): Ticket (Field ((T0).choose)):= u* Ancestor (Return (boost (coarse d) u))
lemma whole {u:Ticket (Field ((T0).choose))}(h:incline u): handle u * Ancestor (boost (coarse d) u)=u:= by
 unfold handle Ancestor; rw [mul_assoc,←_root_.map_mul, mul_comm (Return _), spend_it (preserve_boost _ h),map_one,mul_one]
lemma seat {u:Ticket (Field ((T0).choose))}(h:incline u): incline (handle u):= pool h (preserve_boost _ (investment (preserve_boost (coarse d) h)))
lemma tip {u:Ticket (Field ((T0).choose))}(h:paired u)(hv:incline u): Adjacent (handle u):= by
 intro x y z hz; specialize h x y z hz
 let U(x:Field C.choose):= Stack.read (d (0,x)) u
 let I:= Return (boost (coarse d) u); let v (y:Field C.choose):= Stack.read y I
 change _ * U z= _ * U y at h
 have he (y:Field C.choose): U y * v y=1:= calc
                      _ = Stack.read y ((boost (coarse d) u)*I):=by rw [_root_.map_mul,caught]; rfl
                      _ = 1:= by rw [show boost (coarse d) u * I = 1 from spend_it (preserve_boost _ hv),map_one]
 unfold handle; dsimp only; rw [_root_.map_mul,_root_.map_mul,rOut,rOut]; change _ * v _= _ * v _
 let a:= Stack.read (d (x,y)) u; let b:=Stack.read (d (x,z)) u; change a*_ = b*_
 calc
   _ = a*v y*(U z*v z):= by rw [he,mul_one]
   _ = b* (U y*v y) * v z:= by rw [show a*v y*(U z*v z)= a*U z*(v y*v z) by ring,show a*U z=b*U y from h]; ring
   _ = _:= by rw [he,mul_one]
end Router
end YM.FormalOPE.RG10.MarkovChain
