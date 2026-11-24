import YM.Integration.WilsonOriginalPublicNodalPrefixFree

/-! The measured mean, covariance and bare height operator coincide on the two matched grouped prefixes. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPrefixOperators
open Lattice RG Laurent Bloch PertExtension Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Oracle.Quarry RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Halo RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Geometry RegulatorIR.Gain
open RegulatorIR.Older RegulatorIR.Binding RegulatorIR.Prim RegulatorIR.Taping RegulatorIR.Uniform
open WilsonOriginalPublicNodalPrefixFree (Route training crew bed)
open scoped Classical
variable {X X':Type}{M:X → ℕ}{M':X' → ℕ}{n:Page M → Side}{n':Page M' → Side}
    (C:Circuit M n)(D:Circuit M' n')(j:Choice M)(k:Choice M')(x:X)(y:X')(T:Route C D j k x y)
    {K:KernelChoices}(Y:Program K)(G:Gauge)(Z:∀P:Patch,P.Branches K G)

private def average {a b:ℕ}(u:Next.Free.Flight a b):=
  projectionQ u.patch K (u.duo K.penalty).A0 G
private theorem means {a b c d:ℕ}(u:Next.Free.Flight a b)(v:Next.Free.Flight c d)
    (a':a=c)(b':b=d)(e:HEq u v):average (K:=K) G u=average (K:=K) G v:=by
  subst c;subst d;rw [eq_of_heq e]

private theorem samePatch {P Q:Patch}(a:P.L=Q.L)(b:P.J=Q.J):P=Q:=by cases P;cases Q;congr

include T in
theorem patch (t:ℕ)(l:t<j.age x)(r:t<k.age y):
    C.pactP (wingS j x t l)=D.pactP (wingS k y t r):=by
  apply samePatch
  · exact T.sizes t l r
  · exact T.stage t l.le r.le

include T in
theorem mean (t:ℕ)(l:t<j.age x)(r:t<k.age y):
    C.sails Y G (wingS j x t l)=D.sails Y G (wingS k y t r):=
  means (K:=K) G (C.crew (wingS j x t l)) (D.crew (wingS k y t r)) (T.stage t l.le r.le) (T.stage (t+1) l r) (crew C D j k x y T t l r)

private theorem pulse (P Q:Patch)(A B:Precision.Bed)(a b:ℕ)(r s:Clip)
    (left:Hall A (Y.receipt.α a) (Y.receipt.Ω a) (Y.receipt.η a) r)
    (right:Hall B (Y.receipt.α b) (Y.receipt.Ω b) (Y.receipt.η b) s)
    (p:P=Q)(c:A=B)(d:a=b)(clip:r=s):
    hearth P K G A left (Z _)=hearth Q K G B right (Z _):=by
  subst Q;subst B;subst b;subst s;rfl

include T in
theorem covariance (t:ℕ)(l:t<j.age x)(r:t<k.age y):
    C.pulses Y G Z (wingS j x t l)=D.pulses Y G Z (wingS k y t r):=by
  let v:=(wingS j x t l).prev
  let w:=(wingS k y t r).prev
  have stage:C.J v=D.J w:=T.stage t l.le r.le
  apply pulse Y G Z _ _ _ _ (C.J v) (D.J w) (C.clips Y v) (D.clips Y w) _ _
    (patch C D j k x y T t l r) (bed C D j k x y Y T t l.le r.le) stage
  unfold Circuit.clips
  congr 1
  rw [stage]

include T in
theorem form (t:ℕ)(l:t≤j.age x)(r:t≤k.age y):
    C.scroll_j Y G (briefly j x t l)=D.scroll_j Y G (briefly k y t r):=by
  unfold Circuit.scroll_j
  rw [bed C D j k x y Y T t l r]

end YM.Integration.WilsonOriginalPublicNodalPrefixOperators
end
