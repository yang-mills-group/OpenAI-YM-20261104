import YM.Integration.WilsonOriginalPublicNodalPrefix
import YM.Integration.WilsonOriginalPublicNodalHelperElection

/-! A matched finite prefix determines the actual appointed free training, conditional book and bed. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPrefixFree
open Lattice RG Laurent Bloch PertExtension Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Oracle.Quarry RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Halo RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Geometry RegulatorIR.Gain
open RegulatorIR.Older RegulatorIR.Binding RegulatorIR.Prim RegulatorIR.Taping RegulatorIR.Uniform
open scoped Classical
variable {X X':Type}{M:X → ℕ}{M':X' → ℕ}{n:Page M → Side}{n':Page M' → Side}
    (C:Circuit M n)(D:Circuit M' n')(j:Choice M)(k:Choice M')(x:X)(y:X')

structure Route:Prop where
  age:j.age x=k.age y
  stage:∀t h h',C.J (briefly j x t h)=D.J (briefly k y t h')
  sizes:∀t h h',C.sizeL (wingS j x t h)=D.sizeL (wingS k y t h')

private theorem flights {a b c d:ℕ}(P:Next.Free.Flight a b)(Q:Next.Free.Flight c d)(ac:a=c)(bd:b=d)
    (patch:P.L=Q.L)(trained:HEq P.wing Q.wing):HEq P Q:=by
  subst c;subst d
  have eq:=eq_of_heq trained
  cases P;cases Q
  simp_all

private theorem landed {a b c d:ℕ}(P:Next.Free.Flight a b)(Q:Next.Free.Flight c d)(ac:a=c)(bd:b=d)
    (same:HEq P Q):HEq P.land Q.land:=by
  subst c;subst d
  rw [eq_of_heq same]

theorem training (T:Route C D j k x y)(t:ℕ)(l:t≤j.age x)(r:t≤k.age y):
    HEq (C.training (briefly j x t l)) (D.training (briefly k y t r)):=by
  induction t with
  | zero =>
    change HEq (Next.Free.Train.top (C.J _)) (Next.Free.Train.top (D.J _))
    congr 1
    exact T.stage 0 l r
  | succ t ih =>
    let f:=wingS j x t l
    let f':=wingS k y t r
    change HEq (C.training f.next) (D.training f'.next)
    rw [C.crest,D.crest]
    exact landed _ _ (T.stage t (by omega) (by omega)) (T.stage (t+1) l r)
      (flights _ _ (T.stage t (by omega) (by omega)) (T.stage (t+1) l r) (T.sizes t l r)
        (ih (by omega) (by omega)))

theorem crew (T:Route C D j k x y)(t:ℕ)(l:t<j.age x)(r:t<k.age y):
    HEq (C.crew (wingS j x t l)) (D.crew (wingS k y t r)):=by
  exact flights _ _ (T.stage t l.le r.le) (T.stage (t+1) l r) (T.sizes t l r)
    (training C D j k x y T t l.le r.le)

variable {K:KernelChoices}(Y:Program K)

private def record (v:Σi,Next.Free.Train i)(clip:Clip)(B:Precision.Bed):Prop:=
  Hall B (Y.receipt.α v.1) (Y.receipt.Ω v.1) (Y.receipt.η v.1) clip ∧
  Next.Free.Defined K.penalty (Y.fees v.1) v.2 B ∧ (∀n G,Bid.Sworn B n G) ∧
  (v.2=Next.Free.Train.top _ → ∀p:Side,B.diagonal.acts p=1)

private theorem owns (u:Page M)(B:Precision.Bed):
    C.Certificate Y u B ↔ record Y ⟨C.J u,C.training u⟩ (C.clips Y u) B:=
  ⟨fun h=>⟨h.card,h.flight_s,h.symmetryP,h.top_s⟩,fun h=>⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩⟩

private theorem chosen {α:Type}{P Q:α → Prop}(L:∃v,P v)(R:∃v,Q v)(e:∀v,P v ↔ Q v):
    Classical.choose L=Classical.choose R:=by
  have eq:P=Q:=funext fun v=>propext (e v)
  subst Q
  rfl

theorem bed (T:Route C D j k x y)(t:ℕ)(l:t≤j.age x)(r:t≤k.age y):
    C.tables Y (briefly j x t l)=D.tables Y (briefly k y t r):=by
  let v:=briefly j x t l
  let w:=briefly k y t r
  have stage:C.J v=D.J w:=T.stage t l r
  have routes:(⟨C.J v,C.training v⟩:Σi,Next.Free.Train i)=⟨D.J w,D.training w⟩:=
    Sigma.ext stage (training C D j k x y T t l r)
  have clips:C.clips Y v=D.clips Y w:=by
    unfold Circuit.clips
    congr 1
    rw [stage]
  exact chosen (C.dreams Y v) (D.dreams Y w) fun B=>by rw [owns C Y v B,owns D Y w B,routes,clips]

end YM.Integration.WilsonOriginalPublicNodalPrefixFree
end
