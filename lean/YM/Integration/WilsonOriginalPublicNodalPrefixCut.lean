import YM.Integration.WilsonOriginalPublicNodalPrefixFrame

/-! Pull the actually tuned notebook of either torus to one finite initial interval. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPrefixCut
open Lattice RG PertExtension
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Gain
open RegulatorIR.Oracle RegulatorIR.Older RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Calibration RegulatorIR.Uniform RegulatorIR.FVAAlt2
open WilsonOriginalPublicNodalPrefixFree (Route)
open scoped Classical
variable {X X':Type}{M:X → ℕ}{M':X' → ℕ}{n:Page M → Side}{n':Page M' → Side}
def height (t:ℕ)(_:Unit):ℕ:=t
def last (t:ℕ):Choice (height t):=⟨fun _=>t,fun _=>le_rfl⟩

def into (j:Choice M)(x:X){t:ℕ}(h:t≤j.age x)(p:Page (height t)):Page M:=
  briefly j x p.downW (p.good.trans h)
def edge (j:Choice M)(x:X){t:ℕ}(h:t≤j.age x)(f:Flap (height t)):Flap M:=
  wingS j x f.offset (f.ok.trans_le h)
def clock (k:Choice M')(y:X'){t:ℕ}(h:t≤k.age y)(F:Tent M'):Tent (height t):=F ∘ into k y h

def cut (C:Circuit M n)(j:Choice M)(x:X):Circuit (height (j.age x)) (n ∘ into j x le_rfl) where
  l:=C.l ∘ into j x le_rfl
  P _:=C.P x
  sizeL:=C.sizeL ∘ edge j x le_rfl
  J:=C.J ∘ into j x le_rfl
  seats f:=C.seats (edge j x le_rfl f)
  odd f:=C.odd (edge j x le_rfl f)
  holds f:=C.holds (edge j x le_rfl f)
  stands p:=C.stands (into j x le_rfl p)
  dual p:=C.dual (into j x le_rfl p)
  week p:=C.week (into j x le_rfl p)
  shakes f:=C.shakes (edge j x le_rfl f)
  slow f:=C.slow (edge j x le_rfl f)
  l_p p:=C.l_p (into j x le_rfl p)
  comet p:=C.comet (into j x le_rfl p)

theorem own (C:Circuit M n)(j:Choice M)(x:X):Route C C j j x x:=⟨rfl,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
variable (C:Circuit M n)(D:Circuit M' n')(j:Choice M)(k:Choice M')(x:X)(y:X')
    (T:Route C D j k x y)(root:C.l (Page.opening _ x)=D.l (Page.opening _ y))
    {K:KernelChoices}(Y:Program K)(G:Gauge)(Z:∀P:Patch,P.Branches K G)(c:G.ColorIndex)
    (F:Tent M'){p:ℕ}(book:Notebook D Y G Z c (Rocket.native M') F p)

include T in
theorem line:Route (cut C j x) D (last (j.age x)) k () y:=
  ⟨T.age,fun u h h'=>T.stage u h h',fun u h h'=>T.sizes u h h'⟩

include T root in
theorem vacuum (p:Page (height (j.age x))):
    ((cut C j x).payroll Y G Z (sheet (clock k y T.age.le F))).bulk p=
      (D.payroll Y G Z (sheet F)).bulk (into k y T.age.le p):=by
  obtain ⟨⟨⟩,t,h⟩:=p
  exact WilsonOriginalPublicNodalPrefixFrame.quiet (cut C j x) D (last (j.age x)) k () y
    (line C D j k x y T) root Y G Z (clock k y T.age.le F) F (fun _ _ _=>rfl) t h (h.trans T.age.le)

include T root book in
theorem notebook:
    Notebook (cut C j x) Y G Z c (Rocket.native _) (clock k y T.age.le F) p:=by
  constructor
  · intro a
    have read:=book.clean (into k y T.age.le a)
    refine ⟨?_,read.2⟩
    intro q hq hp
    rw [vacuum C D j k x y T root Y G Z F a]
    exact read.1 q hq hp
  · intro a
    exact book.reference y

end YM.Integration.WilsonOriginalPublicNodalPrefixCut
end
