import YM.OPE.Compatible.Whet.Lap
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
abbrev barrier (P:Patch):=100*Pressure.macroR P+2
structure Town (A:Alps K T i v)(D:Alps K T j v') (U:Boxes G P K.K)(R:ChartRatio G)(s:ℝ):Prop where
    eph:Era U A
    warm:TEX U A.clip D.clip A.live D.live s R
    okay :∀ n:Side,barrier P≤ n.val→ ∃ L g, ReadyV (subStud P K.K n) P.odd_side U A D L g
lemma courtesy (X:Flight i j)(he:A.gear=X.wing)(hd:D.gear=X.land)(h:Mag i j)(p:Medal X.patch G K.K i)(hs:Pilgrim G X K.K A.clip D.clip A.live D.live b R)(hr:LocalRatio R): Town A D (⟨i,h.1,p,A.gear⟩: Boxes G X.patch K.K) R b:=by
      refine ⟨Cascade.Rill.sprig X p h he hd, Votive.elevation X h A D he hd hs hr p,fun n hN=>?_⟩; let S:=X.visit (f:=n*X.L) (c:=n) K.K rfl; have hv: Bid.Larger (G:=G) S:=by
         refine ⟨K.affordable _,?_,?_⟩; change _≤ n.val *X.L.val; apply (le_trans _ (Nat.le_mul_of_pos_right n.val X.L.pos)); exact Nat.le_trans (Nat.le_add_right ..) hN
         unfold barrier at hN;omega
      obtain ⟨x,hx⟩:= testimony _ _ _ A D he hd h p rfl hv; exact ⟨_,x,hx⟩
lemma cuplet {U:Sailing T P p R b}(hr:LocalRatio R)(X:Medal P G K.K P.J)(i:ℕ): Town (U.U i) (U.U (i+1)) (charmSeal X (U.U i).gear) R (U.fare i):=by
      let A:=U.U i; let t:=ship P A.gear; obtain ⟨h,h'⟩:=U.shot i; let D:=U.U (i+1); obtain ⟨s,hs,hT,hA,hh⟩:= h'; have he:s=ship P A.gear:=by rw [show A.gear=s.wing from hT]; cases s; cases hs; rfl
      subst s; exact courtesy t (A:=U.U i) rfl hA h X hh hr
variable {u:ℝ}(h:Town A D U R u)(H:Even n.val)(hx:barrier P≤ n.val)(hi:4≤ i)(hj:4≤ j)(hS:G.Simple)
def bredV (S:Alps K T i v)(x:ℝ)(h:Even n.val)(hp:4 ≤ i)(hs:G.Simple): Bor h S x:= Classical.choice (Bor.bought h S hs hp x)
def genS : Scape K T P n (n*P.L) i j R:=
    let L:= (h.okay n hx).choose; let p:= (h.okay n hx).choose_spec; let g:=p.choose; let hG:= p.choose_spec; let S:= subStud P K.K n
    let X' := Classical.arbitrary (S.Choices); let γ:= roomed S P.odd_side H g U hG.1 X'
    ⟨v,v',0,u,A,D,U,u,(zero_add _).symm,h.warm,rfl,X', H,L,g,hG,bramble H, γ.choose,γ.choose_spec,h.eph,(Classical.choice (buoy (bredV A 0 _ hi hS) X' (K.affordable _))),bredV D u H hj hS⟩
noncomputable def WrS (_D:Alps K T j v') (h:Town A _D U R u)(hr:LocalRatio R)(hs:G.Simple)(ha:Aware d τ): Tower (Shade G) d τ →L[ℝ] Tower (Shade G) d τ:= rebase G ha (-u)∘L actor A U R 0 ⟨hs,hr,h.eph⟩ ha
noncomputable def yankV (D:Alps K T j v')(h:Town A D U R u)(hr:LocalRatio R)(hs:G.Simple)(ha: Aware d τ): solar G d τ →L[ℝ] solar G d τ:=
   (WrS D h hr hs ha∘L (solar G d τ).subtypeL).codRestrict _ (fun x=>aboard _ ha _ (actors 0 _ _ _ _ ha x.val x.property))
local notation "Y!"=>solar G d τ
noncomputable def SpecH (A:Alps K T i v)(H:Even n.val)(hi:4≤ i)(hs:G.Simple)(p:Plot H):=(RGram H p (bredV A 0 H hi hs) (d:=d) (τ:=τ))
lemma topD' (x y:Y!)(a b:Site n)(ht:Aware d τ)(hr:LocalRatio R):
    let T:= genS h H hx hi hj hS
    let X:=yankV D h hr hS ht
    SpecH (D) H hj hS T.E (X x) (X y) a b R= RGram H T.E (show Bor H D u from T.V) (T.upL hS hr ht x) (T.upL hS hr ht y) a b R:=by
       intro T X; let q:=T.upL hS hr ht
       have hh(i:Y!): X i=Tru G ht (q i) (0-u):=by rw [zero_sub]; rfl
       rw [hh,hh]
       exact ledgers H T.E (A:=D) (b:=u) T.V (bredV D 0 H hj hS) (q x) (q y) a b hr hS ht
end YM.OPE.Quit.PriceZ
