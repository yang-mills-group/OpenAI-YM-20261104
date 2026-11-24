import YM.AllOrder.Plateau.Horizon
/-!
# Produce revelations on one actual m,F even with post-L & funded V boundary for masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau.Line
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext Repeat Height Song Geo RG.Shoot
open Push.Uniform Blaze Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Shop Further.PhysicalPeriodLimitF933
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X : Metals G} {D:Rolls X.p} (A : Alloy X D) (F:Factor A) {c f : Side} {n m N k : ℕ}
set_option quotPrecheck false
local notation "a" => A.B.a
local notation "J" => (A.B.a.clock.J (m+1))
local notation "I" => (A.B.a.clock.J m)
local notation "L" => (D.L J)
local notation "x₀" => (A.B.a.clock.hatBeta m)
local notation "z" => betaF G x₀ L
local notation "V" => A.B.a.budget m
local notation "P" => (F.target J I)
local notation "R" => F.shape
local notation "Ω" => (F.expense J I)
local notation "B" => radiusB x₀
local notation "γ" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
local notation "hJ" => (A.B.a.clock.adm (m+1))
local notation "hp" => (A.B.a.clock.adm m)
local notation "K"=> X.p.kernel
local notation "Π"=> A.B.a.S.block m
local notation "s" => Mural.sheet X.p D hJ
local notation "W" => X.p.profile J
local notation "E" => X.p.profile I
local notation "u" => (tall I)
local notation "Y" => (parking u (P).halo)
local notation "d" => (Meadow.studio Y B)
local notation "R₁"=> A.B.kin.path N (m+1)
local notation "R₂"=> A.B.kin.path N m
local notation "Q₀"=> A.B.a.budget (m+1)
local notation "D₀"=>ConnectedActivityE6.loopBill G L x₀
local notation "H'"=> Shop.Pledged -- not yet
local notation "Γ"=> precinct D (i:=I) hJ
local notation "M"=> Bank D (i:=I) hJ
variable {β:ℝ} (π:f.val=c.val*(A.B.a.S.block m).val)(hβ:β∈band A.B.a (m+1))(hk:m<N)
local notation "S"=>Pane.panel A m π
local notation "T"=> orchestra A N π
open Ker Ker.Start Haiku Kinetic.Port Fire PertExtension.Series Radial Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
lemma patch_here : (S).patch=Mural.sheet X.p D hJ:= by
    let U:= (S).patch; have hS:= PriceCompiler.block_eq A.B.valid m; cases h : U with
    | mk k j ht hf ho =>
      have hh : j= J:= by rw [← show (Patch.mk k j ht hf ho).J=j from rfl,← h]; rfl
      have hK : k=D.L J:= by rw [← show (Patch.mk k j ht hf ho).L=k from rfl,← h]; exact PriceCompiler.block_eq A.B.valid m
      change U= _; rw [h]; subst k j; rfl
local notation "U₁"=> Mural.pref D J+A.post.Γ J
local notation "X₁"=> min (Mural.knot D J) (A.post.c J)
local notation "Z₁"=> (A.B.a.clock.loopCap (m+1))
include hk F
abbrev heart (a' b c' :ℝ) {c f :Side} (S':StepData c f):Prop:= ∀ (Fₜ:Forest S'.ratio), Ad G s K c → ∃ ρ, Critical («S»:=S') Fₜ (W).clip R₁ ρ ∧ ClassicalMatch Fₜ (W).clip (E).clip R₁ R₂ ρ∧ FiniteBound Fₜ R₁ R₂ (W).clip (E).clip γ X.O ρ a' b c' -- a binder
lemma thru (h : f=Progress.ClassicalKin.Tent.below s c): heart A (m:=m) (N:=N) U₁ X₁ Z₁ S := by
 subst f; let U:= s; let Y₀:= Pane.orchestra A (m:=m) N π; let V':= Pane.panel A m π; intro K' he
 have hC : V'=dock s K c:= by
     cases hv: V' with
     | mk a' k hL =>
       have hk:a'=s:=by rw [←show (StepData.mk a' k hL).patch=a' from rfl,←hv]; exact patch_here A π
       have hk':k=K:=by rw [←show (StepData.mk a' k hL).kernel=k from rfl,←hv]; exact A.B.valid.kernel
       subst a' k; rfl
 have hd:= params_eq A.B.valid (m+1); have hl := params_eq A.B.valid m
 have hU: ∃ a':ℝ, Quilt Y₀ K' a':= by
     let q:= max (radiusB x₀) 1; have hh:= (V).B_pos; have hx: c.val≤ most c.val x₀:= by
        unfold most Trio.base Trio.tent Meadow.studio Meadow.roomSize Deck.Mint.width; have he:= Nat.le_mul_of_pos_right c.val (show 0<B from hh); omega
     exact ⟨_, Trio.quilt G L c.val x₀ _ Y₀ K' hx (PriceCompiler.block_eq A.B.valid m) (show Bid.Larger (G:=G) V' from hC.symm ▸ he)⟩
 obtain ⟨a₁,hA⟩:= hU; obtain ⟨ρ,hρ,he,hq⟩:= Pane.presents («Y»:=fun _ _ _=> a₁) _ A (Factor.floor F) hk π K' hA; refine ⟨ρ, ?_⟩; rw [show (W).clip=Y₀.high from (congr_arg RG.Stage.clip hd).symm, show (E).clip=Y₀.low from (congr_arg RG.Stage.clip hl).symm]; exact ⟨hρ,he,hq⟩
local notation "s'"=> (A.B.a.S.block m)
variable (H:Lodge D F.shape (fun _ i=> edgeW i) A.delay)
include H
structure Books (x: Plateau.Ticket (Mural.sheet X.p D (A.B.a.clock.adm (m+1))) X.p.kernel X.O (X.p.profile (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (Pane.cloak D (A.B.a.clock.J (m+1)))) : Prop where
    north : x.north=A.B.kin.path N (m+1)
    south : x.south=A.B.kin.path N m
    high : x.alpha=A.B.kin.alpha N m
    fisc : x.paid=D₀

lemma accounting : ∃ i:Γ, Books A (m:=m) (N:=N) i:= by
    let Z:= D₀; let Γ':=X.p; have hi:= params_eq A.B.valid (m+1); have hv:= params_eq A.B.valid m; let B':= A.B.a.clock
    have hf:x₀ ≥Real.exp 1:= ((Shop.lot A F (m:=m) H).script 0 (Nat.zero_le _)).1
    have hr': B'.hatBeta (m+1)=betaF G x₀ L:= PriceCompiler.beta_eq A.B.valid m
    have hb := A.B.support.cap N (m+1) hk
    have hb': B'.loopCap (m+1) ≤ ConnectedActivityE6.loopBill G L x₀:= by
      have hh:= coverBill A.B.a (m+1)|>.2; refine hh.trans_eq ?_; change 2*B'.monitor (m+1)=2*Delay.fineMonitor G L _; unfold Calendar.monitor Delay.fineMonitor; rw [hr']; rfl
    have hg: (R₁).Bounds (W).clip (X.p.profile J).width (X.p.profile J).paths D₀:= by rw [←hi]; exact {hb with two:=budget_loosen hb.two hb'}
    have hg' : (R₂).Bounds (E).clip (X.p.profile I).width (X.p.profile I).paths D₀:= by have hh:= A.B.support.cap N m hk.le; rw [← hv]; exact {hh with two:=budget_loosen hh.two ((coverBill A.B.a m).2.trans (brace _ hf))}
    refine ⟨⟨(show Precision.Towers (D.L J) from PriceCompiler.block_eq A.B.valid m ▸ A.B.M.towers N m),R₁,R₂,γ,Z,hg,hg',Boulevard.coupling A _ _ hk, U₁,X₁,Z₁,lt_min (Mural.knot_pos D J) (A.post.posC _),?_⟩,⟨rfl,rfl,rfl,rfl⟩⟩; intro n
    let f:= (Progress.ClassicalKin.Tent.below s n); have hL: f.val=n.val*(A.B.a.S.block m).val:= by rw [PriceCompiler.block_eq A.B.valid m]; rfl
    let U:= Pane.panel A m hL; have hU: U= dock s K n:= by
         cases hh:U with
         | mk p W' h =>
           have hk:p=s:=by rw [←show (StepData.mk p W' h).patch=p from rfl,←hh]; exact patch_here A hL
           have hk':W'=K:=by rw [←show (StepData.mk p W' h).kernel=W' from rfl,←hh]; exact A.B.valid.kernel
           subst p W'; rfl
    change heart A (m:=m) (N:=N) U₁ X₁ Z₁ (dock s K n)
    rw [← hU]; exact thru A F hL hk rfl
end YM.AllOrder.Plateau.Line
