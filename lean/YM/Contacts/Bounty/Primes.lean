import YM.Contacts.Bounty.Card
/-! # Lift pressed from compatible episodes (Period-panes arguments, reuse Morse). -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Bounty
open AnalyticBridge VerifiedReset Collection Quotes Revest Flute Anthem
open PhysicalNext.Repeat PhysicalNext.Repeat.Roost Terrain
open Function Filter Lattice Wilson RG Pressure Ovens Ovens.Pipes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Org
open UVNext.CouplingReset Push Push.AbsoluteSums Animals Precision RG.Supply Input RG.Shoot PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Next.Scheduling PhysicalNext.ThroughLaunch Time Model Arbor Province.Costing Tucks Milling.Steam
open Pulse ConnectedActivityE6 Testing SectorMeasure Presented Coat Blaze Blaze.March
open Pane Boulevard Poetry Song Deck Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{l q r v t b α β:ℝ}
namespace Trophy
variable {M: Metals G}{D:Rolls M.p}(A:Alloy M D)(B:Factor A) {c f c' f':Side}{i j k N n m o:ℕ} {F Y:bore G}
local notation "E" => A.B.a.params m
local notation "E'" => A.B.a.params (m+1)
local notation "J" => A.B.a.clock.J (m+1)
local notation "I" => A.B.a.clock.J m
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "P" => A.B.a.budget m
local notation "P'" => A.B.a.budget (m+1)
local notation "R" => B.shape
set_option quotPrecheck false
local notation "ω₀" => (B.expense J I)
local notation "ζ" => (B.target J I).halo
local notation "n₀" => (P').B
local notation "K" => A.B.kin.path N (m+1)
local notation "Z" => A.B.kin.path N m
abbrev Emitters (m N:ℕ) (f:Side) (Q:RG.Rep G f) (Ψ: Lecturer Q (A.B.a.budget (m+1)).B) (k:ℕ)(F:bore G)(β:ℝ):Prop:= Q.path= A.B.kin.path N (m+1) ∧ Q.p=A.B.a.budget (m+1) ∧ Q.beta=β ∧ ∀ i,Q.activities.E (Ψ.place i)=integrated (A.B.a.budget (m+1)) F (A.B.a.params (m+1)).clip (A.B.kin.path N (m+1)) k β i
variable (h:f.val=c.val*(A.B.a.S.block m).val) (h':f'.val=c'.val*(A.B.a.S.block m).val)
    {Q:RG.Rep G f}{Q':RG.Rep G f'}{X:Chartlet B.shape A N m h Q}{X':Chartlet B.shape A N m h' Q'}
    {Ξ: Lecturer Q (A.B.a.budget (m+1)).B}{Ψ:Lecturer Q' (A.B.a.budget (m+1)).B}
local notation "T" => Pane.orchestra A N h
local notation "T'" => Pane.orchestra A N h'
local notation "O" => Chi.canonical
abbrev drag (k:ℕ)(F:bore G)(β:ℝ) :=Pales.shade T k F P' β
-- simplicity
lemma exhibited (F:bore G)(β:ℝ) : Trophy.Emitters A m N f (Pales.shade T k F P' β) (Pales.pub T k F P' β) k F β := ⟨rfl,rfl,rfl, Pales.glints⟩ -- implicit all arg incl x
variable (he:Emitters A m N f Q Ξ k F β)(he':Emitters A m N f' Q' Ψ k F β)
include he he'
lemma concordant {K':ℕ} (hz:f'.val=f.val*K'): Poetry.ConcordP hz Ξ Ψ:= by
   intro x V u; rw [he.2.2.2,he'.2.2.2]; rw [← Tucks.codify,← Tucks.codify]; unfold Model.pass; apply congr_arg; exact Slide.rolls hz V x
-- minimum one bill
local notation "θ" => Poetry.studio ζ (radiusB x₀) n₀ o
-- studio strong: 4* & >100B etc.Fine size.Anyscale. using n0.B.Want b fractions.
def certificate (m:ℕ)(o:ℕ):= 8*(Poetry.studio (B.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo (radiusB (A.B.a.clock.hatBeta m)) (A.B.a.budget (m+1)).B o) + 200*(1+(radiusB (A.B.a.clock.hatBeta m))+(A.B.a.budget (m+1)).B+(A.B.a.budget m).B)
variable (hm: m<N) (hc:certificate A B m o≤ c.val)
include h h' X X' A hm hc
lemma lifted (hl : c'.val=c.val*j) (v':ℝ) (i:ℕ) : let V:=Poetry.barony o X Ξ O i v' q; let W := Poetry.barony o X' Ψ O i v' q; Poetry.Override hl W V (A.B.a.budget m):= by
   let hH:= B.pledging.jewels J x₀ (A.B.valid.pays m) I (PriceCompiler.step_paid A.B.a m); obtain ⟨p,q',u,r,g,b,C,d,s,a,i,⟨L,hQ⟩,hx,-⟩:= hH.2 _ _ _ (Pane.orchestra A N h) X.laws.data.funds (Pane.ovation A N h hm B.pledging.conducts.full) Q X
   obtain ⟨p',r',g',s',y,η,a',u',Y,l,j,⟨L',hQ'⟩,hx',-⟩:= hH.2 _ _ _ (Pane.orchestra A N h') X'.laws.data.funds (Pane.ovation A N h' hm B.pledging.conducts.full) Q' X'
   let k:=ζ; let V:=radiusB x₀; let b':= Poetry.generous k V n₀; let p:= Poetry.roomP k V n₀ o
   have hc':p+2*V=θ:= rfl; have hh : 8*(p+2*V)+200*(1+V+n₀+V)≤c.val:=hc; have ht:2*b' ≤ p:= Nat.le_add_left ..; have hz: Poetry.generous 0 V n₀ ≤ b':= by unfold Poetry.generous b' Poetry.generous Mint.width; omega
   intro v V' o V₁ hV; refine Poetry.replay («I»:=X) («T»:=T) (I':=X') («T'»:=T') hl (by omega : 2≤ c.val) rfl (he'.1.trans he.1.symm) (he'.2.1.trans he.2.1.symm) (he'.2.2.1.trans he.2.2.1.symm) o (by change 4*p< _; omega) L L' V₁ hV ?_ (by change 2* (Poetry.generous 0 V n₀ +3)<c.val; omega) (show _ from ?_) _ _ _
   · exact concordant A he he' _ -- h arguments?
   change 2*(p+b')<c.val; omega
variable (hC:certificate A B m o ≤ c'.val)(hw: WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m)) (hs:Geo.Width (A.B.a.budget m) (A.B.a.params m).clip (A.B.a.params m).width) (hP:Pay A m F k N β) (hb:β∈ RG.Shoot.band A.B.a (m+1))
include hC hw hs hP hb
lemma crossing (i:ℕ) : Trio.Compatible (Poetry.barony o X Ξ O i (β+q) q) (Poetry.barony o X' Ψ O i (β+q) q) P θ:= by
   let d:=c*c'; let D:= d*A.B.a.S.block m; have hd:D.val=d.val*(A.B.a.S.block m).val:=rfl; have hd':d.val=c.val*c'.val:=rfl; have ht:d.val=c'.val*c.val:= mul_comm ..; have hs':c.val≤d.val:=Nat.le_mul_of_pos_right _ c'.pos; have hu:d.val≤D.val:= Nat.le_mul_of_pos_right _ (A.B.a.S.block m).pos
   let Y:= Pales.shade (Pane.orchestra A N hd) k F P' β; let Ψ₀:=Pales.pub (Pane.orchestra A N hd) k F (A.B.a.budget (m+1)) β -- P' notation conflict
   unfold certificate at hc hC
   obtain ⟨K',hκ⟩:= Trophy.begs A B hd hm (by omega) (by omega) hb hP
   let T₀:=Poetry.barony o K' Ψ₀ O i (β+q) q
   refine Poetry.chromatic (z:=T₀) (by omega) hd' (lifted A B h hd he (exhibited A hd F β) hm hc hd' (β+q) i) ht (lifted A B h' hd he' (exhibited A hd F β) hm hC ht (β+q) i) (fun v t s V=> (Poetry.rotates ..).symm) (fun v t s V=> (Poetry.rotates ..).symm) ?_
   exact Poetry.regularY o K' O Ψ₀ _ _ P rfl i _ (Trophy.commodity A B hm hd K' (q:=q) hκ hw hs).1|>.sites
omit h' he he' X X' hc hC
-- all strings.Rize.Le.Fee
end Trophy
end YM.Contacts.Bounty
