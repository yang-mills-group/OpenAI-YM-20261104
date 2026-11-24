import YM.Contacts.Epochs.Range
import YM.Contacts.Epochs.Casa

/-! # Arbitrary-law scheduling with post-programming access.
 Quantifiers deliberately mirror Trading & Ruese. Supports compound asks on a proof‐relevant Factor,
 allowing time-purchases and Mark/Phase registers fixed without choosing exploration flows;
 `prep` is *method of charging*, not presumed finally. -/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Concert ThroughLaunch Pressure Testing Contacts.Allium Contacts.Allium.Grant
open Contacts.Bounty.Trophy.Lore Contacts.Bounty.Trophy Contacts.Revest Contacts.Revest.Outlay
open Push.SectorMeasure Terrain ConnectedActivityE6 Blaze Push.Uniform Contacts.Milling -- error
open scoped NNReal
variable {v: Patch}{s:Sheet G}{K:MapPrices}{R:Targets s (ThroughLaunch.bearing s K)}{E:Expenses R}
     {z:Return.Wages}
namespace Concert
variable {k l x i j m:ℕ} {β:ℝ}{L:Side}
variable (X:G.ColorIndex) {M:Metals G}{D:Rolls M.p}{A:Alloy M D}
-- sum.Ice chooses n exactly. hDescriptor Reader current. Wider movement clocks after lengths.
abbrev Stadium (f g: RG.Stage)(σ:ℝ)(k j d:ℕ)(x l:ℝ)(O : ChartRatio G) {Z:Teller G}(T:ConnectedActivityE6.Target G Z){W:ℝ}(B:YM.ConnectedActivityE6.Target.Order G W)(v:Patch): Prop:= ∃ d₁ d₂ d₃:ℕ,∃ H:Push.Uniform.Before G g.width g.paths v.J Z.bind (max f.order k +3), Tenor X v T B O f g k (max f.order k) d H j d₁ d₂ σ x l ∧ Arboric (G:=G) v f g d₁ j d₂ d₃ d k (max f.order k) x l
variable (Z:Factor A)
structure Candles (k m:ℕ)(l:ℝ):Prop where
   ge : (k)≤ A.B.a.clock.J (m+1) +1
   pack : Buzz Z k m l
   ford : let p:=A.B.a.params m; let i:=A.B.a.clock.J m; let j:=A.B.a.clock.J (m+1); Bargain G p (Z.book j i) (Z.scout j i) (A.B.a.clock.hatBeta m) (A.B.a.clock.hatBeta (m+1)) (alphaBound D j)
   after : let p:=A.B.a.params m; let i:=A.B.a.clock.J m; let j:=A.B.a.clock.J (m+1); let u:=A.B.a.params (m+1); let v:=(A.B.a.clock.op m 0).patch
           Stadium X p u (Z.shape.μ j i) k j (dim (Z.target j i|>.halo) k) (A.B.a.clock.hatBeta m) l M.O (Z.target j i) (Z.shape.o j i) v
abbrev Witness (X:G.ColorIndex) (Ψ:Factor A): Prop := ∀ k:ℕ,∀ᶠ m in atTop, Candles X Ψ (fabric k) m (chant k)
def pledge (X:G.ColorIndex) : Decision G := fun _ _ _ Z=>Witness X Z -- implicit fun
set_option maxHeartbeats 500000 in
theorem good (s: Sheet G) (K:MapPrices) (R:Targets s (ThroughLaunch.bearing s K)) (E:Expenses R) (z:Return.Wages) (C: Programs s)(bt: Baton G)(hg:G.Simple) (hp: EpochSeal s (ThroughLaunch.bearing s K) R E): ∃ l,EpochPlan s K R E z C bt (pledge X) l := by
    obtain ⟨L,hL⟩:= brooms R z; refine ⟨L,fun u hr D w Y R' B F S E' q η P θ p hθ H b J V=>?_ ⟩; let A:=V; have ht: wish R z (ThroughLaunch.raise s u).floorL:= fun j i k hh hk L' hp'=> hL j i k hh hk L' ((hr j).trans hp'); obtain ⟨V',hY,hP⟩:=westward R' S p C X z hg hp ht (fun i j=>hθ j i) V; refine ⟨V',hY,fun U hu Zr I' h Q hZ hT hV hS k=>?_ ⟩; -- pledge implicit let binder
    let A':=Q.a; let M:=ThroughLaunch.currency s K u; let A₀:Alloy M D:= ⟨P,θ,U,Zr,I',h,Q⟩; let Z:Factor A₀:=⟨E',F,S,η,q,w,B,R,E,Y,R',bt,z,rays s,mile,b,C,H,p,J,hZ,hT,hV,hS⟩; let N(i):= (A'.clock.op i 0).patch; let J':= A'.clock.J; let x':= A'.clock.hatBeta; let v:= chant k; let K':= fabric k; have hp' := hP U hu;
    filter_upwards [A'.fits.deep.eventually_ge_atTop (s.first),A'.fits.deep.eventually_ge_atTop K'] with m hm hl;
    let i:= J' m; let j:= J' (m+1); have he:StepStages j i:= Push.PriceCompiler.step_paid A' m; have hr: fabric k ≤ j:= hl.trans he.1; have hv:M.p.profile i=s.profile i:= rfl; have hh : k ≤ j:= Nat.le_trans ?_ hr; swap; · unfold fabric; omega -- h after
    have hP:= hp'.porch j i k he hm hh (x' m) (Q.valid.pays m); let P₀:= N m; let L':= D.L j; have hL':P₀.L=L':= Push.PriceCompiler.block_eq Q.valid m; have hS':P₀.Branches s.kernel G:= Q.valid.kernel ▸ (A'.blocks m 0).branches; have hm:(A'.params m)=s.profile i:= params_eq Q.valid m; have hf:A'.params (m+1)=s.profile j:= params_eq Q.valid _; let X':= Q.a; let r':= V'; have hz:= hP.pace P₀ hL' rfl hS';
    change Candles X Z (fabric k) m (chant k); have ht': (A'.clock.hatBeta (m+1))= betaF G (x' m) (D.L j):= Push.PriceCompiler.beta_eq Q.valid m
    refine ⟨by exact hr.trans (Nat.le_succ _), ?_, ?_, ?_⟩
    · refine ⟨?_, ?_,hp'.brim i j k he.1 hh, ?_ ⟩; · change Contacts.Bounty.Trophy.Lore.Priced G (A'.params m) L' (z j i); rw [hm]; exact ht j i k he.1 hh L' (D.large j).need|>.1
      · change Contacts.Bounty.Trophy.Lore.Phase G L' (A'.params m) (z j i) v (alphaBound D j) (x' m) ((R j i).halo) K'; rw [hm]; exact hP.base
      exact ⟨(hp.hForm j i).2.2.2.1.le,hP.pure,hz.1⟩
    · change Bargain G (A'.params m) (F j i) (S j i) (x' m) (A'.clock.hatBeta (m+1)) _; rw [hm,ht']; exact hP.buy
    change Stadium X (A'.params m) (A'.params (m+1)) (R'.μ j i) K' j (dim ((R j i).halo) K') (x' m) v (chart G) (R j i) (R'.o j i) (N m); rw [hf,hm]; exact hz.2
def service : Overlay G:=⟨pledge X, good X⟩
end Concert
end YM.PhysicalNext.Repeat.Legato
