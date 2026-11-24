import YM.LocalLTE.Quay.Ramps
import YM.LocalLTE.Sail.Ratio
/-!
## Direct conditional density moments, dollar conversion.

For real ALL LINKS healthy. Complements retain conditional experiment but
NO division. Does not make an assertion about smoothness of indicators.
Lateral reassignments: these credits use standard λ-moment modules,
ALL products/case.Attachments may upgrade to common storage in future.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
variable {G:Gauge} (M p j:ℕ)
-- Extra gauges for ratio without log. Contains also one auxiliary meta.M.Pay K is same.
structure LaneQ {s:Sheet G}{D:Rolls s}{T:Protection D}(V:Delays T)(p p0:ℕ) :Prop where
   frame i j: StepStages i j→ ∀ x:ℝ,V.betaEntry i≤x→ ∀ β,betaF G x (D.L i)/2 ≤ β→ β≤ 2*betaF G x (D.L i)→ (3+(s.profile i).columns+(s.profile j).columns)*powerR p0 β ≤ powerR p β
variable (hp:p<j)
noncomputable def furtherQ (G:Gauge)(hW:p<j)(S:Elixir G M): Elixir G M where
    invests {X _ _ _ _ _ _} R κ a b V:= S.invests (X:=X) R κ a b V ∧ LaneQ V p j
    pays:=by
       intro X K C Q h k a hp; obtain ⟨w,hV⟩:= S.pays C Q h k a hp
       refine ⟨w,fun l hl D w v T R t e U=>?_⟩
       obtain ⟨Y,hξ,hF⟩:= hV l hl D R t e U
       let cR i g x:= ∀ β,betaF G x (D.L i)/2 ≤ β→ β≤ 2*betaF G x (D.L i)→ (3+(X.profile i).columns+(X.profile g).columns)*powerR j β ≤ powerR p β
       have hh i g:∀ᶠ t:ℝ in atTop,cR i g t:=by
           let a:ℝ:= p; let b:ℝ:= j; have ht:a < b:= Nat.cast_lt.mpr hW; let c:ℝ:=3+(X.profile i).columns+(X.profile g).columns; let r:= D.L i
           filter_upwards [Urns.actualG (G:=G) r (a-b) _ _ (Rate.const c) (by linarith only [ht]), Work.E09.betaF_growth G r |>.eventually_gt_atTop 0] with x hx hξ; intro β h H'; let p:= Coat.gStep β; have hf:0<β:= (half_pos hξ).trans_le h
           have hβ:0<p:=inv_pos.mpr (Real.sqrt_pos.mpr hf); apply le_trans (mul_le_mul_of_nonneg_right (hx β h H') (Real.rpow_nonneg hβ.le (b+1))); apply le_of_eq; rw [← Real.rpow_add hβ]; exact congr_arg (p ^ ·) (show a-b+(b+1)=a+1 from by ring) -- defeq
       obtain ⟨u,-,he',hU⟩:=collect_upper Y.betaEntry _ (fun j=>eventually_transitions j _ _ fun i _=> hh j i); let U': Delays T:= {Y with betaEntry:=u}; have ht: DelayLe Y U':= ⟨he',le_rfl,le_rfl,le_rfl⟩; exact ⟨U',hξ.trans ht,fun X h=>⟨hF X (ht.trans h),⟨fun j i hi t hp=> hU _ t ((h.beta _).trans hp) i hi⟩⟩⟩
-- use Paper conversion on frame reports
variable {d:ℕ}{n:Side}(R:Rep G n){D:Labels.Frame G d} (A:SectionData D)(U:Config G n) {P Q: Coefficient D n}
variable {T:Hol G}{r v s t k δ:ℝ}{m q:ℕ}
open Planned.GuardedAtom Guard MergeProof River Sail Bandage.Harmonics
lemma sparkle (hf:P.Format 0 T R)(h: Exhibition A t m q T R P Q v r s)(hp:P.remBound 0 R v δ)(hB:∀ j:D.Index,R.p.Regular (A.footprint (0:Site n)) (A.places (Pi.single j 1) (0:Site n)) ∧ R.p.supBounds 0 (A.footprint (0:Site n)) (A.places (Pi.single j 1) (0:Site n)) (k*R.p.threshold^(D.grades j).2)) (hh:flags R.p.threshold U=∅)(hv:v≤1)(hk:1 ≤k): let u:=R.eval U; u > 0 ∧ ((u:ℂ)⁻¹*P.density 0 A R U)=P.exponentialEntry 0 A R U ∧ ‖(u:ℂ)⁻¹*P.density 0 A R U -Q.exponentialEntry 0 A R U‖ ≤ (3+k)*s :=by
    intro u; have he:u = Real.exp (R.exponent U):=by unfold u Rep.eval; rw [Activities.gas_one _ _ hh,mul_one]
    have hu:0<u:=he ▸ Real.exp_pos _; have hK i : P.forced i U=0:=by by_contra h'; have hs:=(hf.forcing i U h').1; rw [hh,Finset.inter_empty] at hs; exact ((R.activities.forced i).inventory_ne.ne_empty hs.symm)
    have hq: P.density 0 A R U= (u:ℂ)* P.exponentialEntry 0 A R U:=by
        unfold Coefficient.density; simp_rw [show ∀ i,P.marked R i U=0 from (fun i=>by unfold Coefficient.marked; split; simp only [hK,zero_mul,Finset.sum_const_zero]; next=> rfl),tsum_zero,mul_zero, add_zero]; rfl
    rw [hq,inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr hu.ne')]; exact ⟨hu,rfl,LocalLTE.Sail.readPrice A ⟨h.layout, h.format,h.stock.forced,h.trade,h.fee,h.canon⟩ hp hB U hk hv⟩ -- order.
end YM.PhysicalNext.Repeat.Legato.Spool
