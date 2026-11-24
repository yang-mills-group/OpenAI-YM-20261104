import YM.LocalLTE.Ticket.Chops
import YM.LocalLTE.Ballot.Elegy
import YM.LocalLTE.Ticket.Marsh
/-!
## Buying analytic currency for canonical windows.

Choices for ranks per previous output and order authorized. Use Φ in canon at each step.
Books current report to precision goal p separate from β-price analytic ζ from Πmint.
No extrapolation through infinite-depth.N finite.Goal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spiral
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE.Vinca VoucherB
variable {G:Gauge}{p q r l:ℕ}{e:ℝ}
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
-- physical purchase.Etch pre heights. t schedule at actual level.
variable (M T:ℕ)(he:0<e)(hE: 1-e< -(↑(r+1):ℝ)/2)(ht:e < M/100)(hz:e < (3/8:ℝ)*q)(hx:East.stagnate q 500 < l)
    (hs:-((r:ℝ)+1)/2 ≤ grantZ p T 0)(hu:2-e ≤ grantZ p T 0)
open ClockB Urns
set_option quotPrecheck false
noncomputable def loco : Elixir G M where
    invests {X _ _ _ _ _ _} R κ _ _ V:= Series (X:=X) R M κ q l r p T e V
    pays:= by
       intro X K C P h μ k hK; have hh i j :3/8+(C i j).rate < aust:=by have hp:= (P i j).reach; rw [(h i j).2] at hp; unfold aust; linarith
       have hv(i j:ℕ):= LocalLTE.Fan.EarnStepC (C i j) (P i j) Mallow.aust (hh i j) (by norm_num [aust]); choose w hw using hv
       choose p₀ s H using fun i j (h':ℕ)=> hw i j (X.profile j).order (X.profile j).power M q l h' e μ k hK he ht hz (by rw [(h i j).1]; exact hx)
       let g:=fun i j n=>Gazette.addenda s n i j; obtain ⟨hG,hP⟩:= Gazette.gates s; let a:= Gazette.acc g
       let Y0:GuideF:= fun i j n=> p₀ i j (a i j n)
       refine ⟨fromMax w ⊔ (fun _=>2*l),fun l' hW D _ _ Vt R' _ _ Y=>?_⟩
       let pst i j d (x:ℝ):Prop:=Load (X.profile i) (X.profile j) l r d (D.L i) e (C i j) (R'.μ i j) x∧ minSide G d≤radiusB (betaF G x (D.L i)) ∧ (∀ c:Side, (localSection G d).footprint (0:Site c)⊆Animals.neighbors (l*radiusB x) 0 ∧ (localSection G d).footprint (0:Site c)⊆Animals.neighbors ((D.L i).val*radiusB x) 0) ∧ (∀ n≤T, Spool.Resale (X.profile j) (X.profile i) l d r (D.L i) e (C i j) (R'.μ i j) (grantZ p T n) (grantZ p T (n+1)) x ∧ ∀ β :ℝ,betaF G x (D.L i)/2 ≤ β → β ≤2* betaF G x (D.L i)→ x^(grantZ p T (n+1)) ≤ Spool.powerR p β)∧ Spool.BloomP G d (X.profile j).supportExponent (grantZ p T 0) x
       let τ i j n (x:ℝ):Prop:= LocalLTE.Fan.ManifestC (C i j) (D.L i) (R'.o i j) (P i j) Push.SectorMeasure.Chi.canonical (X.profile j).order (X.profile j).power M q l (a i j n) (Y0 i j n) (g i j n) μ e Mallow.aust x (R'.μ i j)
       let ψ i j (x:ℝ):Prop:= (∀ n≤ T,τ i j n x) ∧ l*radiusB (betaF G x (D.L i))≤(D.L i).val*radiusB x ∧ ∀ d≤j,pst i j d x
       have hN(i j:ℕ)(hh:StepStages i j):∀ᶠ x in atTop, ψ i j x:=by
           obtain ⟨h₁,h₂⟩:= sup_le_iff.mp hW; have he:= R'.consumes i j hh; let L:=D.L i; have hv:(fromMax w) i≤ L.val:= (h₁ i).trans (D.large i).need; have he' :2*l ≤ L.val:= (h₂ i).trans (D.large i).need
           have hT(n):∀ᶠ x in atTop, τ i j n x:=by
              unfold τ; have hp:g i j n=s i j (a i j n):= hP i j n; rw [hp]; exact H i j (a i j n) L ((le_fromMax _ hh).trans hv) _ _ _ he.1 he.2.1 _ -- danger L.
           have ht d :∀ᶠ x in atTop,pst i j d x:=by
              have hρ(n :ℕ)(hp:n≤T) := slant p T (n+1) (Nat.succ_le_succ hp)
              have hU(n:ℕ) : grantZ p T 0 ≤ grantZ p T n:=by unfold grantZ; gcongr; exact n.zero_le
              have hZ(n:ℕ)(hx:n≤T):∀ᶠ x in atTop, Spool.Resale (X.profile j) (X.profile i) l d r L e (C i j) (R'.μ i j) (grantZ p T n) (grantZ p T (n+1)) x ∧ ∀ β :ℝ,betaF G x L/2 ≤ β → β ≤2*betaF G x L → x^(grantZ p T (n+1))≤ Spool.powerR p β:=by
                  have hy:grantZ p T n < grantZ p T (n+1):=by unfold grantZ; push_cast; linarith
                  have he₀: grantZ p T (n+1) ≤ 0:=by linarith only [hρ n hx, Nat.cast_nonneg (α:=ℝ) p]
                  exact (Spool.green _ _ _ _ _ _ _ _ _ _ _ (hy.le.trans he₀) hy he₀ (hs.trans (hU n)) he.2.1 (hu.trans (hU n))).and (Urns.actualG L ((p:ℝ)+1) _ _ (Mallow.flagE L _ he₀) (hρ n hx))
              obtain ⟨u,hu'⟩:= LocalLTE.Port.Sect.insideL G d; filter_upwards [VoucherB.pulse _ _ _ _ _ _ _ _ he.2.1 hE, ((Work.E09.betaF_growth G (D.L i)).eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop (minSide G d))), Work.E01.radiusB_tendsto.eventually_ge_atTop u, Spool.bloomP G d _ (X.profile j).supportExponent, eventually_all.mpr (fun x:Fin (T+1)=> hZ x.val (Nat.le_of_lt_succ x.isLt))] with x hA hE hz hF hT; refine ⟨hA,hE,?_ ,fun n he=> hT ⟨n,Nat.lt_add_one_of_le he⟩,hF⟩
              intro c; constructor
              · exact fun j hj=> (Animals.neighbors_mem ..).2 (((Animals.neighbors_mem ..).1 (hu' c 0 hj)).trans (hz.trans (Nat.le_mul_of_pos_left (radiusB x) (show 0<l from Nat.zero_le _|>.trans_lt hx))))
              exact fun j hj=> (Animals.neighbors_mem ..).2 (((Animals.neighbors_mem ..).1 (hu' c 0 hj)).trans (hz.trans (Nat.le_mul_of_pos_left (radiusB x) (D.L i).property)))
           filter_upwards [eventually_all.mpr (fun k:Fin (T+1)=> hT k.val), Rebuild.geometry (G.slopeConstant * Real.log ((D.L i).val)), eventually_all.mpr (fun k:Fin (j+1)=> ht k.val)] with x hy hh hv; refine ⟨fun n he=> hy ⟨n,Nat.lt_add_one_of_le he⟩, ?_, fun d he=> hv ⟨d,Nat.lt_add_one_of_le he⟩⟩
           refine (Nat.mul_le_mul_left l (show radiusB (betaF G x L) ≤ 2*radiusB x from hh.1.1)).trans ?_; rw [← mul_assoc,mul_comm l]; exact Nat.mul_le_mul_right _ he'
       obtain ⟨u,-,hy,hb⟩:= collect_upper Y.betaEntry _ fun j=>eventually_transitions j _ _ (hN j); let t:Delays Vt:= {Y with betaEntry:=u,shells:= (fun _=>32*(1+l))⊔Y.shells,growth:= (fun _=>1)⊔Y.growth}
       refine ⟨t,⟨hy,le_rfl,le_sup_right,le_sup_right⟩,fun S h=>⟨(show 32*(1+l)≤t.shells 0 from le_sup_left).trans (h.shells _),fun i=> ?_,fun i=> ?_, ⟨Y0,a,g, hG,fun i j he n h' x hx=> (hb i x ((h.beta i).trans hx) j he).1 n h'⟩,fun i j he x hx=> (hb i x ((h.beta i).trans hx) j he).2⟩⟩
       · exact le_trans (show 32*(1+l)≤t.shells i from le_sup_left) (h.shells _)
       exact le_trans (show 1≤ t.growth i from le_sup_left) (h.growth _)
end YM.PhysicalNext.Repeat.Legato.Spiral
