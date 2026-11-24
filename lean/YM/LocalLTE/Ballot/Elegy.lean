import YM.LocalLTE.Ballot.Buttons
import YM.LocalLTE.Vinca.Wreath
/-! Schedule.Named: amount epochs under Warranty. Requests latched. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE.Vinca VoucherB
variable {G:Gauge} {p q r l:ℕ}{e:ℝ}
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
-- local clocks purchased on TRUE allotment R. Coordinate independent after L.
structure Elevera {X:Metals G}{D:Rolls X.p}{C:Targets X.p X.K}{M:Expenses C}{w:Return.Wages}{v:ℕ→ℝ}{T:Protection D}(R:Register D M w v)(m:ℕ)(κ:ℝ)(q l r:ℕ)(e:ℝ)(V:Delays T):Prop where
   side k :32*(1+l)≤V.shells k
   grew i :1≤ V.growth i
   time i j: StepStages i j→∃ k dα:ℕ,∀ y:ℝ,V.betaEntry i≤y→LocalLTE.Fan.ManifestC (C i j) (D.L i) (R.o i j) (M i j) Push.SectorMeasure.Chi.canonical (X.p.profile j).order (X.p.profile j).power m q l i k dα κ e aust y (R.μ i j)
   tempo i j: StepStages i j→∀ y:ℝ,V.betaEntry i≤y→∀ d,d≤j→ VoucherB.Load (X.p.profile i) (X.p.profile j) l r d (D.L i) e (C i j) (R.μ i j) y∧
          minSide G d ≤radiusB (betaF G y (D.L i)) ∧ ∀ c:Side, (localSection G d).footprint (0:Site c) ⊆ Push.AbsoluteSums.Animals.neighbors ((D.L i).val*radiusB y) 0
-- move shadow. Elixir P opportunities
variable (M:ℕ)(he:0<e)(hE: 1-e< -(↑(r+1):ℝ)/2)(ht:e < M/100)(hz:e < (3/8:ℝ)*q)(hx:East.stagnate q 500 < l)
noncomputable def twilight : Elixir G M where
    invests {X _ _ _ _ _ _} R κ _ _ V:= Elevera (X:=X) R M κ q l r e V
    pays:= by
        intro X K C P h μ k hK; have hh i j :3/8+(C i j).rate < aust:=by have hp:= (P i j).reach; rw [(h i j).2] at hp; unfold aust; linarith
        have hv(i j:ℕ):= LocalLTE.Fan.EarnStepC (C i j) (P i j) Mallow.aust (hh i j) (by norm_num [aust]); choose w hw using hv
        choose p₀ s hSig using fun i j:ℕ=> hw i j (X.profile j).order (X.profile j).power M q l i e μ k hK he ht hz (by rw [(h i j).1]; exact hx)
        refine ⟨fromMax w,fun l' hW D _ _ Vt R' _ _ Y=>?_⟩
        let PR(i j:ℕ)(y:ℝ): Prop:= LocalLTE.Fan.ManifestC (C i j) (D.L i) (R'.o i j) (P i j) Push.SectorMeasure.Chi.canonical (X.profile j).order (X.profile j).power M q l i (p₀ i j) (s i j) μ e Mallow.aust y (R'.μ i j)∧ ∀ d≤j, Load (X.profile i) (X.profile j) l r d (D.L i) e (C i j) (R'.μ i j) y ∧ minSide G d≤radiusB (betaF G y (D.L i)) ∧∀ c:Side, (localSection G d).footprint (0:Site c)⊆Push.AbsoluteSums.Animals.neighbors ((D.L i).val*radiusB y) 0
        have hPR (i j:ℕ)(hT:StepStages i j):∀ᶠ x:ℝ in atTop, PR i j x:=by
           have he:= R'.consumes i j hT; apply Eventually.and (hSig i j (D.L i) ((le_fromMax w hT).trans ((hW i).trans (D.large i).need)) _ (R'.o i j) (R'.μ i j) he.1 he.2.1 _)
           have hb(d):∀ᶠ y in atTop, Load (X.profile i) (X.profile j) l r d (D.L i) e (C i j) (R'.μ i j) y ∧ minSide G d≤radiusB (betaF G y (D.L i)) ∧∀ c:Side, (localSection G d).footprint (0:Site c) ⊆ Push.AbsoluteSums.Animals.neighbors ((D.L i).val*radiusB y) 0:=by
               obtain ⟨u,hu⟩:= LocalLTE.Port.Sect.insideL G d; filter_upwards [VoucherB.pulse _ _ _ _ _ _ _ _ he.2.1 hE, ((Work.E09.betaF_growth G (D.L i)).eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop (minSide G d))), Work.E01.radiusB_tendsto.eventually_ge_atTop u] with x hx hy hz
               refine ⟨hx,hy,fun c' a h=>?_⟩; exact (Push.AbsoluteSums.Animals.neighbors_mem ..).2 (((Push.AbsoluteSums.Animals.neighbors_mem ..).1 (hu c' 0 h)).trans (hz.trans (Nat.le_mul_of_pos_left (radiusB x) (D.L i).property))) -- namespace
           filter_upwards [eventually_all.mpr (fun i:Fin (j+1)=>hb i.val)] with x hx d hd; exact hx ⟨d,Nat.lt_succ_of_le hd⟩
        obtain ⟨u,-,hy,hb⟩:= collect_upper Y.betaEntry _ fun j=>eventually_transitions j _ _ (hPR j); let t:Delays Vt:= {Y with betaEntry:=u,shells:= (fun _=>32*(1+l))⊔Y.shells,growth:= (fun _=>1)⊔Y.growth}
        refine ⟨t,⟨hy,le_rfl,le_sup_right,le_sup_right⟩,fun T h=>⟨fun i=> ?_,fun i=> ?_,fun i j he=>⟨p₀ i j,s i j,fun x hx=>(hb i x ((h.beta i).trans hx) j he).1⟩,fun i j he x hx d hd=> (hb i x ((h.beta i).trans hx) j he).2 d hd⟩⟩
        · exact le_trans (show 32*(1+l)≤t.shells i from le_sup_left) (h.shells _)
        exact le_trans (show 1≤ t.growth i from le_sup_left) (h.growth _)
end YM.PhysicalNext.Repeat.Legato
