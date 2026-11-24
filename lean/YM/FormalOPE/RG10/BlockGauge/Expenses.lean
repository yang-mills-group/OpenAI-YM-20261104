import YM.FormalOPE.RG10.BlockGauge.Fabric
/-!
 # expenses of the canonical Wilson formal multi-graph
 One price slot per genuine block step. Retain entire block rule. No extra
 factor two on penalty: one per independent coarse output link.Defer
 proving anything about relation to images from cover when performing graph
 estimates. Scalar determinant `zone` factors will be needed whenever reconstructing
 a normalized picture, although they cancel in joint ratios.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function MeasureTheory PertExtension PertExtension.Orb Lattice RG
open InversionWard Push.Loops
open scoped Classical Topology ContDiff
variable {G:Gauge} {c f n:Side}
namespace Fabric
variable (L : Fabric G n)
 def Cost {n}: Fabric G n → Type
 | .endcap _ _=> Empty
 | .layer _ _ _ _ L => Option L.Cost
@[implicit_reducible] def finiteCost {n: Side}(L:Fabric G n) : Fintype L.Cost:= by cases L with
                                                                                  | endcap => unfold Cost; infer_instance
                                                                                  | layer _ _ _ _ L => letI:= finiteCost L; unfold Cost; infer_instance
termination_by structural L
attribute [instance] finiteCost
abbrev Accounts:= Option L.Cost -- none top premium (not a block)

variable (S:StepData c f)(H:S.patch.Branches S.kernel G)(t:S.Choices)(hf:_root_.Even f.val)(L':Fabric G c)
local notation "Γ"=> layer S H t hf L'
 def regional {n} (L:Fabric G n)(u:L.LinksOn): L.Cost→ℝ := match L with
 | .endcap _ _ => Empty.elim
 | .layer S H t hf L => fun (i:Option L.Cost)=> Option.elim i (penalty S t ((layer S H t hf L).principal u) (L.principal (future S H t hf L u))) (regional L (future S H t hf L u))
 def wilson (u:LinkFrame G n) : ℝ:= Wilson.energy (Orb.liftLinks u)/2
 def price (u:L.LinksOn)(i:L.Accounts) : ℝ:= i.elim (wilson (L.principal u)) (L.regional u)
-- equivalences continuity / measurability
@[fun_prop] lemma future_cont : Continuous (future S H t hf L'):= continuous_pi fun _=> continuous_apply _
@[fun_prop] lemma principal_cont : Continuous L.principal:= continuous_pi fun _=> continuous_apply _
lemma region_gauge {n:Side}(L:Fabric G n)(u:L.LinksOn)(g:Vertex n→ G.El) (a:L.Cost): L.regional (L.loom.spin g u) a=L.regional u a:= by
 cases L with
 | endcap => exact Empty.elim a
 | layer S H t hf L =>
    match a with
    | some i => simp only [regional, Option.elim_some,spin_future]; exact region_gauge L _ _ i
    | none =>
     simp only [regional, Option.elim_none,spin_future,spin_main]
     rw [show ((g ∘ placement S.ratio) ∘ track)= (g ∘ track) ∘ S.ratio.embed from funext (fun x=> congr_arg g (place_track S.ratio x))]; exact motion S H t _ _ _ (track_even g) -- check params
termination_by structural L
lemma main_gauge (g:Vertex n→ G.El)(u:L.LinksOn): wilson (L.principal (L.loom.spin g u))=wilson (L.principal u):= by unfold wilson; rw [L.spin_main, show Orb.liftLinks (even_spin (g ∘ track) (L.principal u))= Lattice.gauge _ _ from funext (fun i=> (Orb.path_law _ _ (track_even g) i).symm),Wilson.energy_gauge]
lemma price_gauge (g:Vertex n→ G.El)(u:L.LinksOn)(a:L.Accounts): L.price (L.loom.spin g u) a=L.price u a:= by cases a with
                                                                                                                        | none=> exact L.main_gauge ..
                                                                                                                        | some i=> exact L.region_gauge ..
lemma charge_clean {n:Side}(L:Fabric G n)(a:L.Cost): Measurable (fun u=> L.regional u a):= by
 cases L with
 | endcap => exact Empty.elim a
 | layer S H t hf L =>
    change Option _ at a
    cases a with
    | none=> simp only [regional, Option.elim_none]
             let p:= principal L ∘ future S H t hf L
             have ha: Continuous p:= (principal_cont L).comp (future_cont S H t hf L)
             have he:= (principal_cont (layer S H t hf L)).measurable.prodMk ha.measurable
             -- compose efficiently, h Measurable diamond from Fintype instances?
             let j:= (layer S H t hf L).principal
             change Measurable (fun u=>penalty S t (j u) (p u))
             have hEq: (fun u=>penalty S t (j u) (p u)) = (fun x=>penalty S t x.1 x.2) ∘ (fun u=> (j u,p u)):=rfl
             rw [hEq]; exact Measurable.comp (measurable_penalty S H t) he
    | some i => simp only [regional,Option.elim_some]; exact (charge_clean L i).comp ((future_cont S H t hf L).measurable)
termination_by structural L
lemma price_clean (a:L.Accounts): Measurable (fun u=> L.price u a):= by cases a with
                                                                         | none=> exact ((Wilson.energy_cont.comp ((Orb.lift_cont G).comp (L.principal_cont))).div_const 2).measurable
                                                                         | some i=> exact L.charge_clean i
lemma regional_nonneg {n:Side}(L:Fabric G n)(a:L.Cost)(u:L.LinksOn): 0≤ L.regional u a:= by
 cases L with
 | endcap => exact Empty.elim a
 | layer S H t hf L =>
    change Option _ at a
    cases a with
    | none=> exact mul_nonneg S.kernel.penalty_pos.le (Finset.sum_nonneg fun _ _ => (G.price_range _).1)
    | some i=> exact regional_nonneg L i _
termination_by structural L
lemma price_nonneg (a:L.Accounts)(u:L.LinksOn): 0≤ L.price u a:= by cases a with
                                                                      | none=> exact div_nonneg (Wilson.energy_nonneg (Orb.liftLinks (L.principal u))) zero_le_two
                                                                      | some i=> exact L.regional_nonneg i u
 def spend (w:L.Accounts→ℝ)(u:L.LinksOn): ℝ:= ∑ a,w a*L.price u a
 def installment (ξ:L.Cost→ℝ)(u:L.LinksOn): ℝ:= ∑ a,ξ a*L.regional u a
lemma budget_sum (ξ:L.Accounts→ℝ)(u:L.LinksOn): L.spend ξ u= ξ none * wilson (L.principal u) + L.installment (ξ ∘ some) u:= by unfold spend installment; rw [Fintype.sum_option]; rfl
lemma tax_split (u:LinksOn Γ)(ξ:(Γ).Cost→ℝ) : (Γ).installment ξ u= ξ none * penalty S t ((Γ).principal u) (L'.principal (future S H t hf L' u)) + L'.installment (ξ ∘ some) (future S H t hf L' u):= by
 unfold installment; change ((∑ a:Option L'.Cost,_ )= _) -- fin instance diff?
 rw [Fintype.sum_option]; rfl
lemma zero_tax (n:Side)(h:_root_.Even n.val)(u:(endcap (G:=G) n h).LinksOn) (ξ:_): (endcap (G:=G) n h).installment ξ u=0:= by unfold installment; change ∑ i:Empty,_ = _; simp
-- used repeatedly. All tags retained at germ per Step S. Fiber/global gap below.
lemma measurable_cost (ξ:L.Accounts→ℝ): Measurable (L.spend ξ):= Finset.measurable_sum _ fun i _=> (price_clean L i).const_mul _
lemma nonneg_cost {ξ:L.Accounts→ℝ}(h:∀ i, 0<ξ i)(u:L.LinksOn): 0≤L.spend ξ u:= Finset.sum_nonneg fun a _=> mul_nonneg (h a).le (L.price_nonneg a u)
lemma invariant_cost (ξ:L.Accounts→ℝ)(u:L.LinksOn)(g:Vertex n→ G.El) : L.spend ξ (L.loom.spin g u) = L.spend ξ u:= Finset.sum_congr rfl fun a _=> congr_arg (ξ a*·) (price_gauge L g u a)
lemma prior_zero (v:LinkFrame G n)(hv: v=1): wilson v=0:= by
 subst v; unfold wilson; rw [show Orb.liftLinks (1:LinkFrame G n)=Orb.links 1 (1:Cotree n→G.El) from congr_arg liftLinks (Eq.symm (funext (fun i=>by change splitLink (1:Trees n→G.El) (1:Cotree n→G.El) i=1; unfold splitLink; split<;>rfl)))]; rw [Orb.flat_at_zero]; ring
lemma block_zero {n:Side}(L:Fabric G n)(a:L.Cost): L.regional 1 a=0:= by
 cases L with
 | endcap => exact Empty.elim a
 | layer S H t hf L=>
    change Option _ at a
    cases a with
    | some i=> exact block_zero L i
    | none => change penalty S t (G:=G) 1 1=0; unfold penalty distance; rw [unit_step S H t]; simp
termination_by structural L
@[simp] lemma price_zero (a:L.Accounts): L.price 1 a=0:= a.recOn (prior_zero (1:LinkFrame G n) rfl) fun i=> L.block_zero i
end Fabric
end YM.FormalOPE.RG10.BlockGauge
