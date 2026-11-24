import YM.AllOrder.Rosary.Shive
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
-- genuine wrap family, minimal occurrence fee (up to poly) via `Gyro.Tooth`, normalize clover anchor to 0 then run ALL oriented actions. No K bake assumptions.
namespace Lapis
open Gyro Next.Scheduling Progress.DirectedRecipe Push.AbsoluteSums
local notation "o" => (0:Site n)
structure Signal (n:Side)(B:ℕ) where
 call : Tooth n B
 at_zero : call.site=0
lemma Signal.in_time (n:Side)(hn:20<n.val)(p:BudgetPoint) : Nonempty (Signal n p.B):=by
 obtain ⟨q⟩:=settle p.B hn; let t : Seat n:=(1,-q.site); let d:= relocate (Push.Local.turnSites 1 (-q.site)) q.toRegularAddress; have he:d.site=0:=(by change Signed.act 1 q.site + (-q.site)=0; rw [Signed.act_one,add_neg_cancel]); have hs:d.support=t.spread q.support:=rfl; refine ⟨⟨⟨d,?_,?_⟩,he⟩⟩; exact mt (spin_wrap (X:=q.support) 1 (-q.site) q.site).mp q.excess; exact (Seat.visit_count (p:=p) t q.support).trans q.economical
variable (s:Signal n p.B) -- h always explicit
abbrev echo := s.call.toRegularAddress
local notation "I"=> Seat n
local notation "R" => echo s
-- f λ val at Halo2.D Ready absolute projection inverted
abbrev kappa (x y:PlaqAxes):ℝ:= if x=y then 1 else 0
def arg (n:Side)(G:Gauge)(α:ℝ)(U:Config G n):= (factor*α)*counter kappa 0 U
local notation "Θ"=> Real.exp ((p.supportExponent+1)*((pitch n p.B:ℝ)+81))
-- price actual card polynomial for simplicity.All bills post
abbrev repu (G:Gauge)(p:BudgetPoint)(a:ℝ):ℝ:= |factor*a| * ((2:ℝ)⁻¹ * ∑ x:PlaqAxes,∑ y:PlaqAxes,|kappa x y| *(pairBill G p*p.threshold^2))
def solid (s':Signal n p.B) (z:Seat n) : RegularAddress n:= z.reg (expand (echo s')) (by have he:(echo s').site=0:=s'.at_zero; rw [← he]; exact (enlarges (echo s')).anchor)
variable (G n) in
lemma meaning (a:ℝ)(U:Config G n):arg n G a U=(factor*a)*((∑ i, ‖petals U 0 i‖^2)/2):= by simp only [arg,counter,quad,kappa,ite_mul,one_mul,zero_mul]; simp [real_inner_self_eq_norm_sq]
abbrev liquid (n:Side) (G:Gauge)(p:BudgetPoint)(a:ℝ):= masked p.threshold {(0 : Site n)} (arg n G a)
variable (a:ℝ)
def wood (G:Gauge) : Herb G n I:= ⟨solid s, fun x=> arg n G a ∘ x.view⟩
def discrepancy (G:Gauge) (U:Config G n):= if Healthy p.threshold (expand (echo s)) U then 0 else liquid n G p a U
-- want reg term adds -a*true; soft adds gap correction? sign if discrepancy true -present, multiply -.
def drizzle (G:Gauge) : Cane G n I:= ⟨fun i=>(solid s i).support,fun i=>⟨_,(solid s i).anchor⟩,fun i U=> - discrepancy s a G (i.view U)⟩
variable (g:G.Simple) (hc:2≤p.B)
local notation "V"=> wood s a G
local notation "Z"=> drizzle s a G
include hc
private lemma rice (x:Seat n):p.mass ((V).addr x).support (turnFee p * repu G p a)≤ Θ*(turnFee p*repu G p a):=by
 let q:= pitch n p.B; have ht:= Geo.enlarge p (echo s) hc; have hk: coverNumber p.B ((V).addr x).support ≤ q+81:= (Seat.visit_count (p:=p) x (expand (echo s))).trans_le (ht.trans_eq (by rw [show coverNumber p.B (echo s).support=q from s.call.economical])); have he':0≤ repu G p a:= by unfold repu; have hx:=pair_nonneg G p; positivity
 refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (mul_nonneg (turnFee_pos p).le he'); refine le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hk : (coverNumber p.B ((V).addr x|>.support):ℝ) ≤ pitch n p.B + 81) p.exponent_pos.le) ?_; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
include g
private lemma root : p.Regular (expand (echo s)) (arg n G a) ∧ Bill p (0:Site n) (Healthy p.threshold {(0:Site n)}) (repu G p a) (arg n G a):= by
 refine ⟨CouplingShape.reg_scale _ (reg_larger (counter_regular _ _ _) ?_), Bill.mul_left (factor*a) (counter_bill ..)⟩; have he:(echo s).site=0:=s.at_zero; rw [← he]; exact Finset.subset_union_right
local notation "F"=> Fintype.card (Seat n)
-- turnFee ≥1 pay soft separately
abbrev food (G:Gauge)(n:Side)(p:BudgetPoint)(a:ℝ):ℝ:= Fintype.card (Seat n)*(Real.exp ((p.supportExponent+1)*((pitch n p.B:ℝ)+81))*(turnFee p*repu G p a))
abbrev flare (G:Gauge)(n:Side)(p:BudgetPoint)(a:ℝ):ℝ:= Fintype.card (Seat n)*(repu G p a*Real.exp ((p.supportExponent+1)*((pitch n p.B:ℝ)+81)))
lemma go : (V).Knows p (food G n p a) ∧ (Z).Ready p (flare G n p a) :=by
 obtain ⟨hs,hv⟩:= root s a g hc; have hy:= hv.nonneg; have hr(x:I):¬Nonwrapping ((solid s x).support) (solid s x).site:= fun h=> s.call.excess (fun i hi=> by
   have H(x':Site n):=Seat.unwrapped x h x'; have hz:= H i (Finset.mem_union_left _ hi); rw [s.at_zero]; exact hz) -- Seat implicit; define Cont
 have h0:{(0:Site n)} ⊆ expand (echo s):=Finset.singleton_subset_iff.mpr (by rw [← s.at_zero]; exact (enlarges (echo s)).anchor)
 have hx (U:Config G n): ‖discrepancy s a G U‖≤ repu G p a:= by
    unfold discrepancy; split; · simpa using hy
    unfold liquid; by_cases he: Healthy p.threshold {(0:Site n)} U; · rw [masked_eq _ _ _ _ he]; exact Bill.norm hv (l:=[]) (by simp) (by simp) he
    rw [masked_ne _ _ _ _ he,norm_zero]; exact hy
 have hQ : GaugeInvariant (discrepancy s a G) ∧ UsesFinal p.threshold (expand (echo s)) (discrepancy s a G) ∧ Measurable (discrepancy s a G)∧ ∀ U,discrepancy s a G U≠0→ ¬Healthy p.threshold (expand (echo s)) U:= by
    refine ⟨?_,?_,?_,fun U h hh=>h (if_pos hh)⟩
    · intro x U; simp only [discrepancy,liquid,masked,Set.indicator,Set.mem_setOf_eq,Healthy,gauge_flags,hs.symmetry x U]; split_ifs <;> rfl
    · intro U x h he; have hQ:= healthy_reads p.threshold _ _ h0 U x h he; have hl(x:Config G n):liquid n G p a x= if Healthy p.threshold {0} x then arg n G a x else 0:= by
         by_cases hp:Healthy p.threshold {0} x; · rw [if_pos hp]; exact masked_eq _ _ _ _ hp
         rw [if_neg hp]; exact masked_ne _ _ _ _ hp
      rw [discrepancy,discrepancy,hl,hl, healthy_reads p.threshold _ _ (Finset.Subset.refl (expand (echo s))) U x h he, hQ,hs.sites U x h]
    exact Measurable.ite (healthy_closed ..).measurableSet measurable_const (Measurable.ite (healthy_closed ..).measurableSet hs.borel measurable_const)
 have hb : GaugeInvariant (- discrepancy s a G) := by intro t U; simp [hQ.1 t U]
 have hw : UsesFinal p.threshold (expand (echo s)) (- discrepancy s a G):= fun U V' ha he=> congr_arg Neg.neg (hQ.2.1 U V' ha he)
 refine ⟨⟨fun t b=> ⟨Seat.move t b, ?_⟩, fun _=> turnFee p*repu G p a, ?_,?_⟩, ⟨fun t b=> ⟨Seat.move t b, ?_⟩, ?_, fun _=> repu G p a, ?_, ?_⟩ ⟩
 · intro i; refine ⟨rfl,i.spread_move t b _,?_⟩; change arg n G a ∘ (Seat.move t b i).view= _; rw [i.view_move]; rfl
 · intro i; refine ⟨ i.regular hs, i.sup hs (Bill.sup hv (fun U he=> healthy_mono h0 he)), ?_,fun h=> (hr i h).elim⟩; change arg n G a (pull _ _ 1)=0; rw [pull_one_field,meaning]; simp
 · intro x; refine Cost.mono (Cost.finite _ (by exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (turnFee_pos p).le hy))) ?_ ?_
   · intro i; split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (turnFee_pos p).le hy)
     exact le_rfl
   intro i; split; exact rice s a hc i; have hh:= turnFee_pos p; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hh.le hy)
 · intro i; refine ⟨i.spread_move ..,?_⟩; change (- discrepancy s a G) ∘ (Seat.move t b i).view= _; rw [i.view_move]; rfl
 · intro i; exact ⟨Push.Local.invariant_pull hb _ _,Push.Local.uses_pull hw _ _,hQ.2.2.1.neg.comp (continuous_pull ..).measurable,fun x hx h=> hx (show - discrepancy s a G (i.view x)=0 by rw [discrepancy,if_pos ((i.healthy ..).mp h),neg_zero])⟩
 · intro i U; change ‖-discrepancy s a G (i.view U)‖ ≤ _; rw [norm_neg]; exact hx _
 intro x; refine Cost.mono (Cost.finite _ (by positivity)) ?_ ?_; · intro i; split; exact mul_nonneg hy (Real.exp_nonneg _); rfl
 intro i; split; · refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hy; have hp:=p.exponent_pos; gcongr; have he:= Geo.enlarge p (echo s) hc; have he' : coverNumber p.B ((Z).addr i)≤ pitch n p.B+81:= (Seat.visit_count (p:=p) i (expand (echo s))).trans_le (he.trans_eq (by rw [show coverNumber p.B (echo s).support=pitch n p.B from s.call.economical])); exact_mod_cast he'
 positivity
lemma pays (U: Config G n): (V).teller p U - (∑' i:I, (Z).values i U)= a*∑ k, heads p k U:= by
 have hy(i:I): (V).occG p i U - (Z).values i U= (factor*a)*heads p i.2 U:= by
    let t:=i.view U; have h0:{(0:Site n)} ⊆ expand (echo s):=Finset.singleton_subset_iff.mpr (by rw [← s.at_zero]; exact (enlarges (echo s)).anchor)
    have hw:Healthy p.threshold {i.2} U↔ Healthy p.threshold {0} t:=by rw [show {i.2}= i.spread {0} by unfold Seat.spread; simp [affine]]; exact i.healthy ..
    have hT : ∀ k, ‖petals t 0 k‖ = ‖petals U i.2 (PlaqAxes.transform i.1 k)‖:=by
       intro k; unfold t Seat.view; rw [petals_moves,affine,Signed.act_zero,zero_add]; apply reframe_norm
    change masked p.threshold (i.spread (expand R)) (arg n G a ∘ i.view) U - -discrepancy s a G t=_; rw [i.distribute,sub_neg_eq_add]; change masked p.threshold (expand R) (arg n G a) t + discrepancy s a G t=_; rw [show masked p.threshold (expand R) (arg n G a) t + discrepancy s a G t = liquid n G p a t from (by
          by_cases he: Healthy p.threshold (expand R) t; · rw [masked_eq _ _ _ _ he, discrepancy,if_pos he, add_zero,liquid, masked_eq _ _ _ _ (healthy_mono h0 he)]
          rw [masked_ne _ _ _ _ he,discrepancy,if_neg he,zero_add])]; unfold liquid heads; by_cases ht : Healthy p.threshold {i.2} U; · rw [masked_eq _ _ _ _ (hw.mp ht),masked_eq _ _ _ _ ht,meaning G n]; simp_rw [hT]; rw [Equiv.sum_comp (PlaqAxes.transform i.1) (fun i'=>‖petals U i.2 i'‖^2)]
    rw [masked_ne _ _ _ _ ht,masked_ne _ _ _ _ (mt hw.mpr ht),mul_zero]
 unfold Herb.teller; rw [tsum_fintype,tsum_fintype,← Finset.sum_sub_distrib]; simp_rw [hy,← Finset.mul_sum]; rw [Fintype.sum_prod_type]; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; linear_combination a*(∑ k:Site n,heads p k U)*factor_card
end Lapis
end YM.AllOrder.Rosary
