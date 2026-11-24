import YM.QuadraticLocal.Startup.Gain
import YM.QuadraticLocal.Travel
/-!
# Access to the unrelated-order, unscaled insertion bootstrap.

`Lesson` for full analytic path packets, behind fixed masks. Evaluates the *unnormalized*
 inserted polynomial at true group globally. Provides flag lifts in same payload for installation
 onto Actor berth. hit accounting in `Honored` envelopes & per-slot tolls, not mere on-chart.L1.
 Sup test mass. `Exert` power.N may be any ℕ fixed.Setup.Stage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spes
open Function Filter Finset Lattice Wilson RG Marker MeasureTheory Push Push.AbsoluteSums Animals
open Affinity Display Integration.LocalComparison ComparisonDensity.Address Comparison.Density.RenderM
open AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection Precision Exterior Extra.Iteration Next.Scheduling Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V I:Type}[DecidableEq V]{R:Census V}{G:Gauge}{n:Side} {k r d s ℓ:ℕ}
variable (D: V → Orbit)(P:BudgetPoint)
set_option quotPrecheck false
local notation "C"=> (fun v=>(D v).Mood)
local notation "T"=> Affinity.Full (E:=C)
local notation "X"=> Display.Lens.portion D
local notation "WX"=> Wallet X
variable (K:∀ v,Submodule ℂ (D v).Mood)(L:V→Support n)(o:V→Site n)
structure Screen (I:Type) (R:Census V) (G:Gauge)(n:Side) where
    mode : I→ R.Mode
    positive : ∀ i, mode i≠ R.quiet
    power : I→ℤ
    rank : I→ℕ
    parcel : ∀ i: I, Token G n C (rank i)
namespace Screen
variable {D L K}
variable (H:Screen D I R G n)
def paints (i:I)(t:TestSpace D) (g:ℝ): Config G n→ℂ:= (↑(g^(H.power i)):ℂ) • (H.parcel i).read t
def rawTerms (i:I)(t:TestSpace D)(g:ℝ)(U:Config G n):= Poly.send (H.mode i) (H.paints i t g U)
-- for arbitrary real rows at assembly, define AUTH independent of p.
variable (L K)
structure Rooted (w: V→ℝ)(c:ℝ)(d:ℕ):Prop where
    leg i : Legal K L (H.mode i) (H.parcel i)
    head v : o v ∈ L v
    size i : (H.parcel i).fall ≤ d ∧ (H.parcel i).plot⊆neighbors d (H.parcel i).root
    money : ∀ x: Site n, SumBudget (fun i=>if x∈(H.parcel i).plot then Poly.toll w (H.mode i)*(H.parcel i).coin else 0) c
-- covenant high. stronger than ≥p+1 wall each individual term because for mixed modes we want to buy smallness PER constituent. Use for launch.L.G grades. budgets route can also require alternative stronger high envelope for copies to avoid combin.R.Poly
structure Loft (m r q: ℕ):Prop where
    rank i : H.rank i≤ r
    price i : (H.power i).natAbs≤ q
    weight i : (m:ℤ) * (H.mode i).val.card ≤ H.power i+(H.rank i:ℤ)
variable {K L}{w: V→ℝ} {b c η:ℝ}
variable (h:Rooted K L o H w c d) -- likely order H L K
include h
lemma packed i : (H.parcel i).root∈(H.parcel i).plot:= (h.leg i|>.wears (0:T)).2 (Finset.mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩)
-- Full masks
variable (g:ℝ)
def render : Lamps T I G P o R where
   mode := H.mode
   live := H.positive
   address i := ⟨(H.parcel i).root,(H.parcel i).plot,H.packed o h i⟩ -- order?
   roots i v hv:= (h.leg i|>.frame v hv) (h.head v)
   nominal t i:= H.paints i t g
   legal t i:= regular_smul _ (Legal.honor P K L _ (h.leg i) t)
   clear _:=False
   pure _ _ _ hv:= hv.elim
local notation "Λ"=> H.render P o h g
local notation "LH"=> (Λ).pullback (readBack X)
lemma esteemed (i:I) (U:Config G n): Eligible K (H.mode i).val (fun t=> (Λ).nominal t i U):= (Legal.reads K L _ (h.leg i) U).cs _
open Canopy
local notation "ΠH"=> (Λ).nominal
local notation "ρ"=> (Λ).ground
-- Shifts exactly for OFF MASK. full U true near.Update
variable [Countable I]
def off (t:T)(i:I)(U:Config G n):= if Healthy P.threshold (H.parcel i).plot U then 0 else H.rawTerms i t g U -- h unused?
local notation "g'"=> H.off P g

def shift: ShiftRows (Wallet (Lens.portion D)) I G P o R where
    place i:= ⟨ρ i,⟨(H.parcel i).root,H.packed o h i⟩⟩
    soap t:=g' (readBack X t)
    cost t i:=by
      let f:=ΠH (readBack X t) i; let s:=ρ i; let hf: P.Regular s f:= (Λ).legal _ _
      refine ⟨fun a U=> ?_,?_, fun U V hx ht=> ?_,fun U A ha v hv=> ?_⟩
      · unfold off rawTerms; rw [show H.paints i _ g (Lattice.gauge a U)=_ from hf.symmetry a U]; unfold Healthy; rw [gauge_flags]; rfl
      · change Measurable (fun U=> if Healthy P.threshold s U then (0:Poly R) else Poly.send (H.mode i) (f U)); exact Measurable.ite (healthy_closed _ _).measurableSet measurable_const ((Overlay.Bands.sends _).measurable.comp hf.borel)
      · have hy:Healthy P.threshold s U = Healthy P.threshold s V:=by unfold Healthy; simp only [Finset.disjoint_iff_inter_eq_empty]; rw [ht]
        unfold off; rw [show Healthy P.threshold ((H.parcel i).plot) U=Healthy P.threshold ((H.parcel i).plot) V from hy]; unfold rawTerms; rw [show H.paints i _ g U= _ from hf.sites U V hx]; rfl
      unfold off at ha; split at ha; contradiction; unfold rawTerms at ha; rw [Poly.part_send] at ha; split at ha; subst A; exact (Λ).roots _ _ hv; exact (ha rfl).elim
    clean t i U h:=by unfold off at h; split at h; contradiction; exact ‹¬ Healthy P.threshold (H.parcel i).plot U›
    skip t i U:=by unfold off rawTerms; split; rfl; rw [Poly.part_send, if_neg (H.positive i).symm]
    single t i U:= by
       unfold off; split; · rw [mul_zero]
       next ht=> ext q; unfold rawTerms; change (Poly.prod (Poly.send _ _) (Poly.send _ _)).part q=0; rw [Poly.cart,if_neg (show ¬(Poly.merges (H.mode i) (H.mode i) q) from fun hx=> H.positive i (Subtype.ext (disjoint_self.mp hx.1)))]
local notation "Δ"=> H.shift P o h g
lemma holds i U : Stencil L (Lens.portion D) K ((Δ).place i).val (fun t=>(Δ).soap t i U):= by
    refine ⟨fun q=>?_⟩; change Addressable _ _ _ _ q.val (fun t=> (g' _ i U).part q); unfold off rawTerms; split
    next=> simp_rw [Poly.part_nil]; exact Addressable.gone
    next=>
      simp_rw [Poly.part_send]; split; next h'=> subst q; exact ⟨Affinity.Eligible.restrict _ (H.esteemed P o h g i U), fun U _ v hv=> (h.leg i).frame v hv⟩
      next=> exact Addressable.gone
variable [Fintype I]
def log (t:T)(U):= ∑ i,H.rawTerms i t g U
lemma log_io (t: Wallet (Lens.portion D))(U: Config G n): (H.log g (readBack X t) U) = (LH).log t U+(Δ).log t U:=by
   unfold log Canopy.ShiftRows.log Lamps.log; rw [tsum_fintype,tsum_fintype,← Finset.sum_add_distrib]; refine sum_congr rfl fun i _=>?_
   change H.rawTerms i (readBack X t) g U= Poly.send _ (((Λ).pullback _).light t _ U)+g' _ i U; unfold off; split_ifs with he
   next ht=> rw [add_zero]; unfold Lamps.light; rw [if_neg (fun ht: ((Λ).pullback (readBack X)).clear i=> ht), masked_eq _ _ _ _ (show Healthy P.threshold (((Λ).pullback (readBack X)).ground i) U from he)]; rfl -- edit ht
   next ht=> unfold Lamps.light; rw [if_neg (fun ht: ((Λ).pullback (readBack X)).clear i=> ht),masked_ne _ _ _ _ (show ¬ Healthy P.threshold (((Λ).pullback (readBack X)).ground i) U from he),Poly.send_zero,zero_add]
-- expose prices via height helper if displacement spans. Pose cover via `slot` extension.
variable (w':V→ℝ) (hw:∀ v,0<w v)
open Ac Legal
omit h [Countable I] [Fintype I] in
private lemma baseNN :0 ≤ baseCost P G k d r:=by
   unfold baseCost; have hp:= P.threshold_pos; have h :0≤ Wages.startup G k P.power P.order:= by unfold Wages.startup; have ht:=lt_of_lt_of_le zero_lt_one (Wages.slot_ge G P.power P.order 0); positivity
   positivity
-- effective payment: w scaling common C per slot. y.Z norm.R.Sample. Lenses.Sequenced
local notation "v'"=> fun i=>b*w i
local notation "τ"=> (P.supportExponent)
local notation "S"=> (LH).ground
private lemma radius i (he:P.B≥d): coverNumber P.B (H.parcel i).plot ≤ 1:=by
    let x:= (H.parcel i).root; apply le_trans (Corona.cover_mono ((h.size i).2.trans (show neighbors d x⊆ neighbors P.B x from Corona.halo_mono he Subset.rfl)) P.B)
    refine le_trans (Corona.list_cost P.B («X»:=_) (D:={x}) ⟨Finset.Subset.refl _,Corona.ship_halo P.B ?_⟩) (by simp); intro i hi j hj; rw [Finset.mem_singleton.mp hi, Finset.mem_singleton.mp hj]
variable (he:d ≤ P.B)(hb:0<b) (hg:0<g)(hη:0≤ η)
local notation "S'"=> fun i=>(H.parcel i).plot
local notation "s'"=> fun i=> H.mode i
local notation "ξ"=> fun i=> Poly.toll v' (H.mode i)
local notation "dμ"=> fun i=> Poly.toll w (H.mode i)
local notation "gσ"=>fun i=>g^(H.power i)
local notation "A'"=> fun i=> (H.parcel i).coin
local notation "vσ"=>fun i=>baseCost P G (H.rank i) d d
local notation "u'"=>fun i=> (b:ℝ)^(H.mode i).val.card
include he hb hg hw hη h
private lemma utility (x':I→ℝ) {a:ℝ}(ha:0≤a)(hx:∀ i,0≤x' i)(hq:∀ i,u' i*x' i*Real.exp a ≤ η): Hit (fun i=>(H.parcel i).plot) P.B (fun i=>ξ i*(x' i*A' i)) a (η*c):=by
    have hz(i): Poly.toll v' (H.mode i)=(u' i)*(dμ i):=by unfold Poly.toll; rw [prod_mul_distrib]; simp
    intro x; apply budget_mono (budget_scale hη (h.money x)); intro i
    · split; exact mul_nonneg (mul_nonneg (Poly.worth (fun v=>mul_pos hb (hw v)) _).le (mul_nonneg (hx _) (h.leg _|>.positive))) (Real.exp_pos _).le; rfl
    intro i; split
    next=>
       change Poly.toll v' _ * _ * _ ≤ _; rw [hz]; let s:= coverNumber P.B ((H.parcel i).plot);
       have hZ:= mul_le_mul_of_nonneg_left (by exact_mod_cast H.radius P o h i he : (s:ℝ)≤1) ha; have hZ:Real.exp (a* s)≤Real.exp a:= Real.exp_monotone (hZ.trans_eq (mul_one a)); let w':= dμ i * A' i; have hb':0≤ w':= mul_nonneg (Poly.worth hw _).le (h.leg i|>.positive); have hI:0≤ u' i * x' i:= mul_nonneg (pow_nonneg hb.le _) (hx _)
       calc _ = ((u' i)*(x' i)* Real.exp (a*s))* w':= by unfold w'; dsimp only; ring
            _ ≤ η * w' := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hZ hI).trans (hq i)) hb'
    next=>rw [mul_zero]
lemma litPays (hz: ∀ i, (b:ℝ)^(H.mode i).val.card * (g^(H.power i)* baseCost P G (H.rank i) d d)*Real.exp P.supportExponent ≤ η) : (LH).Paid (fun i=>b*w i) P.B τ (η*c) := by
    let v i := gσ i * vσ i; have he' i:0≤v i:= mul_nonneg (zpow_nonneg hg.le _) (baseNN P); refine ⟨fun i=>v i * A' i,fun i=>mul_nonneg (he' _) (h.leg _|>.positive),?_,H.utility P o h g hw he hb hg hη _ P.exponent_pos.le he' hz⟩
    intro i t x hx; let T₀:=H.parcel i; let f:= T₀.read (readBack X t); have hz0:P.supBounds x (S' i) f ((vσ i)* T₀.coin):= Legal.mantle P K L T₀ (h.leg i) t _ rfl (h.size _).1 (h.size _).2 x hx
    change P.supBounds x _ (( (↑(gσ i):ℂ)) • f) ((gσ i * vσ i)* A' i); rw [mul_assoc]; apply Push.Local.bound_weaken (bound_smul _ hz0); rw [Complex.norm_real,Real.norm_of_nonneg (zpow_nonneg hg.le _)]
lemma shifted (hz: ∀ i : I, (b:ℝ)^(H.mode i).val.card * (g^(H.power i)* (2* (2:ℝ)^(H.rank i)))*Real.exp (P.supportExponent+1) ≤ η) : (Δ).Budget v' P.B (P.supportExponent+1) (η*c):=by
    let v i:= gσ i * (2*(2:ℝ)^(H.rank i)); have h0 i:0≤ v i:= mul_nonneg (zpow_nonneg hg.le _) (by positivity); let f i:= v i * A' i; have hf i:0≤ f i:= mul_nonneg (h0 i) (h.leg _|>.positive); let Tp i:= Poly.send (H.mode i) (↑(f i)); refine ⟨ Tp,?_,?_⟩
    · intro i t U j; unfold Tp; rw [Poly.part_send]; have hu: ‖(H.paints i (Affinity.readBack X t) g U)‖≤ f i:=by
         let a':=H.parcel i; obtain ⟨hv,hv'⟩:= Legal.sizing K L a' (h.leg i) t _ rfl; change ‖(↑(gσ i):ℂ)* a'.read _ U‖ ≤ _; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (zpow_nonneg hg.le _)]; refine (mul_le_mul_of_nonneg_left (Legal.beyond _ _ U hv hv') (zpow_nonneg hg.le _)).trans_eq ?_; unfold f v; dsimp only; ring
      change ‖(g' (readBack X t) i U).part j‖ ≤ _∧_; unfold off rawTerms; split
      next=> by_cases hv:j=H.mode i; rw [if_pos hv]; exact ⟨by simpa using hf i,rfl⟩; simp [if_neg hv]
      next=> rw [Poly.part_send]; by_cases hv:j=H.mode i; · simp_rw [if_pos hv]; exact ⟨hu,rfl⟩
             simp [if_neg hv]
    convert H.utility P o h g hw he hb hg hη v (a:=P.supportExponent+1) (by have := P.exponent_pos;linarith) h0 hz using 1
    · rfl
    funext i; exact (Poly.solo ..).trans (congr_arg (_*·) ((Complex.norm_real _).trans (Real.norm_of_nonneg (hf i))))
end Screen
end YM.QuadraticLocal.Spes
