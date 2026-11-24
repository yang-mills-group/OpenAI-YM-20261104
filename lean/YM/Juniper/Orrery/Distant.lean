import YM.Juniper.Orrery.Cut
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Progress.DirectedRecipe UVExtension Height
open Ovens Ovens.Pipes Whirl Tabernacle Dales Flare Deck.Mint
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
/-!
 # Tiny expense of E radius cut after *full* fill on forecast trajectory.
 Special kinetic E labels with very long paths:
 width is POST and p.M ~ log² β; we can pay using actual schedule paths,
 not a localization hypothesis on E norm after reset! Erases any term testing
 too long a region. Long TWIRLS whose region itself fits needn't be zero;
 also won't spoil mask-naturalness despite torus covers (Orrery.Rim).
 Receipts use exponential true support and real unscaled log jets.
 -/
variable {G:Gauge} {c:Side} {s b :ℕ} (P: BudgetPoint)
variable (O:PathData G) {v : Clip} {σ C Λ H:ℝ} (h:O.Bounds v σ C Λ) (he:Geo.Width P v σ)
lemma low_short (i:Collection.Faces c) (hh: i.snd.length O ≤ P.B) : ShortF P.B (Quotes.lowEntry G O P i):= by
    suffices hd:Low.home O i.2 P (0:Site c) ⊆ halo P.B {0} by
      rw [Orrery.short_iff]; intro x hx; obtain ⟨p,hp,rfl⟩:= mem_image.mp hx; rw [halo_spec]; have ht : separation 0 p ≤ P.B:= by simpa only [halo_spec,mem_singleton,exists_eq_left] using hd hp
      refine ⟨_,mem_singleton_self _, show separation (lowEntry G O P i).site (affine i.1.1 i.1.2 p) ≤ _ from ?_⟩; rw [show (lowEntry G O P i).site=affine i.1.1 i.1.2 (0:Site c) from by change i.1.2=_; simp [Lattice.affine],spin_separation]; exact ht
    intro a ha; unfold Low.home at ha; unfold Low.length at hh; cases h:i.snd.2 with
    | inl k => rw [h] at ha; exact ha
    | inr j => rw [h] at ha hh; change (i.2.left O j).length+(i.2.right O j).length ≤ _ at hh; rcases mem_union.mp ha with h'|hx
               · rcases mem_union.mp h' with h'|h'; exact h'
                 exact halo_spec.mpr ⟨_,mem_singleton_self _, (separation_comm _ _).trans_le ((VerifiedReset.slot_length _ _ h').trans (by omega))⟩
               exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_comm _ _).trans_le ((VerifiedReset.slot_length _ _ hx).trans (by omega))⟩
lemma high_short (i:Collection.Spikes c) (hh:i.snd.length O ≤ P.B) : ShortF P.B (highEntry G O i):= by
    intro x hx; obtain ⟨p,hp,rfl⟩:= mem_image.mp hx
    let q:= i.2.term O; let y := (0:Site c); apply (neighbors_mem ..).2; change p∈ q.footprint (0:Site c) at hp
    have ht: separation y p ≤ q.length:= Paths.where_slot y q.leg p ((Paths.atom_foot ..) ▸ hp)
    apply le_trans (b:= separation (0:Site c) p) (le_of_eq ?_) (ht.trans hh); rw [show (highEntry G O i).site=affine i.1.1 i.1.2 (0:Site c) from by change i.1.2=_; simp [Lattice.affine],spin_separation i.1.1 i.1.2 (0:Site c) p]

private lemma sale {ι:Type} (σ:ℝ) (b:ℕ) (hσ:0<σ)(l:ι→ℕ) (g:ι→ℝ) (hg:∀ i,0≤g i) (h:SumBudget (fun i=> g i * Real.exp ((σ/2)*l i)) H):
   SumBudget (fun i=> (if l i≤b then 0 else g i) * Real.exp (((σ/2)/2)*l i)) (Real.exp (-σ/4*b)*H):= by
     apply budget_mono (budget_scale (Real.exp_pos _|>.le) h) (fun i=>mul_nonneg (by split; exact le_rfl; exact hg i) (Real.exp_pos ..|>.le)); intro i; split
     next=> rw [zero_mul]; have ht:= hg i; positivity
     next hh=>
       rw [mul_left_comm,← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hg i); have hx: b ≤ l i:= by omega
       linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr hx) hσ.le]
section fill
local notation "E"=> (Real.exp (-σ/4*P.B))
local notation "L"=> lowEntry G O P
local notation "T"=> highEntry G O
local notation "D"=> (lowBase G v P σ C)
local notation "J"=> (highBase G P σ C)
abbrev qface (v : Clip)(i:Collection.Faces c) := if i.2.length O ≤ P.B then 0 else |i.2.mark O v| * lowCost G P (i.2.length O)
abbrev qspike (i:Collection.Spikes c) := if i.2.length O ≤ P.B then 0 else i.2.price O P
include h he
lemma tariffs : Quotes.anchored P («n»:=c) L (qface P O v) (E*D)∧ Quotes.anchored P (n:=c) T (qspike P O) (E*J):= by
    have hp : P.supportExponent / P.B ≤ (σ/2)/2:= by have ht:= he.2.2; linarith only [ (show P.supportExponent / P.B≤ σ/4 from (div_le_div_of_nonneg_right (by linarith : P.supportExponent ≤ P.supportExponent+1) (by positivity)).trans ht)]
    constructor
    · let z (d:Low) := |d.mark O v| * lowCost G P (d.length O); have hz (d:Low):0 ≤ z d:= mul_nonneg (abs_nonneg _) (low_nonneg ..); intro o; unfold lowBase; rw [mul_left_comm]; exact channel_mass _ (fun i:Low=> i.home O P (0:Site c)) (fun i:Low=> if i.length O≤ P.B then 0 else z i) (fun i=> by split; exact le_rfl; exact hz _) (sale _ _ h.width _ z hz (Geo.low_budget G P O h)) lowCount hp (Geo.low_geometry P O · _) o
    let z (d:High) := d.price O P; have hz (d:High):0 ≤ z d:= High.price_nn ..; intro o; unfold highBase; rw [mul_left_comm]; exact Quotes.channel_mass _ (fun i:High=> i.home O (0:Site c)) (fun i:High=> if i.length O≤ P.B then 0 else z i) (fun i=> by split; exact le_rfl; exact hz _) (sale _ _ h.width _ z hz (Geo.high_budget G P O h)) highCount hp (Geo.high_geometry P O · _) o
variable {α Δ:ℝ}(W:Curtain G c)(hw : Curtain.TidyC W P P.B H)(hδ:P.threshold^2*|Δ| ≤ H) (hx:WilsonStartup.Decent v P) -- hδ maybe earned from Budget
local notation "F"=> Collection.shelves W.book O P
local notation "F!"=> Collection.fill W.book O v P W.stamp α Δ
local notation "Z"=> (Collection.incoming W.book O P)
local notation "K"=> Collection.archive W.book O v W.stamp α Δ
local notation "A"=> (turnFee P*(|Δ| * P.threshold^2))
local notation "M"=> (turnFee P*(|α+Δ| * P.threshold^3))
local notation "ε"=> Sum.elim (0:ℕ→ℝ) (Sum.elim (fun i=> A*(qface P O v i)) (fun i:Collection.Spikes c=> M * qspike P O i))
local notation "G'"=> (numbering (Collection.EKey c))
include hw hδ hx
omit h he hx hw hδ in
include P in
private lemma rebate_zero' (j:RegularAddress c) : Residual.rebate j (0:Config G c→ℝ)=0:= by -- include bloat
    have he:= (Residual.label_sub j (0:Config G c→ℝ) 0 (0:Config G c→ℝ) P (show P.Regular j.support (0:Config G c→ℝ) from unspent ..) (show P.Regular j.support (0:Config G c→ℝ) from unspent ..)).1; rwa [sub_self,sub_self] at he
set_option maxRecDepth 6000
set_option maxHeartbeats 600000 in
lemma sticker (hG:G.Simple) : Orrery.Payment P ((F).reg) ((F!).regular - pris P.B (F).reg ((F!).regular)) (E*regularNeed G P v σ C α H):= by
   obtain ⟨l',hl,h'l⟩:= hw.income; let f : Collection.EKey c→ℝ := ε
   have hb (i:Collection.EKey c): P.supBounds (Z i).site (Z i).support (K i) (quoteE O P v α Δ l' i) := Collection.Local.quote_regular hG h hx α Δ (fun i=> (h'l i).2) (fun i=> (h'l i).1) i
   have ht:=Collection.turnFee_pos P|>.le; have hp:=P.threshold_pos.le
   have hE i : P.supBounds (Z i).site (Z i).support ((K-pris P.B Z (K)) i) (f i):= by
     rcases i with i|i|i
     · have he := hw.frames i; by_cases hi:i∈ W.sequence
       · rw [Pi.sub_apply, Orrery.pris, if_pos (?_ : ShortF P.B (Z (.inl i))),sub_self]; exact no_cost ..
         unfold ShortF; intro y hy; obtain h'|h':=mem_union.mp hy; exact he hi h'; obtain ⟨v,hv,h'⟩:= halo_spec.mp h'; rw [mem_singleton.mp hv] at h'; exact (neighbors_mem ..).mpr (h'.trans hx.radius)
       have hh : W.stamp.logRead i=0 := not_ne_iff.mp (mt (W.truncation i) hi); have hm: K (.inl i)=0:= by unfold Collection.archive; dsimp only [Sum.elim_inl]; rw [hh]; exact rebate_zero' P (W.book.reg i) -- remove includes
       rw [Pi.sub_apply,pris,hm]; split <;> (simp only [sub_zero]; exact no_cost ..)
     · by_cases hi : i.snd.length O ≤ P.B
       · have hQ: f (Sum.inr (Sum.inl i))=0:= by change A * (qface P O v i)= 0; rw [qface,if_pos hi,mul_zero]
         rw [hQ,Pi.sub_apply,pris,if_pos (show ShortF P.B (Z (Sum.inr (Sum.inl i))) from Orrery.low_short P O i hi),sub_self]; exact no_cost ..
       have hQ: f (Sum.inr (Sum.inl i))=quoteE O P v α Δ l' (.inr (.inl i)):= by change A*(qface P O v i)= _; rw [qface,if_neg hi]; rfl
       rw [hQ,Pi.sub_apply,pris]; split; · rw [sub_self]; exact VerifiedReset.sup_le (no_cost ..) (hb _).1
       rw [sub_zero]; exact hb _
     by_cases hi : i.snd.length O≤ P.B
     · have hQ: f (Sum.inr (Sum.inr i))= 0:= by change M * (qspike P O i)= 0; rw [qspike,if_pos hi,mul_zero]
       rw [hQ,Pi.sub_apply,pris, if_pos (show ShortF P.B (Z (Sum.inr (Sum.inr i))) from Orrery.high_short P O i hi),sub_self]; exact no_cost ..
     have hQ: f (Sum.inr (Sum.inr i))=quoteE O P v α Δ l' (.inr (.inr i)):= by change M*(qspike P O i)= _; rw [qspike,if_neg hi]; rfl
     rw [hQ,Pi.sub_apply,pris]; split; · rw [sub_self]; exact VerifiedReset.sup_le (no_cost ..) (hb _).1
     rw [sub_zero]; exact hb _
   refine ⟨f∘ G',fun j=> hE (G' j),fun x=>?_⟩
   have hD : Quotes.anchored P Z f (E*regularNeed G P v σ C α H) := by
     intro y; obtain ⟨hv,h₁⟩:= tariffs P O (c:=c) h he; have hT: SumBudget (fun i:ℕ=> if (Z (Sum.inl i)).site=y then P.mass (Z (.inl i)).support 0 else 0) 0:= by simp [SumBudget,BudgetPoint.mass]
     refine budget_loosen (Cost.sum hT (Cost.sum (Quotes.anchored_scale (r:=A) (by positivity) hv y) (Quotes.anchored_scale (r:=M) (by positivity) h₁ y))) ?_
     have hC:= Cost.nonneg h.three; obtain ⟨hv,hv',-⟩:= Collection.budget_pos P G v h.width hC
     have hr : 0 ≤ resetFee G P:=by unfold resetFee; have hz:=Residual.loss_pos G P; positivity
     have hδ' :0≤H:= (show 0 ≤ P.threshold^2 * |Δ| by positivity).trans hδ
     unfold Collection.regularNeed
     apply le_trans _ (mul_le_mul_of_nonneg_left (show (turnFee P*(H*D+(|α| *P.threshold^3+H)*J)) ≤ resetFee G P*H + turnFee P*(H*D+(|α| *P.threshold^3+H)*J) from le_add_of_nonneg_left (mul_nonneg hr hδ')) (Real.exp_pos _|>.le))
     nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδ hv) (mul_nonneg (show 0≤ E from (Real.exp_pos _).le) ht),mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Collection.fresh_allow (α:=α) hδ) hv') (mul_nonneg (show 0 ≤ E from (Real.exp_pos _).le) ht)]
   exact Cost.equiv G' (hD x)
   -- goal pending
end fill
end YM.Juniper.Orrery
