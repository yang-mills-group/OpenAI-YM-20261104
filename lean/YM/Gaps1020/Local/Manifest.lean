import YM.Gaps1020.Local.Dock
import YM.Gaps1020.Local.CheckpointB
set_option autoImplicit false
noncomputable section
namespace YM.Overlay.GapsLocal
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Push Next.Foundations AbsoluteSums GridApprox.Nil
open MergeProof Merge Accent Extra.Iteration
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n m:Side}{V:Type}[Fintype V] [Nonempty V][DecidableEq V]{B:Marker.Census V}{R: RG.Rep G n}{u d c k r:ℝ}{p N:ℕ}(D:Bands B R)(w:V→ℝ)
-- use Donor Towed/Payments. Assemble *all* degrees at once. Billing raw
-- dictionary CoverNumber including members with no positive entries; Hits
-- may set size of K-entry to 0 thereby. ExtraTests still applied on it!
-- `colour` & `foam` grouped but answer theorem keeps `Active`/`Radial`
-- in original (before grouping); no estimation is deduced in that norm
-- by pretending equality with a finite representation.
def colour := tally D.support D.ray
def foam := tally (barcode R.activities ∘ Prod.fst) (uncurry D.tagged)
def perStep (p B:ℕ) := (p:ℝ)*Extra.Multi.siteFactor B
local notation "a" => R.p.B
local notation "b" => R.p.threshold
local notation "e" => R.p.supportExponent-4
local notation "Φ" => D.origins
variable {w}(h:D.Active) (hf:D.Radial w u c d r)(ht:Extra.Multi.Occupancy D.origins N)
omit [Fintype V] [Nonempty V] in
private lemma blank (p:B.Mode)(hp:p.val.Nonempty)(t:ℂ): (Poly.send p t).part B.quiet = 0 := by
   rw [Poly.part_send,if_neg]; intro h; exact hp.ne_empty (Subtype.ext_iff.mp h.symm)
include h hf ht
-- Packages use Towed (marker-by-mode sum), Rooted → any-hit.
omit h hf in
private lemma rootedFunds {X:Type}(v:X→Support n)(k:X→B.Mode)(F:X→ Config G n→ℂ)(w:V→ℝ)(f:X→ℝ)(hw:∀ i,0<w i)
     (h:∀ i,(k i).val.Nonempty)(hp:∀ i,0≤f i∧∀ U,‖F i U‖≤ f i)(he:∀ i:V,SumBudget (fun j=> if i∈(k j).val then Poly.toll w (k j)*R.p.mass (v j) (f j) else 0) c)(hf:∀ i,0<f i→∃ x∈ (k i).val,Φ x∈v i):
    Towed w v (fun i U=> Poly.send (k i) (F i U)) a e (perStep N a*c):=by
   let z i:=Poly.toll w (k i)*R.p.mass (v i) (f i)
   let s i:=Poly.toll w (k i)*f i
   have hu i:s i≤z i:= mul_le_mul_of_nonneg_left (R.p.loMass _ _ (hp i).1) (Poly.worth hw _).le
   have hr i:0≤ s i:= mul_nonneg (Poly.worth hw _).le (hp _).1
   have hi : Extra.Multi.Rooted (fun i=>(k i).val) v a R.p.supportExponent s c:=by
      intro i; convert! he i using 1; funext j; split; next he=> unfold BudgetPoint.mass s; ring
      next h=> rfl
   have he := Overlay.per_system (fun i=> (hr i).trans (hu i)) h he
   refine ⟨s,he.2.1.of_nonneg_of_le hr hu, Extra.Multi.root_hit ht hr (budget_nonneg (hi Classical.ofNonempty)) (mode:=(fun i=>(k i).val)) ?_ (hi.mono hr (fun _=> le_rfl) (by linarith) le_rfl),fun i=> satin (F i) _ (f i) (hp i).1 (hp i).2⟩
   intro i h; exact hf i (pos_of_mul_pos_right h (Poly.worth hw _).le)
private lemma baseE : Towed w D.support D.ray a e (perStep N a*c):=by
   obtain ⟨v,hv,h0⟩:=hf.bulk
   apply rootedFunds (D:=D) ht _ _ (fun i=> masked b (D.support i) (D.H i)) w v hf.pure h.proper ?_ h0 (fun i _=> by obtain ⟨j,hj⟩:= h.proper i; exact ⟨j,hj,h.pins i j hj⟩)
   intro i; refine ⟨(hv i).1,fun U=>?_⟩; obtain ⟨j,hj⟩:= h.proper i
   by_cases he: Healthy R.p.threshold (D.support i) U; rw [masked_eq _ _ _ _ he]; exact ((hv i).2 j hj).2 U he [] (by simp) (by simp)
   rw [masked_ne _ _ _ _ he,norm_zero]; exact (hv i).1
private lemma baseK : Towed w (Prod.fst ∘ barcode R.activities ∘ Prod.fst) (uncurry D.tagged) a e (perStep N a*(d*r)):=by
   obtain ⟨v,hv,h0⟩:= hf.hits; let f (j:ℕ×ℕ):= if D.entries j.1 j.2=0 then 0 else v j
   have hV(j:ℕ×ℕ):0≤f j ∧ f j ≤ v j∧∀ U,‖D.entries j.1 j.2 U‖ ≤ f j:=by
      unfold f; split; next h=> exact ⟨le_rfl,(hv j.1 j.2).1, fun i=> by rw [h]; simp⟩
      next h=> exact ⟨(hv ..).1,le_rfl,(hv ..).2⟩
   apply rootedFunds D ht (Prod.fst ∘ barcode R.activities ∘ Prod.fst) _ (uncurry D.entries) _ f hf.pure (fun j=>h.occurs j.1 j.2) (fun i=> ⟨(hV i).1,(hV i).2.2⟩) ?_ ?_
   · refine fun i=> budget_mono (h0 i) (fun i=> ?_) (fun j=>?_)
     · split; exact mul_nonneg (Poly.worth hf.pure _).le ((hV _).1.trans (R.p.loMass _ _ (hV _).1)); exact le_rfl
     split; next h=> exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hV j).2.1 (Real.exp_pos _).le) (Poly.worth hf.pure _).le
     next h=> exact le_rfl
   intro i hi; obtain ⟨j,hj⟩:= h.occurs i.1 i.2; exact ⟨j,hj,h.retained i.1 i.2 (fun h'=>by simp [f,h'] at hi) _ hj⟩
omit ht hf [Nonempty V] in
private lemma baseEB (i:ℕ): Burns Φ (D.support i) (D.ray i) b:=by
   refine ⟨⟨fun _ _ ht hy=> congr_arg (Poly.send _) (Push.Local.uses_mask _ (h.regular i).sites _ _ ht hy),fun g U=> congr_arg (Poly.send _) (Push.Local.invariant_mask (h.regular i).symmetry _ _ g U),fun j=> ?_,fun U => scope_send _ _ _ (fun j hj=> h.pins i j hj)⟩,fun U he=> by by_contra h; simp [Bands.ray,masked,h] at he,fun _=> blank _ (h.proper _) _⟩
   simp_rw [Bands.ray,Poly.part_send]; split; next h' => exact masked_measurable _ _ _ (h.regular i).borel
   next he=> exact measurable_const

omit ht hf [Nonempty V] in
private lemma baseKF (i j:ℕ) : Flow Φ (barcode R.activities i) (D.tagged i j) b∧ ∀ U,(D.tagged i j U).part B.quiet=0:=by
   let v:= D.entries i j; let X:= R.activities.forced i; let k:= D.marks i j
   refine ⟨⟨⟨fun _ _ hU hv=> congr_arg (Poly.send _) (h.inspects i j _ _ hU hv), fun _ _=> congr_arg (Poly.send _) (h.invi i j _ _),fun k=>?_, fun U=> ?_⟩,fun U hp=>?_⟩,fun U=> blank _ (h.occurs i j) _⟩
   · simp_rw [Bands.tagged,Poly.part_send]; split; exact h.meas i j; exact measurable_const
   · by_cases hh:v=0; change Scoped _ (Poly.send k (v U)); rw [hh,Pi.zero_apply,Poly.send_zero]; exact fun _ _=>rfl
     exact scope_send _ _ _ (fun k hk=> h.retained _ _ hh _ hk)
   exact ⟨(h.keeps i j U (fun hy=> hp (by unfold Bands.tagged; rw [hy,Poly.send_zero]))).1,X.inventory_ne,X.inventory_sup⟩

lemma paysColour : Towed w id (colour D) a e (perStep N a*c) ∧ ∀ i,Burns Φ i (colour D i) b:= ⟨towing D.support _ (baseE D h hf ht) hf.pure,fun _=> transitE D.support (r:=id) (baseEB D h) (fun U=>(D.bulkBound h hf U).1) _⟩
lemma paysFoam : Towed w Prod.fst (foam D) a e (perStep N a*(d*r))∧ ∀ i,Flow Φ i (foam D i) b ∧ ∀ U,(foam D i U).part B.quiet=0:=by
   have h:=baseK D h hf ht; -- shadow
   refine ⟨towing _ (uncurry D.tagged) h hf.pure, fun i=>⟨transitK _ (r:=id) (fun i:ℕ×ℕ=> (baseKF D ?_ i.1 i.2).1) (fun U=> (h.repair hf.pure U).2) _, fun U=>?_⟩⟩
   · assumption
   unfold foam tally; rw [Poly.share]; exact (tsum_congr (fun i=> (baseKF D ‹D.Active› ..).2 U)).trans tsum_zero
   exact (h.repair hf.pure U).2.comp_injective Subtype.val_injective

section math
variable {δ τ:ℝ} (U:Config G n)(hV:R.activities.Valid R.p δ τ)
include hV
local notation "α" => barcode R.activities
local notation "M" => Accent.Mach B D.units
-- reads back the **same** memory (all addresses); no replacing forced
-- occurrence by a field. This is for transfer of `Outfit` to `D` only.
-- `colour` and `foam` are used *internally* to lend the estimates and may
-- not be substituted as differently guarded Banks. Preserve post shelves
-- & costs. No assumption that norm invariant to `proxy` equivalences.
-- Read Repeats.Extra for marches when physically propagating symmetry.
private lemma cram_fibre (i:Box n) : cram (barcode R.activities) (fun i=>D.each i U) i= bar R.activities B U i+foam D i U:=by
   let f(i:ℕ):= Poly.send B.quiet ((R.activities.K i U):ℂ); let F:= fun i:ℕ×ℕ=> D.tagged i.1 i.2 U; let Q i:= ∑' j:ℕ,F (i,j)
   have ht': Summable F:= ((baseK D h hf ht).repair hf.pure U).2; let L:= ℕ
   let T I := {j:L // α j=I}; let t := T i; let G₀ := {j:L×ℕ // α j.1=i}
   have HS: Summable fun j=>Poly.price w (f j):=by simp_rw [f,Poly.solo, Poly.quiet_toll, Complex.norm_real,one_mul]; exact (mass_crest _ hV U).norm
   have he:Summable fun j:t=> f j.val:= (Poly.budgeted hf.pure HS (f:=f) (fun _=> le_rfl)).1.comp_injective Subtype.val_injective
   have h': Summable fun j:t×ℕ=> F (j.1.val,j.2):= ht'.comp_injective (i:= Prod.map (fun i:t=>i.val) (@id ℕ)) (Subtype.val_injective.prodMap injective_id)
   let g:G₀≃ t×ℕ:={ toFun:=fun j=>(⟨j.val.1,j.property⟩,j.val.2), invFun:=fun j=>⟨(j.1.val,j.2),j.1.property⟩, left_inv:=fun _=>rfl,right_inv:=fun _=>rfl }
   change ∑' j:t,(f j.val +Q j.val)=bar R.activities B U i+(∑' j:G₀, F j.val)
   rw [Summable.tsum_add];
   · unfold Q
     rw [show (∑' i:t,∑' j:ℕ,F (i.val,j))=(∑' j:t×ℕ,F (j.1.val,j.2)) from h'.tsum_prod.symm,show (∑' j:G₀,F j.val)=∑' j,F ((g.symm j).val) from (g.symm.tsum_eq (fun j:G₀=>F j.val)).symm]; refine congr_arg (·+(∑' j:t×ℕ,F (j.1.val,j.2))) ?_
     ext p; rw [Poly.share he]; unfold f bar profile; by_cases hp:p=B.quiet <;> simp [cram,Poly.bead, hp]
     rfl
   · exact he
   exact h'.prod
lemma regain : D.density U= Poly.pass M*((Real.exp (R.exponent U):ℂ) • (Poly.pass (∑ j,colour D j U) * Accent.field (fun i=>Accent.bar R.activities B U i+foam D i U) (RG.flags R.p.threshold U))):=by
   unfold Bands.density
   have he:= D.bulkBound h hf U; have hc : D.extra U=M+∑ i,colour D i U:=by
      unfold Bands.extra; have hk:= (Accent.border D.support he.1).tsum_eq
      rw [tsum_fintype] at hk; rw [← hk]; rfl
   have hK:=Accent.rock_out R.activities R.p U (fun i=>D.each i U) hf.pure (D.baseBound h hf hV U).2.2.1 -- extract? nesting!
   have hA:(∑ i,colour D i U).part B.quiet=0:=by rw [Poly.part_sum]; exact Finset.sum_eq_zero (fun i _=> ((paysColour D h hf ht).2 i).sil U)
   rw [hc,Extra.Trajectories.pass_add (Accent.mute B D.units) hA,← funext (cram_fibre D h hf ht U hV), hK,mul_smul_comm,mul_assoc]; rfl
omit h hf ht hV
open Menu in
structure Shard {ι:Type} [Fintype ι](q:ι→Hat B R)(w:V→ℝ)(p:ℝ):Prop where
   price : Menu.Offer D.origins q w R.p.B (R.p.supportExponent-4) p
   trays E U : (∑ i,if (q i).M.crest=E then odour (q i) U else 0)=colour D E U
   forced I U : (∑ i,fragrance (q i) U I)=foam D I U
   completes : D.density = YM.GapsLocal.Full.given q D.units
include h hf ht hV
lemma bait (hA:Menu.Arsenal R) {p:ℝ}(he:2*(perStep N a*c)+2*(perStep N a*(d*r)) ≤ p): ∃ (ι:Type) (_:Fintype ι) (q:ι→Menu.Hat B R), Shard D q w p:=by
   obtain ⟨hy,hy'⟩:= paysColour D h hf ht; obtain ⟨hb,hb'⟩:= paysFoam D h hf ht
   obtain ⟨ι,u',q,hq,he,hG⟩:= Menu.GapsLocal.drydock hy' hb' hy hb hf.pure hA -- shadow
   have hL(U):(∑ i, Menu.odour (q i) U)= ∑ i, colour D i U:=by
      simp_rw [← he]; rw [Finset.sum_comm]; simp
   exact ⟨ι,u',q,⟨hq.fatten ‹_≤p›,he,hG,funext fun U=> by unfold YM.GapsLocal.Full.given; rw [hL]; simp_rw [hG]; exact regain D h hf ht U hV⟩⟩
end math
end YM.Overlay.GapsLocal
