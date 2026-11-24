import YM.OPE.Strobe.Show
/-! # Fixed terminal: Flex resource consumes expense at low support exponent E−3. Spiker port. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
section
omit H
private lemma razor (X:Rep G n) (M:Leaf X)(U:Config G n) : ∑ i, ‖entry M i U‖ ≤ M.weight :=by
    unfold MergeProof.entry; cases h:M.turn; next=> simp only [norm_zero,sum_const_zero]; exact M.profit
    next j=> -- order inspect? cases rewrites?
             rw [Finset.sum_eq_single (barcode X.activities j)]; simp only [↓reduceIte,Complex.norm_real]; exact M.earn U
             · intro a _ ha; simp [Ne.symm ha]
             simp
private lemma chance {X:Rep G n}{i:Site n}{x:ℝ}{S:Lamp G n}(he:S.Flex X i (4*(1/x)))(hv:0<x)(U:Config G n): x*‖S.watch U‖ ≤4 ∧ (∑ i,x*‖S.rays X i U‖) ≤ 4:=by
    obtain ⟨I,f,M,s,h⟩:=he; let p:=∑ i,‖s i‖*(M i).weight; have hp:p≤4*(1/x):= (Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>mul_le_mul_of_nonneg_left (X.p.loMass _ _ ((M j).profit)) (norm_nonneg (s j)))).trans h.pay
    have hX (a:ℝ)(hv':a≤p): x*a≤4:= (mul_le_mul_of_nonneg_left (hv'.trans hp) hv.le).trans_eq (by field_simp)
    constructor
    · refine hX _ ?_; rw [h.lit]; simp only [Pi.add_apply,Finset.sum_apply, Pi.smul_apply,zero_add]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>?_)); rw [norm_smul]; exact mul_le_mul_of_nonneg_left (frame_fee ..) (norm_nonneg _)
    rw [← Finset.mul_sum]; apply hX; rw [h.run]; simp only [Finset.sum_apply,Pi.smul_apply]; apply le_trans (Finset.sum_le_sum (fun i _=> norm_sum_le ..)); rw [sum_comm]; simp_rw [norm_smul, ← Finset.mul_sum]; exact Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (razor ..) (norm_nonneg _)
omit [Fintype I] [DecidableEq I] in
private lemma steady {V':Type}[DecidableEq V'][Fintype V'](A:Rep G n)(Q:Brigade n V') (o:I→Site n) (X:I→Lamp G n) (w:I→ℝ)(he:∀ i,0<w i)(hp:∀ i,(X i).Flex A (o i) (4*(1/w i))) : Vault (w ∘ Prod.snd) (Q.lamp X) (Q.ray A X) 4 4:=by
    refine ⟨fun i U=>?_,fun i U=>?_⟩
    · unfold Brigade.lamp Brigade.calls; split; exact (chance (hp i.snd) (he _) U).1; unfold stepUp; rw [Motion.norm_scalar]; exact (chance (hp i.snd) (he _) _).1
    by_cases hx:i.1=Q.head; unfold Brigade.ray; simp_rw [if_pos hx]; exact (chance (hp i.snd) (he _) _).2
    unfold Brigade.ray; simp_rw [if_neg hx]; unfold floatUp stepUp; rw [← Equiv.sum_comp (puff (Q.spin i.1) (Q.center i.1))]; simp_rw [Equiv.symm_apply_apply,Motion.norm_scalar]; exact (chance (hp i.snd) (he _) _).2
variable (C N k p)
lemma spiked (H:C.Makes) {V₀:Type}[Fintype V₀][DecidableEq V₀]{X:Census V₀}{x y t:ℝ}{w:V₀→ℝ}{k₁:V₀→ Config G (C.side k p)→ℂ}{k₂:V₀→ Box (C.side k p)→ Config G (C.side k p)→ℂ} {o:V₀→Site (C.side k p)}{f:Config G (C.side k p)→ Marker.Poly X} (s:X.Mode) (M:ℂ)
    (hN:k≤N)(ht:0≤t)(hw:∀ i,0 < w i)(hS:Served (R k) k₁ k₂ f o w t 1)(hv:Vault w k₁ k₂ x y)(hi:Integrable f (prior G _)) (he:(∫ U,(f U).part s∂prior G _)=(Wilson.partition G (C.side N p) (C.beta N p):ℂ)*M):‖M‖*Poly.toll w s ≤ Real.exp (Fintype.card (Site (C.side k p))* Vac.treasury C.path.levels k+ Fintype.card V₀*(x+y+2*1)):=by
    let Z':= Fintype.card V₀; let B:=C.path.rep N p k; let T':= C.path.levels; let Q:= T'.clock; have hb:=H.wilson.represents N p k hN; have h':0<Q.hatCoupling k:= inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (T'.fits.delayed k)))
    have he' : Q.hatCoupling k ≤ B.p.threshold:=by
       rw [show B.p=T'.budget k from hb.vac]; exact le_mul_of_one_le_right h'.le (Real.one_le_exp (sq_nonneg _))
    have hg := (sail hw hS hb.good (Overlay.beta_positive H.wilson hN).le hv ht s hi _ h' he' (History.nonnegative C.path H.wilson N p k hN)).trans (Real.exp_monotone (Vac.suffices_bill H.wilson hN Z' ..))
    rw [he,History.partition_eq P H.wilson N p k hN,norm_mul,Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le,mul_comm (Wilson.partition ..),show (Wilson.partition G (C.path.S.side N p) (C.path.β N p N))=Wilson.partition G (C.side N p) (C.beta N p) from rfl,mul_div_cancel_right₀ _ (partition_pos _).ne',mul_one] at hg; exact hg
end
-- finish.V pay layout any. Moment estimate if topical.
def earns (C:Family G)(m j:ℕ):ℝ:= Real.exp ((C.S.a m/C.S.a j)^4*Vac.treasury C.path.levels j+10)
local notation "Z" => (royal C m p)
local notation "W'" => moment (C.beta N p)
local notation "f*" => Config G (C.side N p)
include H
lemma spiking {Q:Config G (C.side k p)→ Marker.Poly (Names (Site (C.side m p)) Unit)}{F:Unit→ Config G (C.side N p)→ℂ}{S:Unit→Lamp G (C.side k p)}{o:Unit→Site (C.side k p)}{w:Unit→ℝ} (hm:m≤k)(hz:C.ref 0 ≤ k)(hk:k≤N)(h: ShowF C N p m k Q F o w S)(hv:(S ()).Flex (R k) (o ()) (4*(1/w ()))):
    (center C.S p (hm.trans hk) 0).rootTest (C.beta N p) (F ()) ≤ earns C m k / w () :=by
    let T':=center C.S p (hm.trans hk) 0;
    have hp:=h.fleet.secure; have hS:= h.fleet.sem.sold; let v:= w (); have hw:0<v:= hp _; let a:=Fibers.mark (Finset.univ:Finset (V × Unit)); let f:=T'.fullAt (fun _=>F ())
    have he:f= fineJob ((Z N).calls F) (Finset.univ : Finset (V × Unit)):=by
       funext U; unfold f Tiling.fullAt fineJob; rw [Fintype.prod_prod_type]; simp_rw [Fintype.prod_unique,callsR (hm.trans hk)]; rfl
    let t:=(C.path.levels.budget k).supportExponent; let z:=(C.S.a m/C.S.a k)^4*Vac.treasury C.path.levels k+10
    have hg:0 ≤ (C.path.levels.budget k).supportExponent-3:= by
       have he':=(H.thor.suns k hz).exp.1; linarith only [he']
    have hP:= spiked C k p N (w:=w ∘ Prod.snd) H.seed a (W' f) hk (t:=t-3) hg (fun i=> hp i.2) (by rw [(H.seed.wilson.represents N p k hk).vac] at hS; exact hS) (steady (R k) (Z k) o S w hp (fun i=> (Subsingleton.elim () i) ▸ hv)) h.fleet.pay (he.symm ▸ (h.sings.budgets a.val))
    have hK: (Fintype.card (V × Unit))=Fintype.card V:= by simp
    have hx: Poly.toll (w ∘ Prod.snd) a=v^(Fintype.card V):=by rw [show w ∘ Prod.snd=(fun _ : V × Unit=>v) from funext (fun i=>by cases i; rfl)]; unfold Poly.toll; change ∏ _ : V × Unit,v=_; rw [Finset.prod_const,card_univ,hK]
    unfold Tiling.rootTest; refine Stock.spacer ‖W' f‖ z v (Fintype.card V) (norm_nonneg _) hw Fintype.card_pos ?_
    rw [hx,hK,Stock.tallies C.S m k p] at hP; exact hP.trans_eq (congr_arg Real.exp (by unfold z; ring))
end YM.OPE.Strobe

