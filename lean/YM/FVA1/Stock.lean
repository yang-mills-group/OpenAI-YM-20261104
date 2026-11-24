import YM.FVA1.Film

/-!
 Virtual polynomial estimates feed physical ones in full operator cost at every
 represented-density coefficient; radius changes on physical readback per-slot
 still to be paid. No estimate on evaluated densities is used to transfer a norm.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA1
open MeasureTheory Finset Function Filter Lattice Wilson RG RG05.Strand Extra.Trajectories
open Marker Overlay Overlay.GapsLocal Push.GridApprox.Nil MergeProof Accent
open Push Push.AbsoluteSums
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {T I J V:Type}[DecidableEq I][Fintype I]
variable {G:Gauge}{n:Side}{R:RG.Rep G n}


structure Stock (I J:Type)[DecidableEq I][Fintype I]{n:Side}(G:Gauge) where
  X : J→Support n
  requires : I → Support n
  bin : J→(FreeCensus I).Mode → Config G n → ℂ
  hard : ℕ → Config G n → Poly (FreeCensus I)

namespace Stock
variable (D:Stock (n:=n) I J G)(P : RG.Rep G n)
structure Room : Prop where
  stays i : (D.X i).Nonempty
  reg i z : P.p.Regular (D.X i) (D.bin i z)
  silent i : D.bin i (FreeCensus I).quiet=0
  placed i z U : D.bin i z U≠0→atlas z D.requires ⊆ D.X i
  parent i U : (D.hard i U).part (FreeCensus I).quiet=(P.activities.K i U :ℂ)
  carries i : UsesFinal P.p.threshold (P.activities.forced i).support (D.hard i)
  invariant i : GaugeInvariant (D.hard i)
  passed i z : Measurable fun U=>(D.hard i U).part z
  warped i z U : (D.hard i U).part z ≠0 → atlas z D.requires ⊆ (P.activities.forced i).support
  permitted i U : D.hard i U ≠0→ (P.activities.forced i).eligible P.p.threshold U

local notation "p0"=> P.p
set_option quotPrecheck false
local notation "K0" => fun i:ℕ=>(P.activities.forced i).support

structure Lent (ρ:I→ℝ)(supportFee regFee Kfee:ℝ): Prop where
  radius : ∀ i,0<ρ i
  extraS : (p0).supportExponent ≤ supportFee
  paints : ∃ u : J→Sheet (FreeCensus I), (∀ i,0≤u i) ∧ Ac.Hit D.X (p0).B (fun i=> wordsPrice ρ (u i)) supportFee regFee ∧
    ∀ i z a, a∈D.X i → (p0).supBounds a (D.X i) (D.bin i z) (u i z)
  hasK : Towed ρ (K0) D.hard (p0).B supportFee Kfee

variable [DecidableEq V] [AddCommGroup T][Module ℂ T]{Γ:Census V}
variable (tag:I→Γ.Mode)(read:I→(V→T)→ℂ)(o:Positions V n)(header : V→(V→T)→ℂ)

/-- The summation convention after assembly is deterministic per bin and unchanged on labels.
Do not move any mask based on the cancellation inside `decSum`. -/
def reinsert : Film J T Γ P where
  tape:=o
  surround:=D.X
  header:=header
  soft x:=fun i=>decSum tag read (D.bin i) x
  gas x i U:= decoder tag (fun j=>read j x) (D.hard i U)

local notation "W"=>D.reinsert P tag read o header

variable (h:∀ i,(tag i).val.Nonempty)

-- useful for any placeholder pfun
omit [AddCommGroup T] [Module ℂ T] in
lemma hard_d (i:ℕ)(x:Config G n)(a:Γ.Mode)(φ:V→T):
    (decoder tag (fun j=>read j φ) (D.hard i x)).part a=
      decSum tag read (fun θ U=>(D.hard i U).part θ) φ a x:= (decSum_eq tag read (fun θ U=>(D.hard i U).part θ) φ a x).symm

include h
lemma fit_reinsert (hR:D.Room P) (hO:∀ i, ∀ j∈(tag i).val, o.stub j ⊆ D.requires i)
    (hK:∀ i,SlotLinear (tag i).val (read i))(hH:∀ i,SlotLinear ({i}:Finset V) (header i))
    {ρ:I→ℝ}{c a b:ℝ}(hL:D.Lent P ρ c a b): (W).Fit:=by
  obtain ⟨u,hu,_,hP⟩:=hL.paints
  refine ⟨hR.stays,hH,fun x i z=> ?_,fun i z U=> slot_dec tag read hK _ _ U,fun x i=> ?_,?_,?_,?_,?_,?_,?_⟩
  · obtain ⟨v,hv⟩:=hR.stays i
    let C k:= ‖read k x‖
    have hF:=dec_reg_bounds tag read x z v (hR.reg i) C (fun _=> le_rfl) (u i) (fun j=> hP i j v hv)
    exact hF.1
  · funext p; change decSum ..=0; rw [decSum_eq,dec_quiet _ _ h]; exact congr_fun (hR.silent i) _
  · intro x i z v hv he; obtain ⟨p,hp⟩:= Function.ne_iff.mp he
    exact dec_stamped tag read z p D.requires (D.X i) x hp (hR.placed i · p) o.stub hO _ hv
  · intro i U z; convert slot_dec tag read hK (fun θ U=>(D.hard i U).part θ) z U using 2 with x
    exact hard_d ..
  · intro x i U; exact (dec_quiet _ _ h _).trans (hR.parent i U)
  · intro x i; let Φ:=decoder tag (fun j=> read j x)
    have hc (b:Γ.Mode) : Measurable (fun U=>(Φ (D.hard i U)).part b):= by
      simp_rw [Φ,dec_part]; exact Finset.measurable_sum _ (fun k _=> (hR.passed i k).mul_const _)
    refine ⟨⟨fun U V hv hx=> congr_arg Φ (hR.carries i _ _ hv hx),fun t U=> congr_arg Φ (hR.invariant i t U),hc, fun U z h=> ?_⟩,fun U hU=>?_⟩
    · by_contra hg; apply h
      rw [show ((W).gas x i U).part z= _ from D.hard_d tag read i U z x] at hg
      exact fun j hj=>(dec_stamped tag read z U D.requires _ x hg (hR.warped i · U) o.stub hO j hj) (o.mem j)
    have ht:= hR.permitted i U (fun hp=> hU (show Φ _=0 from by rw [hp,map_zero]))
    exact ⟨ht.1,(P.activities.forced i).inventory_ne,(P.activities.forced i).inventory_sup⟩
  · intro x i U z v hv he; rw [show ((W).gas x i U).part z= _ from D.hard_d tag read i U z x] at he
    exact dec_stamped tag read z U D.requires _ x he (hR.warped i · U) o.stub hO v hv
  intro x i U hU
  exact hR.permitted i U fun he=> hU (show decoder tag (fun j=> read j x) _=0 from by rw [he,map_zero])
omit h
variable {ρ:I→ℝ}{fee a b F v κ:ℝ}
lemma pays_reinsert (hR:D.Room P)(hL:D.Lent P ρ fee a b)
    (C:Controls V T)(cost:I→ℝ)(h0:∀ i,0≤cost i)(hs:∀ i x,C.Admits x→ ‖read i x‖≤ cost i)
    (w:V→ℝ)(hw:∀ i,0<w i)(hP:∀ i, Poly.toll w (tag i)*cost i≤ρ i)
    (hH:∀ i x,C.Admits x→w i*‖header i x‖≤v)(hκ:0<κ)(hF:b ≤ F*κ): (W).Pays C w fee v a F κ:=by
  obtain ⟨E,hE,hT,hC⟩:=hL.paints
  obtain ⟨g,hg,hB,hY⟩:=hL.hasK
  choose u hu hX hv using hY
  let Z:=decSheet tag cost
  refine ⟨hw,hκ,hL.extraS,hH,⟨Z ∘ E,fun i=> sheet_pos tag cost h0 (hE i), Film.shrink_hit D.X _ (fun i=> Film.sum_words_pos w hw _ (sheet_pos tag cost h0 (hE i))) (fun i=> sheet_price tag cost _ (hE i) _ _ hP hw h0) hT le_rfl,?_⟩,⟨Z ∘ u,fun i=>sheet_pos tag cost h0 (hu i),fun p=> ?_,?_⟩⟩
  · intro i x hx z y hy
    exact (dec_reg_bounds tag read x z y (hR.reg i) cost (fun j=>hs j x hx) _ (fun j=> hC i j y hy)).2
  · apply budget_loosen _ hF
    exact Film.shrink_hit (K0) _ (fun i=>Film.sum_words_pos _ hw _ (sheet_pos tag cost h0 (hu i))) (fun i=> (sheet_price tag cost _ (hu i) _ _ hP hw h0).trans (hv i)) hB (le_refl fee) p
  intro i x hx U y
  exact sheet_cap tag _ cost (fun i=>hs i x hx) _ (hX i U) _

end Stock
end YM.FVA1
