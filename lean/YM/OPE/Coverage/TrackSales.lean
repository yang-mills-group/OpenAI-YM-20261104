import YM.OPE.Coverage.Ratified
import YM.OPE.Coverage.Samples
/-! Servicing a finite differential curve in the exact fixed hierarchy at
log-dense (not all-length) windows, with provenance in Stored. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped Matrix.Norms.Frobenius
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG
open Next.UVStress Spec Maxwell Extra
open WeakScaling (Equipped)
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge}{F:Extraction.Order}{C:Family G}{S:Table C.book}{d D D' n n':ℕ}{μ R:ℝ}{r:ℕ→ℝ} (H:Final C F S)
set_option quotPrecheck false
local notation "Τ" => Bel C.book

variable (p : Stored H r D n μ) (P:(Bel C.book).Hierarchy) (b:∀ e, Nonempty (YM.Spin.change S e))
variable (V': DiffPlan (Bel C.book)) (hμ:R ≤ μ)(hR:(0:ℝ)<R)(he: ∀ e : ℕ, e ≤ d → WeakScaling.Equipped P e n D R)(hd:d ≤ D)
local notation "s₀" => H.sector.derivatives
local notation "𝑻" =>oldChart H p.toShelf
local notation "𝗆" =>p.maps
open WeakScaling
set_option maxHeartbeats 5000000
include b hμ hR he hd
-- explicit P carries the Maxwell dynamics only; no replacement of H by a
-- hierarchy constructed solely for these moments.
theorem deploy_ledger {N : ℕ}(hg:G.Simple)(hn:0 < n) (hN:N≤n) (ht : V'.Inclusions (Bel C.book))(ha : V'.Orientation P.spin)(hV:V'.Derivatives (Bel C.book)):
    ∃ X : Curve (s₀) V' H.room.kernel.spin P.spin N d R,X.r=p.path ∧ X.delta=(fun i=>(p.wheel i).spacing) ∧
       ∀ e≤d,∀ v:(Bel C.book).Field e,∃ v':ℕ→(Bel C.book).Field e,Tendsto v' atTop (𝓝 v) ∧ (fun i=> X.X i e v) =ᶠ[atTop] (fun i=>𝗆 i e (v' i)) :=by
    obtain ⟨K,hK,hD,hV⟩:= ratify H p.toShelf P b V' hμ hR he hd ht ha hV
    let ζ:=p.path
    have hZ : Tendsto ζ atTop (𝓝[>] 0):=by
       apply tendsto_nhdsWithin_iff.mpr
       constructor
       · apply (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr p.fades.2)).congr (fun i=>?_)
         change Real.exp (- -Real.log (p.path i)) = p.path i; exact (neg_neg (Real.log (p.path i))).symm ▸ Real.exp_log (p.fades.1 i)
       exact Eventually.of_forall fun i=> p.fades.1 i
    let old(i t:ℕ):= oldChart H p.toShelf t i (b t)
    have he': ∀ᶠ i in atTop,∀ t≤ d,∀ v, old i t v=𝗆 i t v:=by
       filter_upwards [(eventually_all_finset (Finset.Iic d)).mpr fun t ht=> shelf_equipment_bij H p.toShelf P b hμ hR he hd t (Finset.mem_Iic.mp ht)] with i hi t ht v
       exact LinearMap.congr_fun (old_agrees H p.toShelf b i t (hi _ (Finset.mem_Iic.mpr ht))) v
    let consumers : Curve (s₀) V' H.room.kernel.spin P.spin N d R :=
         { r := ζ
           pos := p.fades.1
           shrinks:= hZ.mono_right nhdsWithin_le_nhds
           delta:=fun i=>(p.wheel i).spacing
           positive:=fun _=>(p.wheel _).space
           fine:= finer_spacing H p hg hn
           X:=K
           graded:=hK
           deriv:=hD
           sampled m hm v hv σ hσ x hx u hu hU := ?sold
           growth m hm v hv σ hσ x hx u hu := ?held }
    case sold =>
         let d' := fun i => (v i).1
         have h := revised (p.maps) K old he' hV hσ (x:=fun i => Extraction.tag ((p.wheel (σ i)).spacing) (u i)) d' hv
             (fun _ => 1) ((Bel C.book).classMoment (Bel C.book) d' x) (r:=ζ)
         have hh (w : ∀ i, (Bel C.book).Field (d' i)) := finer_sample H p hR hμ hg (fun i=>⟨d' i,w i⟩) (hm.trans hN) (fun i=>(hv i).trans hd) σ hσ x hx u hu hU
         exact (h (fun w => by simpa only [one_smul] using! hh w) (fun i => (v i).2)).congr'
           (Eventually.of_forall fun _ => one_smul ℝ _)
    case held =>
         exact revised p.maps K old he' hV hσ _ hv ((fun i=>(p.wheel i).spacing) ∘ σ) 0
              (fun w => grow_samples H p hR hμ hg (fun i=>⟨(v i).1,w i⟩) hn (hm.trans hN) (fun i=>(hv i).trans hd) σ hσ x hx u hu) _
    refine ⟨consumers,rfl,rfl,fun e hv v=> ⟨fun i=> (old i e).symm (K i e v),hV e hv v,?_⟩⟩
    filter_upwards [he'] with i hi
    change K i e v= _; rw [← hi _ hv _,LinearEquiv.apply_symm_apply]
end YM.OPE.Coverage