import YM.RG3.Script.Mesa

/-!
# Compiled pure-source endpoint at a fixed level of the step interface

One receipt for the signed header conservation & analysis on reference hulls
at the SAME registry position/testing data. Source-coordinate+residual on
precisely the same Decks as the pushed d. Preserve entire clock and coupling.
Use on a model z on P (normalized log outputs, but density unnormalized on
Rep), comparison before any forced re-expression vendors. We do NOT identify
coefficients/analytic estimates here. Takes no comparison bound on the full
represented norm or supply of output K: those are produced. For use without
commit to canonical grade include a zero-dimensional section L supplied
explicitly (or use Script phases separately). Keep all support reserves
(in this instance two above stated p threshold, or call strengthening on
residuals before next step). Use with clocks paying the scale dependent
constants esp in Loaded, .Strap and .Bright/.Dawn (EGE). Incoming inherited
analytic errors not priced to be contracted here. See remaining obligations
for uniform construction and unmarked comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Mark
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press RG3.Primary RG3.Law Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration Source Push.Local Estate Edition
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n:Side}{V:Type}[DecidableEq V][Fintype V][Nonempty V]{R:Census V}{ζ:V→Site n}{G:Gauge}
  {P : Rep G n}(d z:Deck R P)(e : Edition ζ R G) {A: Estate n R}{ι:Type*}[Countable ι]
  (T:A.Truss ι G) (F:ℕ→ Config G n→ℂ)
variable {w:V→ℝ} {M:ℕ} {D:V→ℕ}(H:Hol G){X:(s:V)→Labels.Frame G (D s)}(L:(s:V)→SectionData (X s))
local notation "a"=> P.p.supportExponent+1+1
variable {k: V→ℝ} (hk:∀ i,Readable H (L i) P.p n (k i))
 include hk
set_option maxHeartbeats 400000 in

/-- `e` stable residual log prior to aligned tests (can definally retain
other actual books unmodified or also expenses on earned error graphs),
`T` every signed discrepancy between the compact portions of d and z before
adjustment, registered and conserving the log. Canonical model Z may contain
K estimates but they must be on SAME P. Input CStrongCap needed at same scale
before publications. Error assertion includes both exact evaluation and
exact log+marked-forced WITH layout agreement and all three quantitative
budgets. The compilation includes canonical SectionData and user projection
inside THE error, not inflating next-level estimates by full model book. -/
theorem operate (X₀ : Edition ζ R G)(hz':X₀=read P z ζ) (hhz:z.contents.origins=ζ) (hh:d.contents.origins=ζ)
    (hd:d.Active)(hZ:z.Active){u₀ b₀ κ₀ y₀ B₀ u₁ b₁ κ₁ y₁ : ℝ}(hw:∀i,0<w i)(hD:d.Budget w u₀ b₀ κ₀ B₀ y₀)(hb:z.Budget w u₁ b₁ κ₁ B₀ y₁)
    {ued ced bed c₀ c₁ : ℝ}{f f':ℕ→ℝ}(hE:e.Principle P.p)(hPrice:e.Grant P.p w a ued ced bed f')
    (h:T.Agreement F w P.p ζ M (P.p.supportExponent+1) c₀ c₁ f)(hC:0≤ c₀)(hS:0≤c₁)
    (keep:d.log=z.log+e.log P.p+(T.strand P.p).tally)
    {m:ℕ→ℝ}{δ K:ℝ}(hl: Loaded H a m δ L d (e.add (A.render ζ F)) k w)(hK:∀ i,expense P.p.B a ((L i).footprint (ζ i)) (k i) ≤ K)
    {vac mark s χ φ t:ℝ}(Xh: Billboard d.contents w P.p.B (P.p.supportExponent+1) vac mark)
    (rate:(M:ℝ)*siteFactor P.p.B*(c₁+c₀+δ) ≤ s)(hex:s≤1)(hχ:1≤χ)(hg:0≤φ)(hpay:χ*(vac+mark)+2*s ≤ φ)
    (green:(P.p.B+P.p.B+1:ℕ)^4*(φ:ℝ) ≤ 1)(hen:(Real.exp φ-1)/χ ≤ t*B₀) {μ₁ μ₂:ℝ}(hp:P.activities.Valid P.p μ₁ μ₂)(hA:Accessible P):
    let J:= e.add (A.render ζ F)
    let S:= J.sprayed H L d
    let funds := ((ced+c₀)+δ)+K*δ
    ∃ out : Deck R P, let err:= jetty out z S
      out.contents.origins=ζ ∧ read P out ζ=X₀.add S ∧
      out.density=d.density ∧ out.Active ∧ out.Budget w (u₁+(ued+δ)) (b₁+funds) t B₀ (y₁+bed) ∧
      (out.log=z.log+err.log) ∧ (∀ i U,out.contents.each i U=z.contents.each i U+(err.contents.each i U-Kbase i U P)) ∧
      S.Principle P.p ∧ S.Grant P.p w a (ued+δ) funds bed (shuffle (stageCost k w δ) (palm J d H k m (blend f' f) X)) ∧
      err.Active ∧ err.Budget w (ued+δ) funds (t+κ₁) B₀ bed ∧
      ∀ q : V, ∃ c : Coefficient (X q) n, c.Format (ζ q) H P ∧ c.remBound (ζ q) P B₀ (funds/(w q)+(t+κ₁)/(w q)) ∧
        w q*‖c.x 0‖ ≤ (ued+δ)+bed ∧ w q*(X q).coeffSize ((X q).core c.x) ≤ δ ∧
        (c.density (ζ q) (L q) P = fun U=> (d.density U).part (R.fire q) - (z.density U).part (R.fire q)):=by
  intro J S N
  obtain ⟨b,hQ,hE',hF⟩:= Truss.issued h hw hC hS
  have hJ:J.Principle P.p:= principle_plus hE hE'
  let gBase := blend f' f
  have hh' : J.Grant P.p w a ued (ced+c₀) bed gBase:= by simpa only [add_zero] using! grant_plus hw hPrice hF
  let m₁:=shuffle (stageCost k w δ) (palm J d H k m gBase X)
  have hS':S.Grant P.p w a (ued+δ) N bed m₁:= stored hk hh hd hJ hl hw hh' (show P.p.supportExponent+1 ≤ (a:ℝ) from by linarith) hK
  have hS: S.Principle P.p:=primed H hk hh hd hJ
  have He:=living hw hE hPrice (p:=P.p) (by linarith)
  have HF:=living hw hE' hF (p:=P.p) (by linarith)
  have hL:=blowing hk hh hd hJ hl hw hh' h.occupied (le_refl (a:ℝ)) hK hD
  have hx:=hQ.beside (e.log P.p)
  rw [show e.log P.p+(A.render ζ F).log P.p=J.log P.p from funext fun U=> (log_plus _ _ (He U).1 (HF U).1 (He U).2 (HF U).2).symm] at hx
  have hD': d.log=z.log+(e.log P.p+(T.LogRepair F P.p).read.tally):= by rw [keep,add_assoc]; rfl -- rfl??
  have he:= (hx.again hL hw).beside z.log
  obtain ⟨f0,HZ⟩:=affords hb hhz
  rw [← hz'] at HZ; have HZ':X₀.Principle P.p:=by rw [hz']; subst ζ; exact ⟨hZ.articles.proper,hZ.articles.pins,hZ.articles.regular,hZ.captions⟩
  let I:= X₀.add S; let Q:=I.scribe d
  have hZ':z.log=X₀.log P.p:= by rw [hz']; rfl
  have hSn : S.Grant P.p w P.p.supportExponent (ued+δ) N bed m₁:= ⟨hS'.one,hS'.nn,hS'.pay,
    label_budget hw hS'.nn (by linarith : P.p.supportExponent ≤ a) hS'.more,
    label_budget hw (fun _=>norm_nonneg _) (by linarith : P.p.supportExponent ≤ a) hS'.captions⟩
  have Hi:= grant_plus hw HZ hSn
  have Hq:= grant (d:=d) Hi hw le_rfl
  have hT : I.Principle P.p:= principle_plus HZ' hS
  have ht:= authorized hh hT hd
  have h₁: z.log+S.log P.p=Q.log:= by
    rw [hZ',I.deck_log]; have hw' := living hw hS hSn le_rfl; have hm:=living hw HZ' HZ le_rfl
    exact funext fun U=> (log_plus _ U (hm U).1 (hw' U).1 (hm U).2 (hw' U).2).symm
  rw [h₁, ← hD'] at he
  have hs' : χ*(vac+mark)+2*((M:ℝ)*siteFactor P.p.B*c₁+M*siteFactor P.p.B*c₀+M*siteFactor P.p.B*δ) ≤ φ:= by
    have H: (M:ℝ)*siteFactor P.p.B*c₁+M*siteFactor P.p.B*c₀+M*siteFactor P.p.B*δ ≤ s:=by convert rate using 1; ring
    linarith
  have ha0: (M:ℝ)*siteFactor P.p.B*c₁+M*siteFactor P.p.B*c₀+M*siteFactor P.p.B*δ ≤1:=le_trans (by rw [mul_add,mul_add] at rate; exact rate) hex
  let out: Deck R P := (he.publish hh Xh hw hp.forced hd ha0).task hA Q
  obtain ⟨h_o,ho',hU⟩:= he.copy hh Xh hw hp.forced hd ha0 χ φ hχ hs' hg green hA rfl hD hen hb.radial.factor (principle hT) Hq.1 hT.vertical Hq.2
  change out.Active at h_o
  let err:=jetty out z S
  have heer:err.Active:=lyric _ _ hS h_o hZ rfl hhz
  have hB:err.Budget w (ued+δ) N (t+κ₁) B₀ bed:= kept out z hSn le_rfl ho' hb
  have Hℓ:out.log=z.log+err.log:=h₁.symm
  refine ⟨out,rfl,?_,hU,h_o,ho',Hℓ,?_,hS,hS',heer,hB,fun q=>?_⟩
  · rfl
  · exact packed out z ho' hb h_o hZ hp _
  have HE:= (trunk hk hh hd hJ hl hw (show P.p.supportExponent+1 ≤ (a:ℝ) from by linarith) q).2.2.2.2
  have hδ : w q*(X q).coeffSize (J.petition H d q) ≤ δ:= by exact (mul_le_mul_of_nonneg_left HE (hw q).le).trans_eq (by field_simp [(hw q).ne'])
  obtain ⟨Hq0,H1,H2,H3,H4,H5⟩:=income d J hw q (hk q) (z:=err) (show err.contents.origins=ζ from rfl) rfl hJ hd hh hB heer hp hδ
  refine ⟨_,H3,H4,H1,H2, H5.trans ?_⟩
  have hC:=one_stamp out z err h_o hZ heer ho' hb hB hp Hℓ (packed out z ho' hb h_o hZ hp _) q
  change out.density=d.density at hU;rw [hU] at hC
  exact funext fun U=>by rw [hC U]; ring
end YM.RG3.Script.Mark
