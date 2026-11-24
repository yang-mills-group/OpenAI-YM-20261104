import YM.RG3.Script.Picnic.Buds
/-!
# Whole roster kept through every Scripts price & fusion, held test version

Register conservation & low jet tests over all requested data.
Caption costs included. Billing suppliers may improve by using per-ΘPrice
when not intending held-derivative readout. Keeps true geometry join.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Picnic
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Ink
  Extra.Multi Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset Extra.Iteration Edition RG3.Primary Push.Local Source Estate
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V : Type} [DecidableEq V][Fintype V][Nonempty V]{R:Census V}{ζ : V→Site n}{G : Gauge}
  {Θ : Type*}[Nonempty Θ]{P : Rep G n} (d z:Taste Θ ζ P R)
  (Et : Θ→Edition ζ R G)(A:Estate n R) {ι:Type*} [Countable ι] (T : Θ→ Estate.Truss A ι G)
  (F:Θ→ℕ→ Config G n→ℂ){w: V→ℝ}{D: V→ℕ}(H: Hol G){I:(s:V)→Labels.Frame G (D s)}(L:(s:V)→SectionData (I s)){k: V→ℝ}(hr:∀ s,Readable H (L s) P.p n (k s))

-- Deterministic engine. Mark.operate core has ∃ proofs, here expose
-- feeds and corrections literally so one set of vouchers independent of
-- Θ is created internally without hypothesizing the result.
def logo (x:Θ):= (Et x).add (A.render ζ (F x))
def ripe (x:Θ):= (logo (ζ:=ζ) Et A F x).sprayed H L (d.leaf x)
def onto (x:Θ):=(Edition.read P (z.leaf x) ζ).add (ripe d Et A F H L x)
def visor (x:Θ):=Join.series ((T x).LogRepair (F x) P.p).notes (tonic (d.leaf x) (logo (ζ:=ζ) Et A F x) H L hr)
def compass (u:ι→ℝ)(c m:ℕ→ℝ)(I:(s:V)→Labels.Frame G (D s))(k:V→ℝ) (x:Θ):=
    Sum.elim (((T x).LogRepair (F x) P.p).rates u c) (bracken (d.leaf x) (logo (ζ:=ζ) Et A F x) k H I m)

def Estimate (M:ℕ)(P:Rep G n)(fit sig δ:ℝ): ℝ:= ((M:ℝ)*siteFactor P.p.B*sig+M*siteFactor P.p.B*fit)+M*siteFactor P.p.B*δ

local notation "B"=>P.p.supportExponent+1+1
variable {d z Et A T F H L} -- remove
variable {γ a b u s fit sig δ vac mark c₁ t₁ c₀ t₀ κ u₀ u₁ a₀ a₁ K σ χ:ℝ} {M:ℕ} {m f₁ f₀ g : ℕ→ℝ}{t:ι→ℝ}
local notation "here"=>visor d Et A T F H L hr
variable (hd: d.Snacks w u₀ c₀ t₀ κ a₀)(hz:z.Snacks w u₁ c₁ t₁ κ a₁)
    (hv:Voucher Et P.p w (P.p.supportExponent+1+1) u s a f₀ g)
    (hi:∀ x,(T x).Agreement (F x) w P.p ζ M (P.p.supportExponent+1) fit sig f₁)
    (hF:∀ x,(T x).Strap w P.p (P.p.supportExponent+1+1) sig t)
    (hx:∀ x y,(T x).filing=(T y).filing)
    (Keep: ∀ x,(d.leaf x).log=(z.leaf x).log+(Et x).log P.p+((T x).strand P.p).tally)
    (hf:0≤fit)(hs:0 ≤ sig)
    (hh:∀ x,Loaded H (P.p.supportExponent+1+1) m δ L (d.leaf x) (logo (ζ:=ζ) Et A F x) k w)
    (hK:∀ i,expense P.p.B (P.p.supportExponent+1+1) ((L i).footprint (ζ i)) (k i) ≤ K)
include hd hz hv hi hF Keep hr hf hs hh hK hx


set_option maxHeartbeats 500000 in
theorem compilation :
    let tₚ x:= (d.leaf x)
    let c x:= logo (ζ:=ζ) Et A F x
    let Q := ripe d Et A F H L
    let out:= endorse d (onto d z Et A F H L)
    let b:=Classical.arbitrary Θ
    let fees:= compass d Et A T F H t f₁ m I k b
    let v:=s+fit+δ+K*δ
    (∀ x, Join P.p (tₚ x).log (out.leaf x).log w ζ (here x) fees (Estimate M P fit sig δ)) ∧
      Nonempty (Ledger here) ∧
      Voucher Q P.p w (P.p.supportExponent+1+1) (u+δ) v a (shuffle (stageCost k w δ) (palm (c b) (tₚ b) H k m (Edition.blend f₀ f₁) I)) (Edition.blend g (fun _=>0)) ∧
      Nonempty (out.Store w (u₁+(u+δ)) (c₁+v) (a₁+a)) ∧
      (∀ x, (out.leaf x).log=(z.leaf x).log+(Q x).log P.p) ∧
      (∀ x,(c x).Principle P.p):= by
  intro tp c Q out b ε gap
  have hw:= hd.strong.radii
  have hW x:= Truss.issuedBy (hi x) (hF x) hw hf hs
  have hδ:0≤δ:= budget_nonneg ((hh b).2 (Classical.arbitrary _))
  have hΛ: Voucher (fun x=> A.render ζ (F x)) P.p w (P.p.supportExponent+1+1) 0 fit 0 f₁ (fun _=>0):=⟨⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩,fun x=>(hW x).2.1,fun x=>(hW x).2.2,
    fun i=>⟨le_rfl,fun _=>norm_zero.le⟩,fun x i=>by simpa [Estate.render,Estate.verse] using (hW x).2.2.captions i⟩
  have hV : Voucher c P.p w (P.p.supportExponent+1+1) u (s+fit) a (Edition.blend f₀ f₁) (Edition.blend g (fun _=>0)) := by simpa only [add_zero] using! hv.into hw hΛ
  have hQ:= summer H L hr (fun i=>d.root) (fun i=>(d.snack hd i).1) hV hh hw (show _≤(P.p.supportExponent+1+1) from by linarith) hK b
  let W:=grants z hz
  have hB' := (Voucher.into (grants z hz) hw (Voucher.ease hQ hw (show _ ≤ (P.p.supportExponent+1+1) from by linarith)))
  obtain ⟨Z⟩:= menu_store d hB' hw le_rfl
  have he x : (out.leaf x).log=(z.leaf x).log+(Q x).log P.p:=by
    rw [show out.leaf x = _ from endorsed_eq d hB'.toFirm x,← show (read P (z.leaf x) ζ).log P.p=(z.leaf x).log from rfl,deck_log]
    have ht := z.snack hz x
    have hr := living hw ((grants z hz).stays x) ((grants z hz).backs x) (le_refl _) (p:=P.p)
    have hp := living hw (hQ.stays x) (hQ.backs x) (show P.p.supportExponent ≤ (P.p.supportExponent+1+1) from by linarith)
    funext U
    exact log_plus P.p U (hr U).1 (hp U).1 (hr U).2 (hp U).2
  refine ⟨fun x=>?_,⟨?ledger⟩,hQ,⟨Z⟩,he,hV.stays⟩
  case ledger=>
    constructor
    rintro x y (i|i); rfl; exact (hV.toFirm.scattering H L hr d.leaf).column x y i -- actually column for tonic i
  have hS:= blowing hr (d.root) (d.snack hd x).1 (hV.stays x) (hh x) hw (hV.backs x) (hi x).occupied (le_refl _) hK (d.snack hd x).2
  have hr x:= living hw (hΛ.stays x) (hΛ.backs x) (p:=P.p) (show _ ≤ (P.p.supportExponent+1+1) from by linarith)
  have hB x:= living hw (hv.stays x) (hv.backs x) (p:=P.p) (show _ ≤ (P.p.supportExponent+1+1) from by linarith)
  have hb': (c x).log P.p=(Et x).log P.p+(A.render ζ (F x)).log P.p:= funext fun U=> log_plus _ U (hB x U).1 (hr x U).1 (hB x U).2 (hr x U).2
  have h':= ((hW x).1).beside ((Et x).log P.p)
  rw [← hb'] at h'
  have h'' := (h'.again hS hw).beside ((z.leaf x).log)
  have HK : (z.leaf x).log+ ((Et x).log P.p + ((T x).LogRepair (F x) P.p).read.tally)=(tp x).log:= by
    unfold tp; rw [Keep x]; exact (add_assoc ..).symm
  have hQ' : ε=compass d Et A T F H t f₁ m I k x:= by
    unfold ε compass
    congr 1
    · unfold RG3.Render.Stage.Repair.rates Truss.LogRepair Truss.strand Estate.trace RG3.Render.Stage.Trace.cash; simp only; rw [hx _ x]
    funext i; unfold bracken Primary.ink Primary.earns Edition.scribe; dsimp only; rw [show (logo (ζ:=ζ) Et A F b).pins= (logo (ζ:=ζ) Et A F x).pins from hV.toFirm.pins b x]
  rw [hQ',he x]
  rw [HK] at h''; exact h''
end YM.RG3.Script.Picnic
