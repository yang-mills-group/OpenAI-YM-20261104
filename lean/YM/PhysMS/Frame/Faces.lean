import YM.PhysMS.Frame.Phases
import YM.PhysMS.Frame.Macroscopic

/-! # All-length measured nonperturbative comparison platform. (Single horizon form here
plus the previous nested one.) Identity output and correlation use the same physical frames on
continuous UV lengths. In particular identifies their leading **free** predictions and proves the
kinematics to transfer any coupling-power results paid on either array.
Positive-order estimates for the measure itself vs independent continuum coefficients are a separate
concern; not claiming them in these statements. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Filter Set Spec OPE OPE.Orbits OPE.Nesting Trace Trace.Pilot
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(H:Leading F J)(h:Foundation F R)
    {I Y : Type}[Fintype I][Fintype Y]{d:I→ℕ}{e:Y→ℕ}
    (v:(i:I)→ (Climb.Bel C.book).Field (d i))(w:Labels S e)(m:ℕ)
    (M η δ ε:ℝ)(hM:0≤M)(hη:0<η)(hδ:0<δ)(he:0<ε)
include H h hM hη hδ he
lemma single_report : ∀ᶠ r in trail, ∀ (x:I→E4)(y:Y→ E4)(o:E4), WithinRoom r M η x o → ClearOf o y δ →
    ‖algebraError F R x o (born J r v) y w m‖ ≤ r^(m+1-ε) ∧ ∀ q:Viewers F, ‖formula F R x o (born J r v) y w m q‖ ≤ r^(m+1-ε) := by
    let U := (I→E4) × (Y→E4) × E4 × Viewers F; let K r(s:U) := WithinRoom r M η s.1 s.2.2.1 ∧ ClearOf s.2.2.1 s.2.1 δ
    let P r (s:U) := Levy.invoice (d:=d) F R s.2.2.1 w s.2.2.2 m s.1 s.2.1 (born J r v); let B:= (↑m:ℝ)+1
    suffices hp : ∀ᶠ r in trail, ∀ i:U,K r i→ ‖P r i‖ ≤ r^(B-ε) by
       filter_upwards [hp,h.discrepancy I Y _ _ (Orbits.tags (d:=d) 0|>voices) w M η δ ε hM hη hδ he m] with r hr hf x y o hx hy
       have hh(p:Viewers F): ‖formula F R x o (born J r v) y w m p‖ ≤ r^(B-ε):= by rw [phase_invoice]; exact hr (x,y,o,p) ⟨hx,hy⟩
       specialize hf x o y hx hy
       exact ⟨glance_contract F ((norm_nonneg _).trans (hh none)) |>.2 (fun p=> (congr_arg norm (formula_seen F R _ _ _ y w m p hf.1 hf.2.1)).trans_le (hh p)),hh⟩
    apply uniform_power he (fun s l hl ht hc => ?_)
    let p r:Viewers F:= (s r).2.2.2; let x r:=(s r).1; let y r:=(s r).2.1; let o r:=(s r).2.2.1; let A r d:= Levy.invoice F R (d:=d) (o r) w (p r) m (x r) (y r)
    have hρ(a:I→ℕ)(v:Labels S a)(ε:ℝ)(hh:0<ε):=hc.and ((h.discrepancy I Y _ _ v w M η δ ε hM hη hδ hh m).filter_mono ht) -- ∀ᶠ
    let r:ℝ→ℝ:=id
    refine total F R J H (r:=r) (tendsto_id.mono_left ht) v (-B) A ?_ ?_
    · intro e he; filter_upwards [hρ d 0 ε (by assumption)] with r hr u; obtain ⟨h,hS⟩:= hr.1
      exact matchInvoice F R he m _ _ _ _ ((hr.2 _ (o r) _ h hS).1)
    intro e hm u; apply RateLE.mono (a:=-(B-weight e)) _ (by linarith only [])
    refine pays_power (r:=r) (fun ε h=>?_) (tendsto_id.mono_left ht)
    filter_upwards [hρ e u ε h] with i hp; rw [show A i e u = _ from (phase_invoice F R m _ _ _ u w (p i)).symm]; obtain ⟨h,h'⟩:= hp.1; exact (hp.2 _ (o i) _ h h').2.2.2 _

omit hδ [Fintype I]
open Climb
variable (hg:G.Simple)(X:Scaling S){n:ℕ}{p:Caps n}(v:MaxwellSlots C p)
local notation "actor" r => Orbits.tags (born J r v)
local notation "noY" => fun z=> (Short.extra (z:=z):S.Tag)

include X hg
theorem singleton_head : ∀ᶠ r in trail, ∀ x:Points n, WithinRoom 1 M η x.ofLp 0 →
      ∀ q:Viewers F, ‖measured F q (J r) v r x - Short.scalar F R (r • x).ofLp (actor r) 0‖ ≤ r^(4-ε):= by
    filter_upwards [single_report F R J H h v (voices noY) 3 M η 1 ε hM hη one_pos he,self_mem_nhdsWithin] with r hr hp x hx q
    have hz : r • x∈conf n:= Work.A05.smul_conf hp (conf_room hη hx); let p:=(r • x).ofLp; let v':= actor r; let b(e:ℕ):= formula F R p 0 (voices v') Short.gapPos (voices noY) e q
    have ht: measured F q (J r) v r x=Orbits.moment (spectator F q) p (voices v'):= point_moment F q v' hz
    rw [ht]; change ‖Orbits.moment (spectator F q) p (voices v')-_‖≤_
    rw [← Short.identity_formula F R X hg p v' 0 q hz, Short.Bottom.unchanged F R X hg _ _ _ _ (by simp : 0≤(3:ℕ))]
    apply le_trans ((hr p Short.gapPos 0 (scale_room hη hp hx) (by constructor <;> intro j <;> cases j)).2 q)
    norm_num

end YM.PhysMS.Frame
