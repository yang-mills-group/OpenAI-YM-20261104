import YM.LocalLTE.Fan.Local
import YM.LocalLTE.Marked.Roots
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette
lemma incomeA (X:Coat T F) (H: Cash W s η L Q o t T R)(hX:X.x=s)(hm:X.width=o.K) (hT:Stamp T)(x: Directions G c)(p:= (gStep R.beta,x)) (hP:p=(gStep R.beta,x))(hp:(timeΛ X p).manifest) (z: Air f G)(he:∀ i,|z i|≤ postponement L s o):
    (inputΛ X z p=(timeΛ X p).input (worldZ (timeΛ X p) R.beta z))∧(∀ (W: Finset (Bond f)),(timeΛ X p).enforce (2*o.a) (worldZ (timeΛ X p) R.beta z) W=1) ∧RG.flags R.p.threshold (inputΛ X z p)=∅:=by
  have hθ:=H.laws.data; have hx:=H.laws.intake
  obtain ⟨h₀,h₁,h₂,h₃⟩:=hθ.safety
  let Z:=timeΛ X p
  let U:=worldZ Z R.beta z; have he' : Z.liftA R.beta z=U:= Vine.shine Z (show Room P S T Z.x from hX.symm ▸ H.laws.data.room
    ) hp R.beta z
  have hV (v:Site c): Z.watch v o.ξ R.beta Z.B z:= fun i hi=> le_trans (he i) (by
    apply le_trans (b:=o.ξ*(Z.t*(gStep R.beta)⁻¹)) (mul_le_mul_of_nonneg_left _ o.rare.le) (le_of_eq (by ring))
    unfold Coat.t; rw [show Z.x=s from hX, ← hθ.funds.length_eq]; exact (charge_area S s T R hx))
  have hi : Intake P T Z.x R := hX.symm ▸ hx -- check
  have hz:= h₃ F Z hX hm hp; have hf:0 < Z.t:= R.p.threshold_pos.trans_eq hi.received.temp
  have hA:0<o.a*Z.t:=mul_pos o.large hf
  have HH (i: Bond f): Z.cone (2*o.a) U i=1:= Z.serves hA _ _ (by
     rw [Z.premiere hA U i]; swap
     · have hP := Z.watch_bonds (atEdge S i) hf o.rare.le hx.positive (hV (atEdge S i)) i (by rw [separation_self]; omega) (hz.1 i)
       rw [← he']; exact hP.2.trans (mul_le_mul_of_nonneg_right (by linarith) hf.le)
     norm_num)
  have hs : switchΛ X z p=U:= by change _=worldZ (timeΛ X p) _ _; rw [hP,rims]
  have hU: Z.input U=inputΛ X z p:= by rw [openingΛ, hs]
  have hF (i:Bond f)(W : Finset (Bond f)): Z.enforce (2*o.a) U W=1:= Finset.prod_eq_one fun i _=> HH _
  have hj: RG.flags R.p.threshold (inputΛ X z p) = ∅:= by
    apply Finset.not_nonempty_iff_eq_empty.mp; rintro ⟨y,hy⟩
    obtain ⟨k,-,hk⟩:= (flags_spec ..).mp hy; let i:= S.ratio.parent k.1
    have he : ¬ Inside i Z.seeds (30*Z.B) := X.blank_no i _
    have hp : toll (Z.input (Z.liftA _ z)) k < Z.t/4 := (hz.2 hT i he R.beta hx.positive z (hV i)).2.1 k rfl
    rw [he',hU] at hp; rw [hi.received.temp] at hk; change Z.t < toll _ k at hk; linarith only [hf,hp,hk]
  exact ⟨hU.symm,fun W=> hF (0,0) W,hj⟩

-- model pointer. Approx OUT.GI.X.Width needs rear Clock. F sampled canonical on cone. Reader uses passed mark leaves, no Force aid.
structure Mind (M:Leaf R)(v:Config G f→ℝ)(κ:ℝ)(p n:ℕ) : Prop where
   ink:∃ i:ℕ,M.turn=.logKey i
   reads: M.ingredient=RG.masked R.p.threshold M.crest v
   health: ∃ (i:ℕ),M.turn=.logKey i ∧ R.p.supBounds (R.activities.reg i|>.site) M.crest v M.weight ∧ R.p.Regular M.crest v ∧ ∃ t≤n, FrameBox.Polynomial t κ (R.activities.reg i|>.site) p v
variable {ι:Type}[Fintype ι](M:ι→Lotus.Leaf R)(φ:ι → Config G f → ℝ)(κ:ℝ)
local notation "mz"=> Merge.Palette.sign M S
local notation "E"=> Disk G c
variable (Q: YM.ConnectedActivityE6.Target G P)(D:Merge.Tickets (Merge.Palette.sign M S))(H:Cash W t μ L Q o a T R)(he: ∀ i∈D.val,Mind (M i) (φ i) κ j n)(X:Coat T F)(p:Disk G c) -- issue Q rebind T.W lifts
local notation "X'"=> (timeΛ X p)
local notation "W'"=> team M D
def oils (b:Air f G):= ∏ i∈D.val, φ i (inputΛ X b p) -- uses φ
abbrev payment (z:Air f G):= Team.paidU W' (timeΛ X p) (o.a) (worldZ X' R.beta z)
omit [Fintype ι] in
lemma feesA (z:Air f G): ‖payment (o:=o) M D X p z‖ ≤ (team M D).weight:= (W').coin ..
omit [Fintype ι] in
lemma tightenM (b:Air f G)(v:F.Slice G): payment (o:=o) M D (X.wrapY v) p b=payment (o:=o) M D X p b:=by
    let Z:= timeΛ X p; let T:= (timeΛ (X.wrapY v) p); let q:=worldZ Z R.beta b
    have hv: voltage T=voltage Z := (tighten X v p 0).2.2; have hz:worldZ T R.beta b=q:=by unfold q worldZ; rw [hv]; rfl
    change (W').paidU T _ (worldZ T R.beta b)=_
    rw [hz]; change _=(W').paidU Z _ q
    unfold Team.paidU; refine prod_congr rfl (fun i _=>?_); unfold Leaf.paidU; rw [(tighten X v p q).1]; rfl
variable (L': Finset (Veil c f))(Y: Molecule S)(hh: D.reach⊆Y) (hq:Y\D.reach=Fan.arm L')
include hh hq
-- tap.Title: X.u time(Λ).Fan.Chi dormant.
omit [Fintype ι] in
lemma quantum (I: Finset (Tubular f G))(h: (Pond.circuit I (timeΛ X p).relating).PosDef):
    (team M D).qlocal4a_cinema (timeΛ X p) Y W o.a Q.table Q.halo I=∫ z,payment (o:=o) M D X p (Pond.spill I z)* (node X p R Q o.a L' (Pond.spill I z)) ∂ Fan.pool I X p:=by
    let Z:= timeΛ X p; let K:= team M D
    have hf (x:F.Slice G)(b:Air f G): K.qlocal4a_floret (Z.wrapY x) Y W o.a Q.table (Matter.own Y) Q.halo b= payment (o:=o) M D X p b* (node X p R Q o.a L' b):= by
       unfold Team.qlocal4a_floret; rw [if_pos (show (K.signs S)⊆ Y from by rw [show K.signs S=D.reach from Merge.Palette.label M D]; exact hh), show Y\ K.signs S= Fan.arm L' from (label M D|>.symm ▸ hq)]
       apply congr_arg₂ (·*·) (tightenM (o:=o) M D X p b x) _
       unfold node Polar.floating; rw [arm,prod_image]; swap; · exact fun i _ j _ h=> runOut h
       refine prod_congr rfl fun i _=> congr_arg (fun x=>Real.exp x-1) (wrapV X x p b i) -- k.B
    have hv(z:Body (↥I))(x): (W'|>.qlocal4a_floret (Z.wrapY x) Y W o.a Q.table (Matter.own Y) Q.halo (Pond.spill I z))=_:= hf x (Pond.spill I z)
    dsimp only [Z] at hv; unfold Team.qlocal4a_cinema; simp_rw [hv]; rw [integral_const,probReal_univ,one_smul]; exact (Shield.recommends _ h _).symm
omit hh hq
variable (hX:X.x=t)(hK:X.width=o.K)(hp:(timeΛ X p).manifest)
include H hX hK hp he
omit [Fintype ι] in
lemma prides (hT:Stamp T) (b:Air f G) (x: Directions G c)(hβ:p=(gStep R.beta,x)) (hf:∀ i: Tubular f G, |b i|≤ postponement L t o): payment (o:=o) M D X p b= oils M φ D X p b:=by
    obtain ⟨ht,h,hB⟩:= Fan.incomeA X H hX hK hT x p hβ hp b hf
    unfold payment Team.paidU team; rw [Finset.prod_image]; swap; · exact fun i hi j hj hz=> D.prop hi hj (congr_arg (fun i:Leaf R=> i.turn.badge S) hz)
    refine prod_congr rfl fun i hi=>?_ ; unfold Leaf.paidU Leaf.fond; rw [h, ←ht, (he i hi).reads,mul_one,masked_eq _ _ _ _]; unfold Healthy; rw [hB]; simp
end YM.LocalLTE.Fan
