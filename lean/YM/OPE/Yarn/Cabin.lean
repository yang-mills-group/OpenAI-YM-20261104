import YM.OPE.Yarn.Pit
/-! # Paying singlets at the very same history with custom rung
- Uses the exact Legend, retains the solo path as data. Adapted from
Replicas/Flank and Aeolus. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I: Type}[Fintype I][DecidableEq I]{G:Gauge}{n: Side} {C:Family G} {k z i j p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ) {w:ℝ} {x:C.label d} {X:Extra.Histories.Music (C.labels.level d) C.path N p}
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "F" => C.labels.level d
local notation "L" => C.localSection d
local notation "X!"=> ((C.factory d N p).terminal)
variable (o:∀ i, Site (C.S.side i p)) (hc:∀ i:ℕ,k ≤ i→ i<N→ o (i+1)= (C.path.levels.clock.op i p).ratio.embed (o i))
include H
lemma curtain (hv:C.ref d ≤ k)(hk:k ≤ N): ∃ X:Extra.Histories.Music (C.labels.level d) C.path N p, Patrol.Lyrics X W (waybill C.path.levels) D:=by obtain ⟨X,hX,hL,hY,hθ⟩:= (H.cuts.system.costs.aim d N p (hv.trans hk)).lyrics; exact ⟨X,hX,hL,hY,hθ⟩
structure Patent (C:Family G) (N p:ℕ) (t: Site (C.S.side N p))(F':Lamp G (C.S.side N p))(q:Config G (C.S.side N p)→ℂ)(w:ℝ) : Prop where
   pays : Continuous q
   writes U: ((C.path.rep N p N).eval U:ℂ)* q U=F'.disburse (C.path.rep N p N) U
   patent : ∃ (z : MergeProof.Response G (C.side N p)) (x:ℝ), Attainment (C.path.rep N p N).p t z x ∧ w*x ≤ far C.path.levels N ∧ hook (C.path.rep N p N).activities (C.path.rep N p N).p.threshold z=F'.rays (C.path.rep N p N)
omit H in
lemma bond_paid {i:ℕ}(hq:C.ref d ≤ i) (hv:i ≤ N)(h:Patrol.Lyrics X W ψ D) : bond P N p X i ((X!).symm x) = Spindle.paid C d i N p x:=by
    have hp:parcel C d i N p x=(X.tone i).plays ((X!).symm x):=by unfold parcel; rw [h.entries];rfl
    unfold Next.Rank.Spindle.paid Price.awake Price.columns; rw [Size.smul]; unfold bond; congr 1;rw [← (h.sung.earned i hq hv).currents ((X!).symm x)]; exact congr_arg (C.labels.level d).coeffSize (congr_arg Coefficient.x hp.symm)
include hc
lemma first_wish (h: Patrol.Lyrics X W ψ D)(hx:C.ref d ≤ k)(hk:k ≤ N)(hw:0<w)(hp:w*bond P N p X k x ≤ ζ d k): ∃ S, Drive P k N N p o (stair η w k) D S le_rfl ∧ Patent C N p (o N) (S N) (C.O N p (X! x) (o N)) (stair η w k N)∧ ∀ i:ℕ,k ≤ i→ i≤N → (S i).watch=soarF P L N p X x (1,false) o i ∧ (S i).rays (R i) = soarK P N p X x (1,false) o i:=by
    obtain ⟨b,hQ,hL,hB,hb,hH⟩:= H.cuts.system.costs.heights d k N p hx hk
    have hZ:= h.sung; have hs:Sung L P N p C.params W k X:= ⟨hZ.head,hk, fun i hi=> hZ.earned _ (hx.trans hi), fun i hi=>hZ.step _ (hx.trans hi)⟩; let q i:=stair η w k i; have hv i:= H.protectors w hw k i; have hx'(i)(he:k ≤ i): q (i+1)=η i*q i:= H.fall_march he
    obtain ⟨f,hF,hh⟩:= stater P C.params L W (ζ d) (far T) ψ b k N p X x (1,false) o (stair η w k) D H.seed.wilson (H.seed.sections d) hs (fun m h _=> hv m) (fun i hi _=> H.stair_factor _ i.lt_succ_self hi hw) (by
       apply cost_chain P C.params L W (ζ d) k N p X x q (κ:=k) _ (fun i _ _=>(hv i).le) hk _ (fun i _ _=>hv i) H.cuts.system.costs.cost H.cuts.system.costs.back hs _ -- edit
       · exact le_rfl
       · intro i h hp; rw [hx' i h]; exact le_trans (le_of_eq (b:=η i* (((C.S.block i).val:ℝ)^d * (C.path.levels.params (i+1)).columns)*ζ d i*q i) (by ring)) (mul_le_mul_of_nonneg_right (hL.cost i h) (hv i|>.le))
       rw [show q k =w from H.anchor_march hw]; exact hp
       ) hQ hB hb hH hc (h.coins _) (fun i hi he=>by obtain ⟨v,K,hp,hz⟩:=H.cuts.system.costs.night.days N p i he; exact ⟨h.bells i (hx.trans hi) he,hp.propagate⟩)
    let S i:= if hi:k ≤ i ∧ i≤N then Lamp.mk (soarF P L N p X x (1,false) o i) (f i) (hF.stocked i hi.1 hi.2) else default
    have hΩ(i)(he:k ≤ i)(hp:i ≤ N): (S i).watch=soarF P L N p X x (1,false) o i∧ (S i).sparks=f i:= by unfold S; simp [he,hp]
    refine ⟨S,⟨fun i hi he=>?_⟩,?_,fun i hi he=>⟨(hΩ _ hi he).1,(by unfold Lamp.rays; rw [(hΩ _ hi he).2]; exact hh i hi he)⟩⟩
    · obtain ⟨Y,v,s,t,hy,hX,hξ,hu,H⟩:= hF.sways i hi he; let hh:= hΩ (i+1) (hi.trans i.le_succ) he; let hq:=hΩ i hi he.le; refine ⟨⟨Y,v,s,t,hy,?_,hX,hξ,hu⟩,?_⟩
      · unfold Lamp.rays; rw [hh.1,hh.2,hq.2]; nth_rw 2 [hc i hi he]; rw [Ratio.embed_parent]; exact H
      unfold Lamp.disburse; rw [hh.1,hh.2,hq.1,hq.2]; exact hF.feeds i hi he
    have ht: stepUp (1,false) (o N) (Source.initial L P N p x 0)=C.O N p ((X!) x) (o N):= by
       rw [show Source.initial L P N p x 0=C.O N p _ 0 from ?_]; exact itemT C _ _ _ H.seed .. -- edit direction
       unfold Family.O TransferData.cylinder; rw [LinearEquiv.symm_apply_apply]
    refine ⟨C.continuousO ..,?_,?_⟩; · intro U; rw [← ht]; unfold Lamp.disburse; rw [(hΩ N hk le_rfl).1,(hΩ N hk le_rfl).2]; exact hF.writes U
    unfold Lamp.rays; rw [(hΩ N hk le_rfl).2]; exact hF.patent
omit hc
-- arbitrary starts through Wage
local notation "V" => (Site (C.side j p))
lemma bloom {o:I→Site (C.side N p)}{x:I→ Config G (C.side N p)→ℂ}{w:I→ℝ}{X:I→Lamp G (C.S.side N p)} (hn:j ≤ N)(hc: Occupancy ((royal C j p N).place o) (r N))(hw:∀ i,0<w i)(hp:∀ i, Patent C N p (o i) (X i) (x i) (w i)): ∃ Q, Wagon C N p j N hn le_rfl Q x ∅ o X w := by
   let Q':= (R N); let S:= royal C j p N; let v:=S.head; let G':= S.lamp X; let t:= Names V I; let F₀:=birth t Q' (S.calls x); have hT : Script P N p hn le_rfl Prod.fst (Finset.univ ×ˢ (∅:Finset I)) F₀ (S.calls x):=by
      refine Script.born hn _ H.seed.wilson fun i=>?_ ; rw [callsR hn]; exact GridApprox.replica_env _ _ (RG.Envelope.compactC (hp i.2|>.pays))
   have he:= H.cuts.system.costs.night.endow N; have hC:=(H.seed.wilson.represents N p N le_rfl); let φ i:= ((hC.good.labels.moves (S.spin i).1 (S.center i)).some)
   choose O y ht he' hu using fun i=>(hp i).patent; let Z (j:V×I):=if j.1=v then O j.2 else upwards (S.spin j.1) (S.center j.1) (O j.2)
   have hz(j:V×I): Attainment Q'.p (S.place o j) (Z j) (y j.2):=by unfold Z Brigade.place; split; exact ht j.2; exact rise _ _ (ht j.2)
   let e:ℝ:= (C.path.levels.budget N).supportExponent-3; obtain ⟨hZ,hU,hI,hF⟩:= he; obtain ⟨K,hK,hK',hK0⟩:= S.candle P _ _ X H.seed.wilson (le_refl N); let u:= far T N
   have hΩ : Garnish Q'.p (S.place o) Z (w ∘ Prod.snd) Q'.p.supportExponent u:= cloth hz (fun i=>he' i.2) (fun i=>(hw i.2).le)
   have hA:= hI; unfold Q' at * -- maybe
   refine ⟨F₀,hT,?_, hT.budget,hw⟩; rw [← show (fun i=> profile (R N|>.activities) (K i))=S.ray (R N) X from funext hK']; rw [hC.vac]
   -- rewriting p changes output.Mirror nurture
   apply spawn hC.good.labels Z hΩ _ S.moves (fun i=>⟨φ i⟩) hc hZ (fun i=>hw i.2) le_rfl hU _ _ (fun U=>(Tour.bright P H.seed.wilson N p _ le_rfl U).ne') zero_le_one hK _ _
   · intro i hi j; simp [Z,(show i ≠ v from hi),(show S.head=v from rfl)]
   · rw [hC.vac]; linarith only [hI]
   · rw [hC.vac]; exact hF
   · rintro ⟨i,j⟩; rw [hK']; by_cases hi:i=v; subst i; unfold Z Brigade.ray; rw [if_pos rfl,if_pos rfl]; exact hu j
     unfold Z Brigade.ray; rw [if_neg hi, if_neg hi, hooked _ _ (φ _), hu]
   rintro ⟨i,j⟩ U; by_cases hi:i=v; subst i; rw [hK0]; unfold Brigade.lamp Brigade.calls; rw [if_pos rfl,if_pos rfl]; exact (hp j).writes U
   rw [show S.calls x (i,j)= _ from (if_neg hi:S.calls x (i,j)=stepUp (S.spin i) (S.center i) (x j)),show S.lamp X (i,j)=stepUp (S.spin i) (S.center i) (X j).watch from if_neg hi,opals (S.spin i) P H.seed.wilson (le_refl N) (S.center i) (X j).watch (φ i) (X j|>.lit) (hK (i,j)) (by rw [hK']; unfold Brigade.ray; rw [if_neg hi]; rfl),stepUp]; simp_rw [stepUp,show ∀ U,coin (R N) (X j).watch (X j).sparks U= _ from fun U=>(hp j|>.writes _).symm, scalar_mul, Motion.scalar_real]; rw [WardBin.Wheels.rep_spins (S.spin i).1 H.seed.wilson le_rfl]
end YM.OPE.Yarn

