import YM.OPE.Yarn.Broker
/-! # Strobe bloom implies read of that literal birth. Port bloom. -/
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
local notation "V" => (Site (C.side j p))
lemma rosate {o:I→Site (C.side N p)}{x:I→ Config G (C.side N p)→ℂ}{w:I→ℝ}{X:I→Lamp G (C.S.side N p)} (hn:j ≤ N)(hc: Occupancy ((royal C j p N).place o) (r N))(hw:∀ i,0<w i)(hp:∀ i, Patent C N p (o i) (X i) (x i) (w i)): Wagon C N p j N hn le_rfl (birth (Names V I) (R N) ((royal C j p N).calls x)) x ∅ o X w := by
   let Q':= (R N); let S:= royal C j p N; let v:=S.head; let G':= S.lamp X; let t:= Names V I; let F₀:=birth t Q' (S.calls x); have hT : Script P N p hn le_rfl Prod.fst (Finset.univ ×ˢ (∅:Finset I)) F₀ (S.calls x):=by
      refine Script.born hn _ H.seed.wilson fun i=>?_ ; rw [callsR hn]; exact GridApprox.replica_env _ _ (RG.Envelope.compactC (hp i.2|>.pays))
   have he:= H.cuts.system.costs.night.endow N; have hC:=(H.seed.wilson.represents N p N le_rfl); let φ i:= ((hC.good.labels.moves (S.spin i).1 (S.center i)).some)
   choose O y ht he' hu using fun i=>(hp i).patent; let Z (j:V×I):=if j.1=v then O j.2 else upwards (S.spin j.1) (S.center j.1) (O j.2)
   have hz(j:V×I): Attainment Q'.p (S.place o j) (Z j) (y j.2):=by unfold Z Brigade.place; split; exact ht j.2; exact rise _ _ (ht j.2)
   let e:ℝ:= (C.path.levels.budget N).supportExponent-3; obtain ⟨hZ,hU,hI,hF⟩:= he; obtain ⟨K,hK,hK',hK0⟩:= S.candle P _ _ X H.seed.wilson (le_refl N); let u:= far T N
   have hΩ : Garnish Q'.p (S.place o) Z (w ∘ Prod.snd) Q'.p.supportExponent u:= cloth hz (fun i=>he' i.2) (fun i=>(hw i.2).le)
   have hA:= hI; unfold Q' at * -- maybe
   refine ⟨hT,?_, hT.budget,hw⟩; rw [← show (fun i=> profile (R N|>.activities) (K i))=S.ray (R N) X from funext hK']; rw [hC.vac]
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

