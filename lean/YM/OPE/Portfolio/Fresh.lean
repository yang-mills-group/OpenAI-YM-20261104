import YM.OPE.Portfolio.Nudge
import YM.OPE.Replicas.Aeolus
/-!
# Start with many simultaneous branches headed to different enactment levels. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{H:History G}{N p m i b:ℕ}
set_option quotPrecheck false
variable (L:Playout H p m N V){I:Type}[Fintype I][DecidableEq I]
variable {r:ℕ→ℕ}{A: ∀ N p m:ℕ,m<N→ GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{δ φ:ℕ→ℝ}{X:I→ Config G (H.S.side N p)→ℂ}{f:I→ Cup (H.rep N p N)}
local notation "Δ"=> H.rep N p N
local notation "E"=> (H.levels.budget N)
structure Entrance (H:History G) (N p:ℕ)(o:Site (H.S.side N p)) (f:Cup (H.rep N p N))(F:Config G (H.S.side N p)→ℂ) (W x:ℝ) : Prop where
    income U: ((H.rep N p N).eval U:ℂ)*F U=f.pays U
    discrete: ∃ ψ:Response G (H.S.side N p),∃ h:ℝ,Attainment (H.rep N p N|>.p) o ψ h ∧ W*h ≤ x ∧ hook (H.rep N p N).activities (H.rep N p N).p.threshold ψ=f.leaves
namespace Playout
lemma generation (s:Ward (Names V I)) (h:H.Selected)(ht:Moonlit H r δ φ A) {o:I→Site (H.S.side N p)}{W:I→ℝ} (hm:m≤N)(hp:L.occupied (r N) o)(hw:∀ i,0<W i) (hh:∀ i,Entrance H N p (o i) (f i) (X i) (W i) (φ N)) : L.Market s o f (L.intention X N le_rfl) W ((E).supportExponent-3) :=by
    unfold intention; rw [gust_base]; obtain ⟨k,hk,hK⟩:= L.representing f h hm le_rfl
    choose ψ t hF hW hκ using fun i=> (hh i).discrete
    let v:=L.primary; let Z:=Δ; have hA:= h.represents N p N le_rfl; let Q i:=L.positions N i; let a:= L.tint; let u(i:V×I):= if i.1=L.primary then ψ i.snd else upwards (a i.1) (Q i.1) (ψ i.2)
    have hb:=hA.vac; obtain ⟨hc,hY,hψ,hI⟩:= ht.endow N
    let F'(i:V×I):= stepUp (a i.1) (Q i.1) (X i.2)
    let π i:= (hA.good.labels.moves (a i).1 (Q i)).some
    have ht(k:V×I): Attainment Z.p (L.spectrum N o k) (u k) (t k.snd):= by
       obtain ⟨i,k⟩:=k; unfold u; split; next hr=> change i=v at hr; rw [hr,L.principal o hm le_rfl k]; exact hF k
       exact rise _ _ (hF _)
    refine ⟨hw, Bard.of_serves s ?_⟩
    rw [hK]; let q:=r N; let φ':=φ N
    have hw'(i:V×I):0 < W i.snd:= hw _; apply spawn (F:=F') hA.good.labels u (cloth ht (fun i=>hW i.snd) (fun i=>hw' i|>.le)) ?_ (fun i _=>L.swapped i) (fun i=>⟨π i⟩) hp hc hw' le_rfl hY ?_ (by rw [hb]; exact hI) (fun U=>(Tour.bright H h N p _ le_rfl U).ne') zero_le_one hk ?_ ?_
    · intro i hi j; unfold u; simp [hi]
    · rw [hb]; exact hψ.trans_eq (by ring)
    · rintro ⟨b,i⟩; change _= profile _ (k (b,i)); rw [show profile _ (k (b,i))= _ from congr_fun hK.symm (b,i)]; unfold u; split; next he=> change b=L.primary at he; rw [he,L.fleur f hm le_rfl]; exact hκ i
      rw [hooked _ _ (π b), hκ i]; rfl
    intro i U; obtain ⟨b,i⟩:=i; have he : coin Z (L.cupsReg N f (b,i)) (k (b,i)) = stepUp (a b) (Q b) (f i).pays:= opals (a b) H h le_rfl (Q b) (f i).home (π b) (f i).held (hk _) ((congr_fun hK.symm _).trans (congr_arg (floatUp (a b) (Q b)) (f i).fitted))
    rw [he]; unfold F' stepUp; simp_rw [← show ∀ U,(Z.eval U:ℂ)*X i U=(f i).pays U from hh i|>.income, scalar_mul, Motion.scalar_real]; unfold Z; rw [WardBin.Wheels.rep_spins (a b).1 h le_rfl]; first|rfl|done
end Playout
end YM.MergeProof.Ribbons.ManyCopies.Cadet
