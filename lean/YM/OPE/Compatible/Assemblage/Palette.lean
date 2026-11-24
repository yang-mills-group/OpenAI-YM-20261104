import YM.OPE.Compatible.Assemblage.Threshold
/-!
# One fixed-family calibration followed up to *its own* starting depth
Using actual C cylinders. Can choose the depth separately on every slot.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Next.Rank
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{N p k q j d:ℕ}{V:Type}[Fintype V][DecidableEq V]{P:Ensemble V}
variable {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}
variable {Z o:Track C.path V p}{v:C.label d}{a:ℝ}
variable (hC:C.Makes)(hp:Scrim C W u ψ φ δ ζ r D)
set_option quotPrecheck false
local notation "g"=> fun x y=>stepUp (P.move x) (o N x) (C.O N p v 0) y
local notation "F"=> C.labels.level d
local notation "Y"=> C.localSection d
local notation "H"=> C.path
local notation "θ"=> C.factory d N p
local notation "ς"=>((C.factory d N p).terminal.symm v)
def purse (w:ℝ)(φ:ℕ→ℝ)(k i:ℕ):= march (fun _:Unit=>w) φ k i ()
-- proceedings through exact Stamp, and affordable rough reprogram secondary move from the stop independent of the actual copy orientations finally chosen.
include hC hp
set_option maxHeartbeats 200000 in
lemma harvest (hN:k+1≤ N)(hk:C.ref d≤ k)(ha:0<a)
    (h_b:a*Spindle.paid C d (k+1) N p v≤ζ d (k+1))(h_o:Migrating C.path (k+1) p N o)
    (hx:∀ x i,k+1 ≤ i → i ≤ N → x≠P.v→ o i x= affine (P.move x).1 (Z i x) (o i P.v)):
    let w:=purse a φ (k+1)
    ∃ X:Travel C.path V p, Run P D N p (k+1) N Z o X w∧ Budges P C.path N p (u N) (w N) (Z N) (X N) g ∧ (∀ i:ℕ,k+1 ≤ i→ i ≤ N→ Stamp (N:=N) P (C.localSection d) (Z i) ((C.factory d N p).entries i ((C.factory d N p).terminal.symm v)) (X i)) ∧ ∃ c:ℂ, a*‖c‖≤1 ∧
     Blade (C.path.rep N p (k+1)) (o (k+1) P.v) ((X (k+1)).oil P.v) (profile (C.path.rep N p (k+1)).activities ((X (k+1)).gas P.v)) c (1/a):=by
   intro w; let b:= k+1; have hk':C.ref d≤ b:= hk.trans k.le_succ
   obtain ⟨M,hI,hS,hK,hY⟩:= (hp.costs.aim d N p (hk'.trans hN)).lyrics
   obtain ⟨t,hF',hD,hY',hr,hV'⟩:= hp.costs.heights d b N p hk' hN
   let Y':= C.localSection d; let v':=ς; have he:k<N:=hN
   let Q(i):= (M.tone i).plays v'; have hζ(i): (θ).entries i (ς)=Q i:=by rw [hI]; rfl
   have hf:Brine H b δ φ:=⟨fun i _=> hp.costs.stay.water _ (Nat.zero_le i),fun i _=>hp.costs.stay.mint _ (Nat.zero_le i),fun i _=>hp.costs.stay.split _ (Nat.zero_le i),fun i _=>hp.costs.stay.support _ (Nat.zero_le i)⟩
   have hz : Sung Y' H N p C.params W b M:= ⟨hS.head,hN,fun j hi=> hS.earned _ (hk'.trans hi),fun j hi=> hS.step _ (hk'.trans hi)⟩
   have hw(i:ℕ)(h:b ≤ i):0<w i:= march_pos _ _ _ _ _ (fun _=>ha) hf i h _
   have hu'(i:ℕ)(h:b ≤ i):w (i+1)=φ i*w i:=by change purse a φ b _=φ i * purse a φ b i; unfold purse; rw [march,if_pos h]
   have hw': w b=a:= congr_fun (marines _ φ _ (fun _=>ha)) ()
   have ht:w b*bond H N p M b v' ≤ ζ d b:=by
     rw [hw']; refine le_trans (le_of_eq (congr_arg (a*·) ?_)) h_b; unfold Spindle.paid Price.awake Price.columns; rw [Size.smul]; unfold bond; congr 1; rw [← (hz.earned b le_rfl hN).currents v']; change (F).coeffSize (Q b).x= (F).coeffSize ((θ).entries b ς).x; rw [hζ]
   have h_f : ∀ i:ℕ,b ≤ i → i ≤ N → w i*bond H N p M i v' ≤ ζ d i:=by
       refine cost_chain H C.params Y W (ζ d) b N p M v' w le_rfl (fun i hi _=> (hw i hi).le) hN (fun i hi hn=>?_) (fun i hi _=> hw i hi) hp.costs.cost hp.costs.back hz ht
       rw [hu' i hi]; refine le_trans (le_of_eq (b:=φ i*(((C.S.block i).val:ℝ)^d * (C.path.levels.params (i+1)).columns)*ζ d i*w i) ?_) (mul_le_mul_of_nonneg_right (hD.cost i hi) (hw i hi|>.le))
       have hl:C.S=C.path.S:=rfl
       rw [hl]; ring
   have h_w : Guided Y C.params H N p b N Q D w:= wake_earned Y (fun i hi _=>hw i hi) (fun i hi _=> by rw [hu' i hi]; exact mul_le_of_le_one_left (hw i hi|>.le) (hD.level _ hi)) hF' M _ hz (fun i hi hn=> hK i (hk'.trans hi) hn) h_f
   have hc:= hC.wilson; obtain ⟨hf,a₀,H_A⟩:= h_w.fits N hN le_rfl
   obtain ⟨X,h_X,h_K⟩:= realize P Y (o N) hc le_rfl (fun x he=>hx x N hN le_rfl he) hf H_A (hC.sections _)
   have he' (i:ℕ)(hk:i<N) : SoundDoor (C.path.levels.clock.op i p) (D N p i hk):= by obtain ⟨v,z,h,-⟩:= hp.costs.night.days N p i hk; exact h.propagate
   obtain ⟨O,hO,hE,h_R⟩:= prints P Y h_w hc (hC.sections _) (fun i _=>he' i) (O:=Z) le_rfl hN X h_X h_K h_o (fun i hi hp x ht=> hx x i hi hp ht)
   refine ⟨O,hO,?_,fun i hi ht=> (hζ i).symm ▸ h_R i hi ht,?_⟩
   · rw [hE]; apply authenticated Y hz (hC.sections _) hY' hr hV' (hY _) hc (h_f N hN le_rfl) (hw N hN) h_X; intro i; rw [h_K]; rfl
   refine ⟨_,hw' ▸ h_w.spice b le_rfl hN, ?_⟩
   -- get Tale using Sung instead of Guided to lift from k preceding. Price purchased with Fiesta at k to fix missing k+1 ink, while C input at b was priced there.
   obtain ⟨t',hK',-⟩:= hp.costs.heights d k N p hk (le_of_lt he)
   obtain ⟨s,hx',hQ⟩:= hK k hk he; let q':= (M.tone b).index v'; have hf: (Q b).x=q':= (hz.earned b le_rfl hN).currents _
   let Z':=orbitCost F*(F).coeffSize q' * (ψ k+2*((H).levels.params b).columns); let w':= (M.tone k).charge v'
   have hv: Tale s 0 0 ((((H).S.block k).val:ℂ)^d) ((Q b).exponentialEntry 0 Y ((H).rep N p b)) (profile (C.path.rep N p b).activities (Q b).forced) (profile (C.path.rep N p k).activities (Q k).forced) ((Q b).x 0) Z' w' (D N p k he):=by rw [hf]; exact hQ _
   let Y₀:=(C.path.levels.clock.op k p).ratio; obtain ⟨p',h_T,hz'⟩:= stamped_hop Y (Q k) (Q b) hc he (he' _ he) hv hx' 0; rw [show Y₀.embed 0=0 from Y₀.root.map_zero] at hz'
   -- blade+sacc.
   let R:= (H).rep N p b; let x:=o b P.v; let v₀:= alto H b d; let f':= v₀ • (Q b).exponentialEntry 0 Y R; let k':= v₀ • profile R.activities (Q b).forced
   obtain ⟨p₀⟩:= (hc.represents N p b hN).good.labels.moves (1:Signed) x
   obtain ⟨_,_,hU,-⟩:= hp.costs.night.days N p k he
   have h : Blade R 0 f' k' (v₀*((Q b).x 0)) (2*(‖v₀‖*Z')):=by simp only [radiant,sunny,Ribbons.stepid,Ribbons.floatid] at hz'; exact chronicle _ _ h_T hz' hU.tunes (he' k he)
   let m:Motion := (1,false); have hb:= bearer m x f' k' p₀ h; rw [scale_F,scale_K,show affine m.1 x 0=x from by simp [affine]] at hb
   rw [(h_R b le_rfl hN).price, (h_R b le_rfl hN).real', hO.steers b le_rfl hN]; apply hb.more; apply (le_div_iff₀ ha).2
   let C₀:= orbitCost F*(ψ k+2*((H).levels.params b).columns); have hu:C₀ ≥0:=mul_nonneg (zero_le_one.trans (orbitCost_one_le ..)) (add_nonneg (hK'.tap k le_rfl) (mul_nonneg (by norm_num) (zero_le_one.trans ((H).levels.params b).columns_ge)))
   have hz':a*bond H N p M b v' ≤ ζ d b:= hw' ▸ ht; have hf':Z'=C₀*(F).coeffSize q':=by unfold Z' C₀; ring
   rw [show 2*(‖v₀‖*Z')*a=2*C₀*(a*bond H N p M b v') from ?_]; exact (mul_le_mul_of_nonneg_left hz' (mul_nonneg zero_le_two hu)).trans ((show 2*C₀*(ζ d b)≤1 from by unfold C₀; rw [← mul_assoc]; exact hK'.room k le_rfl))
   rw [hf']; unfold bond q' v₀; ring
end YM.MergeProof.Ribbons.ManyCopies.Stem
