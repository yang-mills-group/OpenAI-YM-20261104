import YM.LocalLTE.Hall.Trim
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Channels
/-! # Re-box in curved coordinates, maintaining ambient jets -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox.Hall
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
open AnalyticBridge GaussianFieldAlignment GaussianFieldAlignment.Locations SectorMeasure.Oriented
variable {G : Gauge} {c :Side} {m d:ℕ}
variable (s: Signed) (b : Site c) {o:Site c}
open Grove
abbrev turnX (t:Site c):=affine s b t
local notation "a"=>turnX s b
lemma smallest (i:Bond c) (y:Site c): fits i y m ↔ fits (sendEdge s b i) (a y) m:= by
   have hh (j:Bond c)(y:Site c):fits j y m ↔ pinPos j ⊆ neighbors m y := by unfold fits pinPos; rw [Finset.insert_subset_iff,Finset.singleton_subset_iff]
   rw [hh,hh,GaussianFieldAlignment.Locations.pin_map]
   simp only [Finset.image_subset_iff]; have hx i: separation (a y) (a i)=separation y i:= by simp [turnX,affine]
   constructor
   · intro h j hk; apply (neighbors_mem ..).mpr; rw [show affine s b j=a j from rfl,hx]; exact (neighbors_mem ..).mp (h hk)
   intro h j hk; exact (neighbors_mem ..).mpr (hx j ▸ (neighbors_mem ..).mp (h j hk))
lemma turn_lad (p q:Site c) : lad (a p) (a q)= lad p q:=by
   unfold lad; rw [turnX,turnX,affine,affine,add_sub_add_right_eq_sub,← s.act_sub]; rw [← Equiv.sum_comp s.perm]; refine Finset.sum_congr rfl fun i hi=> ?_
   simp only [Lattice.lift,Signed.act_at]; split; next h=> rw [ZMod.natAbs_valMinAbs_neg]
   rfl
local notation "τ"=> StepData.sendSites s b
lemma neo {i:Site c} {o:Site c} (h:i ≠ τ o): (τ).symm i≠o:= by intro hx; exact h ((Equiv.symm_apply_eq _).1 hx) -- edit
variable (X:Grove o)
lemma away (i j:Site c): separation (τ i) (τ j)=separation i j:= by change separation (a i) (a j)=_; simp [turnX,affine]
def transplanted : Grove (τ o) where
   parent i h:= τ (X.parent ((τ).symm i) (neo s b h))
   link i h := Step.rotate (X.link ((τ).symm i) (neo s b h)) s
   stops i hi:= by change affine s b _ + _ = _; rw [← GaussianFieldAlignment.Locations.affine_plus s]; simp_rw [Grove.stops]; exact (τ).apply_symm_apply i -- edit
   shrinks i hi:= by let u:= (τ).symm i; have he (x y:Site c) : lad (τ x) (τ y)=lad x y:= turn_lad s b x y; rw [he]; have hx:= X.shrinks ((τ).symm i) (neo s b hi); rw [← he o ((τ).symm i),Equiv.apply_symm_apply] at hx; exact hx
   closer i hi:= by rw [away]; refine le_trans (X.closer (τ|>.symm i) (neo s b hi)) ?_; rw [← away s b o (τ|>.symm i),Equiv.apply_symm_apply]
local notation "W"=> transplanted s b X
lemma parents (i:Site c)(h:i≠o) : (W).parent (τ i) (show τ i ≠ τ o from fun he=> h ((τ).injective he)) = τ (X.parent i h):= by apply congr_arg (τ); congr 1; apply Equiv.symm_apply_apply
lemma links (i:Site c)(h:i≠o) : (W).link (τ i) (show τ i ≠ τ o from fun he=> h ((τ).injective he)) = Step.rotate (X.link i h) s:= by unfold transplanted; simp only [Equiv.symm_apply_apply]
lemma trans_road (i:Site c) : (W).road (τ i)=(X.road i).map (·.rotate s):=by
    rw [Grove.road,Grove.road]; by_cases h:i=o
    · rw [dif_neg (fun hi=> hi (congr_arg (turnX s b) h)),dif_neg (not_not_intro h)]; rfl
    rw [dif_pos h,dif_pos (show τ i≠ τ o from fun hx=> h ((τ).injective hx)), List.map_append,List.map_cons,List.map_nil, links s b X i h,parents s b X i h]; exact congr_arg (fun v=> v++_) (trans_road _)
termination_by lad o i
decreasing_by exact X.shrinks ..
lemma uplights (U: Config G c)(i:Site c) : X.uplink (pull s b U) i=(W).uplink U (τ i):= by unfold Grove.uplink; rw [travel_pull,trans_road]; rfl
lemma orient (U: Config G c) : pull s b ((W).fix U)=X.fix (pull s b U):=by
   funext i; unfold Grove.fix; change ((posDir i.2).rotate s).read _ _= X.uplink (pull s b U) i.1 * _ * _
   rw [uplights,uplights,Step.gauge_read,← GaussianFieldAlignment.Locations.affine_plus]; rfl
lemma pact (m:ℕ)(i:Bond c): (W).Twig m (sendEdge s b i)↔ X.Twig m i:=by
   have he (i: Site c)(h:i≠o): sendEdge s b ((X.link i h).used (X.parent i h)) = ((W).link (τ i) (show τ i ≠ τ o from fun he=> h ((τ).injective he))).used ((W).parent (τ i) (show τ i ≠ τ o from fun he=> h ((τ).injective he))):= by rw [Hall.parents,Hall.links,GaussianFieldAlignment.Locations.send_used]; rfl -- dep motives issue edit
   have hk(j:Site c): j∈neighbors m o ↔ τ j ∈ neighbors m (τ o):= by rw [neighbors_mem,neighbors_mem, Hall.away]
   constructor
   · rintro ⟨j,h,hp,H⟩; obtain ⟨j,rfl⟩:= (τ).surjective j; have hi:j≠o:= fun h'=> h (congr_arg (turnX s b) h'); refine ⟨j,hi,(hk j).mpr hp,(StepData.sendBonds s b).injective ?_⟩; exact (he j hi|>.trans H)
   rintro ⟨j,hj,hp,H⟩; let e:τ j≠τ o:= fun he=> hj ((τ).injective he); exact ⟨τ j,e,(hk j).mp hp,(he j hj).symm.trans (congr_arg (sendEdge s b) H)⟩
def crane : Directions G c→L[ℝ] Directions G c:= ContinuousLinearMap.pi (fun i=> if s.flip i.2 then -ContinuousLinearMap.proj (sendEdge s b i) else ContinuousLinearMap.proj (sendEdge s b i))
lemma valCrane (v:Directions G c) (i:Bond c): crane s b v i = if s.flip i.2 then -v (sendEdge s b i) else v (sendEdge s b i):= by unfold crane; rw [ContinuousLinearMap.pi_apply]; split <;> rfl
lemma rotated {κ v:ℝ} (h : Reliable G κ v) (U:Config G c)(m:ℕ): X.crook m Chi.canonical κ (pull s b U)=crane s b ((W).crook m Chi.canonical κ U):= by
   funext i; unfold crook; rw [valCrane]; have he:X.Spare m i↔ (W).Spare m (sendEdge s b i):= and_congr (smallest ..) (not_congr (pact ..|>.symm)); by_cases hp:X.Spare m i
   · simp only [shore_apply,if_pos hp,if_pos (he.mp hp)]; rw [← Hall.orient s b X, Channels.read_back]; cases H : s.flip i.2
     · simp
     simp only [if_true]; exact h.inverse Chi.canonical _
   simp only [shore_apply,if_neg hp,if_neg (mt he.mpr hp),neg_zero,ite_self]
-- global Poly convention
lemma packet {κ v:ℝ}(h: Reliable G κ v) (m:ℕ) (P:Cabana.Pkt (Directions G c) d) : FrameBox.realise X m κ P ∘ pull s b = realise W m κ (fun i=> (P i).compContinuousLinearMap (fun _=> crane s b)):= by
   funext U; unfold realise; simp only [Function.comp_apply,rotated s b X h U m,Cabana.actual,Finset.sum_apply]; rfl
end YM.LocalLTE.FrameBox.Hall
