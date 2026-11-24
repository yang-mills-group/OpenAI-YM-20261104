import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Devices
/-! # Apply the precursor `SingleLog` to the old shadow, as needed for Flash259HorizonFork

Parameters are real-scale comparisons. No degenerate exteriors in this application to
**fixed** true-scale exterior banks (all active in the Readout in G.5 against old shadow).
Supports uniformly away at every rotation. Make turn & tint pricing over the actual rotations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Filter Set Asymptotics MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open scoped Topology Classical BigOperators
open Node Log
attribute [local instance] YM.Work.A15.compact_ortho Orbits.measO Orbits.borelO
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {P:Prescription F.sector.derivatives}
    {I J V:Type}[Fintype I][Fintype J] {d:I→ℕ}{e:J→ℕ}{M δ:ℝ}
    (mn:0≤M)(dp:0<δ)
    {l:Filter V}{r:V→ℝ}{x:V→ I→E4}{o:V→E4}
local notation "late" => 𝓝[>] (0:ℝ)
local notation "charge" k:max => fun i:V=> r i ^ k / r i^(∑ i,d i) -- orderwise money
local notation "ρ" => F.room.kernel.spin
local notation "X" => F.sector.turns
variable (H:SingleLog F P) (u:Labels S d) (h:ℕ)
    (hr:Tendsto r l late) (hx:∀ᶠ i in l, WithinRoom (r i) M δ (x i) (o i))
    {y:V→J→E4} {a:ℝ}(ha:0<a)(hy:∀ᶠ i in l, ClearOf (o i) (y i) a)
local notation "Z" => fun i:V=> shadowOld P h (x i) (o i) u
include hx hr ha hy mn dp H
lemma purchased (v:Labels S e) (p:V→Viewers F) :
    Allowance l r (charge (h+1)) (fun i=> discrepancy (spectator F (p i)) h (x i) (o i) u (Z i) (y i) v) ∧
      ∀ᶠ i in l, Function.Injective (beside (x i) (y i)) ∧ Function.Injective (beside (sole (o i)) (y i)) := by
  obtain ⟨k,V⟩:= H.horizons I J (Orbits.names u) (Orbits.names v) _ _ _ dp mn ha h
  have hp := ((hr.eventually V).and (hx.and hy)).mono fun i e=> e.1 _ _ _ e.2.1 e.2.2
  refine ⟨⟨k,IsBigO.of_bound' ?_⟩,hp.mono fun i h=>⟨h.1,h.2.1⟩⟩
  filter_upwards [hp,hr.eventually self_mem_nhdsWithin,log_pays hr] with i ⟨hi,hh,H⟩ ht hv
  rw [discrepancy_old _ _ _ _ _ _ _ (spectate ..) (spectate_respects _ _) (spectate_ready ..) hh, Real.norm_of_nonneg (by change 0< r i at ht; positivity)]
  exact (H.phaseBound (p i)).trans_eq (mul_comm (badge _ ^ k) _)
lemma traces (p:V→Viewers F) (v:V→Labels S e) (hv:∀ j, Allowance l r (fun _=>1) (fun i=>v i j)) :
    Allowance l r (charge (h+1)) (fun i=> discrepancy (spectator F (p i)) h (x i) (o i) u (Z i) (y i) (v i)) := by
  simp_rw [far_distance]
  exact variate hr _ v (fun v=>by simpa only [far_distance] using ((purchased F mn dp H u h hr hx ha hy v p).1)) hv
omit ha hy
lemma margin (k : ℕ) : ∀ᶠ i in l, orbitMargin P k (x i) (o i) := by
  apply eventually_dock _ _ _ k
  · refine tendsto_pi_nhds.mpr fun j=>?_; refine squeeze_zero_norm' (hx.mono fun i h=> h.1 j) ?_
    simpa only [mul_zero] using ((tendsto_nhdsWithin_iff.mp hr).1.const_mul M)
  filter_upwards [hx,hr.eventually self_mem_nhdsWithin] with i h hi j k e; by_contra ne; have h:= h.2 j k ne; rw [e,sub_self,norm_zero] at h; exact (mul_pos dp hi).not_ge h

omit F hx hr H mn dp
lemma solid (e:Exterior C.book) : ∃ a:ℝ, 0<a ∧ ∀ (r:E4) (k:Ortho), ClearOf r (swung e k r) a := by
  have he:= beside_distinct.mp (bearing_clear e)
  have hp (i:Fin e.n) : 0 < ‖bearing e i‖ := norm_pos_iff.mpr ((show (0:E4)≠_ from he.2.2 () i).symm)
  have hq (i j : Fin e.n)(h:i≠j) : 0 < ‖bearing e i-bearing e j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (he.2.1.ne h))
  have H : ∀ᶠ i in late, ∀ u:Fin e.n, i ≤ ‖bearing e u‖ := eventually_all.mpr fun i=> eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (hp i))
  have HH : ∀ᶠ i in late, ∀ u v:Fin e.n, u≠v→ i ≤ ‖bearing e u-bearing e v‖ := eventually_all.mpr fun i=> eventually_all.mpr fun j=> eventually_all.mpr fun h=> eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (hq i j h))
  obtain ⟨a,e1,e2,e3⟩:= (H.and (HH.and self_mem_nhdsWithin)).exists; refine ⟨a,e3,fun o k=>?_⟩
  constructor
  · intro i; unfold swung; rw [norm_sub_rev o, add_sub_cancel_left]; exact (congr_arg (_ ≤ ·) (LinearIsometryEquiv.norm_map (Ortho.motion k) (bearing e i))).mpr (e1 i)
  intro i j h; unfold swung; rw [add_sub_add_left_eq_sub]
  change a ≤ ‖Ortho.motion k (bearing e i)-Ortho.motion k (bearing e j)‖ ; rw [ ← map_sub, LinearIsometryEquiv.norm_map ]; exact e2 i j h
lemma landed {E:Type}[NormedAddCommGroup E] (k:V→Ortho) (f:Ortho→E) (hf:Continuous f) : (f ∘ k) =O[l] fun i=>(1:ℝ) := by
  obtain ⟨C,hC⟩:=isCompact_univ.exists_bound_of_continuousOn hf.continuousOn; exact IsBigO.of_bound C (Eventually.of_forall fun i=> (hC _ (mem_univ (k i))).trans_eq (by rw [norm_one,mul_one]))

include hx hr F mn dp H
lemma evaluations (L:(X).Laws F.sector.derivatives ρ) (b:Exterior C.book) (k:V→Ortho) :
    Allowance l r (charge (h+1)) (fun i=> discrepancy S h (x i) (o i) u (Z i) (swung b (k i) (o i)) (turnsPort X (k i) b)) ∧
    Allowance l r (charge (h+1)) (fun i=> discrepancy S h (x i) (o i) (bar ρ u) (S.conj ρ h (Z i)) (swung b (k i) (o i)) (turnsPort X (k i) b)) := by
  let y i:= swung b (k i) (o i); let w i:=turnsPort X (k i) b; let ζ:=fun (_:V)=> (none: Viewers F)
  obtain ⟨a,ha,e⟩:= solid b
  have hk : ∀ᶠ i in l,ClearOf (o i) (y i) a := Eventually.of_forall fun i=> e _ _
  have hw (j): Allowance l r (fun i=>1) (fun i=> w i j) :=
    Allowance.covers (landed k _ (L.spin (expo b j) (Orbits.fields S b j)))
  have hz (j) : Allowance l r (fun i=>1) (fun i=>bar ρ (w i) j) := Allowance.linear (LinearMap.toContinuousLinearMap (conjugateR ρ (expo b j))) (hw j)
  refine ⟨traces F mn dp H u h hr hx ha hk ζ w hw,(traces F mn dp H u h hr hx ha hk ζ (fun i=>bar ρ (w i)) hz).travels ?_⟩
  have hi:= (purchased F mn dp H u h hr hx ha hk (fields S b) ζ).2
  refine IsBigO.of_bound' ?_; filter_upwards [hi] with i ⟨ho,hz⟩; refine le_of_eq (Eq.trans (b:= ‖star (discrepancy S h (x i) (o i) u (Z i) (y i) (bar ρ (w i)))‖) ?_ (norm_star _))
  apply congr_arg norm; rw [discrepancy,discrepancy,star_sub]
  change _ - (Orbits.whole S (sole _) _ (y i) (w i)) = _ - star (Orbits.whole S (sole _) _ _ (bar _ (w i)))
  have hw := whole_bar (v:=u) (w:=bar ρ (w i)) ρ F.room.kernel ho
  have ht:= whole_bar (v:= fun _=> Z i) (w:=bar ρ (w i)) ρ F.room.kernel hz
  rw [bar_bar] at ht; rw [← hw,bar_bar]; exact congr_arg (_-·) (show _=_ from ht)
end YM.OPE.Flash259HorizonFork
