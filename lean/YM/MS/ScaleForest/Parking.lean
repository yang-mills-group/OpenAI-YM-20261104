import YM.MS.ScaleForest.Tally
import YM.MS.ScaleForest.TwoVertices
/-!
# Weight-zero within the single-port convergence

A vacancy may BE a reported coefficient (not zeroing out all rank zero).
But when h=0 establish the `parked` rank-zero/vanishing
criterion (`Vacancy`). Also show for the quotient
germ itself, so we can keep poles in the regulator integration across the
rest of a graph.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {h k n:ℕ} {b : Bool} {R: Result G} {F H X Y : Flats G} {p : ℤ}

def parked (p:ℤ)(F:Flats G): Prop:= ∃ V: Mob G, Form0 false V∧Goods 0 V∧ Goods p V∧ Pact F (collapsed (fun _=>V))
lemma park_z (hm : Pact F 0) (p:ℤ) : parked p F := ⟨0,Form0.zero,(good 0 G).zero_mem,(good p G).zero_mem,fun i=> by simpa only [collapsed,show (fun _ : ℂ=> (0:Mob G))=0 from rfl, Finsupp.single_zero] using hm i⟩
lemma park_visit (V:LocalVertex G b 0) : parked V.rank (collapsed (fun _=> V.symbol)) := by
   have hc : Moony false ((instructions (vertex V)).renorm) := all0 (clockMoon (vertex V).accepted.usable.clock)
   have hm : Form0 false V.symbol:= by rw [renorm_vertex] at hc; obtain hp:= sunny (hc 0); simpa only [collapsed,Finsupp.single_eq_same] using hp.exists.choose_spec
   refine ⟨V.symbol, hm,fun m l h=>?_,V.slots,same_pact _⟩
   rw [mod_int] at h; have hv:= massive (ray l); rw [mass,ray_dim] at hv;
   rw [V.scaling.complete hm.price]; apply t_exc; simpa only [Nat.cast_zero,mass] using (by rw [ray_len] at hv; omega: (0:ℤ)<fieldDim wfield l)

variable (K:LineRule G) (ht:parked p F)
include ht

private theorem mark_stay_ready : Moony false F := by
   obtain ⟨V,hV,h,hP,hQ⟩:= ht; have hp: Sun false (fun _=> V):= ⟨ mer.uLive (Live.stays hV.price), Eventually.of_forall fun _=> hV.token⟩; exact fun i=> by
      obtain he:=Sun.HeapS.single hp 0 i; exact he.congr ((hQ i).symm)

theorem fails_u : Pact (closePages K.half F) 0:= by
   obtain hm:= mark_stay_ready ht; obtain ⟨V,hV,h,hP,hQ⟩:= ht; let L:= collapsed (fun _=> V);
   have hl : Moony false L:= mark_stay_ready (F:=L) (p:=p) ⟨V,hV,h,hP,same_pact L⟩; refine pact_comp (closePages_congr K.ok hm hl hQ) ?_; intro i
   filter_upwards [Shine.high0] with x hx;  unfold L; rw [close_single]; rw [Finsupp.single_apply]; split; · exact empty_close h x hV (K.ok.forms _) hx 0
   rfl

theorem fails_b (X : Flats G) (b:Bool): Pact (connect b K X F) 0:= by
   obtain ⟨V,hV,h,hP,hQ⟩:= ht; unfold connect; have h: bridgePages K.half X (collapsed (fun _=>V))=0:= by
      unfold bridgePages; refine Finset.sum_eq_zero (f:=fun i:ℕ=> (collapsed (fun _=>V)).sum (fun n y => Finsupp.single (n+i) (fun z:ℂ=> bridgeG K.half (X i z) (y z)))) ?_
      intro m hm
      rw [Finsupp.sum_single_index];
      · exact ( congr_arg (Finsupp.single (0+m)) (funext (fun z=> emptyBridge h)) ).trans (Finsupp.single_zero _)
      simp_rw [ Pi.zero_apply, bridgeG_eq K.ok.rev, ← schedule, map_zero ]; exact Finsupp.single_zero ..
   obtain hf := bridgePages_congr K.ok (same_pact X) hQ; rw [h] at hf
   convert! pact_scaled hf (factor b : ℂ) using 1; simp

omit ht
private theorem stalling {X : GraphSum G b h} (hp : Pact X.instructions.force 0) (hx : X.instructions.classicalTerm=0) :
    X.instructions.pole=0∧ Pact X.instructions.renorm 0 := by
   obtain ht:= X.accepted.after; rw [hx] at ht; exact (uniqueK ht Joint.zero (pact_sym hp) EventuallyEq.rfl).symm

theorem Vacancy (X : GraphSum G b h) (hx:h=0) : parked X.slots X.instructions.renorm ∧ ∀ u∈X.quotients, parked X.slots u := by
   induction X with
   | vertex V=> subst_vars; exact ⟨ by rw [renorm_vertex]; exact park_visit V,fun u hu=> (by simp only [quotients,List.mem_singleton] at hu; rw [hu]; exact park_visit V)⟩
   | @loop b h K X ih=>
      obtain ⟨hp,hh⟩:=ih hx; let T:=loop K X; obtain ⟨hU,hV⟩:= stalling (X:=T) (fails_u K hp) rfl; refine ⟨ park_z hV _,fun u hu=> ?_ ⟩;
      rw [quotients,List.mem_cons,List.mem_map] at hu; rcases hu with rfl|⟨v,hv,rfl⟩
      · unfold T at hU; rw [hU]; exact park_z (by rw [collapsed,Finsupp.single_zero]; exact same_pact _) _
      apply park_z; convert! integratePages_congr h (fails_u K (hh v hv)) using 1
   | @bridge b h K X Y ih it=>
      obtain ⟨hp,hh⟩:= it hx; let T:=bridge K X Y; obtain ⟨hU,hV⟩:= stalling (X:=T) (fails_b K hp _ b) rfl; refine ⟨ park_z hV _,fun u hu=> ?_ ⟩; rw [quotients,List.mem_cons] at hu; rcases hu with rfl|hu
      · unfold T at hU; rw [hU]; exact park_z (by rw [collapsed,Finsupp.single_zero]; exact same_pact _) _
      obtain ⟨i,hi,H⟩:= List.mem_flatMap.mp hu; obtain ⟨v,hv,rfl⟩:= List.mem_map.mp H; apply park_z; convert! integratePages_congr h (fails_b K (hh v hv) _ b) using 1

lemma quotientRank (X : GraphSum G b h) : ∀ u∈ X.quotients, OfRank X.slots u:= by
   induction X with
   | vertex V=> intro u h; simp only [quotients,List.mem_singleton] at h; rw [h]; exact collapse_rank (Eventually.of_forall fun _=> V.slots)
   | @loop b h K X ih=>
      intro u hu; rw [quotients,List.mem_cons,List.mem_map] at hu; rcases hu with rfl|⟨v,hv,rfl⟩
      · exact collapse_rank (Eventually.of_forall (loop K X).accepted.legs_ct)
      obtain ⟨f,hf⟩:= X.quotient_valid v hv; exact integrate_rank (Sewable.loop hf.clock h K.ok) (loop_rank (ih v hv) hf.clock K.ok)
   | @bridge b h K X Y ih it=>
      intro u hu; rw [quotients,List.mem_cons] at hu; rcases hu with rfl|hu
      · exact collapse_rank (Eventually.of_forall (bridge K X Y).accepted.legs_ct)
      obtain ⟨x,hx,hu⟩:= List.mem_flatMap.mp hu; obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hu
      exact integrate_rank (connect_sewable (X.quotient_valid x hx).choose_spec (Y.quotient_valid y hy).choose_spec K)
         ((bridge_rank (ih x hx) (it y hy) K.ok).realScale (factor b))
end YM.MS.ScaleForest
