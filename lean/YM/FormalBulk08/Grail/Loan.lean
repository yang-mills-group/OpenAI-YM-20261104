import YM.FormalBulk08.Grail.Bend

/-! Prefix estimate on lower formal grades of a single profile.
No power penalties until actual window, numeric score use only fixed d/e.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Tensor
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{l n D d m e r :ℕ}{A B η θ σ : ℝ}{o:Loc G 1}{Y: Anthem D G} {F: Frame G d}

/-- q measures annihilated/paid weights STRICTLY below q. Thus the
marginal diagonal uses q=weight while for an irrelevant perturbation use d+1. -/
def Bonds (F:Labels.Frame G d) (a:Loc G 1)(η:ℝ)(q e r:ℕ)(Y:Anthem D G)(B:ℝ):Prop:=
    0≤B ∧ (∀ v, Torrid (Y v e r) η (B*‖v‖) a) ∧ ∀ v:Letter F, Pose.slots F v=r → Pose.weight F v<q → ‖pearlJ F (Y (inside F v D) e r) (mint F v)‖ ≤ B

def Deposit (a:Loc G 1)(σ:ℝ)(Y:Anthem D G)(e:ℕ)(B:ℝ) :=0≤B ∧ ∀ j<e,∀ (r:ℕ) p, Knoxville (fame _) σ (0,a) (Y p j r) (B*‖p‖)

lemma shells (Y:Anthem D G)(h:Clef o Y l)(p): Authorized (Y p):= by
    let f := Kemp.banner l (Y p)
    refine fun z x i j=> coastal z x i j (Y p) f ?_ (.of_forall fun m=> (solo_iff Y).mp h.ward m p)
    intro i j _; unfold f; simp_rw [badge (Y p) (h.fare.1 _) (h.fare.2.1 _) le_rfl]; obtain ⟨s,C,hs,-,he⟩:=h.fare.2.2 i j; exact (sieve_kalm _ (he p) hs.le).1
lemma victual (F:Labels.Frame G d)(a:Loc G 1)(e r q l D:ℕ)(h:2*η < σ)(hs:0≤η) :∃ C :ℝ,0≤C ∧∀ Y:Anthem D G, Clef a Y l→∀ B:ℝ, Deposit a σ Y e B→ (∀ v:Letter F,Pose.weight F v<q→Pose.slots F v=r→PowerSeries.coeff e (echo F Y v)=0) → Bonds F a η q e r Y (C*B):= by
   have he' : 0<σ:=by linarith
   have hh :∃ A:ℝ,0≤A ∧∀ Y: Anthem D G,Clef a Y l→∀ B:ℝ,Deposit a σ Y e B→∀ p,Torrid (Y p e r) η ((A*B)*‖p‖) a:= by
      cases r with
      | zero=> exact ⟨0,le_rfl,fun _ _ _ _ _ _ he=>by omega⟩
      | succ u=> obtain ⟨A,hA,H⟩:=marker_print a e u h hs; refine ⟨_,hA,fun Y hy B hb p=> ?_⟩; rw [mul_assoc]; exact current.mpr (H (Y p) (shells Y hy p) (hy.fare.2.1 p _ _) _ (mul_nonneg hb.1 (norm_nonneg _)) (fun j hj i ht he=>hb.2 j hj i p))
   choose X hX HX using fun (v:Letter F)(t:ℕ)=> pearl_cost F a v t he'
   let Z(v:Letter F):= ∑ j∈Finset.range r, X v j*‖inside F v D‖
   let C:=∑ v,Z v; have hz v:0≤Z v:= Finset.sum_nonneg (fun j _=> mul_nonneg (hX v j) (norm_nonneg _));
   have hc:0≤ C:= Finset.sum_nonneg (fun i _=>hz i)
   obtain ⟨A,hA,H⟩:=hh; refine ⟨C+A,add_nonneg hc hA,fun Y hy B hB Hk=>⟨mul_nonneg (add_nonneg hc hA) hB.1,fun i=>torrid_mono (H Y hy _ hB i) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hc) hB.1) (norm_nonneg _)),fun v hv hw=>?_⟩⟩
   let p:=inside F v D
   have he:=Hk v hw hv; rw [echoline,hv,Finset.sum_range_succ, Nat.sub_self, if_pos (Nat.zero_le _),Nat.sub_zero] at he
   apply le_trans _ (mul_le_mul_of_nonneg_right (show Z v≤ C+A from (Finset.single_le_sum (fun i _=>hz i) (Finset.mem_univ v)).trans (le_add_of_nonneg_right hA)) hB.1);rw [eq_neg_of_add_eq_zero_right he,norm_neg]; apply (norm_sum_le ..).trans
   unfold Z; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i hi; rw [Finset.mem_range] at hi; split
   next hx=> apply le_trans (HX v i _ _ (hB.2 _ (by omega) i p)) (le_of_eq ?_); ring
   next => rw [norm_zero]; exact mul_nonneg (mul_nonneg (hX ..) (norm_nonneg _)) hB.1

lemma hypotheses (a:Loc G 1)(F: Frame G d) (h q n:ℕ)(he:q≤d+1)(s:Dawn.Seasons)(D l :ℕ)(U: Fin n→Place.Potential G) (r:Fin n→ℕ)(hr:∀ i,0<r i)(hp:(∑ i,r i) + Chapel.upper s <q)(hw:∀ i,U i∈rangeLt (Axis→G.Color) (r i))(H: Source.Hol G)(hs:0<η) :
    ∃ C:ℝ,0≤C ∧ ∀ Y: Anthem D G, Clef a Y l → ∀ B:ℝ, Bonds F a η q h n Y B →∀ A, Knoxville (fame _) η (0,a) (Y (Dawn.cone D s) h n) A →
        ‖tariffs (fun j=> assigns (U j)) (Y (Dawn.cone D s) h n)‖ ≤ C*B:= by
    obtain he' :=(Cases.arity hr).trans (show (∑ i,r i)≤ d by omega)
    let p:= Dawn.cone D s; let c:= q-Chapel.upper s
    -- apply radar width needs Knoxville at η on T: not supplied generally. Can require separately
    obtain ⟨C,hC,hQ⟩:= radar a F n c r U hw (by omega) he' (by unfold c;omega) hs
    let d':=max 1 ‖p‖; have hd: 1≤ d':= le_max_left ..
    refine ⟨C*d',mul_nonneg hC (zero_le_one.trans hd),fun Y hY B hB A hT=>?_⟩ -- require
    let T:= Y p h n; have ht: Monic (slate T d n) := monic_slate a T H hs hT (perfumed Y hY p h n) _ _
    rw [mul_assoc]; refine hQ T (hY.fare.2.1 p h n) ht _ A (mul_nonneg (zero_le_one.trans hd) hB.1) hT (torrid_mono (hB.2.1 p) ?_) (fun i hi hx=>?_)
    · rw [mul_comm _ B]; exact mul_le_mul_of_nonneg_left (le_max_right ..) hB.1
    have hk : Chapel.upper s≤d := by omega
    let j: Letter F := ⟨(i,(⟨s,(Dawn.paper_is _).mpr hk⟩:Dawn.Spring d)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (F.grades i).1+Chapel.upper s≤d from (by unfold c at hi;omega)⟩⟩
    have hz : Pose.weight F j<q := by change (F.grades i).1+ Chapel.upper s< q; unfold c at hi; omega
    exact (hB.2.2 j hx hz).trans (le_mul_of_one_le_left hB.1 hd)
end YM.FormalBulk08.Grail
