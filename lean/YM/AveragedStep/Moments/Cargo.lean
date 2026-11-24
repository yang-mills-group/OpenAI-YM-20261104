import YM.AveragedStep.Moments.Raw
import YM.AveragedStep.Stokes.Larger
/-! # Uniform cost of coarse plaquettes under the real Wilson push at
the cutoff. Implicit constants can depend on the Patch & exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice Wilson RG MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}{τ:ℝ}

lemma list_asFin {ι:Type*}(z:ι→ℝ)(l:List ι): (l.map z).sum = ∑ i:Fin l.length,z (l.get i):=by
  rw [show (l.map z)= List.ofFn (z ∘ (List.get l)) from ?_,List.sum_ofFn]; rfl
  rw [← List.map_ofFn,List.ofFn_get]
lemma ranked_list (hb:S.patch.Branches S.kernel G) {m:ℕ}(hm:m≠0) {ι:Type*}(l:List ι)(z:ι→Query S G)(C:ℝ)
    (H:∀ i, Ranked τ (z i) m C) : Ranked τ (fun i x=> (l.map fun k=>z k i x).sum) m
       ((l.length:ℝ)^m*((l.length:ℝ)*C)):=by
  simp_rw [list_asFin]; simpa using Ranked.sum hb Finset.univ (fun j:Fin l.length=>z (l.get j)) (fun _=>C) (fun j _ => H _) hm

lemma scaled_bill (p : Config G f)(l:List (Face (Per f))) : τ*Loops.bill p l=(l.map fun i=> τ*G.chord (faceValue p i)).sum:=by simp_rw [Loops.bill,list_asFin,Finset.mul_sum]
lemma ranked_plus (hb:S.patch.Branches S.kernel G){m:ℕ}(hm:m≠0) {q r:Query S G}{B C:ℝ}(h:Ranked τ q m B)(he:Ranked τ r m C):
    Ranked τ (q+r) m (2^m*(B+C)):=by
  let Q: Bool→Query S G:= fun b=>cond b r q; let P:Bool→ℝ:=fun b=>cond b C B
  have hh:=Ranked.sum (τ:=τ) hb (Finset.univ : Finset Bool) Q P
     (fun (i:Bool) _=> by cases i <;> first|exact h|exact he) hm
  change Ranked τ (fun i x=>q i x+r i x) m (2^m*(B+C))
  simpa only [Fintype.sum_bool,Q,P,Bool.cond_true,Bool.cond_false,add_comm (r _ _),add_comm C,
    Finset.card_univ,Fintype.card_bool,Nat.cast_ofNat] using hh

-- one finite list of noise links along any given coarse path
abbrev touched {R:Type*}[AddCommGroup R][One R](x:Four R): Walk→List (Edge (Four R))
 | []=>[]
 | a::w=> a.used x :: touched (x+a.vec) w
lemma touched_length {R:Type*}[AddCommGroup R][One R](x:Four R)(w:Walk):
    List.length (touched x w) = w.length:=by induction w generalizing x <;> simp_all [touched]
lemma compare_tracks(U Q:Config G c)(x:Site c)(w:Walk): G.chord (travel U x w*(travel Q x w)⁻¹) ≤
    ((touched x w).map fun e=> G.chord (U e*(Q e)⁻¹)).sum:=by
  induction w generalizing x with
  | nil=>simp [travel,touched]
  | cons a w ih=>
    have he : G.chord (a.read U x*(a.read Q x)⁻¹)=G.chord (U (a.used x)*(Q (a.used x))⁻¹):=by
      unfold Step.read; split; apply Loops.chord_inv_pair
      rfl
    change G.chord (_ * _) ≤ G.chord _ + _
    rw [travel,travel]; exact (Loops.chord_prod ..).trans (add_le_add he.le (ih _))

def cargo {c f:Side}(S:StepData c f)(τ:ℝ)(p:Face (Per c)):Query S G := fun _ x=> τ*G.chord (faceValue x.2 p)
lemma cargo_admit {τ:ℝ}{p:Face (Per c)}:Admits (cargo (G:=G) S τ p):=fun _=>env_continuous
  (continuous_const.mul (G.continuous_chord.comp ((continuous_travel ..).comp continuous_snd)))
lemma cargo_positive {τ:ℝ}(h:0≤τ){p:Face (Per c)}(i:S.Choices)(x:Board G c f):0 ≤ cargo S τ p i x:=
  mul_nonneg h (G.chord_nonneg _)
set_option synthInstance.maxHeartbeats 80000 in
lemma cargo_price (G:Gauge)(P:Patch)(K:KernelChoices)(h:P.Branches K G)(d:ℕ):
    ∃ C:ℝ,0≤C ∧ ∀ᶠ τ:ℝ in atTop,∀ (c f:Side)(S:StepData c f),S.patch=P→S.kernel=K→
      4∣f.val → ∀ p:Face (Per c), Ranked τ (cargo S (G:=G) τ p) d (C*lag τ ^d):=by
  by_cases hd:d=0
  · subst d
    refine ⟨1,zero_le_one,Eventually.of_forall (fun τ c f S hs hk _ _=> ?_)⟩
    simpa only [pow_zero,mul_one] using Ranked.zero (τ:=τ) (by rw [hs,hk]; exact h) cargo_admit
  obtain ⟨D,hD,m,H⟩:= Loops.plaquette_prediction h
  obtain ⟨B,hB,hb⟩:= face_paid G d
  obtain ⟨A,hA,hA'⟩:= noise_paid G K d
  let C:=2^d*(4^d*(4*A)+D^d*((m:ℝ)^d*(m*B)))
  refine ⟨C,by unfold C; positivity,?_⟩
  filter_upwards [hA',eventually_ge_atTop (1:ℝ)] with τ HA hτ c f S hp hk hF p
  have he:=H c f S hp hk p
  have hS : S.patch.Branches S.kernel G:=by rw [hp,hk]; exact h
  obtain ⟨l,hl,Hl⟩:= he
  let w:=square p.2.val.1 p.2.val.2; let T:=touched p.1 w
  have ht:T.length=4:=(touched_length p.1 w).trans rfl
  let N (i:S.Choices)(x:Board G c f):ℝ:=(T.map fun e=>scaledNoise S τ e i x).sum
  let F (i:S.Choices)(x:Board G c f):ℝ:=(l.map fun e=>scaledFace G S τ e i x).sum
  have hx(e:Face (Per f)): Ranked τ (scaledFace G S τ e) d (B*lag τ^d) := by
    refine ⟨face_admits G S τ e,?_⟩; simp_rw [abs_of_nonneg (scaledFace_pos _ _ (zero_le_one.trans hτ) _ _ _)] -- args?
    exact hb τ hτ _ _ S hS hF e
  have hg(e:Edge (Site c)): Ranked τ (scaledNoise S (G:=G) τ e) d A := by
    refine ⟨noise_admits S τ e hS,?_⟩; simp_rw [abs_of_nonneg (scaledNoise_pos S (zero_le_one.trans hτ) _ _ (_:Board G c f))]
    exact HA S hk hS e
  let q:=cargo S (G:=G) τ p
  let Z:Query S G:=N+(D • F:Query S G)
  apply Ranked.enlarge (C:=2^d*((T.length:ℝ)^d*(T.length*A)+ |D|^d*((l.length:ℝ)^d*(l.length*(B*lag τ^d)))))
  · apply Ranked.below (q:=Z) hS cargo_admit (ranked_plus hS hd (ranked_list hS hd T _ _ hg) ((ranked_list hS hd l _ _ hx).scale D))
    intro i x _
    have hi (e):0 ≤ scaledNoise S τ e i x:= scaledNoise_pos S (zero_le_one.trans hτ) _ _ _
    let Q:= S.prediction x.1 i; let y:=faceValue x.2 p; let z:=faceValue Q p
    change |τ*G.chord y| ≤ |N i x+D*F i x|
    apply (le_abs_self _) |>.trans'
    rw [abs_of_nonneg (mul_nonneg (zero_le_one.trans hτ) (G.chord_nonneg _)),show y=(y*z⁻¹)*z by group]
    apply (mul_le_mul_of_nonneg_left (G.chord_triangle _ _) (zero_le_one.trans hτ)).trans
    rw [mul_add]
    apply add_le_add
    · apply (mul_le_mul_of_nonneg_left (compare_tracks x.2 Q p.1 w) (zero_le_one.trans hτ)).trans_eq
      simp_rw [N,T,list_asFin,Finset.mul_sum,Q,scaledNoise]
    apply (mul_le_mul_of_nonneg_left (Hl _ i) (zero_le_one.trans hτ)).trans_eq
    rw [mul_left_comm, scaled_bill]; rfl
  rw [ht,abs_of_nonneg hD]; norm_num1 -- cleans 4
  have hL : 1 ≤ lag τ:=lag_ge hτ
  have hh:(l.length:ℝ) ≤ (m:ℝ):=by exact_mod_cast hl
  unfold C
  rw [mul_assoc,add_mul, mul_assoc (D^d), mul_assoc ((m:ℝ)^d),mul_assoc (m:ℝ)]
  gcongr (?_^d * (?_ + (D ^ d * (?_ * (?_ * _))))); exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)
  gcongr
end YM.AveragedStep
