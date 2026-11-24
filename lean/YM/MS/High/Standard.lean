import YM.MS.High.Adjust
/-!
# The all-order Taylor part of the regulator comparison

This theorem doesn't use equality of any two regulators for fields,
limits of any inverse from a regulator, or an (even local counterterm) existence
 without supplying specific elementary data. The assumptions needed here are
 on the two high-mode flows (including master identities) and concrete local
 tables. They are standing arguments for these helper results, not assumptions on
 `G` and not available without the construction and the D-continuation proof.
 For positions use them before multiple-mark and finite-period calculations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm Color Local.Physical Knobs
open scoped Topology ContDiff
variable {G: Gauge} {U:ℕ→Type} {k: Knobs U G}

-- location of Y at all times n. Only concrete real scalar choices polyn in logμ. The `Move` sign is minus.
structure Tuning (k : Knobs U G) (F : Recount G) (v: Law G): Prop where
    commute (P): Spheres wave (spaceL G) (k.wake P) (k.wake P) ((2:ℂ)⁻¹) 1 true
    rates (P): Rising true (k.wake P)
    stamp : ∃ w₀:ℝ, w₀≠0 ∧ Class v 4 ∧ ∀ i j k, Mark.token v i j k=(Mark.LieColor i j k:ℂ)*(w₀:ℂ)
    leads (P): ∀ x w, net w=0→ List.length w=3 → ∀ j:ℕ, fieldDim wfield w+j≤4→ torch j (k.wake P 1 x) w=torch j (F 1 x) w
    -- offered changes in the bare definitions, at n for rank 2 and n>=2 for rank3. Only need jets here.
    scale (n:ℕ) (h:1≤n) (p q:ℝ→ℝ) (hp: Ready p) (hq: Ready q) (P): ∃ Q,Move true k P Q n 2 4 (fun i=>ranktwo (p i) (q i))
    jump (n:ℕ) (h:1<n) (p:ℝ→ℝ) (hp: Ready p) (P): ∃ Q,Move true k P Q n 3 4 (fun i=>(p i:ℂ) • v)
structure Disc (b:Bool) (d:ℕ) (B F:Recount G) (C:ℂ) (h:ℤ): Prop where
    master : Spheres id (spaceD G) B F C d b
    good : Good b G h F
    open' : Rising b F
-- instantiate action.
theorem action {F: Recount G} (H:G.Simple) (D:Disc true 1 F F ((2:ℂ)⁻¹) 4) {v: Law G} (L:Tuning k F v) (p:Code U) : ∃ P, Fixed (k.wake P) F true 4 1 := by
   refine assigned L.commute D.master D.good L.rates D.open' ?_ (by norm_num) ?_ p
   · intro X n hn hp i hi s; rw [paths,Finset.mem_Ico] at hi; exact hp _ (by omega) (by omega) _ (fun _=> Nat.succ_pos _)
   intro n hn r hr u hu hux X EE HE
   let M:= k.wake X n-F n; let V := slice M true r u
   have hz := advanced (L.commute X) D.master hn hr EE
   have hp : Ready V:= slice_ready hz hux (Ready.sub ((L.commute X).poly n) (D.master.poly n))
   have hv (i:ℝ) : Class (V i) u:= {
      solid:= slice_solid hz hux fun t=> ((L.commute X).trueC n t).sub (D.master.trueC n t)
      graded:= slice_form hz hux
      signed:= slice_signed hz hux fun t=> SignedScope.sub ((L.commute X).reflects n t rfl) (D.master.reflects n t rfl)
      closed:= fun w hw=> closes (L.commute X) D.master D.good hn hr EE hux HE i w (fun _=>hw) }
   have h0 : 0<r:=hr rfl
   rcases lt_or_eq_of_le hux with h1|h1; exact ⟨X, Move.refl V fun i w hw hp=> lower_at H h1 (hv i) (hw rfl) (by omega)⟩
   subst u; rcases lt_or_ge r 4 with h1|h1; swap
   · exact ⟨X,Move.refl V (fun i w hw hx=> large_class (hv i) (le_refl 4) r h1 w (hw rfl) hx)⟩
   rcases (show r=1 ∨ r=2 ∨ r=3 from by omega) with hr1|hr1|hr1 <;> subst r
   · refine ⟨X,Move.refl V ?_⟩; intro i w hw h; obtain ⟨j,rfl⟩:=List.length_eq_one_iff.mp h; exact (hv i).single H j (hw rfl)
   · obtain ⟨p,q,hp,hq,H⟩:= pair_inter H hp hv; obtain ⟨Z,hZ⟩:= L.scale n hn p q hp hq X; exact ⟨Z,hZ.replace fun i w hw hx=> H i w (hw rfl) hx⟩
   obtain ⟨w,hw,hC,hx⟩:= L.stamp; rcases eq_or_ne n 1 with he|he
   · subst n; exact ⟨X,Move.refl V (fun i w hw h=> zero_triple_born (le_refl 4) (L.commute X) F D.master (L.leads X) i w (hw rfl) h)⟩
   obtain ⟨p,hp,he'⟩:= cube_inter H hC hw hx hp hv; obtain ⟨Z,hZ⟩:= L.jump n (by omega) p hp X; exact ⟨Z,hZ.replace fun i w hw h=> he' i w (hw rfl) h⟩

-- Mark: families per homogeneous marked data incl log polynomials and exacts.
-- `screen_two` later version with prescribed order0, fixed tuning parameters (initial untouched).
structure Marked (k:Knobs U G) (B:Recount G) (C:Deck G) (d:ℤ): Prop where
   law (P): Spheres wave (spaceL G) B (k.wake P) 1 0 false
   occurs (P): Rising false (k.wake P)
   moves (P) (n r) (v:ℤ) (h:0≤ v) (ht:v ≤ d) p q (hp:Ready p) (hq:Ready q)
         (hc : ∀ i,p i∈C.carries v r) (hd:∀ i,q i∈ Lease G (v-1) r (-1)): ∃ Q, Move false k P Q n r v (fun i=> p i+natQ (q i))

theorem mark {F B H:Recount G} {C:Deck G} {v:ℤ} (h:Fixed B H true 4 1) (D:Disc false 0 H F 1 v) (hv:0≤v) (H': Marked k B C v) (p:Code U) : ∃ P, Fixed (k.wake P) F false v 0:= by
   refine assigned (B:= fun _=>B) H'.law D.master D.good H'.occurs D.open' ?_ hv ?_ p
   · intro X n hx hv i hi s; rw [paths, Finset.mem_Ico] at hi; exact h _ (by omega) _ (fun _=> Nat.succ_pos _)
   intro n hn r hr u hu hux X EE HE
   let M:= k.wake X n-F n; let V := slice M false r u
   have hz := advanced (H'.law X) D.master hn hr EE
   have hp : Ready V:= slice_ready hz hux (Ready.sub ((H'.law X).poly n) (D.master.poly n))
   have hv (i:ℝ) : V i∈ Lease G u r 0:= lease_one.mpr ⟨slice_solid hz hux fun t=> ((H'.law X).trueC n t).sub (D.master.trueC n t),slice_form hz hux,rank_slice⟩
   have hx (i:ℝ) : natQ (V i)=0:= funext fun j=> closes (H'.law X) D.master D.good hn hr EE hux HE i j (fun v=>Bool.noConfusion v)
   obtain ⟨p,q,hp,hq,hu',hv,h'⟩:= mark_inter hp hv hx C
   obtain ⟨Z,hZ⟩:= H'.moves X n r u hu hux p q hp hq hu' hv; exact ⟨Z,hZ.replace fun i w hw hi=> congr_fun (congr_fun h' i) w⟩
end YM.MS.High
