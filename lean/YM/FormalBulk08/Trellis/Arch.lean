import YM.FormalBulk08.Trellis.Ferment
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Trellis
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X I:Type}{W:Lab G K I}{ρ:ChartRatio G}{E e r d D R:ℕ}{o:Loc G 1}{F:Frame G d}{H:Hol G}{T:SectionData F}
-- price submoves any direction endpoint. For interior measuring split (not needed) allow telescope via supplied ratios Priced etc.
variable (q:Quota F H W o D E R)(u:Use W ρ E)(h: LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤ R)
variable {τ:Time X}{s:X→ℕ}(P:Dove.Lab.Voyage W s) (f l:X→ℕ)(hf:∀ i,(P.bed i).b ≤ f i) (hp:∀ i, f i+l i ≤ (P.bed i).b+s i)
   (w:Soft τ (fun i=>(chron _).day (P.bed i))) (hz:Soft τ (fun i=>sowing (W.V (P.bed i).a).S (P.bed i).b ((P.bed i).b+s i)))
open Dove.Lab.Voyage
include q u h a hs ht hb hr hf hp w hz
lemma chiro (p: X→ℕ)(he:(∀ i,p i=(P.bed i).b) ∨(∀ i,p i=(P.bed i).b+s i)):
    let A:= spine P ρ a P.summit; let B:= spine P ρ a P.top
    let Q:=fun i=>bornM (ρ:=ρ) (W:=W) (T:=T) a q.horizon (P.bed i).a (P.summit i)
    let S:=fun i=>bornM (ρ:=ρ) (W:=W) (T:=T) a q.horizon (P.bed i).a (P.top i)
    ∀ (x y:Letter F), Priced (tbook τ l) (fun i=> Dend P i.z) (fun i=> ropes (A i.z) (Q i.z) (p i.z) (f i.z) i.i x y) (fun i=>ropes (B i.z) (S i.z) (p i.z) (f i.z) i.i x y) E:= by
    intro A B Q S; obtain ⟨pS,qS⟩:=kingdom P u h a hs w hz
    obtain ⟨D,X,Y⟩:= runway u P τ w hz
    have hU i:l i ≤ s i:=by have hh:=hf i;have ht:=hp i;omega
    have hhSoft:= D.below (g:=fun i=>(l i:ℝ)) (fun i=> by rw [Nat.abs_cast,Nat.abs_cast]; exact_mod_cast hU i)
    let v(i:Dove.Walk l):= (f i.z+i.i); let M(i:Dove.Walk l):= (P.bed i.z).b
    have hv i : M i ≤ v i:= (hf i.z).trans (Nat.le_add_right ..)
    have hh i: v i < M i + s i.z:= (Nat.add_lt_add_left i.away (f i.z)).trans_le (hp i.z)
    let g(i:Dove.Walk l): Dove.Walk s:=⟨i.z,v i-M i,(by have :=hv i; have :=hh i;omega)⟩; have hD i:0≤ Dend P i:=(ratioR_pos ..).le; have hG i: v i= (P.bed (g i).z).b + (g i).i := by change v i=M i + (v i - M i); have :=hv i;omega
    have he1 i : (ridge P (g i)).b=v i:=hG i |>.symm
    have hK: Priced (tcash τ l) (fun i=> Dend P i.z) (fun i=> expanse (A i.z) (p i.z) (v i)) (fun i=> expanse (B i.z) (p i.z) (v i)) E:= by
        rcases he with he|he <;> simp_rw [he]
        · intro j hj; have hx(i:Dove.Walk l):=hG i; simp_rw [hG]; exact (pS _ hj).link (fun i=> stubW (g i))
        intro j hj; let D(i:Dove.Walk l):Lengths s:=⟨i.z,M i+s i.z-v i,by have:=hv i; have :=hh i;omega⟩
        have hx i:v i= (P.bed i.z).b+s i.z-(D i).i:= by change _=M i+_-(_-_); have := hh i;omega
        simp_rw [hx]; exact (qS _ hj).link D
    have hb' i: spinR targetPower (ridge P (g i)) ≤ Dend P i.z:= ratio_test P _ _ (Nat.le_add_right ..) (Nat.add_lt_add_left (g i).away _)
    have hp(x y:Letter F) : Priced (tcash τ l) (fun i=> Dend P i.z) (fun i=> (flow (A i.z) (p i.z) (v i)) ((Q i.z (v i))⁻¹ x y)) (fun i=> (flow (B i.z) (p i.z) (v i)) ((S i.z (v i))⁻¹ x y)) E := by
        refine priced_flow (T:=fun i:Dove.Walk l=> (Q i.z (v i))⁻¹ x y) ?_ hK
        intro j hj; have he:=Pact_lift (g:=fun i:Dove.Walk l=>ridge P (g i)) (X.reach g) (runwayBack q u h a hs ht hb hr x y j hj) hb'
        -- y.Born definitional with transport
        simp_rw [hG]; exact he
    let R (i:Dove.Walk l):= ridge P (g i)
    let μ i (j:ℕ)(w:Letter F):= (heightK (((W.V (P.bed i).a).S).block (f i+j)) d (Pose.weight F w))⁻¹
    have H (i:Dove.Walk l) : Found (slots F) (Pose.weight F) (Matrix.map ((Q i.z (v i))⁻¹) (flow (A i.z) (p i.z) (v i))) (μ i.z i.i) := by
        refine pours (primes (h:=down ?_)) (A i.z) _ _; apply (mat_begins a h q hs ht hb _ _ _ ((P.bed i.z).zone.trans (hv i)) ((hh i).trans_le (P.high _))).1
    have H2 (i:Dove.Walk l): Found (slots F) (Pose.weight F) (((S i.z (v i))⁻¹).map (flow (B i.z) (p i.z) (v i))) (μ i.z i.i):= by refine pours (primes (down ?_)) _ _ _; exact (mat_begins a h q hs ht hb _ _ _ ((P.bed i.z).zone.trans (hv i)) (((hh i).trans_le (P.high _)).trans_le (P.extra _))).1
    intro x y; exact riders (Q:=fun i j=>((Q i (f i+j))⁻¹).map (flow (A i) (p i) (f i+j))) (Z:=fun i j=>((S i (f i+j))⁻¹).map (flow (B i) (p i) (f i+j))) H H2 (fun i j=> inv_le_one_of_one_le₀ (crown_weight _ j)) hp (fun x y=>Priced.constant _ _ ((1:Pennants (Letter F)) x y) E) hhSoft hD x y
end YM.FormalBulk08.Trellis
