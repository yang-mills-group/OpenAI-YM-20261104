import YM.FVA2.O.Dust.Birth
/-!
# Rapidly-decaying estimates on multi-mark connected pieces

`cinder`: keep all chart derivatives in the actual `Nilp` estimate. Applies to
meshes in *unit length* setups and at least two marks (only `Known` required for
fewer). See `O/Dust/Aroma` for corresponding full product bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Cool
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Osc MS.Osc.Snap MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real MS.Tide
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors Fuse Job.Belt
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type} {F H:Glade G I}{U:Planet G I}{z p:I→ QP}{q b:ℤ}{v:ℝ}{u i:ℕ}{P:Geo I}{B:Deck G}{K: Booked B}{M: MS_Data G K}{X:Rake.Dance G I W}
local notation "Qx"=> (east P false)
local notation "m0"=> (fun _:I=>planeF)
local notation "K0"=> Geo.constantP G I (PlanetD G)
lemma cold (h:0<q): Job.Break ( G:=G ) false false (Below P) (stamp (Lower P) q) (stamp (Lower P) q):= by
    obtain hp :0<(q:ℝ):= (by exact_mod_cast h); apply breakWalk ( ΒEast P false ) _ hp; refine ⟨ fun _=>posS _|>.le,1, zero_lt_one,fun p q' hq hz=>?_⟩; simp only [ stamp,Lower,Below,coldE,one_mul, a_e,← Real.exp_add ]; unfold δf; apply le_of_eq; congr 1; change _= -(q:ℝ)*(tstart p - tstart q')+ tstart p*q; ring
lemma dustp (hr:F=river ( sailP m0 K0 F + H ))(he:Nilp P H)(hf: Stroll false ( sailP m0 K0 F+ H ))(hk:collect F) : Nilp P F:= by
    intro k; let q:=max 1 k; let v:= stamp (Lower P) q; have ht : 0<q:= lt_max_of_lt_left (by norm_num); have hp: nn v:= fun _=>posS _|>.le; let S:= (sailP m0 K0 F+H);
    have hF : Dash false (Below P) F S 0:= by have hv:= follows (K:=Below P) (b:=false) (F:=S) (fun _=>rfl); exact (show river S= F from hr.symm ) ▸ hv
    have hV: Safe P F q:= by
       apply marching ( b:=false ) ( c:=false ) ( ΒEast P false ) hp hf hF ( Latch.Lease.zero hp ) (aboveC (Below P) false hk); intro r hv hx E _ _ _ w hw ht'
       obtain ⟨ε,hε,hS⟩:= cold (G:=G) ( P:=P ) ht E w ht' (fun x=>Bool.noConfusion x)
       have hw':Flow (Below P) K0 1 := (masterD G I P).well -- Flow price aliases
       have hz : coinF false ( Below P) S v r:= Lens.plus ( (one_mul v) ▸ penny hx hp hw' (fun i=>zero_le_one) ( Tall (Lower P) 5 (by omega) ) (fun E _=> tom (Lower P) 5 (by omega) ) ) ( pinch ( he q ) hv ); exact ⟨ _, ε, hε,hz E w hw ht',hS ⟩
    exact safe_raise hV ( le_max_right .. )
variable [LinearOrder W]{x:Position W I}{R:W→ Rake.Label B}{s:Finset W}
lemma cinder (hs:P.θ=0) (h:Mesh P x)(hx:DOrd K P M R x X): ∀ n, Known P ( X s n ) ∧ (2≤ s.card → Nilp P (X s n)) := by
    induction s using Finset.strongInductionOn with | _ s ih =>
    by_cases he:s.card≥2; swap
    · intro n; obtain hz|hz:= s.eq_empty_or_nonempty; · rw [hz,hx.1]; exact ⟨ (Nilp.zero (P:=P) (G:=G)).known, fun H=> False.elim (by simp at H)⟩ -- he dependent mismatch
      obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by have hp:= Finset.card_pos.mpr hz; omega); rw [hx.2.1]; exact ⟨ ⟨_,safeM (R i)⟩,fun hx=>False.elim (he hx)⟩
    intro k; induction k using Nat.strong_induction_on with | h k hk=>
    have hp: Nilp P (Src x m0 K0 K0 (approach P M) X s k):= by
        refine Nilp.add (Nilp.sum _ (fun i hi=> Nilp.lonely (( hk i (Finset.mem_Ico.mp hi|>.2)).2 he) )) ( Nilp.sum _ (fun i hi=>Nilp.sum _ (fun j hj=> ?_ )) ); exact regionA hs (Rake.space h hi) ((ih i (n_small hi|>.1 ) j.1).1) (( ih ( s\i ) (n_small hi |>.2.2.2 ) j.2 ).1)
    obtain hY:= hx.2.2 s he k; have hu : Nilp P (X s k) := dustp hY.2.2 hp ( winter ( builder M h R ) hx (Finset.card_pos.mp (show s.card>0 from by omega)) k|>.walk ) hY.1; exact ⟨ hu.known,fun _=>hu⟩
end YM.FVA2.O.Cool
