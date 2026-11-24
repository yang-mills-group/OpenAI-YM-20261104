import YM.MS.Vista.Summer
/-!
# Completing geometry.Horizon.B Lighting from n/16 clearance. User can pick centered reps.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{I A':Type}{M:Visa I}{K:Belt I}{b:Bool}
    {L:I→Side}{A B:I→ Cover}
local notation "Φ"=> Ap K (tickA L)
local notation "Ϝ"=> enterV L b
lemma centered_size (X:I→Cover)(L:I→Side)(h:∀ i,X i=Lattice.lift ( wrap (L i) (X i) )): Quota L X:= by
   refine ⟨1,zero_lt_one,fun i=>?_⟩; nth_rw 1 [h]; rw [budget_geom,one_mul]; obtain he:= sizeX (wrap ( L i ) ( X i )); exact_mod_cast (show pdist ( wrap (L i) (X i)) ≤ (L i).val from by omega) -- Occ.
lemma Fixed_paid (k:Half): width L (loci ( enterV L b ) k):= centered_size _ _ (fun i=> by simp [ loci, Tloc,enterV,dimT ])
lemma net_quota (hx:width L A)(he:width L B): Mileage K.price ( Ap K ( A-B ) ) Φ:= by
    obtain ⟨h,h0,hx⟩:= hx; obtain ⟨U,hU,h⟩:= he; refine ⟨ _,add_pos h0 hU,0,fun i=>?_⟩; change ‖embed ( A i.1-B i.1 )‖ ≤ _; rw [emb_sub]; refine ( norm_sub_le .. )|>.trans ( (add_le_add (hx _) (h _)) |>.trans_eq ?_ ); unfold Ap tickA; rw [pow_zero,mul_one,add_mul ]
lemma Act_p (h:∀ i:K.time,K.price.length i ≤ Ap K (tickA L) i)(hf:width L A)(hp:width L B)(hx:∀ b:Bool,∀ i,mine (dimT L i) (wrap (dimT L i) ( env b A B i ))) : TPaid K (μF K L) Φ A B:= ⟨ h,fun b=> radar (L:=Miles K L) K.price h (fun i=> hx b i.1), net_quota hf hp ⟩
lemma adjacent (L:I→ Side)(i:I)(p:Half): wrap (dimT L i) ( loci (enterV L b) p i )=thin (L i) p:= wrap_lift _
lemma ω_n (P:Lattice.Side)(x:Cover): wrap P (taste b x)= if b then wrap P x else - wrap P x:= by cases b; exact map_neg ( wrap P ) _; rfl
lemma away_core (h: Clearance L A)(p:Half) (c:Bool) (i:I): mine ( dimT L i ) ( wrap (dimT L i) ( env c (loci Ϝ p) A i )):= by
    simp_rw [env,Dph,map_add,adjacent,ω_n]; cases c; · rw [ if_neg (by decide :¬false=true), ← sub_eq_add_neg ]; exact (mine_sym ..)|>.mpr ( h i p ) -- add_neg rap.Defeq need convert
    rw [if_pos rfl,add_comm,mine1 _ _]; exact h i p
lemma block_core (p q:Half)(h:p≠q)(c:Bool)(i:I): mine (dimT L i ) (wrap (dimT L i) (env c (loci Ϝ p) (loci Ϝ q) i)):= by
    simp_rw [env,Dph,map_add,ω_n,adjacent ]; cases c; · simp only [Bool.false_eq_true,↓reduceIte,← sub_eq_add_neg]; exact δ_side p q h
    rw [if_pos rfl,mine1 _ _ ]; exact δ_side p q h
lemma campZ (h:∀ i:K.time,K.price.length i ≤ Φ i)(hv:width L A)(hx: Clearance L A): Width K L Ϝ A:= ⟨fun i=> Act_p h (Fixed_paid i) hv (away_core hx i), fun i j hi=> Act_p h ( Fixed_paid i ) ( Fixed_paid j) (block_core i j hi) ⟩ -- resolve
lemma repHero (hp:Clearance L A)(V:Visa I): RepT V L A:= by
   let K:= Mid V L; refine ⟨radar (L:=Miles K L) K.price (fun i=> astral i ) ?_ ⟩; intro i; have h w:= hp i.1 w; refine ?_; unfold Miles dimT; rw [Ap,Vary, map_add ]; exact mine2 _ h
lemma Sedona (hp:Clearance L A)(he:width L A) (V:Visa I): Place V L b A:={ mind := campZ (fun i=> astral i) he hp, after:=campZ (fun i=> (afterM i).le ) he hp, center:=repHero hp V }
end YM.MS.Vista
